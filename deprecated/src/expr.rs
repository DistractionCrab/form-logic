/// This module defines the properties for expressions. Expressions come in two
/// flavors: Singular and Sequential. Singular variables represent a single
/// thing, whereas Sequential expressions represent a sequences of possible
/// objects. Sequence expressions have an arity, which represent the lower
/// bound on the number of objects that can substituted into the sequence;
/// This bound is never 0, and subtituting fewer than the arity is not
/// permitted.

use std::ops::Sub;
use std::borrow::Borrow;
use std::convert::Into;

use knowledge_base as kbase;
use subst;
use formula;

use self::kbase::ContextBase;
use subst::Info as SInfo;
use formed::Info as FInfo;
use Ptr;

/// Type representing the identifier for composite expressions.
pub type CompName = String;

/// Encompassing type for all expressions, both singular and sequential.
#[derive(Clone, PartialEq)]
pub enum Expr {
	Singular(Singular),
	Seq(SeqVar),
}

/// Singular expressions.
#[derive(Clone, PartialEq)]
pub enum Singular {
	Head(Ptr<SeqVar>),
	Composite(CompName, Vec<Expr>),
	Lambda(Lambda),
	LambdaSeq(LambdaSeq),
	LambdaInst(LambdaInst),
	LambdaSeqInst(LambdaSeqInst),
	Const(Const),
	Free(Free),
	Arb(Arb),
	Formula(Ptr<formula::Formula>),
}

/// The types of names that can be used for constants. Uses strings for
/// most, but has an unsigned integer variant that is used for substitution
/// resolving.
#[derive(Clone, PartialEq, Eq)]
pub enum ConstName {
	String(String),
	Subbed(usize)
}

/// An arbitrary constant, used for ForAll proof contexts.
#[derive(Clone, PartialEq)]
pub struct Arb(pub ConstName);

/// Free variables, used for substitution.
#[derive(Clone, PartialEq)]
pub struct Free(pub ConstName);

/// Standard constant that needs to be defined.
#[derive(Clone, PartialEq)]
pub struct Const(pub ConstName);

/// Sequential variables.
#[derive(PartialEq, Clone)]
pub enum SeqVar {
	Free(FreeSeq),
	Arb(ArbSeq),
	Tail(Ptr<SeqVar>),
	Const(SeqConst),
	List(Vec<Singular>)
}

/// An arbitrary sequences; Has a name and arity. Used for ForAllSeq proof
/// constexts.
#[derive(Clone, PartialEq)]
pub struct ArbSeq {
	pub name: ConstName, 
	pub arity: usize
}

/// Free sequence used for subsitution.
#[derive(Clone, PartialEq)]
pub struct FreeSeq {
	pub name: ConstName, 
	pub arity: usize
}

/// Sequential constant that is defined.
#[derive(PartialEq, Eq, Clone)]
pub struct SeqConst {
	pub name: ConstName, 
	pub arity: usize
}

/// Lambda expressions that allow for free variables to exist in an
/// expression without causing issues for well-formedness. These are
/// primarily used for function definition axioms and so forth.
#[derive(Clone, PartialEq)]
pub struct Lambda<T: Clone + PartialEq = Free> {
	form: Ptr<Singular>, 
	var: T
}
pub type LambdaSeq = Lambda<FreeSeq>;

/// The expression representing substituting into a lambda expression, or 
/// rather function application.
#[derive(Clone, PartialEq)]
pub struct LambdaInst<T = Free, E = Singular>
where
	T: Clone + PartialEq,
	E: Clone + PartialEq,
{
	lambda: Lambda<T>, 
	sub: Ptr<E>
}

pub type LambdaSeqInst = LambdaInst<FreeSeq, SeqVar>;

/// Internal type for easy computation of arity well-formedness
#[derive(PartialEq, Eq, Clone, Copy)]
enum Arity {
	WF(usize), // Wellformed-arity.
	UD // Undefined arity; Results from too many tails.
}

impl Expr {
	/// Used to expand sequential substitions.
	pub fn expand(&self) -> Vec<Expr> {
		match self {
			Expr::Singular(s) => vec!(Expr::Singular(s.expand())),
			Expr::Seq(s) => match s.expand() {
				Ok(l) => l.iter().map(|x| Expr::Singular(x.clone())).collect(),
				Err(s) => vec!(Expr::Seq(s))
			}
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&'a self, kbase: &'a FInfo<'a,K>) -> bool {
		match self {
			&Expr::Singular(ref s) => s.well_formed(kbase),
			&Expr::Seq(ref s) => s.well_formed(kbase)
		}
	}

	pub fn substitute(&self, info: &SInfo) -> Expr {
		match self {
			&Expr::Singular(ref s) => Expr::Singular(s.substitute(info)),
			&Expr::Seq(ref s) => Expr::Seq(s.substitute(info)),
		}
	}

	pub fn max_sub_index(&self) -> usize {
		match self {
			&Expr::Singular(ref s) => s.max_sub_index(),
			&Expr::Seq(ref s) => s.max_sub_index(),
		}
	}
}

impl ToString for Expr {
	fn to_string(&self) -> String {
		match self {
			Expr::Singular(s) => s.to_string(),
			Expr::Seq(s) => s.to_string(),
		}
	}
}

impl Into<Expr> for String {
	fn into(self) -> Expr {
		Singular::Const(Const::from_string(self)).to_expr()
	}
}

impl Into<Expr> for &'static str {
	fn into(self) -> Expr {
		Singular::Const(Const::from_str(self)).to_expr()
	}
}

impl Singular {
	pub fn arb_str(name: &str) -> Singular {
		let cname = ConstName::from_str(name);
		Singular::Arb(Arb(cname))
	}

	pub fn free_str(name: &str) -> Singular {
		let cname = ConstName::from_str(name);
		Singular::Free(Free(cname))
	}

	pub fn const_str(name: &str) -> Singular {
		let cname = ConstName::from_str(name);
		Singular::Const(Const(cname))
	}

	pub fn to_expr(self) -> Expr {
		Expr::Singular(self.clone())
	}

	pub fn expand(&self) -> Singular { 
		match self {
			Singular::Head(b) => match b.expand() {
				Ok(l) => l.first().unwrap().clone(),
				Err(a) => Singular::Head(Ptr::new(a))
			},
			a@Singular::Const(_) => a.clone(),
			Singular::Composite(s, l) => Singular::Composite(
				s.clone(),
				l.iter().flat_map(|x| x.expand()).collect()),
			Singular::Lambda(l) => Singular::Lambda(l.expand()),
			Singular::LambdaInst(l) => Singular::LambdaInst(l.expand()),
			Singular::LambdaSeq(l) => Singular::LambdaSeq(l.expand()),
			Singular::LambdaSeqInst(l) => Singular::LambdaSeqInst(l.expand()),
			a@Singular::Free(_) => a.clone(),
			a@Singular::Arb(_) => a.clone(),
			Singular::Formula(f) => Singular::Formula(f.expand().ptr()),
		}
	}
	

	pub fn from_int(i: usize) -> Singular {
		Singular::Const(Const::from_int(i))
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
		match self {
			Singular::Head(b) => b.well_formed(info),
			Singular::Composite(name, ref vars) => info.has_expr(name) &&
				vars.iter().all(|x| x.well_formed(info)),
			Singular::Const(name) => info.has_const(name),
			Singular::Lambda(v) => v.well_formed(info),
			Singular::LambdaInst(l) => l.well_formed(info),
			Singular::LambdaSeq(v) => v.well_formed(info),
			Singular::LambdaSeqInst(l) => l.well_formed(info),
			Singular::Free(name) => info.has_free(name),
			Singular::Arb(name) => info.has_arb(name),
			Singular::Formula(f) => f.well_formed(info),
		}
	}

	pub fn max_sub_index(&self) -> usize {
		match self {
			Singular::Head(ref s) => s.max_sub_index(),
			Singular::Const(Const(c)) => match c {
				&ConstName::Subbed(u) => u,
				_ => 0
			}
			Singular::Composite(_, ref exps) 
				=> exps.iter().map(|x| x.max_sub_index()).max().unwrap(),
			Singular::Lambda(ref l) => l.max_sub_index(),
			Singular::LambdaInst(ref l) => l.max_sub_index(),
			Singular::LambdaSeq(ref l) => l.max_sub_index(),
			Singular::LambdaSeqInst(ref l) => l.max_sub_index(),
			Singular::Free(ref l) => l.max_sub_index(),
			Singular::Arb(ref l) => l.max_sub_index(),
			Singular::Formula(f) => f.max_sub_index(),
		}
	}

	pub fn substitute(&self, info: &SInfo) -> Singular {
		match self {
			Singular::Head(b) => Singular::Head(b.substitute(info).ptr()),
			Singular::Composite(name, exps) 
				=> Singular::Composite(
					name.clone(), 
					exps.iter().map(|x| x.substitute(info)).collect()),
			a@Singular::Const(_) => a.clone(),
			Singular::Lambda(l) => Singular::Lambda(l.substitute(info)),
			Singular::LambdaInst(l) => Singular::LambdaInst(l.substitute(info)),
			Singular::LambdaSeq(l) => Singular::LambdaSeq(l.substitute(info)),
			Singular::LambdaSeqInst(l) => Singular::LambdaSeqInst(l.substitute(info)),
			Singular::Free(f) => info.substitute(f),
			a@Singular::Arb(_) => a.clone(),
			Singular::Formula(f) => Singular::Formula(f.substitute(info).ptr()),
		}
	}

	pub fn ptr(self) -> Ptr<Singular> {
		Ptr::new(self)
	}
}

impl ToString for Singular {
	fn to_string(&self) -> String {
		match self {
			Singular::Head(b) => format!("head({})", b.to_string()),
			Singular::Composite(name, exps) => {
				/*let iter = exps.iter();
				let mut names = String::new();
				names.push_str(iter.next().unwrap().to_string().as_str());
				for a in iter {
					names.push_str(", ");
					names.push_str(a.to_string().as_str())
				}*/				
				format!(
					"{}({})",
					name.to_string(), 
					exps.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "))
			},
			Singular::Const(a) => a.to_string(),
			Singular::Lambda(l) => l.to_string(),
			Singular::LambdaInst(l) => l.to_string(),
			Singular::LambdaSeq(l) => l.to_string(),
			Singular::LambdaSeqInst(l) => l.to_string(),
			Singular::Free(f) => f.to_string(),
			Singular::Arb(a) => a.to_string(),
			Singular::Formula(f) => f.to_string(),
		}
	}
}

impl Into<Singular> for String {
	fn into(self) -> Singular {
		Singular::Const(Const::from_string(self))
	}
}

impl Into<Singular> for &'static str {
	fn into(self) -> Singular {
		Singular::Const(Const::from_str(self))
	}
}

impl SeqConst {
	pub fn new(name: ConstName, arity: usize) -> SeqConst {
		SeqConst {
			name: name,
			arity: arity
		}
	}

	pub fn from_cname(name: ConstName, arity: usize) -> SeqConst {
		SeqConst {
			name: name,
			arity: arity
		}
	}

	pub fn from_string(name: String, arity: usize) -> SeqConst {
		SeqConst {
			name: ConstName::from_string(name),
			arity: arity
		}
	}

	pub fn from_str(name: &str, arity: usize) -> SeqConst {
		SeqConst {
			name: ConstName::from_str(name),
			arity: arity
		}
	}

	pub fn to_seq(self) -> SeqVar {
		SeqVar::Const(self)
	}

	pub fn replace_with(&self, i: usize) -> SeqConst {
		SeqConst {
			name: ConstName::from_int(i),
			arity: self.arity
		}
	}

	pub fn max_sub_index(&self) -> usize {
		match &self.name {
			&ConstName::Subbed(i) => i,
			_ => 0
		}
	}
}

impl ToString for SeqConst {
	fn to_string(&self) -> String {
		format!("{}..{}", self.name.to_string(), self.arity)
	}
}

impl Into<SeqConst> for (String, usize) {
	fn into(self) -> SeqConst {
		SeqConst::from_string(self.0, self.1)
	}
}

impl Into<SeqConst> for (&'static str, usize) {
	fn into(self) -> SeqConst {
		SeqConst::from_str(self.0, self.1)
	}
}

impl ConstName {
	pub fn replace_with(&self, i: usize) -> ConstName {
		ConstName::Subbed(i)
	}

	pub fn from_int(i: usize) -> ConstName { ConstName::Subbed(i) }

	pub fn from_string(i: String) -> ConstName { ConstName::String(i) }
	pub fn from_str(i: &str) -> ConstName { ConstName::String(i.to_string()) }

	pub fn max_sub_index(&self) -> usize {
		match self {
			&ConstName::Subbed(u) => u,
			_ => 0
		}
	}

	pub fn to_const(&self) -> Const { 
		Const(self.clone())
	}

	pub fn to_expr(&self) -> Expr {
		Expr::Singular(Singular::Const(Const(self.clone())))
	}

	pub fn to_singular(&self) -> Singular {
		Singular::Const(Const(self.clone()))
	}
}

impl ToString for ConstName {
	fn to_string(&self) -> String {
		match self {
			ConstName::String(s) => { s.clone() },
			ConstName::Subbed(i) => { format!("c{}", i) }
		}
	}
}

impl Into<ConstName> for String {
	fn into(self) -> ConstName { ConstName::from_string(self) }
}

impl Into<ConstName> for &'static str {
	fn into(self) -> ConstName { ConstName::from_str(self) }
}

impl Arity {
	pub fn is_defined(&self) -> bool {
		match self {
			&Arity::UD => false,
			_ => true
		}
	}
}

impl Sub<usize> for Arity {
	type Output = Arity;
	fn sub(self, rhs: usize) -> Arity {
		match self {
			Arity::WF(0) => Arity::UD,
			Arity::WF(n) => Arity::WF(n - rhs),
			_ => Arity::UD
		}
	}
}

impl Arb {
	pub fn from_string(name: String) -> Arb {
		Arb(ConstName::from_string(name))
	}

	pub fn from_str(name: &str) -> Arb {
		Arb(ConstName::from_str(name))
	}

	pub fn from_cname(name: ConstName) -> Arb {
		Arb(name)
	}

	pub fn max_sub_index(&self) -> usize {
		self.0.max_sub_index()
	}	

	pub fn to_singular(self) -> Singular {
		Singular::Arb(self)
	}
}

impl ToString for Arb {
	fn to_string(&self) -> String {
		format!("&{}", self.0.to_string())
	}
}

impl Into<Arb> for String {
	fn into(self) -> Arb {
		Arb::from_string(self)
	}
}

impl Into<Arb> for &'static str {
	fn into(self) -> Arb {
		Arb::from_str(self)
	}
}

impl ArbSeq {
	pub fn from_cname(name: ConstName, arity: usize) -> ArbSeq {
		ArbSeq {
			name: name,
			arity: arity
		}
	}

	pub fn from_string(name: String, arity: usize) -> ArbSeq {
		ArbSeq {
			name: ConstName::from_string(name),
			arity: arity
		}
	}

	pub fn from_str(name: &str, arity: usize) -> ArbSeq {
		ArbSeq {
			name: ConstName::from_str(name),
			arity: arity
		}
	}

	pub fn to_seq(self) -> SeqVar {
		SeqVar::Arb(self)
	}

	pub fn max_sub_index(&self) -> usize {
		self.name.max_sub_index()
	}
}

impl ToString for ArbSeq {
	fn to_string(&self) -> String {
		format!("&{}..{}", self.name.to_string(), self.arity)
	}
}

impl Into<ArbSeq> for (String, usize) {
	fn into(self) -> ArbSeq { ArbSeq::from_string(self.0, self.1) }
}

impl Into<ArbSeq> for (&'static str, usize) {
	fn into(self) -> ArbSeq { ArbSeq::from_str(self.0, self.1) }
}

impl SeqVar {

	pub fn free_str(name: &str, arity: usize) -> SeqVar {
		SeqVar::Free(
			FreeSeq { name: ConstName::from_str(name), arity: arity })
	}

	pub fn arb_str(name: &str, arity: usize) -> SeqVar {
		SeqVar::Arb(
			ArbSeq { name: ConstName::from_str(name), arity: arity })
	}

	pub fn const_str(name: &str, arity: usize) -> SeqVar {
		SeqVar::Const(
			SeqConst { name: ConstName::from_str(name), arity: arity })
	}

	pub fn free_string(name: String, arity: usize) -> SeqVar {
		SeqVar::Free(
			FreeSeq { name: ConstName::from_string(name), arity: arity })
	}

	pub fn arb_string(name: String, arity: usize) -> SeqVar {
		SeqVar::Arb(
			ArbSeq { name: ConstName::from_string(name), arity: arity })
	}

	pub fn const_string(name: String, arity: usize) -> SeqVar {
		SeqVar::Const(
			SeqConst { name: ConstName::from_string(name), arity: arity })
	}

	pub fn ptr(self) -> Ptr<SeqVar> {
		Ptr::new(self)
	}

	pub fn to_expr(self) -> Expr {
		Expr::Seq(self)
	}

	pub fn max_sub_index(&self) -> usize {
		match self {
			SeqVar::List(l) => l.iter().map(|x| x.max_sub_index()).max().unwrap(),
			SeqVar::Tail(b) => b.max_sub_index(),
			SeqVar::Const(c) => match &c.name {
				&ConstName::Subbed(u) => u,
				_ => 0
			}
			SeqVar::Free(f) => f.max_sub_index(),
			SeqVar::Arb(f) => f.max_sub_index(),
		}
	}

	fn arity(&self) -> Arity {
		match self {
			SeqVar::Free(f) => Arity::WF(f.arity),
			SeqVar::Arb(f) => Arity::WF(f.arity),
			SeqVar::List(l) => Arity::WF(l.len()),
			SeqVar::Const(n) => Arity::WF(n.arity),
			SeqVar::Tail(r) => match r.arity() {
				Arity::WF(s) if s > 0 => r.arity() - 1,
				_ => Arity::UD
			}
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		match self {
			SeqVar::Free(f) => info.has_free_seq(f),
			SeqVar::Arb(f) => info.has_arb_seq(f),
			SeqVar::List(l) => l.iter().all(|x| x.well_formed(info)),
			SeqVar::Const(c) => info.has_seq_const(c),
			SeqVar::Tail(t) => t.arity().is_defined() && t.well_formed(info)
		}
	}

	pub fn substitute(&self, info: &SInfo) -> SeqVar {
		match self {
			SeqVar::List(l) => SeqVar::List(l.iter().map(|x| x.substitute(info)).collect()),
			a@SeqVar::Const(_) => a.clone(),
			SeqVar::Free(f) => info.substitute_seq(f),
			a@SeqVar::Arb(_) => a.clone(),
			SeqVar::Tail(t) => SeqVar::Tail(Ptr::new(t.substitute(info))),
		}
	}

	pub fn expand(&self) -> Result<Vec<Singular>, SeqVar> {
		match self {
			SeqVar::List(l) => Ok(l.clone()),
			SeqVar::Tail(t) => match t.expand() {
				Ok(v) => Ok(v[1..].to_vec()),
				e => e
			},
			a => Err(a.clone())
			
		}
	}
}

impl ToString for SeqVar {
	fn to_string(&self) -> String {
		match self {
			SeqVar::Free(f) => f.to_string(),
			SeqVar::Arb(f) => f.to_string(),
			SeqVar::List(f) => {
				format!("list({})",
					f.iter()
						.map(|x| x.to_string())
						.collect::<Vec<String>>()
						.join(", "))
			},
			SeqVar::Const(f) => f.to_string(),
			SeqVar::Tail(f) => format!("tail({})", f.to_string())
		}
	}
}

impl Into<SeqVar> for (String, usize) {
	fn into(self) -> SeqVar {
		SeqVar::const_string(self.0, self.1)
	}
}

impl Into<SeqVar> for (&'static str, usize) {
	fn into(self) -> SeqVar {
		SeqVar::const_str(self.0, self.1)
	}
}


impl FreeSeq {
	pub fn from_cname(name: ConstName, arity: usize) -> FreeSeq {
		FreeSeq {
			name: name,
			arity: arity
		}
	}

	pub fn from_string(name: String, arity: usize) -> FreeSeq {
		FreeSeq {
			name: ConstName::from_string(name),
			arity: arity
		}
	}

	pub fn from_str(name: &str, arity: usize) -> FreeSeq {
		FreeSeq {
			name: ConstName::from_str(name),
			arity: arity
		}
	}

	pub fn from_int(name: usize, arity: usize) -> FreeSeq {
		FreeSeq {
			name: ConstName::from_int(name),
			arity: arity
		}
	}

	pub fn replace_with(&self, i: usize) -> FreeSeq {
		FreeSeq {
			name: ConstName::Subbed(i),
			arity: self.arity
		}
	}

	pub fn to_seq(self) -> SeqVar {
		SeqVar::Free(self)
	}

	pub fn arity(&self) -> usize {
		self.arity
	}

	pub fn max_sub_index(&self) -> usize {
		self.name.max_sub_index()
	}
}

impl ToString for FreeSeq {
	fn to_string(&self) -> String {
		format!("*{}..{}", self.name.to_string(), self.arity)
	}
}

impl Into<FreeSeq> for (String, usize) {
	fn into(self) -> FreeSeq {
		FreeSeq::from_string(self.0, self.1)
	}
}

impl Into<FreeSeq> for (&'static str, usize) {
	fn into(self) -> FreeSeq {
		FreeSeq::from_str(self.0, self.1)
	}
}


impl Free {
	pub fn max_sub_index(&self) -> usize {
		self.0.max_sub_index()
	}

	pub fn from_cname(s: ConstName) -> Free {
		Free(s)
	}
	
	pub fn from_string(s: String) -> Free {
		Free(ConstName::String(s))
	}

	pub fn from_str(s: &str) -> Free {
		Free(ConstName::String(s.to_string()))
	}

	pub fn from_int(i: usize) -> Free {
		Free(ConstName::Subbed(i))
	}

	pub fn from_name(name: ConstName) -> Free {
		Free(name)
	}

	pub fn to_singular(self) -> Singular {
		Singular::Free(self)
	}
}

impl ToString for Free {
	fn to_string(&self) -> String {
		format!("*{}", self.0.to_string())
	}
}

impl Into<Free> for String {
	fn into(self) -> Free { Free::from_string(self) }
}

impl Into<Free> for &'static str {
	fn into(self) -> Free { Free::from_str(self) }
}

impl Const {
	pub fn max_sub_index(&self) -> usize {
		self.0.max_sub_index()
	}

	pub fn to_singular(self) -> Singular {
		Singular::Const(self)
	}
	
	pub fn from_string(s: String) -> Const {
		Const(ConstName::String(s))
	}

	pub fn from_str(s: &str) -> Const {
		Const(ConstName::from_str(s))
	}

	pub fn from_int(i: usize) -> Const {
		Const(ConstName::Subbed(i))
	}

	pub fn from_cname(name: ConstName) -> Const {
		Const(name)
	}
}

impl ToString for Const {
	fn to_string(&self) -> String {
		format!("*{}", self.0.to_string())
	}
}

impl Into<Const> for String {
	fn into(self) -> Const {
		Const::from_string(self)
	}
}

impl Into<Const> for &'static str {
	fn into(self) -> Const {
		Const::from_str(self)
	}
}

impl PartialEq<String> for Const {
	fn eq(&self, rhs: &String) -> bool {
		match self {
			Const(ConstName::String(s)) => PartialEq::eq(s, rhs),
			_ => false
		}
	}
}

impl Lambda {	
	fn expand(&self) -> Lambda {
		Lambda {
			form: Ptr::new(self.form.expand()),
			var: self.var.clone()
		}
	}

	pub fn new(form: Singular, var: Free) -> Lambda {
		Lambda {
			form: Ptr::new(form),
			var: var
		}
	}

	pub fn substitute(&self, info: &SInfo) -> Lambda {
		if info.replaces(&self.var) {
			self.clone()
		} else {
			let (exp, f) = info.chain(self.form.borrow(), &self.var);
			Lambda::<Free>::new(exp, f)
		}
	}
	
	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
		self.form.well_formed(&info.append_free(&self.var))
	}

	pub fn max_sub_index(&self) -> usize {
		let u = self.form.max_sub_index();
		let v = self.var.max_sub_index();
		std::cmp::max(u, v)
	}
}

impl ToString for Lambda {
	fn to_string(&self) -> String {
		format!("lambda {} [{}]", self.var.to_string(), self.form.to_string())
	}
}

impl LambdaSeq {

	fn expand(&self) -> LambdaSeq {
		LambdaSeq {
			form: Ptr::new(self.form.expand()),
			var: self.var.clone()
		}
	}

	pub fn new(form: Singular, var: FreeSeq) -> LambdaSeq {
		LambdaSeq {
			form: Ptr::new(form),
			var: var
		}
	}

	pub fn substitute(&self, info: &SInfo) -> LambdaSeq {
		if info.replaces_seq(&self.var) {
			self.clone()
		} else {
			let (exp, f) = info.chain_seq(self.form.borrow(), &self.var);
			LambdaSeq::new(exp, f)
		}
	}
	
	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
		self.form.well_formed(&info.append_free_seq(&self.var))
	}

	pub fn max_sub_index(&self) -> usize {
		let u = self.form.max_sub_index();
		let v = self.var.max_sub_index();
		std::cmp::max(u, v)
	}
}

impl ToString for LambdaSeq {
	fn to_string(&self) -> String {
		format!("lambda* {} [{}]", self.var.to_string(), self.form.to_string())
	}
}

impl subst::Substitute for Lambda {
	fn substitute(&self, info: &SInfo) -> Lambda {
		Lambda::<Free>::substitute(self, info)
	}

	fn max_sub_index(&self) -> usize {
		Lambda::<Free>::max_sub_index(self)
	}
}


impl subst::Substitute for LambdaSeq {
	fn substitute(&self, info: &SInfo) -> LambdaSeq {
		LambdaSeq::substitute(self, info)
	}
	
	fn max_sub_index(&self) -> usize {
		LambdaSeq::max_sub_index(self)
	}
}

impl LambdaInst {
	pub fn extract(&self) -> Singular {
		let info = subst::Expr::Singular(
				self.lambda.var.clone(), 
				Clone::clone(self.sub.borrow()))
			.to_form();
		self.lambda.form.substitute(&info)
	}


	fn expand(&self) -> LambdaInst {
		LambdaInst {
			lambda: self.lambda.expand(),
			sub: Ptr::new(self.sub.expand())
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
		self.lambda.well_formed(info) && self.sub.well_formed(info)
	}

	pub fn max_sub_index(&self) -> usize {
		std::cmp::max(self.lambda.max_sub_index(), self.sub.max_sub_index())
	}

	pub fn substitute(&self, info: &SInfo) -> LambdaInst {
		LambdaInst{
			lambda: self.lambda.substitute(info), 
			sub: Ptr::new(self.sub.substitute(info))
		}
	}

	pub fn new(l: Lambda, s: Singular) -> LambdaInst {
		LambdaInst {
			lambda: l,
			sub: Ptr::new(s)
		}
	}
}

impl ToString for LambdaInst {
	fn to_string(&self) -> String {
		format!("{}[{} <- {}]", 
			self.lambda.form.to_string(), 
			self.lambda.var.to_string(), 
			self.sub.to_string())
	}
}

impl LambdaSeqInst {

	pub fn new(l: LambdaSeq, s: SeqVar) -> LambdaSeqInst {
		LambdaSeqInst {
			lambda: l,
			sub: Ptr::new(s)
		}
	}

	pub fn extract(&self) -> Singular {
		let info = subst::Expr::Seq(
				self.lambda.var.clone(), 
				Clone::clone(self.sub.borrow()))
			.to_form();
		self.lambda.form.substitute(&info)
	}

	fn expand(&self) -> LambdaSeqInst {
		LambdaSeqInst {
			lambda: self.lambda.expand(),
			sub: self.sub.clone()
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
		self.lambda.well_formed(info) && self.sub.well_formed(info)
	}

	pub fn max_sub_index(&self) -> usize {
		std::cmp::max(self.lambda.max_sub_index(), self.sub.max_sub_index())
	}

	pub fn substitute(&self, info: &SInfo)
	-> LambdaSeqInst {
		LambdaSeqInst{
			lambda: self.lambda.substitute(info), 
			sub: Ptr::new(self.sub.substitute(info))
		}
	}
}

impl ToString for LambdaSeqInst {
	fn to_string(&self) -> String {
		format!("{}[{} <= {}]", 
			self.lambda.form.to_string(), 
			self.lambda.var.to_string(), 
			self.sub.to_string())
	}
}

impl subst::Substitute for Singular {
	fn substitute(&self, info: &SInfo) -> Singular {
		Singular::substitute(self, info)
	}
	fn max_sub_index(&self) -> usize {
		Singular::max_sub_index(self)
	}
}