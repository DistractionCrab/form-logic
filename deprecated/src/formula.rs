use std::ops::Deref;
use std::convert::Into;
use std::cmp::max;
use std::string::ToString;

use expr;
use subst;
use knowledge_base as kbase;

use Ptr;
use self::kbase::ContextBase;
use subst::Info as SInfo;
use subst::Expr as EInfo;
use formed::Info as FInfo;

pub type FormPtr = Ptr<Formula>;

#[derive(Clone, PartialEq)]
pub enum Formula {
	True,
	False,
	IFF(IFF),
	Relation(Relation),
	And(And),
	Or(Or),
	Not(Not),
	Implies(Implies),
	ExpSubst(ExpSubst),
	FormSubst(FormSubst),
	ForAllSeq(ForAllSeq),
	ForAll(ForAll),
	Exists(Exists),
	Free(Free),
	Arb(Arb),
	Schema(Schema),
	Eq(Eq),
}

#[derive(Clone, PartialEq)]
pub struct Relation(String, Vec<expr::Expr>);

#[derive(Clone, PartialEq)]
pub struct Not { pub form: FormPtr }

#[derive(Clone)]
pub struct ExpSubst { form: FormPtr, sub: subst::Expr }

#[derive(Clone, PartialEq)]
pub struct Free { var: FormName }

#[derive(Clone, PartialEq)]
pub struct Arb { var: FormName }

#[derive(Clone)]
pub struct Schema {
	pub var: Free, 
	pub form: FormPtr
}
#[derive(Clone, PartialEq)]
pub struct Eq(pub expr::Singular, pub expr::Singular);

#[derive(Clone, PartialEq, Eq)]
pub enum FormName {
	String(String),
	Subbed(usize)
}

#[derive(Clone)]
pub struct ForAllSeq { 
	pub var: expr::FreeSeq, 
	pub form: FormPtr 

}
#[derive(Clone)]
pub struct FormSubst { 
	form: FormPtr, 
	var: Free, 
	sub: FormPtr
}

macro_rules! max {
	($x: expr) => ($x);
	($x:expr, $($y:expr),+) => { std::cmp::max($x, max!($($y),+)) };
}

macro_rules! to_form_impl {
	($struct: ident) => {
		impl $struct {
			pub fn to_form(&self) -> Formula { Formula::$struct(self.clone())}
		}
	}
}

macro_rules! bin_string {
	(Or) => ("Or");
	(And) => ("And");
	(Implies) => ("Implies");
	(IFF) => ("IFF");

}

macro_rules! binform_impl {
	($form: ident) => {

		#[derive(Clone)]
		pub struct $form { pub left: FormPtr, pub right: FormPtr }

		to_form_impl!($form);

		impl $form {

			pub fn new(left: Formula, right: Formula) -> $form {
				$form { left: left.ptr(), right: right.ptr() }
			}

			pub fn expand(&self) -> $form {
				$form {
					left: self.left.expand().ptr(), 
					right: self.right.expand().ptr()
				}
			}

			pub fn substitute(&self, info: &SInfo) 
			-> $form {
				$form {
					left: self.left.substitute(info).ptr(),
					right: self.right.substitute(info).ptr()
				}
			}

			pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
				self.left.well_formed(info) && self.right.well_formed(info)
			}

			pub fn max_form_sub_index(&self) -> usize {
				std::cmp::max(self.left.max_form_sub_index(), self.right.max_form_sub_index())
			}

			pub fn max_sub_index(&self) -> usize {
				std::cmp::max(self.left.max_sub_index(), self.right.max_sub_index())
			}

			pub fn form(a: FormPtr, b: FormPtr) -> Formula { 
				Formula::$form( $form {
					left: a,
					right: b
				})
			}

			pub fn eq(&self, rhs: &$form) -> bool {
				self.bin_seq().iter()
					.zip(rhs.bin_seq().iter())
					.all(|(a, b)| { PartialEq::eq(a, b) })
			}

			pub fn bin_seq<'a>(&'a self) -> Vec<&'a Formula> {
				let mut v = vec!();
				
				fn recurse<'a>(form: &'a Formula, v: &mut Vec<&'a Formula>) {
					match form {
						Formula::$form(f) => {
							recurse(f.left.deref(), v);
							recurse(f.right.deref(),v );
						},
						f => { v.push(f) }
					}
				}

				recurse(self.left.deref(), &mut v);
				recurse(self.right.deref(), &mut v);

				v
			}
		}

		impl PartialEq<$form> for $form {
			fn eq(&self, rhs: &$form) -> bool {
				$form::eq(self, rhs)
			}
		}

		impl ToString for $form {
			fn to_string(&self) -> String {
				format!("{}({}, {})", 
					bin_string!($form).to_owned(), 
					self.left.to_string(), 
					self.right.to_string())
			}
		}
	}
}

macro_rules! quant_impl {
	($quant: ident) => {

		#[derive(Clone)]
		pub struct $quant { pub var: expr::Free, pub form: FormPtr }

		to_form_impl!($quant);

		impl $quant {
			pub fn from_str(v: &str, form: Formula) -> $quant {
				$quant {
					var: expr::Free::from_str(v),
					form: form.ptr()
				}
			}

			pub fn from_string(v: String, form: Formula) -> $quant {
				$quant {
					var: expr::Free::from_string(v),
					form: form.ptr()
				}
			}

			pub fn from_free(v: expr::Free, form: Formula) -> $quant {
				$quant {
					var: v,
					form: form.ptr()
				}
			}

			pub fn expand(&self) -> $quant {
				$quant {
					var: self.var.clone(),
					form: self.form.expand().ptr()
				}
			}

			pub fn instantiate(&self, exp: &expr::Singular) -> Formula {
				let info = EInfo::Singular(self.var.clone(), exp.clone()).to_form();
				self.form.substitute(&info)
			}

			pub fn substitute(&self, info: &SInfo) -> $quant {
				if info.replaces(&self.var) {
					self.clone()
				} else {
					let (exp, f) = info.chain(self.form.deref(), &self.var);
					$quant { var: f, form: exp.ptr() }
				}
			}

			
			pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
				self.form.well_formed(&info.append_free(&self.var))
			}

			pub fn max_form_sub_index(&self) -> usize {
				self.form.max_form_sub_index()
			}

			pub fn max_sub_index(&self) -> usize {
				max(self.var.max_sub_index(), self.form.max_sub_index())
			}

			pub fn eq(&self, rhs: &$quant) -> bool {
				let i = max(self.max_sub_index(), rhs.max_sub_index());
				let name = expr::Free::from_int(i + 1);
				let sub1 = subst::Expr::Singular(self.var.clone(), name.clone().to_singular());
				let sub2 = subst::Expr::Singular(rhs.var.clone(), name.to_singular());
				self.form.substitute(&sub1.to_form()) == rhs.form.substitute(&sub2.to_form())
			}
		}
		
		impl ToString for $quant {
			fn to_string(&self) -> String {
				format!("{} {} [{}]", 
					stringify!($quant), 
					self.var.to_string(),
					self.form.to_string())
			}
		}

		impl PartialEq<$quant> for $quant {
			fn eq(&self, rhs: &$quant) -> bool {
				$quant::eq(self, rhs)
			}
		}
	}
}

binform_impl!(IFF);
binform_impl!(Implies);
binform_impl!(And);
binform_impl!(Or);

quant_impl!(ForAll);
quant_impl!(Exists);

to_form_impl!(ForAllSeq);
to_form_impl!(Arb);
to_form_impl!(Free);
to_form_impl!(Not);
to_form_impl!(Schema);
to_form_impl!(Eq);
to_form_impl!(ExpSubst);
to_form_impl!(FormSubst);

impl Formula {
	pub fn from_name(name: FormName) -> Formula {
		Formula::Free(Free::new(name))
	}

	pub fn from_int(i: usize) -> Formula {
		Formula::Free(Free::new(FormName::from_int(i)))
	}

	pub fn to_form(self) -> Formula { self }

	pub fn expand(&self) -> Formula {
		match self {
			Formula::True         => Formula::True,
			Formula::False        => Formula::False,
			Formula::IFF(f)       => Formula::IFF(f.expand()),
			Formula::Relation(f)  => Formula::Relation(f.expand()),
			Formula::And(f)       => Formula::And(f.expand()),
			Formula::Or(f)        => Formula::Or(f.expand()),
			Formula::Not(f)       => Formula::Not(f.expand()),
			Formula::Implies(f)   => Formula::Implies(f.expand()),
			Formula::ExpSubst(f)  => Formula::ExpSubst(f.expand()),
			Formula::FormSubst(f) => Formula::FormSubst(f.expand()),
			Formula::ForAllSeq(f) => Formula::ForAllSeq(f.expand()),
			Formula::ForAll(f)    => Formula::ForAll(f.expand()),
			Formula::Exists(f)    => Formula::Exists(f.expand()),
			Formula::Free(f)      => Formula::Free(f.expand()),
			Formula::Schema(f)    => Formula::Schema(f.expand()),
			Formula::Eq(f)        => Formula::Eq(f.expand()),
			Formula::Arb(f)       => Formula::Arb(f.expand()),
		}
	}

	pub fn substitute(&self, info: &SInfo) -> Formula {
		match self {
			Formula::True         => Formula::True,
			Formula::False        => Formula::False,
			Formula::IFF(f)       => Formula::IFF(f.substitute(info)),
			Formula::Relation(f)  => Formula::Relation(f.substitute(info)),
			Formula::And(f)       => Formula::And(f.substitute(info)),
			Formula::Or(f)        => Formula::Or(f.substitute(info)),
			Formula::Not(f)       => Formula::Not(f.substitute(info)),
			Formula::Implies(f)   => Formula::Implies(f.substitute(info)),
			Formula::ExpSubst(f)  => Formula::ExpSubst(f.substitute(info)),
			Formula::FormSubst(f) => Formula::FormSubst(f.substitute(info)),
			Formula::ForAllSeq(f) => Formula::ForAllSeq(f.substitute(info)),
			Formula::ForAll(f)    => Formula::ForAll(f.substitute(info)),
			Formula::Exists(f)    => Formula::Exists(f.substitute(info)),
			Formula::Free(f)      => f.substitute(info),
			Formula::Arb(f)       => f.substitute(info),
			Formula::Schema(f)    => Formula::Schema(f.substitute(info)),
			Formula::Eq(f)        => Formula::Eq(f.substitute(info)),
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		match self {
			Formula::True         => true,
			Formula::False        => true,
			Formula::IFF(f)       => f.well_formed(info),
			Formula::Relation(f)  => f.well_formed(info),
			Formula::And(f)       => f.well_formed(info),
			Formula::Or(f)        => f.well_formed(info),
			Formula::Not(f)       => f.well_formed(info),
			Formula::Implies(f)   => f.well_formed(info),
			Formula::ExpSubst(f)  => f.well_formed(info),
			Formula::FormSubst(f) => f.well_formed(info),
			Formula::ForAllSeq(f) => f.well_formed(info),
			Formula::ForAll(f)    => f.well_formed(info),
			Formula::Exists(f)    => f.well_formed(info),
			Formula::Free(f)      => f.well_formed(info),
			Formula::Arb(f)       => f.well_formed(info),
			Formula::Schema(f)    => f.well_formed(info),
			Formula::Eq(f)        => f.well_formed(info),
		}
	}

	pub fn max_sub_index(&self) -> usize {
		match self {
			Formula::True         => 0,
			Formula::False        => 0,
			Formula::IFF(f)       => f.max_sub_index(),
			Formula::Relation(f)  => f.max_sub_index(),
			Formula::And(f)       => f.max_sub_index(),
			Formula::Or(f)        => f.max_sub_index(),
			Formula::Not(f)       => f.max_sub_index(),
			Formula::Implies(f)   => f.max_sub_index(),
			Formula::ExpSubst(f)  => f.max_sub_index(),
			Formula::FormSubst(f) => f.max_sub_index(),
			Formula::ForAllSeq(f) => f.max_sub_index(),
			Formula::ForAll(f)    => f.max_sub_index(),
			Formula::Exists(f)    => f.max_sub_index(),
			Formula::Free(f)      => f.max_sub_index(),
			Formula::Arb(f)       => f.max_sub_index(),
			Formula::Schema(f)    => f.max_sub_index(),
			Formula::Eq(f)        => f.max_sub_index(),
		}
	}

	pub fn max_form_sub_index(&self) -> usize {
		match self {
			Formula::True         => 0,
			Formula::False        => 0,
			Formula::IFF(f)       => f.max_form_sub_index(),
			Formula::Relation(f)  => f.max_form_sub_index(),
			Formula::And(f)       => f.max_form_sub_index(),
			Formula::Or(f)        => f.max_form_sub_index(),
			Formula::Not(f)       => f.max_form_sub_index(),
			Formula::Implies(f)   => f.max_form_sub_index(),
			Formula::ExpSubst(f)  => f.max_form_sub_index(),
			Formula::FormSubst(f) => f.max_form_sub_index(),
			Formula::ForAllSeq(f) => f.max_form_sub_index(),
			Formula::ForAll(f)    => f.max_form_sub_index(),
			Formula::Exists(f)    => f.max_form_sub_index(),
			Formula::Free(f)      => f.max_form_sub_index(),
			Formula::Arb(f)       => f.max_form_sub_index(),
			Formula::Schema(f)    => f.max_form_sub_index(),
			Formula::Eq(f)        => f.max_form_sub_index(),
		}
	}

	pub fn implies(self, other:Formula) -> Formula {
		Formula::Implies(Implies::new(self, other))
	}

	pub fn iff(self, other:Formula) -> Formula {
		Formula::IFF(IFF::new(self, other))
	}

	pub fn ptr(self) -> FormPtr {
		Ptr::new(self)
	}
}

impl ToString for Formula {
	fn to_string(&self) -> String { 
		match self {
			Formula::True         => "true".to_string(),
			Formula::False        => "false".to_string(),
			Formula::IFF(f)       => f.to_string(),
			Formula::Relation(f)  => f.to_string(),
			Formula::And(f)       => f.to_string(),
			Formula::Or(f)        => f.to_string(),
			Formula::Not(f)       => f.to_string(),
			Formula::Implies(f)   => f.to_string(),
			Formula::ExpSubst(f)  => f.to_string(),
			Formula::FormSubst(f) => f.to_string(),
			Formula::ForAllSeq(f) => f.to_string(),
			Formula::ForAll(f)    => f.to_string(),
			Formula::Exists(f)    => f.to_string(),
			Formula::Free(f)      => f.to_string(),
			Formula::Arb(f)       => f.to_string(),
			Formula::Schema(f)    => f.to_string(),
			Formula::Eq(f)        => f.to_string(),
		}
	}
}

impl Into<Formula> for bool {
	fn into(self) -> Formula {
		if self {
			Formula::True
		} else {
			Formula::False
		}
	}
}

impl Into<expr::Singular> for Formula {
	fn into(self) -> expr::Singular {
		expr::Singular::Formula(self.ptr())
	}
}

impl Into<expr::Expr> for Formula {
	fn into(self) -> expr::Expr {
		expr::Singular::Formula(self.ptr()).to_expr()
	}
}

impl subst::Substitute for Formula {
	fn substitute(&self, info: &SInfo) -> Formula {
		Formula::substitute(self, info)
	}
	fn max_sub_index(&self) -> usize {
		Formula::max_sub_index(self)	
	}
}

impl ExpSubst {

	pub fn expand(&self) -> ExpSubst {
		self.clone()
	}

	pub fn new(form: FormPtr, sub: subst::Expr) -> ExpSubst { 
		ExpSubst { form: form, sub: sub }
	}

	pub fn extract(&self) -> Formula {
		self.form.substitute(&self.sub.clone().to_form())
	}

	pub fn substitute(&self, info: &SInfo) -> ExpSubst {
		match info {
			SInfo::Expr(ein) => {
				if ein.replaces_info(&self.sub) {
					self.clone()
				} else {
					let (exp, f) = ein.chain_info(self.form.deref(), &self.sub);
					ExpSubst { sub: f, form: exp.ptr() }
				}		
			}
			_ => ExpSubst { 
				sub: self.sub.clone(), 
				form: self.form.substitute(info).ptr()
			},
		}	
	}

	pub fn eq(&self, rhs: &ExpSubst) -> bool {
		match (&self.sub, &rhs.sub) {
			(subst::Expr::Singular(f1, s1), subst::Expr::Singular(f2, s2)) => {
				if s1 == s2 {
					let i = max!(
						f1.max_sub_index(), 
						s1.max_sub_index(),
						f2.max_sub_index(), 
						s2.max_sub_index());
					let name = expr::Free::from_int(i + 1).to_singular();
					let sub1 = subst::Expr::Singular(f1.clone(), name.clone()).to_form();
					let sub2 = subst::Expr::Singular(f2.clone(), name).to_form();
					self.form.substitute(&sub1) == rhs.form.substitute(&sub2)
				} else {
					false
				}
			},
			(subst::Expr::Seq(f1, s1), subst::Expr::Seq(f2, s2)) => {
				if s1 == s2 && f1.arity() == f2.arity() {
					let i = max!(
						f1.max_sub_index(), 
						s1.max_sub_index(),
						f2.max_sub_index(), 
						s2.max_sub_index());
					let name = expr::FreeSeq::from_int(i + 1, f1.arity()).to_seq();
					let sub1 = subst::Expr::Seq(f1.clone(), name.clone()).to_form();
					let sub2 = subst::Expr::Seq(f2.clone(), name).to_form();
					self.form.substitute(&sub1) == rhs.form.substitute(&sub2)
				} else {
					false
				}
			},
			_ => false
		}
	}


	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool 
	{
		let k = self.sub.append_finfo(info);
		let b2 = self.sub.well_formed(info);
		let b0 = self.form.well_formed(&k);
		b0 && b2
	}

	pub fn max_form_sub_index(&self) -> usize {
		self.form.max_form_sub_index()
	}

	pub fn max_sub_index(&self) -> usize {
		std::cmp::max(self.form.max_sub_index(), self.sub.max_sub_index())
	}
}

impl PartialEq<ExpSubst> for ExpSubst {
	fn eq(&self, rhs: &ExpSubst) -> bool {
		ExpSubst::eq(self, rhs) 
	}
}

impl ToString for ExpSubst {
	fn to_string(&self) -> String { 
		format!("{}[{}]", self.form.to_string(), self.sub.to_string())

	}
}

impl FormName {
	pub fn from_int(i: usize) -> FormName {
		FormName::Subbed(i)
	}

	pub fn from_str(i: &str) -> FormName {
		FormName::String(i.to_string())
	}

	pub fn from_string(i: String) -> FormName {
		FormName::String(i)
	}

	pub fn max_form_sub_index(&self) -> usize {
		match self {
			&FormName::Subbed(i) => i,
			_ => 0
		}
	}

	pub fn to_form(&self) -> Formula {
		Formula::Free(Free::new(self.clone()))
	}
}

impl ToString for FormName {
	fn to_string(&self) -> String {
		match self {
			FormName::String(s) => { s.clone() },
			FormName::Subbed(i) => { format!("f{}", i) }
		}
	}
}


impl ForAllSeq {
	pub fn expand(&self) -> ForAllSeq {
		ForAllSeq { var: self.var.clone(), form: self.form.expand().ptr() }
	}

	pub fn new(var: expr::FreeSeq, form: Formula) -> ForAllSeq {
		ForAllSeq{
			var: var,
			form: form.ptr()
		}
	}

	pub fn from_str(name: &str, arity: usize, form: Formula) -> ForAllSeq {
		ForAllSeq{
			var: expr::FreeSeq::from_str(name, arity),
			form: form.ptr()
		}	
	}

	pub fn from_string(name: String, arity: usize, form: Formula) -> ForAllSeq {
		ForAllSeq{
			var: expr::FreeSeq::from_string(name, arity),
			form: form.ptr()
		}	
	}

	pub fn from_free(name: expr::FreeSeq, form: Formula) -> ForAllSeq {
		ForAllSeq{
			var: name,
			form: form.ptr()
		}	
	}

	pub fn substitute(&self, info: &SInfo) -> ForAllSeq {
		if info.replaces_seq(&self.var) {
			self.clone()
		} else {
			let (exp, f) = info.chain_seq(self.form.deref(), &self.var);
			ForAllSeq::new(f, exp)
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		//let form = self.var.to_const();
		let k = info.append_free_seq(&self.var);
		self.form.well_formed(&k)
	}

	pub fn max_form_sub_index(&self) -> usize {
		std::cmp::max(self.form.max_sub_index(), self.var.name.max_sub_index())
	}

	pub fn max_sub_index(&self) -> usize {
		std::cmp::max(self.var.max_sub_index(), self.form.max_sub_index())
	}

	pub fn instantiate(&self, exp: &expr::SeqVar) -> Formula {
		let info = EInfo::Seq(self.var.clone(), exp.clone()).to_form();
		self.form.substitute(&info)
	}

	pub fn eq(&self, rhs: &ForAllSeq) -> bool {
		if self.var.arity() == rhs.var.arity() {
			let i = max(self.var.max_sub_index(), rhs.var.max_sub_index());
			let name = expr::FreeSeq::from_int(i + 1, self.var.arity()).to_seq();
			let sub1 = subst::Expr::Seq(self.var.clone(), name.clone()).to_form();
			let sub2 = subst::Expr::Seq(rhs.var.clone(), name).to_form();
			self.form.substitute(&sub1) == rhs.form.substitute(&sub2)
		} else {
			false
		}
	}
}

impl ToString for ForAllSeq {
	fn to_string(&self) -> String {
		format!("forall* {} [{}]", self.var.to_string(), self.form.to_string())
	}
}

impl PartialEq<ForAllSeq> for ForAllSeq {
	fn eq(&self, rhs: &ForAllSeq) -> bool {
		ForAllSeq::eq(self, rhs)
	}
}

impl FormSubst {

	pub fn expand(&self) -> FormSubst {
		FormSubst {
			form: self.form.expand().ptr(),
			var: self.var.clone(),
			sub: self.sub.expand().ptr()
		}
	}

	pub fn extract(&self) -> Formula {
		let info = SInfo::Formula(self.var.clone(), self.sub.deref().clone());
		self.form.substitute(&info)
	}

	pub fn new(form: Formula, var: Free, sub: Formula) -> FormSubst {
		FormSubst { 
			form: form.ptr(), 
			var: var, 
			sub: sub.ptr()
		}
	}

	pub fn substitute(&self, info: &SInfo) -> FormSubst {
		if info.replaces_form(&self.var) {
			self.clone()
		} else {
			let (exp, f) = info.chain_form(&self.form, &self.var);
			FormSubst::new(exp, f, self.sub.substitute(info))
		}
	}


	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		let k = info.append_free_form(&self.var);
		let b2 = self.sub.well_formed(info);
		let b0 = self.form.well_formed(&k);
		b0 && b2
	}

	pub fn max_form_sub_index(&self) -> usize {
		let t1 = self.form.max_form_sub_index();
		let t2 = self.var.max_form_sub_index();
		let t3 = self.sub.max_form_sub_index();
		max!(t1, t2, t3)
	}

	pub fn max_sub_index(&self) -> usize {
		std::cmp::max(self.form.max_sub_index(), self.sub.max_sub_index())
	}

	pub fn eq(&self, rhs: &FormSubst) -> bool {
		if self.sub == rhs.sub {
			let i = max!(
				self.var.max_form_sub_index(), 
				rhs.var.max_form_sub_index(),
				self.form.max_form_sub_index(),
				rhs.form.max_form_sub_index());
			let name = FormName::from_int(i + 1).to_form();
			let sub1 = subst::Info::Formula(self.var.clone(), name.clone());
			let sub2 = subst::Info::Formula(rhs.var.clone(), name);
			self.form.substitute(&sub1) == rhs.form.substitute(&sub2)
		} else {
			false
		}
	}
}

impl ToString for FormSubst {
	fn to_string(&self) -> String { 
		format!("{}[{} <<== {}]", 
			self.form.to_string(),
			self.var.to_string(),
			self.sub.to_string())

	}
}

impl PartialEq<FormSubst> for FormSubst {
	fn eq(&self, rhs: & FormSubst) -> bool {
		FormSubst::eq(self, rhs)
	}
}

impl Schema {

	pub fn expand(&self) -> Schema {
		Schema {
			var: self.var.clone(),
			form: self.form.expand().ptr()
		}
	}

	pub fn instantiate(&self, exp: &Formula) -> Formula {
		let info = SInfo::Formula(self.var.clone(), exp.clone());
		self.form.substitute(&info)
	}

	pub fn new(fname: Free, form: Formula) -> Schema {
		Schema {
			var: fname,
			form: form.ptr()
		}
	}

	pub fn from_free(fname: Free, form: Formula) -> Schema {
		Schema {
			var: fname,
			form: form.ptr()
		}
	}

	pub fn from_str(fname: &str, form: Formula) -> Schema {
		Schema {
			var: Free::from_str(fname),
			form: form.ptr()
		}
	}

	pub fn from_string(fname: String, form: Formula) -> Schema {
		Schema {
			var: Free::from_string(fname),
			form: form.ptr()
		}
	}

	pub fn substitute(&self, info: &SInfo) -> Schema {
		if info.replaces_form(&self.var) {
			self.clone()
		} else {
			let (exp, f) = info.chain_form(&self.form, &self.var);
			Schema::new(f, exp)
		}
	}


	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		let k = info.append_free_form(&self.var);
		self.form.well_formed(&k)
	}

	pub fn max_form_sub_index(&self) -> usize {
		std::cmp::max(self.form.max_form_sub_index(), self.form.max_form_sub_index())
	}

	pub fn max_sub_index(&self) -> usize {
		 self.form.max_sub_index()
	}

	pub fn eq(&self, rhs: &Schema) -> bool {
		let i = max!(
			self.var.max_form_sub_index(), 
			rhs.var.max_form_sub_index(),
			self.form.max_form_sub_index(), 
			rhs.form.max_form_sub_index());
		let name = FormName::from_int(i + 1).to_form();
		let sub1 = subst::Info::Formula(self.var.clone(), name.clone());
		let sub2 = subst::Info::Formula(rhs.var.clone(), name);
		self.form.substitute(&sub1) == rhs.form.substitute(&sub2)
	}
}

impl ToString for Schema {
	fn to_string(&self) -> String {
		format!("schema {} [{}]", self.var.to_string(), self.form.to_string())
	}
}

impl PartialEq<Schema> for Schema {
	fn eq(&self, rhs: &Schema) -> bool {
		Schema::eq(self, rhs)
	}
}

impl Relation {
	pub fn new(name: String, vars: Vec<expr::Expr>) -> Relation {
		Relation(name, vars)
	}

	pub fn to_form(self) -> Formula {
		Formula::Relation(self)
	}

	pub fn expand(&self) -> Relation {
		Relation(self.0.clone(), self.1.iter().flat_map(|x| x.expand()).collect())
	}

	pub fn substitute(&self, info: &SInfo)  -> Relation {
		Relation(
			self.0.clone(), 
			self.1.iter().map(|x| x.substitute(info)).collect())
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		info.has_relation(&self.0) && self.1.iter().all(|x| x.well_formed(info))
	}

	pub fn max_form_sub_index(&self) -> usize {
		0
	}

	pub fn max_sub_index(&self) -> usize {
		self.1.iter().map(|x| x.max_sub_index()).max().unwrap()
	}
}

impl ToString for Relation {
	fn to_string(&self) -> String {
		format!("{}({})", 
			self.0.to_string(),
			self.1.iter()
				.map(|x| { x.to_string() })
				.collect::<Vec<String>>()
				.join(", "))
	}
}

impl Arb {

	pub fn expand(&self) -> Arb {
		self.clone()
	}

	pub fn new(fname: FormName) -> Arb { Arb { var: fname } }

	pub fn from_string(fname: String) -> Arb { 
		Arb { var: FormName::from_string(fname) } 
	}

	pub fn from_str(fname: &str) -> Arb { 
		Arb { var: FormName::from_str(fname) } 
	}

	pub fn substitute(&self, _info: &SInfo)  -> Formula {
		Formula::Arb(self.clone())
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		info.has_arb_form(self) 
	}

	pub fn max_form_sub_index(&self) -> usize {
		match &self.var {
			&FormName::Subbed(i) => i,
			_ => 0
		}
	}

	pub fn max_sub_index(&self) -> usize {
		0
	}
}

impl ToString for Arb {
	fn to_string(&self) -> String {
		self.var.to_string()
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

impl Free {

	pub fn expand(&self) -> Free {
		self.clone()
	}

	pub fn from_int(i: usize) -> Free {
		Free::new(FormName::Subbed(i))
	}

	pub fn new(fname: FormName) -> Free { Free { var: fname } }

	pub fn from_str(name: &str) -> Free {
		Free {
			var: FormName::from_str(name)
		}
	}

	pub fn from_string(name: String) -> Free {
		Free {
			var: FormName::from_string(name)
		}
	}

	pub fn substitute(&self, info: &SInfo)  -> Formula {
		match info {
			&SInfo::Formula(ref name, ref form) => if PartialEq::eq(name, &self) {
				form.clone()
			} else {
				Formula::Free(self.clone())
			},
			_ => Formula::Free(self.clone())
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		info.has_free_form(&self) 
	}

	pub fn max_form_sub_index(&self) -> usize {
		match &self.var {
			&FormName::Subbed(i) => i,
			_ => 0
		}
	}

	pub fn max_sub_index(&self) -> usize {
		0
	}
}

impl ToString for Free {
	fn to_string(&self) -> String {
		self.var.to_string()
	}
}


impl Into<Free> for String {
	fn into(self) -> Free {
		Free::from_string(self)
	}
}

impl Into<Free> for &'static str {
	fn into(self) -> Free {
		Free::from_str(self)
	}
}

impl Not {

	pub fn new(f: Formula) -> Not {
		Not { form: f.ptr() }
	}

	pub fn expand(&self) -> Not {
		Not { form: self.form.expand().ptr() }
	}

	pub fn substitute(&self, info: &SInfo) -> Not {
		Not { form: self.form.substitute(info).ptr() }
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
		self.form.well_formed(info)
	}

	pub fn max_form_sub_index(&self) -> usize {
		self.form.max_form_sub_index()
	}

	pub fn max_sub_index(&self) -> usize {
		self.form.max_sub_index()
	}
}

impl ToString for Not {
	fn to_string(&self) -> String {
		format!("not({})", self.form.to_string())
	}
}

impl Eq {

	pub fn expand(&self) -> Eq {
		Eq(self.0.expand(), self.1.expand())
	}

	pub fn substitute(&self, info: &SInfo) -> Eq {
		Eq(self.0.substitute(info), self.1.substitute(info))
	}

	pub fn max_form_sub_index(&self) -> usize {
		0
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
			-> bool {
		self.0.well_formed(info) && self.1.well_formed(info)
	}

	pub fn max_sub_index(&self) -> usize {
		std::cmp::max(self.0.max_sub_index(), self.1.max_sub_index())
	}


	pub fn new(e1: expr::Singular, e2: expr::Singular) -> Eq {
		Eq(e1, e2)
	}
}

impl ToString for Eq {
	fn to_string(&self) -> String {
		format!("{} = {}", self.0.to_string(), self.1.to_string())
	}
}


