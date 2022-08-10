use std::collections::LinkedList;
use std::ops::Deref;
use std::sync::Arc;

use Ptr;
use formula;
use expr;
use subst::Expr as EInfo;
use knowledge_base as kbase;
use knowledge_base::{
	KnowledgeBase,
	ResultBase,
	ContextBase
};
use formed::Info as FInfo;

/// Reference type for Deductions.
pub type Work = Ptr<Deduction>;

/// The results from performing a deduction: 
/// - Ok(resulting knowledgebase)
/// - Err(The stack of steps and their error messages.)
pub type DResult<K> = Result<kbase::ResultBase<K>, LinkedList<(Work, String)>>;

/// Initializes the error stack.
pub fn err<K>(msg: String, step: Work) -> DResult<K> {
	let mut l = LinkedList::new();
	l.push_back((step, msg));
	Err(l)
}

/// Appends to the result the ty
pub fn stack<K>(result: DResult<K>, msg: (Work, String)) -> DResult<K> {
	match result {
		Err(mut l) => {
			l.push_back(msg);
			Err(l)
		},
		r => r
	}
}

pub enum Deduction {
	EmptyStep,
	IFFIntro(IFFIntro),
	IFFExtract(IFFExtract),
	SubstExtract(SubstExtract),
	AndIntro(AndIntro),
	OrIntro(OrIntro),
	AndExtract(AndExtract),
	SubstIntro(SubstIntro),
	OrExtract(OrExtract),
	ImplyIntro(ImplyIntro),
	ImplyExtract(ImplyExtract),
	NegationIntro(NegationIntro),
	NegationExtract(NegationExtract),
	EqualityIntro(EqualityIntro),
	Substitution(Substitution),
	ForAllSeqExtract(ForAllSeqExtract),
	ForAllExtract(ForAllExtract),
	ForAllSeqIntro(ForAllSeqIntro),
	ForAllIntro(ForAllIntro),
	ExistsIntro(ExistsIntro),
	ExistsExtract(ExistsExtract),
	SchemaExtract(SchemaExtract),
	SchemaIntro(SchemaIntro),
	Sequence(Sequence),
	Let(Let),
	ExpSubstReduction(ExpSubstReduction),
	FormSubstReduction(FormSubstReduction),
	LambdaInstIntro(LambdaInstIntro),
	LambdaSeqInstIntro(LambdaSeqInstIntro),
}

#[derive(Clone)]
pub struct IFFIntro { thm: formula::IFF, w1: Work, w2: Work }

#[derive(Clone)]
pub struct SubstIntro { thm: formula::ExpSubst, w: Work }

#[derive(Clone)]
pub struct IFFExtract{ thm: formula::IFF, w: Work }
#[derive(Clone)]
pub struct AndIntro { thm: formula::And, w1: Work, w2: Work }

#[derive(Clone)]
pub struct OrIntro { thm: formula::Or, w1: Work, w2: Work }

#[derive(Clone)]
pub struct AndExtract {thm: formula::And, w: Work }

#[derive(Clone)]
pub struct ImplyIntro{ thm: formula::Implies, w: Work }

#[derive(Clone)]
pub struct ImplyExtract { thm: formula::Implies, w1: Work, w2: Work }

#[derive(Clone)]
pub struct OrExtract { 
	thm: formula::Or, 
	to_thm: formula::FormPtr,
	w1: Work, 
	w2: Work, 
	w3: Work
}
#[derive(Clone)]
pub struct NegationIntro {thm: formula::Not, w: Work }

#[derive(Clone)]
pub struct NegationExtract { thm: formula::Not, w1: Work, w2: Work }

#[derive(Clone)]
pub struct EqualityIntro(pub expr::Singular);

#[derive(Clone)]
pub struct Substitution { 
	t1: expr::Singular, 
	t2: expr::Singular,
	c: expr::Free,
	form: formula::Formula, 
	w1: Work, 
	w2: Work
}

#[derive(Clone)]
pub struct ForAllSeqExtract {
	thm: formula::ForAllSeq,
	sub: expr::SeqVar,  
	w: Work
}

#[derive(Clone)]
pub struct ForAllExtract{
	thm: formula::ForAll, 
	sub: expr::Singular,
	w: Work
}

#[derive(Clone)]
pub struct ForAllSeqIntro {
	thm: formula::ForAllSeq,
	letv: expr::ArbSeq,
	w: Work
}

#[derive(Clone)]
pub struct SubstExtract{ thm: formula::ExpSubst, w: Work }

#[derive(Clone)]
pub struct LambdaSeqInstIntro	{
	v: expr::Singular,
	inst: expr::LambdaSeqInst,
	work: Work
}

#[derive(Clone)]
pub struct ForAllIntro {
	thm: formula::ForAll,
	letv: expr:: Arb,
	w: Work
}

#[derive(Clone)]
pub struct ExistsIntro {
	thm: formula::Exists,
	var: expr::Singular,
	w: Work
}

#[derive(Clone)]
pub struct ExistsExtract {
	thm: formula::Exists,
	var: expr::Const,
	w: Work
}

#[derive(Clone)]
pub struct SchemaExtract { 
	thm: formula::Schema, 
	form: formula::Formula, 
	w: Work
}

#[derive(Clone)]
pub struct SchemaIntro {
	thm: formula::Schema,
	letv: formula::Arb,
	w: Work
}

#[derive(Clone)]
pub struct Sequence(Work, Work);

#[derive(Clone)]
pub struct Let(String, expr::Singular, Work);

#[derive(Clone)]
pub struct ExpSubstReduction {
	thm: formula::ExpSubst, 
	work: Work
}

#[derive(Clone)]
pub struct FormSubstReduction {
	thm: formula::FormSubst, 
	work: Work
}

#[derive(Clone)]
pub struct LambdaInstIntro	{
	v: expr::Singular,
	inst: expr::LambdaInst,
	work: Work
}

impl Deduction {
	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K> 
	{
		match self {
			Deduction::EmptyStep             => Ok(kbase.clone()),
			Deduction::IFFIntro(f)           => f.deduce(kbase),
			Deduction::IFFExtract(f)         => f.deduce(kbase),
			Deduction::SubstExtract(f)       => f.deduce(kbase),
			Deduction::AndIntro(f)           => f.deduce(kbase),
			Deduction::OrIntro(f)            => f.deduce(kbase),
			Deduction::AndExtract(f)         => f.deduce(kbase),
			Deduction::SubstIntro(f)         => f.deduce(kbase),
			Deduction::OrExtract(f)          => f.deduce(kbase),
			Deduction::ImplyIntro(f)         => f.deduce(kbase),
			Deduction::ImplyExtract(f)       => f.deduce(kbase),
			Deduction::NegationIntro(f)      => f.deduce(kbase),
			Deduction::NegationExtract(f)    => f.deduce(kbase),
			Deduction::EqualityIntro(f)      => f.deduce(kbase),
			Deduction::Substitution(f)       => f.deduce(kbase),
			Deduction::ForAllSeqExtract(f)   => f.deduce(kbase),
			Deduction::ForAllExtract(f)      => f.deduce(kbase),
			Deduction::ForAllSeqIntro(f)     => f.deduce(kbase),
			Deduction::ForAllIntro(f)        => f.deduce(kbase),
			Deduction::ExistsIntro(f)        => f.deduce(kbase),
			Deduction::ExistsExtract(f)      => f.deduce(kbase),
			Deduction::SchemaExtract(f)      => f.deduce(kbase),
			Deduction::SchemaIntro(f)        => f.deduce(kbase),
			Deduction::Sequence(f)           => f.deduce(kbase),
			Deduction::Let(f)                => f.deduce(kbase),
			Deduction::ExpSubstReduction(f)  => f.deduce(kbase),
			Deduction::FormSubstReduction(f) => f.deduce(kbase),
			Deduction::LambdaInstIntro(f)    => f.deduce(kbase),
			Deduction::LambdaSeqInstIntro(f) => f.deduce(kbase),
		}
	}

	pub fn begin<K: KnowledgeBase>(&self, k: K) -> DResult<K> {
		let kbase = kbase::ResultBase::new(k);
		self.deduce(&kbase)
	}

	pub fn ptr(self) -> Work {
		Arc::new(self)
	}

	pub fn to_deduction(self) -> Deduction { self }
}

macro_rules! impl_to_deduct {
	($t: ident) => {
		impl $t {
			pub fn to_deduction(&self) -> Deduction { 
				Deduction::$t(Clone::clone(self)) 
			}
			pub fn ptr(self) -> Work {
				Arc::new(self.to_deduction())
			}
		}
	}
}

impl_to_deduct!(IFFIntro);
impl_to_deduct!(IFFExtract);
impl_to_deduct!(SubstExtract);
impl_to_deduct!(AndIntro);
impl_to_deduct!(OrIntro);
impl_to_deduct!(AndExtract);
impl_to_deduct!(SubstIntro);
impl_to_deduct!(OrExtract);
impl_to_deduct!(ImplyIntro);
impl_to_deduct!(ImplyExtract);
impl_to_deduct!(NegationIntro);
impl_to_deduct!(NegationExtract);
impl_to_deduct!(EqualityIntro);
impl_to_deduct!(Substitution);
impl_to_deduct!(ForAllSeqExtract);
impl_to_deduct!(ForAllExtract);
impl_to_deduct!(ForAllSeqIntro);
impl_to_deduct!(ForAllIntro);
impl_to_deduct!(ExistsIntro);
impl_to_deduct!(ExistsExtract);
impl_to_deduct!(SchemaExtract);
impl_to_deduct!(SchemaIntro);
impl_to_deduct!(Sequence);
impl_to_deduct!(Let);
impl_to_deduct!(ExpSubstReduction);
impl_to_deduct!(FormSubstReduction);
impl_to_deduct!(LambdaInstIntro);
impl_to_deduct!(LambdaSeqInstIntro);




impl IFFIntro {
	pub fn new(thm: formula::IFF, w1: Deduction, w2: Deduction) -> IFFIntro {
		IFFIntro {
			thm: thm,
			w1: w1.ptr(),
			w2: w2.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>
	{
		let k1 = kbase.clone().result_ptr(self.thm.left.clone());
		let k2 = kbase.clone().result_ptr(self.thm.right.clone());
		
		match self.w1.deduce(&k1) {
			Ok(k) => if k.deduced(&self.thm.right) {
				match self.w2.deduce(&k2) {
					Ok(k) => if k.deduced(&self.thm.left) {
						let form = formula::Formula::IFF(self.thm.clone());
						let new = kbase.clone().result_form(form);
						Ok(new)
					} else {
						let msg = format!("Failed to deduce {} in case 2.", 
							(self.thm).left.to_string());
						err(msg, self.to_deduction().ptr())
					},
					e => e
				}
			} else {
				let msg = format!("Failed to deduce {} in case 1.", 
					(self.thm).right.to_string());
				err(msg, self.to_deduction().ptr())
			}
			e => e
		}
	}
}


impl SubstIntro {
	pub fn new(thm: formula::ExpSubst, w: Deduction) -> SubstIntro {
		SubstIntro {
			thm: thm,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>
	{
		let f = self.thm.extract();
		match self.w.deduce(kbase) {
			Ok(k) => {
				if k.deduced(&f) {
					Ok(k.result_form(f))
				} else {
					let msg = format!("Failed to deduce {}.", 
						f.to_string());
					err(msg, self.to_deduction().ptr())
				}
			}
			e => e
		}
	}
}

impl IFFExtract {

	pub fn new(thm: formula::IFF, w: Deduction) -> IFFExtract {
		IFFExtract {
			thm: thm,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w.deduce(kbase) {
			Ok(k) => {
				let (b1, b2) = 
					(k.deduced(self.thm.left.deref()), k.deduced(self.thm.right.deref()));
				if !(b1 || b2) {
					let msg = format!("Failed to deduce either formula.");
					err(msg, self.to_deduction().ptr())
				} else {
					if b1 {
						Ok(k.result_ptr(self.thm.right.clone()))
					} else {
						Ok(k.result_ptr(self.thm.left.clone()))
					}
				}
			}
			e => e
		}
	}
}



impl SubstExtract {

	pub fn new(thm: formula::ExpSubst, w: Deduction) -> SubstExtract {
		SubstExtract {
			thm: thm,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		let f = self.thm.extract();
		match self.w.deduce(kbase) {
			Ok(k) => {
				if k.deduced(&self.thm.to_form()) {
					Ok(k.result_form(f))
				} else {
					let msg = format!("Failed to deduce {}.", 
						self.thm.to_string());
					err(msg, self.to_deduction().ptr())
				}
			}
			e => e
		}
	}
}



impl AndIntro {

	pub fn new(thm: formula::And, w1: Deduction, w2: Deduction) -> AndIntro {
		AndIntro {
			thm: thm,
			w1: w1.ptr(),
			w2: w2.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w1.deduce(kbase) {
			Ok(k1) => match self.w2.deduce(&k1) {
				Ok(k2) => {
					let (b1, b2) = (
						k2.deduced(self.thm.left.deref()), 
						k2.deduced(self.thm.right.deref()));
					if b1 && b2 {
						Ok(k2.result_form(self.thm.to_form()))
					} else if !b1 {
						let msg = format!("Failed to deduce {}.", 
							self.thm.left.to_string());
						err(msg, self.to_deduction().ptr())
					} else {
						let msg = format!("Failed to deduce {}.", 
							self.thm.right.to_string());
						err(msg, self.to_deduction().ptr())
					}
				}
				e => e
			},
			e => e
		}
	}
}


impl OrIntro {

	pub fn new(thm: formula::Or, w1: Deduction, w2: Deduction) -> OrIntro {
		OrIntro {
			thm: thm,
			w1: w1.ptr(),
			w2: w2.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  
	{
		match self.w1.deduce(kbase) {
			Ok(k1) => match self.w2.deduce(&k1) {
				Ok(k2) => {
					let (b1, b2) = (
						k2.deduced(self.thm.left.deref()), 
						k2.deduced(self.thm.right.deref()));
					if b1 || b2 {
						Ok(k2.result_form(self.thm.to_form()))
					} else if !b1 {
						let msg = format!("Failed to deduce {}.", 
							self.thm.left.to_string());
						err(msg, self.to_deduction().ptr())
					} else {
						let msg = format!("Failed to deduce {}.", 
							self.thm.right.to_string());
						err(msg, self.to_deduction().ptr())
					}
				}
				e => e
			},
			e => e
		}
	}
}

impl AndExtract {

	pub fn new(thm: formula::And, w: Deduction) -> AndExtract {
		AndExtract {
			thm: thm,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w.deduce(kbase) {
			Ok(k) => {
				let k = k
					.result_ptr(self.thm.left.clone())
					.result_ptr(self.thm.right.clone());
				Ok(k)
			}
			e => e
		}
	}
}

impl OrExtract {

	pub fn new(
		thm: formula::Or, 
		to_thm: formula::Formula, 
		w1: Deduction, 
		w2: Deduction, 
		w3: Deduction) 
	-> OrExtract {
		OrExtract {
			thm: thm,
			to_thm: to_thm.ptr(),
			w1: w1.ptr(),
			w2: w2.ptr(),
			w3: w3.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w1.deduce(kbase) {
			Ok(k1) => if k1.deduced(&self.thm.to_form()) {
				let kc1 = k1.result_ptr(self.thm.left.clone());
				let kc2 = k1.result_ptr(self.thm.right.clone());
				match self.w2.deduce(&kc1) {
					Ok(k2) => if k2.deduced(self.to_thm.deref()) {
						match self.w3.deduce(&kc2) {
							Ok(_k3) => if k2.deduced(self.to_thm.deref()) {
								let k = kbase.result_ptr(self.to_thm.clone());
								Ok(k)
							} else {
								let msg = format!("Failed to deduce theorem in case 2.");
								err(msg, self.to_deduction().ptr())
							},
							e => e
						}
					} else {
						let msg = format!("Failed to deduce theorem in case 1.");
						err(msg, self.to_deduction().ptr())
					},
					e => e
				}
			} else {
				let msg = format!("Failed to deduce {}.", 
					self.thm.to_string());
				err(msg, self.to_deduction().ptr())
			},
			e => e
		}
	}
}


impl ImplyIntro {

	pub fn new(thm: formula::Implies, w: Deduction) -> ImplyIntro {
		ImplyIntro {
			thm: thm,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		let assume = kbase.result_ptr(self.thm.left.clone());
		match self.w.deduce(&assume) {
			Ok(_k) => {
				let k = kbase.result_form(self.thm.clone().to_form());
					//.result_ptr(self.thm.left.clone())
					//.result_ptr(self.thm.right.clone());
				Ok(k)
			}
			e => e
		}
	}
}

impl ImplyExtract {

	pub fn new(thm: formula::Implies, w1: Deduction, w2: Deduction) -> ImplyExtract {
		ImplyExtract {
			thm: thm,
			w1: w1.ptr(),
			w2: w2.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w1.deduce(kbase) { 
			Ok(k1) => if k1.deduced(&self.thm.to_form()) {
				match self.w2.deduce(&k1) {
					Ok(k2) => {
						if k2.deduced(&self.thm.left) {
							let k = k2.result_ptr(self.thm.right.clone());
							Ok(k)
						} else {
							let msg = format!(
								"Didn't deduce premise {}", 
								self.thm.left.to_string());
							err(msg, self.to_deduction().ptr())		
						}
					},
					e => e
				}
			} else {
				let msg = format!("Didn't deduce implication {}", self.thm.to_string());
				err(msg, self.to_deduction().ptr())
			},
			e => e
		}
	}
}

// Proof by Contradiction: Assume P conclude False, therefore Not(P)
impl NegationIntro {

	pub fn new(thm: formula::Not, w: Deduction) -> NegationIntro {
		NegationIntro {
			thm: thm,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		let assume = kbase.result_ptr(self.thm.form.clone()).ptr();
		match self.w.deduce(&assume) {
			Ok(k) => if k.deduced(&formula::Formula::False) {
				Ok(kbase.result_form(self.thm.to_form()))
			} else {
				let msg = format!("Failed to deduce a contradiction.");
				err(msg, self.to_deduction().ptr())
			},
			e => e
		}
	}
}

impl NegationExtract {

	pub fn new(thm: formula::Not, w1: Deduction, w2: Deduction) -> NegationExtract {
		NegationExtract {
			thm: thm,
			w1: w1.ptr(),
			w2: w2.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w1.deduce(kbase) {
			Ok(_k1) => match self.w2.deduce(kbase) {
				Ok(k2) => {
					let c1 = k2.deduced(&self.thm.to_form());
					let c2 = k2.deduced(&self.thm.form.clone());
					if c1 && c2 {
						Ok(k2.result_form(formula::Formula::False))
					} else if !c1 {
						let msg = format!("Failed to deduce the negation.");
						err(msg, self.to_deduction().ptr())
					} else {
						let msg = format!("Failed to deduce the inner form.");
						err(msg, self.to_deduction().ptr())
					}
				},
				e => e
			}, 
			e => e
		}
	}
}

impl EqualityIntro {
	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		let form = formula::Eq::new(self.0.clone(), self.0.clone()).to_form();
		Ok(kbase.result_form(form))
	}
}

impl Substitution {

	pub fn new(
		t1: expr::Singular, 
		t2: expr::Singular,
		c: expr::Free,
		form: formula::Formula, 
		w1: Deduction, 
		w2: Deduction) 
	-> Substitution {
		Substitution {
			t1: t1,
			t2: t2,
			c: c,
			form: form, 
			w1: w1.ptr(), 
			w2: w2.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w1.deduce(kbase) {
			Ok(k1) => {
				let c1 = k1.deduced(
					&formula::Eq::new(self.t1.clone(), self.t2.clone()).to_form());
				let c2 = k1.deduced(
					&formula::Eq::new(self.t2.clone(), self.t1.clone()).to_form());
				if c1 || c2 {
					let s1 = EInfo::Singular(self.c.clone(), self.t1.clone()).to_form();
					let s2 = EInfo::Singular(self.c.clone(), self.t2.clone()).to_form();
					let form = self.form.substitute(&s1);
					let kf = k1.result_form(form.clone()).ptr();
					match self.w2.deduce(&kf) {
						Ok(k2) => if k2.deduced(&form) {
							let form = self.form.substitute(&s2);
							Ok(k2.result_form(form))
						} else {
							let msg = format!("Failed to deduce the desired formula.");
							err(msg, self.to_deduction().ptr())
						},
						e => e
					}
				} else {
					let msg = format!("Failed to deduce equality of t2 and t2.");
					err(msg, self.to_deduction().ptr())
				}
			},
			e => e
		}
	}
}

impl ForAllSeqExtract {

	pub fn new(thm: formula::ForAllSeq, sub: expr::SeqVar, w: Deduction) -> ForAllSeqExtract {
		ForAllSeqExtract {
			thm: thm,
			sub: sub,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w.deduce(kbase) {
			Ok(k1) => if k1.deduced(&self.thm.to_form()) {
				let thm = self.thm.instantiate(&self.sub);
				Ok(k1.result_form(thm))
			} else {
				let msg = format!("Failed to deduce ForAll statement");
				err(msg, self.to_deduction().ptr())
			}, 
			e => e
		}
	}
}


impl ForAllExtract {

	pub fn new(thm: formula::ForAll, sub: expr::Singular, w: Deduction) -> ForAllExtract {
		ForAllExtract {
			thm: thm,
			sub: sub,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w.deduce(kbase) {
			Ok(k1) => if k1.deduced(&self.thm.to_form()) {
				let thm = self.thm.instantiate(&self.sub);
				Ok(k1.result_form(thm))
			} else {
				let msg = format!("Failed to deduce ForAll statement");
				err(msg, self.to_deduction().ptr())
			}, 
			e => e
		}
	}
}


impl ForAllSeqIntro {

	pub fn new(thm: formula::ForAllSeq, letv: expr::ArbSeq, w: Deduction) 
	-> ForAllSeqIntro {
		ForAllSeqIntro {
			thm: thm,
			letv: letv,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		if kbase.has_arb_seq(&self.letv) {
			let msg = format!("Constant in use.");
			err(msg, self.to_deduction().ptr())
		} else {
			let kf = kbase.result_arb_seq(self.letv.clone()).ptr();
			let result = self.thm.instantiate(&self.letv.clone().to_seq());
		
			match self.w.deduce(&kf) {
				Ok(k1) => if k1.deduced(&result) {
					Ok(k1.result_form(self.thm.clone().to_form()))
				} else {
					let msg = format!("Failed to deduce inner statement");
					err(msg, self.to_deduction().ptr())
				}, 
				e => e
			}
		}
	}
}

impl ForAllIntro {

	pub fn new(thm: formula::ForAll, letv: expr::Arb, w: Deduction) -> ForAllIntro {
		ForAllIntro {
			thm: thm,
			letv,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		if kbase.has_arb(&self.letv) {
			let msg = format!("Constant in use.");
			err(msg, self.to_deduction().ptr())
		} else {
			let kf = kbase.result_arb(self.letv.clone()).ptr();
		
			match self.w.deduce(&kf) {
				Ok(k1) => if k1.deduced(&self.thm.to_form()) {
					Ok(k1.result_form(self.thm.to_form()))
				} else {
					let msg = format!("Failed to deduce inner statement");
					err(msg, self.to_deduction().ptr())
				}, 
				e => e
			}
		}
	}
}

impl ExistsIntro {

	pub fn new(thm: formula::Exists, var: expr::Singular, w: Deduction) -> ExistsIntro {
		ExistsIntro {
			thm: thm,
			var: var,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w.deduce(kbase) {
			Ok(k) => {
				let f = self.thm.instantiate(&self.var);
				if k.deduced(&f) {
					Ok(k.result_form(self.thm.to_form()))
				} else {
					let msg = format!("Failed to deduce inner statement");
					err(msg, self.to_deduction().ptr())
				}
			},
			e => e
		}
	}
}

impl ExistsExtract {

	pub fn new(thm: formula::Exists, var: expr::Const, w: Deduction) -> ExistsExtract {
		ExistsExtract {
			thm: thm,
			var: var,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w.deduce(kbase) {
			Ok(k) => {
				let c = expr::Singular::Const(self.var.clone());
				let f = self.thm.instantiate(&c);
				if k.deduced(&self.thm.to_form()) {
					Ok(k.result_form(f))
				} else {
					let msg = format!("Failed to deduce inner statement");
					err(msg, self.to_deduction().ptr())
				}
			},
			e => e
		}
	}
}

impl SchemaExtract {

	pub fn new(thm: formula::Schema, form: formula::Formula, w: Deduction) -> SchemaExtract {
		SchemaExtract {
			thm: thm,
			form: form,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.w.deduce(kbase) {
			Ok(k) => if k.deduced(&self.thm.to_form()) {
				let thm = self.thm.instantiate(&self.form);
				Ok(k.result_form(thm))
			} else {
				let msg = format!("Failed to deduce inner statement");
				err(msg, self.to_deduction().ptr())
			},
			e => e
		}
	}
}

impl SchemaIntro {

	pub fn new(thm: formula::Schema, letv: formula::Arb, w: Deduction) -> SchemaIntro {
		SchemaIntro {
			thm: thm,
			letv: letv,
			w: w.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		if kbase.has_arb_form(&self.letv) {
			let msg = format!("formula constant in use.");
			err(msg, self.to_deduction().ptr())
		} else {
			let kf = kbase.result_arb_form(self.letv.clone()).ptr();
			let result = self.thm.instantiate(&self.letv.to_form());
		
			match self.w.deduce(&kf) {
				Ok(k1) => if k1.deduced(&result) {
					Ok(k1.result_form(self.thm.to_form()))
				} else {
					let msg = format!("Failed to deduce inner statement");
					err(msg, self.to_deduction().ptr())
				}, 
				e => e
			}
		}
	}
}

impl Sequence {

	pub fn new(w1: Deduction, w2: Deduction) -> Sequence {
		Sequence(w1.ptr(), w2.ptr())
	}

	pub fn cons(w1: Deduction, w2: Deduction) -> Deduction {
		match w1 {
			Deduction::EmptyStep => w2,
			w1 => match w2 {
				Deduction::EmptyStep => w1,
				w2 => Sequence(w1.ptr(), w2.ptr()).to_deduction()
			}
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.0.deduce(kbase) {
			Ok(k) => match self.1.deduce(&k) {
				r@Ok(_) => r,
				e => e
			},
			e => e
		}
	}
}

impl Let {

	pub fn new(v: String, s: expr::Singular, w: Deduction) -> Let {
		Let(v, s, w.ptr())
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		let c = expr::Const(expr::ConstName::String(self.0.clone()));
		if kbase.has_const(&c) {
			let msg = format!("Cannot overwrite constant.");
			err(msg, self.to_deduction().ptr())
		} else {
			let k = kbase.result_const(c.clone())
				.result_form(formula::Eq::new(c.to_singular(), self.1.clone()).to_form());
			match self.2.deduce(&k) {
				Ok(k) => Ok(k.remove_const(&self.0)),
				k => k
			}			
		}
	}
}

impl ExpSubstReduction {

	pub fn new(thm: formula::ExpSubst, 	work: Deduction) -> ExpSubstReduction {
		ExpSubstReduction {
			thm: thm,
			work: work.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.work.deduce(kbase) {
			Ok(k) => if k.deduced(&self.thm.to_form()) {
				let k = k.result_form(self.thm.extract());
				Ok(k)
			} else {
				let msg = format!("Did not deduce the subst form.");
				err(msg, self.to_deduction().ptr())
			}
			e => e
		}
	}
}

impl FormSubstReduction {

	pub fn new(thm: formula::FormSubst, work: Deduction) -> FormSubstReduction {
		FormSubstReduction {
			thm: thm,
			work: work.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		match self.work.deduce(kbase) {
			Ok(k) => if k.deduced(&self.thm.to_form()) {
				let k = k.result_form(self.thm.extract());
				Ok(k)
			} else {
				let msg = format!("Did not deduce the subst form.");
				err(msg, self.to_deduction().ptr())
			}
			e => e
		}
	}
}

impl LambdaInstIntro {

	pub fn new(v: expr::Singular, inst: expr::LambdaInst, work: Deduction) 
	-> LambdaInstIntro {
		LambdaInstIntro {
			v: v,
			inst: inst,
			work: work.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		let s = self.inst.extract();
		if self.v.well_formed(&FInfo::new(kbase)) {
			if s == self.v {
				Ok(kbase.result_form(
					formula::Eq::new(self.v.clone(), s.clone()).to_form()))
			} else {
				let msg = format!("Lambda is not equal to the expression.");
				err(msg, self.to_deduction().ptr())
			}
		} else {
			let msg = format!("Desired constant is not well formed.");
			err(msg, self.to_deduction().ptr())
		}
	}
}



impl LambdaSeqInstIntro {

	pub fn new(v: expr::Singular, inst: expr::LambdaSeqInst, work: Deduction) 
	-> LambdaSeqInstIntro {
		LambdaSeqInstIntro {
			v: v,
			inst: inst,
			work: work.ptr()
		}
	}

	pub fn deduce<K: KnowledgeBase>(&self, kbase: &ResultBase<K>) 
	-> DResult<K>  {
		let s = self.inst.extract();
		if self.v.well_formed(&FInfo::new(kbase)) {
			if s == self.v {
				Ok(kbase.result_form(
					formula::Eq::new(self.v.clone(), s.clone()).to_form()))
			} else {
				let msg = format!("Lambda is not equal to the expression.");
				err(msg, self.to_deduction().ptr())
			}
		} else {
			let msg = format!("Desired constant is not well formed.");
			err(msg, self.to_deduction().ptr())
		}
	}
}