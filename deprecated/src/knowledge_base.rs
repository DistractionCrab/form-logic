/// This module holds the information that defines the possible operations
/// for a KnowledgeBase, the root logical structure for holding proven theorem
/// and axioms, and a ContextBase, an extension of the KnowledgeBase that can
/// contain arbitrary variables (used in proving quantifiers).

use formula;
use expr;
use std::sync::Arc;
use std::ops::Deref;

/// Default pointer type for a knowledge base.
pub type KBasePtr<T> = Arc<T>;

/// Returns the pointer type for a knowledge base.
pub fn ptr<K: Clone>(kbase: &K) -> KBasePtr<K> {
	Arc::new(Clone::clone(kbase))
}

/// This trait defines the operations for a knowledge base.
pub trait KnowledgeBase {
	/// Returns whether or not the formula has been proven. Implementors
	/// Should check for well-formedness as a safe-guard for internal errors.
	fn deduced(&self, form: &formula::Formula) -> bool;

	/// Returns whether or not the constant has been defined/declared.
	fn has_const(&self, c: &expr::Const) -> bool;

	/// Returns whether or not the sequence constant has been defined/declared.
	fn has_seq_const(&self, c: &expr::SeqConst) -> bool;

	/// Returns whether or not the relation name has been defined.
	fn has_relation(&self, r: &String) -> bool;

	/// Returns whether or not the function symbol has been defined.
	fn has_expr(&self, expr: &String) -> bool;
}

/// This trait extends knowledge base operations to handle the needed information
/// during proofs. Specifically for arbitrary constants being defined in the
/// ForAll proof contexts.
pub trait ContextBase: KnowledgeBase {
	fn has_arb(&self, ab: &expr::Arb) -> bool;
	fn has_arb_seq(&self, ab: &expr::ArbSeq) -> bool;
	fn has_arb_form(&self, ab: &formula::Arb) -> bool;
}

/// ContextBase implementation for proofs. Uses a knowledge base implementor
/// as its root, and is extended as needed.
pub enum ResultBase<K> {
	Root(Arc<K>),
	Arb(expr::Arb, Arc<ResultBase<K>>),
	ArbSeq(expr::ArbSeq, Arc<ResultBase<K>>),
	ArbForm(formula::Arb, Arc<ResultBase<K>>),
	Formula(formula::Formula, Arc<ResultBase<K>>),
	FormPtr(formula::FormPtr, Arc<ResultBase<K>>),
	Const(expr::Const, Arc<ResultBase<K>>),
	SeqConst(expr::SeqConst, Arc<ResultBase<K>>),
}

impl <K> Clone for ResultBase<K> {
	fn clone(&self) -> ResultBase<K> {
		match self {
			ResultBase::Root(r) => ResultBase::Root(r.clone()),
			ResultBase::Formula(f, k) => ResultBase::Formula(f.clone(), k.clone()),
			ResultBase::FormPtr(f, k) => ResultBase::FormPtr(f.clone(), k.clone()),
			ResultBase::Const(f, k) => ResultBase::Const(f.clone(), k.clone()),
			ResultBase::SeqConst(f, k) => ResultBase::SeqConst(f.clone(), k.clone()),
			ResultBase::Arb(f, k) => ResultBase::Arb(f.clone(), k.clone()),
			ResultBase::ArbSeq(f, k) => ResultBase::ArbSeq(f.clone(), k.clone()),
			ResultBase::ArbForm(f, k) => ResultBase::ArbForm(f.clone(), k.clone()),
		}
	}
}

impl <K: KnowledgeBase> ResultBase<K> {
	
	/// Returns a reference to the root knowledge base.
	fn get_kbase<'a>(&'a self) -> &'a K {
		match self {
			ResultBase::Root(k) => k.deref(),
			ResultBase::Formula(_, k) => k.get_kbase(),
			ResultBase::FormPtr(_, k) => k.get_kbase(),
			ResultBase::Const(_, k) => k.get_kbase(),
			ResultBase::SeqConst(_, k) => k.get_kbase(),
			ResultBase::Arb(_, k) => k.get_kbase(),
			ResultBase::ArbSeq(_, k) => k.get_kbase(),
			ResultBase::ArbForm(_, k) => k.get_kbase(),
		}
	}

	/// Returns the kbase with the given constant removed.
	pub fn remove_const(&self, name: &String) -> ResultBase<K> {
		match self {
			ResultBase::Root(_) => self.clone(),
			ResultBase::Formula(f, k) => 
				ResultBase::Formula(f.clone(), k.remove_const(name).ptr()),
			ResultBase::FormPtr(f, k) => 
				ResultBase::FormPtr(f.clone(), k.remove_const(name).ptr()),
			ResultBase::Const(c, k) => if PartialEq::eq(c, name) {
				k.remove_const(name)
			} else {
				ResultBase::Const(c.clone(), k.remove_const(name).ptr())
			},
			ResultBase::SeqConst(s, k) => 
				ResultBase::SeqConst(s.clone(), k.remove_const(name).ptr()),
			ResultBase::Arb(a, k) => 
				ResultBase::Arb(a.clone(), k.remove_const(name).ptr()),
			ResultBase::ArbSeq(a, k) => 
				ResultBase::ArbSeq(a.clone(), k.remove_const(name).ptr()),
			ResultBase::ArbForm(a, k) => 
				ResultBase::ArbForm(a.clone(), k.remove_const(name).ptr()),
		}
	}

	/// Wraps this object in a pointer type.
	pub fn ptr(&self) -> KBasePtr<ResultBase<K>> { 
		Arc::new(self.clone()) 
	}

	pub fn new(kbase: K) -> ResultBase<K> {
		ResultBase::Root(Arc::new(kbase))
	}

	/// Appends a formula pointer to this result base.
	pub fn result_ptr(&self, form: formula::FormPtr) -> ResultBase<K> {
		ResultBase::FormPtr(form, self.ptr())
	}

	/// Appends a formula to this result base.
	pub fn result_form(&self, form: formula::Formula) -> ResultBase<K> {
		ResultBase::Formula(form, Arc::new(self.clone()))
	}

	/// Appends a sequence constant to this result base.
	pub fn result_seq_const(&self, sq: expr::SeqConst) -> ResultBase<K> {
		ResultBase::SeqConst(sq, Arc::new(self.clone()))
	}

	/// Appends a constant to this result base.
	pub fn result_const(&self, sq: expr::Const) -> ResultBase<K> {
		ResultBase::Const(sq, Arc::new(self.clone()))
	}

	/// Appends an arbitrary constant to this result base.
	pub fn result_arb(&self, sq: expr::Arb) -> ResultBase<K> {
		ResultBase::Arb(sq, Arc::new(self.clone()))
	}

	/// Appends an arbitrary sequence constant to this result base.
	pub fn result_arb_seq(&self, sq: expr::ArbSeq) -> ResultBase<K> {
		ResultBase::ArbSeq(sq, Arc::new(self.clone()))
	}

	/// Appends an arbitrary formula to this result base.
	pub fn result_arb_form(&self, sq: formula::Arb) -> ResultBase<K> {
		ResultBase::ArbForm(sq, Arc::new(self.clone()))
	}
}

impl <K: KnowledgeBase> KnowledgeBase for ResultBase<K> {
	fn deduced(&self, form: &formula::Formula) -> bool { 
		match self {
			ResultBase::Root(r) => r.deduced(form),
			ResultBase::Arb(_, k) => k.deduced(form),
			ResultBase::ArbSeq(_, k) => k.deduced(form),
			ResultBase::ArbForm(_, k) => k.deduced(form),
			ResultBase::Formula(f, kbase) => form == f || kbase.deduced(form),
			ResultBase::FormPtr(f, kbase) => f.deref() == form || kbase.deduced(form),
			ResultBase::Const(_, kbase) => kbase.deduced(form),
			ResultBase::SeqConst(_, kbase) => kbase.deduced(form),
		}
	}

	fn has_const(&self, c: &expr::Const) -> bool { 
		match self {
			ResultBase::Arb(_, k) => k.has_const(c),
			ResultBase::ArbSeq(_, k) => k.has_const(c),
			ResultBase::ArbForm(_, k) => k.has_const(c),
			ResultBase::Root(r) => r.has_const(c),
			ResultBase::FormPtr(_, k) => k.has_const(c),
			ResultBase::Const(cr, k) => PartialEq::eq(cr, c) || k.has_const(c),	
			ResultBase::SeqConst(_, kbase) => kbase.has_const(c),
			ResultBase::Formula(_, kbase) => kbase.has_const(c),
		} 
	}
	fn has_seq_const(&self, c: &expr::SeqConst) -> bool { 
		match self {
			ResultBase::Arb(_, k) => k.has_seq_const(c),
			ResultBase::ArbSeq(_, k) => k.has_seq_const(c),
			ResultBase::Root(r) => r.has_seq_const(c),
			ResultBase::FormPtr(_, k) => k.has_seq_const(c),
			ResultBase::Const(_, k) => k.has_seq_const(c),
			ResultBase::SeqConst(sc, k) 
				=> PartialEq::eq(sc, c) || k.has_seq_const(c),
			ResultBase::Formula(_, kbase) => kbase.has_seq_const(c),
			ResultBase::ArbForm(_, kbase) => kbase.has_seq_const(c),
		} 
	}
	fn has_relation(&self, r: &String) -> bool { self.get_kbase().has_relation(r) }
	fn has_expr(&self, expr: &String) -> bool { self.get_kbase().has_expr(expr) }
}

impl <K: KnowledgeBase> ContextBase for ResultBase<K> {
	fn has_arb(&self, c: &expr::Arb) -> bool { 
		match self {
			ResultBase::Arb(f, k) => PartialEq::eq(f, c) || k.has_arb(c),
			ResultBase::ArbSeq(_, k) => k.has_arb(c),
			ResultBase::ArbForm(_, k) => k.has_arb(c),
			ResultBase::Root(_) => false,
			ResultBase::FormPtr(_, k) => k.has_arb(c),
			ResultBase::Const(_, k) => k.has_arb(c),
			ResultBase::SeqConst(_, k) => k.has_arb(c),
			ResultBase::Formula(_, kbase) => kbase.has_arb(c),
		} 
	}

	fn has_arb_seq(&self, c: &expr::ArbSeq) -> bool { 
		match self {
			ResultBase::ArbSeq(f, k) => PartialEq::eq(f, c) || k.has_arb_seq(c),
			ResultBase::Arb(_, k) => k.has_arb_seq(c),
			ResultBase::ArbForm(_, k) => k.has_arb_seq(c),
			ResultBase::Root(_) => false,
			ResultBase::FormPtr(_, k) => k.has_arb_seq(c),
			ResultBase::Const(_, k) => k.has_arb_seq(c),
			ResultBase::SeqConst(_, k) => k.has_arb_seq(c),
			ResultBase::Formula(_, kbase) => kbase.has_arb_seq(c),
		} 
	}

	fn has_arb_form(&self, c: &formula::Arb) -> bool { 
		match self {
			ResultBase::ArbForm(f, k) => PartialEq::eq(f, c) || k.has_arb_form(c),
			ResultBase::Arb(_, k) => k.has_arb_form(c),
			ResultBase::ArbSeq(_, k) => k.has_arb_form(c),
			ResultBase::Root(_) => false,
			ResultBase::FormPtr(_, k) => k.has_arb_form(c),
			ResultBase::Const(_, k) => k.has_arb_form(c),
			ResultBase::SeqConst(_, k) => k.has_arb_form(c),
			ResultBase::Formula(_, kbase) => kbase.has_arb_form(c),
		} 
	}
}