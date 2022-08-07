/// This module holds the information that defines the possible operations
/// for a KnowledgeBase, the root logical structure for holding proven theorem
/// and axioms, and a ContextBase, an extension of the KnowledgeBase that can
/// contain arbitrary variables (used in proving quantifiers).

use formula;
use Ptr;
use std::ops::Deref;

/// Default pointer type for a knowledge base.
pub type KBasePtr<T> = Ptr<T>;

/// Returns the pointer type for a knowledge base.
pub fn ptr<K: Clone>(kbase: &K) -> KBasePtr<K> {
	Ptr::new(Clone::clone(kbase))
}

/// This trait defines the operations for a knowledge base.
pub trait KnowledgeBase {
	/// Returns whether or not the formula has been proven. Implementors
	/// Should check for well-formedness as a safe-guard for internal errors.
	fn contains(&self, form: &formula::Formula) -> bool;

	/// Returns whether or not the constant has been defined/declared.
	fn has_const(&self, c: &formula::ConstName) -> bool;
}


/// ContextBase implementation for proofs. Uses a knowledge base implementor
/// as its root, and is extended as needed.
pub enum ResultBase<K> {
	Err(String),
	Root(Ptr<K>),
	Formula(formula::Formula, Ptr<ResultBase<K>>),
	FormPtr(formula::Form, Ptr<ResultBase<K>>),
	Const(formula::ConstName, Ptr<ResultBase<K>>),
}


impl <K> Clone for ResultBase<K> {
	fn clone(&self) -> ResultBase<K> {
		match self {
			ResultBase::Err(s) => ResultBase::Err(s.clone()),
			ResultBase::Root(r) => ResultBase::Root(r.clone()),
			ResultBase::Formula(f, k) => ResultBase::Formula(f.clone(), k.clone()),
			ResultBase::FormPtr(f, k) => ResultBase::FormPtr(f.clone(), k.clone()),
			ResultBase::Const(f, k) => ResultBase::Const(f.clone(), k.clone()),
		}
	}
}


impl <K: KnowledgeBase> ResultBase<K> {

	/// Wraps this object in a pointer type.
	pub fn ptr(&self) -> KBasePtr<ResultBase<K>> { 
		Ptr::new(self.clone()) 
	}

	pub fn new(kbase: K) -> ResultBase<K> {
		ResultBase::Root(Ptr::new(kbase))
	}

	/// Appends a formula pointer to this result base.
	pub fn result_ptr(&self, form: formula::Form) -> ResultBase<K> {
		ResultBase::FormPtr(form, self.ptr())
	}

	/// Appends a formula to this result base.
	pub fn result_form(&self, form: formula::Formula) -> ResultBase<K> {
		ResultBase::Formula(form, Ptr::new(self.clone()))
	}


	/// Appends a constant to this result base.
	pub fn result_const(&self, sq: formula::ConstName) -> ResultBase<K> {
		ResultBase::Const(sq, Ptr::new(self.clone()))
	}


	pub fn is_err(&self) -> bool {
		match self {
			ResultBase::Err(_) => true,
			_ => false
		}
	}
}

impl <K: KnowledgeBase> KnowledgeBase for ResultBase<K> {
	fn contains(&self, form: &formula::Formula) -> bool { 
		match self {
			ResultBase::Err(_) => false,
			ResultBase::Root(r) => r.contains(form),
			ResultBase::Formula(f, kbase) => form == f || kbase.contains(form),
			ResultBase::FormPtr(f, kbase) => f.deref() == form || kbase.contains(form),
			ResultBase::Const(_, kbase) => kbase.contains(form),
		}
	}

	fn has_const(&self, c: &formula::ConstName) -> bool { 
		match self {
			ResultBase::Err(_) => false,
			ResultBase::Root(r) => r.has_const(c),
			ResultBase::FormPtr(_, k) => k.has_const(c),
			ResultBase::Const(cr, k) => PartialEq::eq(cr, c) || k.has_const(c),	
			ResultBase::Formula(_, kbase) => kbase.has_const(c),
		} 
	}
}

