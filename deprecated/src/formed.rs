/// This mod holds information about the formation of statements.
/// The Formed information depends on a ContextBase, which respresents the
/// evolving knowledge base as a proof goes on; This is meant to deal with
/// declaration of arbitrary variables.

use knowledge_base::ContextBase;
use expr;
use formula;

/// The structure for holding needed information for determining well-formedness
/// of formula and expressions. At the root is a knowledge base, and the
/// information can have free variables appended to it to deal with the
/// nested nature of quantifiers.
pub enum Info<'a, K: ContextBase + 'a> {
	Root(&'a K),
	Exp(&'a expr::Free, &'a Info<'a, K>),
	ExpSeq(&'a expr::FreeSeq, &'a Info<'a, K>),
	Form(&'a formula::Free, &'a Info<'a, K>)
}

impl <'a, K: ContextBase + 'a> Info<'a, K> {

	/// Constructs an Info struct using the given knowledge base as its root.
	pub fn new(a: &'a K) -> Info<'a, K> {
		Info::Root(a)
	}

	/// Appends a free variable to the information.
	pub fn append_free(&'a self, f: &'a expr::Free) -> Info<'a, K> {
		Info::Exp(f, self)
	}

	/// Appends a free sequence variable to the information.
	pub fn append_free_seq(&'a self, f: &'a expr::FreeSeq) -> Info<'a, K> {
		Info::ExpSeq(f, self)
	}
	/// Appends a free formula to the information.
	pub fn append_free_form(&'a self, f: &'a formula::Free) -> Info<'a, K> {
		Info::Form(f, self)
	}

	/// Returns whether or not the given free variable is held in this info.
	pub fn has_free(&self, f: &expr::Free) -> bool {
		match self {
			Info::Exp(a, n) => PartialEq::eq(*a, f) || n.has_free(f),
			Info::ExpSeq(_, n) => n.has_free(f),
			Info::Form(_, n) => n.has_free(f),
			_ => false
		}
	}

	/// Returns whether or not the given free sequence variable is held in 
	/// this info.
	pub fn has_free_seq(&self, f: &expr::FreeSeq) -> bool {
		match self {
			Info::ExpSeq(a, n) => PartialEq::eq(*a, f) || n.has_free_seq(f),
			Info::Exp(_, n) => n.has_free_seq(f),
			Info::Form(_, n) => n.has_free_seq(f),
			_ => false
		}
	}

	/// Returns whether or not the given free formula is held in this info.
	pub fn has_free_form(&self, f: &formula::Free) -> bool {
		match self {
			Info::Form(a, n) => PartialEq::eq(*a, f) || n.has_free_form(f),
			Info::Exp(_, n) => n.has_free_form(f),
			Info::ExpSeq(_, n) => n.has_free_form(f),
			_ => false
		}
	}

	// See KnowledgeBase::has_const.
	pub fn has_const(&self, c: &expr::Const) -> bool {
		match self {
			Info::Exp(_, n) => n.has_const(c),
			Info::ExpSeq(_, n) => n.has_const(c),
			Info::Form(_, n) => n.has_const(c),
			Info::Root(k) => k.has_const(c)
		}	
	}

	// See KnowledgeBase::has_seq_const.
	pub fn has_seq_const(&self, c: &expr::SeqConst) -> bool {
		match self {
			Info::Exp(_, n) => n.has_seq_const(c),
			Info::ExpSeq(_, n) => n.has_seq_const(c),
			Info::Form(_, n) => n.has_seq_const(c),
			Info::Root(k) => k.has_seq_const(c)
		}
	}

	// See KnowledgeBase::has_relation.
	pub fn has_relation(&self, c: &String) -> bool {
		match self {
			Info::Exp(_, n) => n.has_relation(c),
			Info::ExpSeq(_, n) => n.has_relation(c),
			Info::Form(_, n) => n.has_relation(c),
			Info::Root(k) => k.has_relation(c)
		}
	}

	// See KnowledgeBase::has_expr.
	pub fn has_expr(&self, c: &String) -> bool {
		match self {
			Info::Exp(_, n) => n.has_expr(c),
			Info::ExpSeq(_, n) => n.has_expr(c),
			Info::Form(_, n) => n.has_expr(c),
			Info::Root(k) => k.has_expr(c)
		}
	}

	// See ContextBase::has_arb.
	pub fn has_arb(&self, c: &expr::Arb) -> bool { 
		match self {
			Info::Exp(_, n) => n.has_arb(c),
			Info::ExpSeq(_, n) => n.has_arb(c),
			Info::Form(_, n) => n.has_arb(c),
			Info::Root(k) => k.has_arb(c)
		} 
	}

	// See ContextBase::has_arb_seq.
	pub fn has_arb_seq(&self, c: &expr::ArbSeq) -> bool { 
		match self {
			Info::Exp(_, n) => n.has_arb_seq(c),
			Info::ExpSeq(_, n) => n.has_arb_seq(c),
			Info::Form(_, n) => n.has_arb_seq(c),
			Info::Root(k) => k.has_arb_seq(c)
		} 
	}

	// See ContextBase::has_arb_form.
	pub fn has_arb_form(&self, c: &formula::Arb) -> bool { 
		match self {
			Info::Exp(_, n) => n.has_arb_form(c),
			Info::ExpSeq(_, n) => n.has_arb_form(c),
			Info::Form(_, n) => n.has_arb_form(c),
			Info::Root(k) => k.has_arb_form(c)
		} 
	}
}