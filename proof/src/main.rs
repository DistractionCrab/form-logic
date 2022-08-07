extern crate sqlite;
extern crate logic;

use std::collections::HashSet;
use std::rc::Rc;
use logic::{
	knowledge_base,
	formula,
	deduction
};

use logic::formula::Formula;
use logic::deduction::Deduction;

pub type Ptr<K> = Rc<K>;


const DB_FILE_NAME: &str = "PROOF_DATABASE.db";
const DB_INIT_STR1: &str = "
	CREATE TABLE theories (
		theorem TEXT NOT NULL, 
		description TEXT NOT NULL,
		theory TEXT NOT NULL,
		proof TEXT NOT NULL,
		proof_raw TEXT NOT NULL
	)
";

const DB_INIT_STR2: &str = "
	CREATE TABLE constants (
		name TEXT NOT NULL, 
		description TEXT NOT NULL,
		theory TEXT NOT NULL
	)
";

struct Database {
	theories: sqlite::Connection
}

impl Database {
	fn new() -> Database {
		let conn = sqlite::open(DB_FILE_NAME);

		Database {
			theories: conn.unwrap()
		}
	}

	fn init(&mut self) {
		//self.db.execute()
	}
}

impl knowledge_base::KnowledgeBase for Database {
	/// Returns whether or not the formula has been proven. Implementors
	/// Should check for well-formedness as a safe-guard for internal errors.
	fn contains(&self, form: &formula::Formula) -> bool {
		false
	}

	/// Returns whether or not the constant has been defined/declared.
	fn has_const(&self, c: &formula::ConstName) -> bool {
		false
	}
}

pub enum Theorem {
	Ref(String),
	Form(formula::Formula),
}

pub enum AST {
	Let(Vec<String>, Ptr<AST>),
	Assume(formula::Formula, Ptr<AST>),
	Thus(formula::Formula),
	Apply(formula::Formula, Theorem),
	Alias(String, Ptr<AST>),
	Step(String, Ptr<AST>),
	By(Theorem),
	Exists(Theorem, String),
	Seq(Vec<AST>),
	Case(Formula, Ptr<AST>),
}

pub enum Thus {
	Form(Formula),

}

pub struct Generator {
	ast: AST,
	thm: Formula
}

impl Generator {
	pub fn generate_proof(&self) -> Deduction {
		let mut a = vec!();
		self.generate_inner(&mut a);
		deduction::Deduction::EmptyStep
	}

	fn generate_inner(&self, v: &mut Vec<Deduction>) -> Deduction {
		match self {
			AST::Let(v, a) => {				
				
				deduction::Deduction::EmptyStep
			}
			AST::Thus(f) => self.thus(f),
			_ => deduction::Deduction::EmptyStep
		}
	}

	fn thus(&self, f: &Formula) -> deduction::Deduction {
		match f {
			Formula::Eq(l, r)     => 
			Formula::IFF(l, r)     =>
			Formula::And(l, r)     =>
			Formula::Or(l, r)      =>
			Formula::Implies(l, r) =>
			Formula::Not(l)        =>
			Formula::Relation(l)   =>
			Formula::ForAllSeq(ar, v, e) => 
			Formula::ForAll(v, e) => 
			Formula::Exists(v, e) => 
			Formula::Free(v) => 
			Formula::Const(v) =>
			Formula::Subst(body, v, sub)
			Formula::True => true,
			Formula::False => true,
		}
	}
}

fn main() {
	println!("Hello, world!");
}
