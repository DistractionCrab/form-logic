extern crate sqlite;
extern crate logic;

use std::collections::HashSet;
use logic::{
	knowledge_base,
	formula,
	expr
};

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
	fn deduced(&self, form: &formula::Formula) -> bool {
		false
	}

	/// Returns whether or not the constant has been defined/declared.
	fn has_const(&self, c: &expr::Const) -> bool {
		false
	}

	/// Returns whether or not the sequence constant has been defined/declared.
	fn has_seq_const(&self, c: &expr::SeqConst) -> bool {
		false
	}
}

fn main() {
	println!("Hello, world!");
}
