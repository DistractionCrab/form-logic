use std::sync::Arc;

pub type Ptr<K> = Arc<K>;

#[macro_use]
pub mod writing;
pub mod deduction;
pub mod expr;
pub mod formed;
pub mod formula;
pub mod knowledge_base;
pub mod subst;
pub mod theorems;
