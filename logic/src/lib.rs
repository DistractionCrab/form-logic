extern crate either;
extern crate serde;

//use std::sync::Arc;
use std::rc::Rc;

pub type Ptr<K> = Rc<K>;

pub mod formula;
pub mod deduction;
pub mod knowledge_base;