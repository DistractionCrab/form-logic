extern crate either;
extern crate serde;

use serde::Serialize;
use serde::Deserialize;

use std::string::ToString;
use std::collections::LinkedList;

use Ptr;
use either::Either;
use knowledge_base::KnowledgeBase;

pub type Form = Ptr<Formula>;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum Formula {
	True,
	False,
	Eq(Form, Form),
	IFF(Form, Form),
	Relation(Vec<Expr>),
	And(Form, Form),
	Or(Form, Form),
	Not(Form),
	Implies(Form, Form),
	Subst(Form, ConstName, Form),
	//FormSubst(FormSubst),
	ForAllSeq(u64, ConstName, Form),
	ForAll(ConstName, Form),
	Exists(ConstName, Form),
	Free(ConstName),
	Const(ConstName),
}

impl Formula {

	pub fn const_to_relation(v: &Vec<ConstName>) -> Formula {
		Formula::Relation(v.iter().map(|x| Expr::Formula(Formula::Const(x.clone()))).collect())
	}

	pub fn well_formed<K: KnowledgeBase>(&self, k: &K) -> bool {
		let l = LinkedList::new();
		let f = LinkedList::new();
		self.well_formed_inner(k, &l, &f)
	}

	pub fn well_formed_inner<K: KnowledgeBase>(
		&self, 
		k: &K, 
		frees: &LinkedList<ConstName>,
		freeseqs: &LinkedList<(u64, ConstName)>) 
	-> bool {
		match self {
			Formula::Eq(l, r)     => l.well_formed_inner(k, frees, freeseqs) && r.well_formed_inner(k, frees, freeseqs),
			Formula::IFF(l, r)     => l.well_formed_inner(k, frees, freeseqs) && r.well_formed_inner(k, frees, freeseqs),
			Formula::And(l, r)     => l.well_formed_inner(k, frees, freeseqs) && r.well_formed_inner(k, frees, freeseqs),
			Formula::Or(l, r)      => l.well_formed_inner(k, frees, freeseqs) && r.well_formed_inner(k, frees, freeseqs),
			Formula::Implies(l, r) => l.well_formed_inner(k, frees, freeseqs) && r.well_formed_inner(k, frees, freeseqs),
			Formula::Not(l)        => l.well_formed_inner(k, frees, freeseqs),
			Formula::Relation(l)   => l.iter().all(|x| x.well_formed_inner(k, frees, freeseqs)),
			Formula::ForAllSeq(ar, v, e) => {
				let mut a = freeseqs.clone();
				a.push_front((*ar, v.clone()));
				e.well_formed_inner(k, frees, &a)
			},
			Formula::ForAll(v, e) => {
				let mut a = frees.clone();
				a.push_front(v.clone());
				e.well_formed_inner(k, &a, freeseqs)
			}
			Formula::Exists(v, e) => {
				let mut a = frees.clone();
				a.push_front(v.clone());
				e.well_formed_inner(k, &a, freeseqs)
			}
			Formula::Free(v) => frees.contains(v),
			Formula::Const(v) => k.has_const(v),
			Formula::Subst(body, v, sub) =>  {
				let mut a = frees.clone();
				a.push_front(v.clone());
				body.well_formed_inner(k, &a, freeseqs) && sub.well_formed_inner(k, frees, freeseqs)
			}
			Formula::True => true,
			Formula::False => true,
		}
	}

	pub fn substitute(&self, c: &ConstName, f: &Formula) -> Formula {
		match self {
			Formula::Eq(l, r)     => Formula::Eq(
				l.substitute(c, f).ptr(), 
				r.substitute(c, f).ptr()),
			Formula::IFF(l, r)     => Formula::IFF(
				l.substitute(c, f).ptr(), 
				r.substitute(c, f).ptr()),
			Formula::And(l, r)     => Formula::And(
				l.substitute(c, f).ptr(), 
				r.substitute(c, f).ptr()),
			Formula::Or(l, r)      => Formula::Or(
				l.substitute(c, f).ptr(), 
				r.substitute(c, f).ptr()),
			Formula::Implies(l, r) => Formula::Implies(
				l.substitute(c, f).ptr(), 
				r.substitute(c, f).ptr()),
			Formula::Not(l)        => Formula::Not(l.substitute(c, f).ptr()),
			Formula::Relation(l)   => Formula::Relation(
				l.iter().map(|x| x.substitute(c, f)).collect()),
			Formula::ForAllSeq(_, _, e) => e.substitute(c, f),
			o@Formula::ForAll(v, e) => if c == v {
				o.clone()
			} else {
				Formula::ForAll(v.clone(), e.substitute(c, f).ptr())
			}
			o@Formula::Exists(v, e) => if c == v {
				o.clone()
			} else {
				Formula::Exists(v.clone(), e.substitute(c, f).ptr())
			}
			o@Formula::Free(v) => if v == c {
				f.clone()
			} else {
				o.clone()
			}
			o@Formula::Const(_) => o.clone(),
			o@Formula::Subst(body, v, sub) => if v == c {
				o.clone()
			} else {
				Formula::Subst(body.substitute(c, f).ptr(), v.clone(), sub.substitute(c, f).ptr())
			}
			Formula::True => Formula::True,
			Formula::False => Formula::False,
		}
	}

	pub fn substitute_seq(&self, ar: u64, c: &ConstName, f: &Vec<Formula>) -> Formula {
		match self {
			Formula::Eq(l, r)     => Formula::Eq(
				l.substitute_seq(ar, c, f).ptr(), 
				r.substitute_seq(ar, c, f).ptr()),
			Formula::IFF(l, r)     => Formula::IFF(
				l.substitute_seq(ar, c, f).ptr(), 
				r.substitute_seq(ar, c, f).ptr()),
			Formula::And(l, r)     => Formula::And(
				l.substitute_seq(ar, c, f).ptr(), 
				r.substitute_seq(ar, c, f).ptr()),
			Formula::Or(l, r)      => Formula::Or(
				l.substitute_seq(ar, c, f).ptr(), 
				r.substitute_seq(ar, c, f).ptr()),
			Formula::Implies(l, r) => Formula::Implies(
				l.substitute_seq(ar, c, f).ptr(), 
				r.substitute_seq(ar, c, f).ptr()),
			Formula::Not(l)        => Formula::Not(l.substitute_seq(ar, c, f).ptr()),
			Formula::Relation(l)   => {
				let mut v: Vec<Expr> = vec!();
				for mut s in l.iter().map(|x| x.substitute_seq(ar, c, f)) {
					v.append(&mut s);
				} 
				Formula::Relation(v)
			},
			o@Formula::ForAllSeq(a, v, e) => if *a == ar && v == c {
				o.clone()
			} else {
				Formula::ForAllSeq(*a, v.clone(), e.substitute_seq(ar, c, f).ptr())
			},
			Formula::ForAll(v, e) => Formula::ForAll(v.clone(), e.substitute_seq(ar, c, f).ptr()),
			Formula::Exists(v, e) => Formula::Exists(v.clone(), e.substitute_seq(ar, c, f).ptr()),
			o@Formula::Free(_) => o.clone(),
			o@Formula::Const(_) => o.clone(),
			Formula::Subst(body, v, sub) => Formula::Subst(
				body.substitute_seq(ar, c, f).ptr(),
				v.clone(),
				sub.substitute_seq(ar, c, f).ptr()),
			Formula::True => Formula::True,
			Formula::False => Formula::False,
		}
	}

	pub fn ptr(self) -> Form { Form::new(self) }
}

impl std::hash::Hash for Formula {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			Formula::Eq(l, r)      => { "Eq".hash(state); l.hash(state); r.hash(state); }
			Formula::IFF(l, r)     => { "IFF".hash(state); l.hash(state); r.hash(state); }
			Formula::And(l, r)     => { "And".hash(state); l.hash(state); r.hash(state); }
			Formula::Or(l, r)      => { "Or".hash(state); l.hash(state); r.hash(state); }
			Formula::Implies(l, r) => { "Implies".hash(state); l.hash(state); r.hash(state); }
			Formula::Not(l)        => { "Not".hash(state); l.hash(state); }
			Formula::Relation(l)   => { l.iter().for_each(|f| f.hash(state)); }
				
			Formula::ForAllSeq(_, _, e) => { "ForAllSeq".hash(state); e.hash(state); }
			Formula::Exists(_, e) => { "Exists".hash(state); e.hash(state); }
			Formula::ForAll(_, e) => { "ForAll".hash(state); e.hash(state); }
			Formula::Free(_) => { "FreeVar".hash(state);  }
			Formula::Const(_) => { "Const".hash(state);  }
			Formula::Subst(body, _, sub) => { "Subst".hash(state); body.hash(state); sub.hash(state) }
			Formula::True => true.hash(state),
			Formula::False => false.hash(state),
		}
	}
}

impl ToString for Formula {
    fn to_string(&self) -> String {
		match self {
			Formula::Eq(l, r)     => format!("Eq({}, {})", l.to_string(), r.to_string()),
			Formula::IFF(l, r)     => format!("IFF({}, {})", l.to_string(), r.to_string()),
			Formula::And(l, r)     => format!("And({}, {})", l.to_string(), r.to_string()),
			Formula::Or(l, r)      => format!("Or({}, {})", l.to_string(), r.to_string()),
			Formula::Implies(l, r) => format!("Implies({}, {})", l.to_string(), r.to_string()),
			Formula::Not(l)        => format!("Not({})", l.to_string()),
			Formula::Relation(l)   => 
				format!("({})", l.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")),
			Formula::ForAllSeq(a, v, e) => format!(
				"ForAllSeq(({}, {}), {})", 
				a.to_string(), 
				v.to_string(),
				e.to_string()),
			Formula::Exists(v, e) => format!("Exists({}, {})", v.to_string(), e.to_string()),
			Formula::ForAll(v, e) => format!("ForAll({}, {})", v.to_string(), e.to_string()),
			Formula::Free(v) => format!("#\"{}\"", v.to_string()),
			Formula::Const(c) => format!("\"{}\"", c.to_string()),
			Formula::Subst(body, v, sub) => format!(
				"Subst(({}, {}), {})", 
				body.to_string(), 
				v.to_string(),
				sub.to_string()),
			Formula::True => true.to_string(),
			Formula::False => false.to_string(),
		}
	}
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum ConstName {
	String(Ptr<String>),
	Int(u64)
}

impl ToString for ConstName {
	fn to_string(&self) -> String {
		match self {
			ConstName::String(s) => format!("\"{}\"", s),
			ConstName::Int(i) => format!("'{}\'", i),
		}
	}
}



#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
	Formula(Formula),
	Head(Seq),
	Seq(Seq),
}

impl Expr {
	pub fn substitute(&self, c: &ConstName, f: &Formula) -> Expr {
		match self {
			Expr::Formula(e) => Expr::Formula(e.substitute(c, f)),
			s => s.clone()
		}
	}

	fn well_formed_inner<K: KnowledgeBase>(
		&self, 
		k: &K,
		frees: &LinkedList<ConstName>,
		freeseqs: &LinkedList<(u64, ConstName)>) 
	-> bool {
		match self {
			Expr::Formula(e) => e.well_formed_inner(k, frees, freeseqs),
			Expr::Head(s) => s.well_formed_inner(k, frees, freeseqs),
			Expr::Seq(s) => s.well_formed_inner(k, frees, freeseqs),
		}
	}

	pub fn substitute_seq(&self, ar: u64, c: &ConstName, f: &Vec<Formula>) -> Vec<Expr> {
		match self {
			Expr::Formula(e) => vec!(Expr::Formula(e.substitute_seq(ar, c, f))),
			Expr::Head(s) => match s.substitute_seq(ar, c, f) {
				Either::Left(s) => vec!(Expr::Head(s)),
				Either::Right(v) => if v.len() > 0 {
					vec!(Expr::Formula(v[0].clone()))
				} else {
					vec!()
				}
			}
			Expr::Seq(s) => match s.substitute_seq(ar, c, f) {
				Either::Left(s) => vec!(Expr::Seq(s)),
				Either::Right(v) => v.iter().map(|e| Expr::Formula(e.clone())).collect()
			}
		}
	}
}

impl std::hash::Hash for Expr {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			Expr::Formula(e) => e.hash(state),
			Expr::Head(s) => { "Head".hash(state); s.hash(state); }
			Expr::Seq(s) => { "Seq".hash(state); s.hash(state); }
		}
	}
}

impl ToString for Expr {
	fn to_string(&self) -> String {
		match self {
			Expr::Formula(e) => e.to_string(),
			Expr::Head(s) => format!("Head({})", s.to_string()),
			Expr::Seq(s) => format!("Seq({})", s.to_string()),
		}
	}
}


#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum Seq {
	Free(u64, ConstName),
	Tail(Ptr<Seq>)
}

impl std::hash::Hash for Seq {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			Seq::Free(_, _) => "FreeSeq".hash(state),
			Seq::Tail(p) => { "Tail".hash(state); p.hash(state) }
		}
	}
}

impl Seq {
	pub fn substitute_seq(&self, ar: u64, c: &ConstName, f: &Vec<Formula>) -> Either<Seq, Vec<Formula>> {
		match self {
			o@Seq::Free(a, v) => if *a == ar && v == c { 
				Either::Right(f.clone()) 
			} else { 
				Either::Left(o.clone())
			}
			Seq::Tail(p) => match p.substitute_seq(ar, c, f) {
				Either::Left(s) => Either::Left(Seq::Tail(s.ptr())),
				Either::Right(mut s) => { s.pop(); Either::Right(s) }
			}
		}
	}

	fn well_formed_inner<K: KnowledgeBase>(
		&self, 
		k: &K,
		frees: &LinkedList<ConstName>,
		freeseqs: &LinkedList<(u64, ConstName)>) 
	-> bool {
		match self {
			Seq::Free(a, v) => freeseqs.contains(&(*a, v.clone())),
			Seq::Tail(p) => p.well_formed_inner(k, frees, freeseqs)			
		}
	}

	pub fn arity(&self) -> Option<u64> {
		match self {
			Seq::Free(a, _) => Some(*a),
			Seq::Tail(s) => match s.arity() {
				Some(v) => if v == 0 {
					None
				} else {
					Some(v - 1)
				}
				None => None
			}
		}	
	}

	pub fn ptr(self) -> Ptr<Seq> { Ptr::new(self) }
}

impl Seq {
	fn to_string(&self) -> String {
		match self {
			Seq::Free(a, v) => format!("\"{}\"...{}", v.to_string(), a.to_string()),
			Seq::Tail(p) => format!("Tail({})", p.to_string())
		}
	}
}
