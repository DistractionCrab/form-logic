use formula;
use expr;

use expr::{
	Singular, 
	SeqVar,
	Free,
	FreeSeq
};
use formula::{
	Formula,
};
use formed::Info as FInfo;
use knowledge_base::ContextBase;


#[derive(Clone, PartialEq)]
pub enum Info {
	Formula(formula::Free, Formula),
	Expr(Expr)	
}

#[derive(Clone, PartialEq)]
pub enum Expr {
	Singular(Free, Singular),
	Seq(FreeSeq, SeqVar)
}

pub trait Substitute {
	fn substitute(&self, info: &Info) -> Self;
	fn max_sub_index(&self) -> usize;
}

impl Expr {
	pub fn sub_str(name: &str, s: Singular) -> Expr {
		Expr::Singular(Free::from_str(name), s)
	}

	pub fn sub_free(name: Free, s: Singular) -> Expr {
		Expr::Singular(name, s)
	}

	pub fn append_finfo<'a, K>(&'a self, info: &'a FInfo<'a, K>) -> FInfo<'a, K> 
	where
		K: ContextBase
	{
		match self {
			Expr::Singular(f, _) => info.append_free(&f),
			Expr::Seq(f,_) => info.append_free_seq(&f)
		}
	}

	pub fn replaces(&self, name: &Free) -> bool {
		match self {
			Expr::Singular(f, _) => PartialEq::eq(f, name),
			_ => false
		}
	}

	pub fn replaces_seq(&self, name: &FreeSeq) -> bool {
		match self {
			Expr::Seq(f, _) => PartialEq::eq(f, name),
			_ => false
		}
	}

	pub fn replaces_info(&self, name: &Expr) -> bool {
		match self {
			Expr::Seq(f1, _) => match name {
				Expr::Seq(f2, _) => PartialEq::eq(f1, f2),
				_ => false
			},
			Expr::Singular(f1, _) => match name {
				Expr::Singular(f2, _) => PartialEq::eq(f1, f2),
				_ => false
			}
		}
	}

	pub fn substitute(&self, name: &Free) -> Singular {
		match self {
			Expr::Singular(f, s) => if PartialEq::eq(f, name) {
				s.clone()
			} else {
				expr::Singular::Free(name.clone())
			},
			_ => expr::Singular::Free(name.clone())
		}
	}

	pub fn substitute_seq(&self, name: &FreeSeq) -> SeqVar {
		match self {
			Expr::Seq(f, s) => if PartialEq::eq(f, name) {
				s.clone()
			} else {
				expr::SeqVar::Free(name.clone())
			},
			_ => expr::SeqVar::Free(name.clone())
		}
	}

	pub fn max_sub_index(&self) -> usize {
		match self {
			Expr::Singular(c, s) 
				=> std::cmp::max(c.max_sub_index(), s.max_sub_index()),
			Expr::Seq(c, s) => std::cmp::max(c.max_sub_index(), s.max_sub_index()),
		}
	}

	pub fn subs_with(&self, name: &Free) -> bool {
		match self {
			Expr::Singular(_, expr::Singular::Free(f)) => PartialEq::eq(f, name),
			_ => false
		}
	}

	pub fn subs_with_seq(&self, name: &FreeSeq) -> bool {
		match self {
			Expr::Seq(_, expr::SeqVar::Free(f)) => PartialEq::eq(f, name),
			_ => false
		}
	}

	pub fn to_form(&self) -> Info {
		Info::Expr(self.clone())
	}

	pub fn chain<S: Substitute + Clone>(&self, s: &S, free: &Free) -> (S, Free) {
		let i = std::cmp::max(self.max_sub_index(),	s.max_sub_index()) + 1;
		if self.subs_with(free) {
			match self {
				Expr::Singular(_, _) => {
					let new_name = Free::from_int(i);		
					let new_info = Expr::Singular(
							free.clone(),
							expr::Singular::Free(new_name.clone()))
						.to_form();
					(s.substitute(&new_info).substitute(&self.to_form()), Free::from_int(i))
				},
				_ => (s.substitute(&self.to_form()), free.clone())
			}
		}
		else {
			(s.substitute(&self.to_form()), free.clone())
		}
	}

	pub fn chain_seq<S: Substitute + Clone>(&self, s: &S, free: &FreeSeq) 
	-> (S, FreeSeq) 
	{
		let i = std::cmp::max(self.max_sub_index(),	s.max_sub_index()) + 1;
		if self.subs_with_seq(free) {
			match self {
				Expr::Singular(_, _) => {
					let new_name = free.replace_with(i);
					let new_info = Expr::Seq(
							free.clone(),
							expr::SeqVar::Free(new_name.clone()))
						.to_form();
					(s.substitute(&new_info).substitute(&self.to_form()), 
						free.replace_with(i))
				},
				_ => (s.substitute(&self.to_form()), free.clone())
			}
		}
		else {
			(s.substitute(&self.to_form()), free.clone())
		}
	}

	pub fn chain_info<S: Substitute + Clone>(&self, s: &S, free: &Expr)
	-> (S, Expr) 
	{
		match free {
			Expr::Singular(f, ex) => {
				let (s, new_f) = self.chain(s, f);
				(s, Expr::Singular(new_f, ex.clone()))
			},
			Expr::Seq(f, ex) => {
				let (s, new_f) = self.chain_seq(s, f);
				(s, Expr::Seq(new_f, ex.clone()))
			},
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		match self {
			Expr::Singular(_, f) => f.well_formed(info),
			Expr::Seq(_, f) => f.well_formed(info),
		}
	}
}

impl ToString for Expr {
	fn to_string(&self) -> String {
		match self {
			Expr::Singular(f, s) => {
				format!("{} <- {}", f.to_string(), s.to_string())
			},
			Expr::Seq(f, s) => {
				format!("{} <= {}", f.to_string(), s.to_string())
			},
		}
	}
}

impl Info {


	pub fn replaces(&self, name: &Free) -> bool {
		match self {
			Info::Expr(Expr::Singular(f, _)) => PartialEq::eq(f, name),
			_ => false
		}
	}

	pub fn max_sub_index(&self) -> usize {
		match self {
			Info::Formula(c, s) 
				=> std::cmp::max(c.max_form_sub_index(), s.max_form_sub_index()),
			_ => 0,
		}
	}

	pub fn replaces_seq(&self, name: &FreeSeq) -> bool {
		match self {
			Info::Expr(Expr::Seq(f, _)) => PartialEq::eq(f, name),
			_ => false
		}
	}

	pub fn replaces_form(&self, name: &formula::Free) -> bool {
		match self {
			Info::Formula(f, _) => PartialEq::eq(f, name),
			_ => false
		}
	}

	pub fn chain<S: Substitute + Clone>(&self, s: &S, free: &Free) -> (S, Free) {
		match self {
			Info::Expr(i) => i.chain(s, free),
			_ => panic!("Attempted chained substitution for vars with form info.")
		}
	}

	pub fn chain_seq<S: Substitute + Clone>(&self, s: &S, free: &FreeSeq) 
	-> (S, FreeSeq) 
	{
		match self {
			Info::Expr(i) => i.chain_seq(s, free),
			_ => panic!("Attempted chained substitution for vars with form info.")
		}
	}

	pub fn subs_with(&self, name: &formula::Free) -> bool {
		match self {
			Info::Formula(_, f) => PartialEq::eq(f, &name.to_form()),
			_ => false
		}
	}

	pub fn chain_form(&self, s: &Formula, free: &formula::Free) -> (Formula, formula::Free) 
	{
		let i = std::cmp::max(self.max_sub_index(),	s.max_sub_index()) + 1;
		if self.subs_with(free) {
			match self {
				Info::Formula(_, s) => {
					let new_name = formula::Free::from_int(i);
					let form = formula::Formula::Free(new_name.clone());
					let new_info = Info::Formula(free.clone(), form.clone());
					(s.substitute(&new_info).substitute(self), new_name)
				},
				_ => (s.substitute(self), free.clone())
			}
		}
		else {
			(s.substitute(self), free.clone())
		}
	}

	pub fn well_formed<'a, K: ContextBase>(&self, info: &FInfo<'a, K>) 
	-> bool {
		match self {
			Info::Formula(_, f) => f.well_formed(info),
			Info::Expr(Expr::Singular(_, f)) => f.well_formed(info),
			Info::Expr(Expr::Seq(_, f)) => f.well_formed(info),
		}
	}

	pub fn substitute(&self, name: &Free) -> Singular {
		match self {
			Info::Expr(Expr::Singular(f, s)) => if PartialEq::eq(f, name) {
				s.clone()
			} else {
				expr::Singular::Free(name.clone())
			},
			_ => expr::Singular::Free(name.clone())
		}
	}

	pub fn substitute_seq(&self, name: &FreeSeq) -> SeqVar {
		match self {
			Info::Expr(Expr::Seq(f, s)) => if PartialEq::eq(f, name) {
				s.clone()
			} else {
				expr::SeqVar::Free(name.clone())
			},
			_ => expr::SeqVar::Free(name.clone())
		}
	}
}

impl ToString for Info {
	fn to_string(&self) -> String {
		match self {
			Info::Formula(f, s) => {
				format!("{} <<== {}", f.to_string(), s.to_string())
			},
			Info::Expr(f) => {
				f.to_string()
			},
		}
	}
}