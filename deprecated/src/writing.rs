use formula::{Or, And, Formula};

/// Macro used to import necessary name spaces for using macros in this
/// module.
#[macro_export]
macro_rules! imports {
	() => {
		#[allow(unused_imports)]
		use std::convert::Into;
		#[allow(unused_imports)]
		use formula;
		#[allow(unused_imports)]
		use expr;
		#[allow(unused_imports)]
		use deduction;
		#[allow(unused_imports)]
		use subst;
		#[allow(unused_imports)]
		use writing::{get_or, get_and};	
	}
}


/// Creates an Or-formula with the given array of formulas.Formula
/// This is a left-ordered tree, i.e. a or be or c === (a or b) or c
pub fn get_or(l: Formula, r: Formula, forms: &[Formula]) -> Or {
	let f = Or::new(l, r);
	forms.iter().fold(f, |acc, x| { Or::new(acc.to_form(), x.clone()) })
}

pub fn get_and(l: Formula, r: Formula, forms: &[Formula]) -> And {
	let f = And::new(l, r);
	forms.iter().fold(f, |acc, x| { And::new(acc.to_form(), x.clone()) })
}

#[macro_export]
macro_rules! or {
	($l: expr, $r: expr $(, $rest:expr)*) => {
		{
			get_or($l, $r, &[$($rest),*])
		}
	}
}

#[macro_export]
macro_rules! and {
	($l: expr, $r: expr $(, $rest:expr)*) => {
		{
			get_and($l, $r, &[$($rest),*])
		}
	}
}


#[macro_export]
macro_rules! r {
	($name:ident($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			formula::Relation::new(stringify!($name).to_string(), v).to_form()
		}
	};
	({$name:expr}($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			formula::Relation::new($name.to_string(), v).to_form()
		}
	}
}

#[macro_export]
macro_rules! expr_list {
	($out:expr; *{ $name:expr }..$ct:expr,  $($more:tt)+) => { 
		{
			let name = Into::into($name);
			$out.push(expr::FreeSeq::from_cname(name, $ct).to_seq().to_expr());
			expr_list!($out; $($more)+);
		}
	};
	($out:expr; &{ $name:expr }..$ct:expr,  $($more:tt)+) => { 
		{
			let name = Into::into($name);
			$out.push(expr::ArbSeq::from_cname(name, $ct).to_seq().to_expr());
			expr_list!($out; $($more)+);
		}
	};
	($out:expr; { $name:expr }..$ct:expr,  $($more:tt)+) => { 
		{
			let name = Into::into($name);
			$out.push(expr::SeqConst::from_cname(name, $ct).to_seq().to_expr());
			expr_list!($out; $($more)+);
		}
	};	
	($out:expr; *{ $name:expr }..$ct:expr) => { 
		{
			let name = Into::into($name);
			$out.push(expr::FreeSeq::from_cname(name, $ct).to_seq().to_expr());
		}
	};
	($out:expr; &{ $name:expr }..$ct:expr) => { 
		{
			let name = Into::into($name);
			$out.push(expr::ArbSeq::from_cname(name, $ct).to_seq().to_expr());
		}
	};
	($out:expr; { $name:expr }..$ct:expr) => { 
		{
			let name = Into::into($name);
			$out.push(expr::SeqConst::from_cname(name, $ct).to_seq().to_expr());
		}
	};	
	($out:expr; *{ $name:expr }, $($more:tt)+) => { 
		{
			let name = Into::into($name);
			$out.push(expr::Free::from_cname(name).to_singular().to_expr());
			expr_list!($out; $($more)+);
		}
	};
	($out:expr; *{ $name:expr }) => { 
		{
			let name = Into::into($name);
			$out.push(expr::Free::from_cname(name).to_singular().to_expr());
		}
	};
	($out:expr; &{ $name:expr }, $($more:tt)+) => { 
		{
			let name = Into::into($name);
			$out.push(expr::Arb::from_cname(name).to_singular().to_expr());
			expr_list!($out; $($more)+);
		}
	};
	($out:expr; &{ $name:expr }) => { 
		{
			let name = Into::into($name);
			$out.push(expr::Arb::from_cname(name).to_singular().to_expr());
		}
	};
	($out:expr; { $name:expr }, $($more:tt)+) => { 
		{
			$out.push(Into::<Expr>::into($name));
			expr_list!($out; $($more)+);
		}
	};
	($out:expr; { $name:expr }) => { 
		{
			$out.push(Into::<Expr>::into($name));
		}
	};
	($out:expr; *$name:ident..$ct:expr, $($more:tt)+) => { 
		$out.push(SeqVar::free_str(stringify!($name), $ct).to_expr());
		expr_list!($out; $($more)+);
	};
	($out:expr; *$name:ident..$ct:expr) => { 
		$out.push(SeqVar::free_str(stringify!($name), $ct).to_expr());
	};
	($out:expr; *$name:ident, $($more:tt)+) => { 
		$out.push(Singular::free_str(stringify!($name)).to_expr());
		expr_list!($out; $($more)+);
	};
	($out:expr; *$name:ident) => { 
		$out.push(Singular::free_str(stringify!($name)).to_expr());
	};
	($out:expr; & $name:ident..$ct:expr, $($more:tt)+) => { 
		$out.push(SeqVar::free_str(stringify!($name), $ct).to_expr());
		expr_list!($out; $($more)+);
	};
	($out:expr; & $name:ident..$ct:expr) => { 
		$out.push(SeqVar::free_str(stringify!($name), $ct).to_expr());
	};
	($out:expr; & $name:ident, $($more:tt)+) => { 
		$out.push(Singular::arb_str(stringify!($name)).to_expr());
		expr_list!($out; $($more)+);
	};
	($out:expr; & $name:ident) => { 
		$out.push(Singular::arb_str(stringify!($name)).to_expr());
	};
	($out:expr; {$name:expr}($($params:tt)+), $($more:tt)*) => {
		$out.push(s!({$name}($($params)+)).to_expr());
		expr_list!($out; $($more)+);
	};
	($out:expr; {$name:expr}($($params:tt)+)) => {
		$out.push(s!({$name}($($params)+)).to_expr());
	};
	($out:expr; $name:ident($($params:tt)+), $($more:tt)*) => {
		$out.push(s!($name($($params)+)).to_expr());
		expr_list!($out; $($more)+);
	};
	($out:expr; $name:ident($($params:tt)+)) => {
		$out.push(s!($name($($params)+)).to_expr());
	};
	($out:expr; $name:ident..$ct:expr, $($more:tt)+) => { 
		$out.push(SeqVar::free_str(stringify!($name), $ct).to_expr());
		expr_list!($out; $($more)+);
	};
	($out:expr; $name:ident..$ct:expr) => { 
		$out.push(SeqVar::free_str(stringify!($name), $ct).to_expr());
	};
	($out:expr; $name:ident, $($more:tt)+) => {
		$out.push(expr::Singular::const_str(stringify!($name)).to_expr());
		expr_list!($out; $($more)+);
	};
	
	($out:expr; $name:ident) => {
		$out.push(expr::Singular::arb_str(stringify!($name)).to_expr());
	};
	
}

#[macro_export]
macro_rules! e {
	(e!($($stuff:tt)+)) => {
		e!($($stuff)+)
	};
	($name:ident($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			expr::Singular::Composite(stringify!($name).to_string(), v).to_expr()
		}
	};
	({$name:expr}($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			expr::Singular::Composite($name.to_string(), v).to_expr()
		}
	};
	(*#{ $name:expr }) => { 
		Into::<expr::FreeSeq>::into($name).to_seq().to_expr()
	};
	(&#{ $name:expr }..$ct:expr) => { 
		Into::<expr::ArbSeq>::into($name).to_seq().to_expr()
	};
	(#{ $name:expr }..$ct:expr) => { 
		Into::<expr::SeqConst>::into($name).to_seq().to_expr() 
	};
	(*{ $name:expr }) => { 
		{
			let name = Into::into($name);
			expr::Free::from_cname(name).to_singular().to_expr()
		}
	};
	(&{ $name:expr }) => { 
		{
			let name = Into::into($name);
			expr::Arb::from_cname(name).to_singular().to_expr()
		}
	};
	({ $name:expr }) => { Into::<expr::Expr>::into($name) };
	(*$name:ident..$ct:expr) => { 
		expr::SeqVar::free_str(stringify!($name), $ct).to_expr()
	};
	(&$name:ident..$ct:expr) => { 
		expr::SeqVar::arb_str(stringify!($name), $ct).to_expr()
	};
	($name:ident..$ct:expr) => { 
		expr::SeqVar::const_str(stringify!($name), $ct).to_expr()
	};
	(*$name:ident) => { 
		expr::Singular::free_str(stringify!($name)).to_expr()
	};
	($name:ident) => {
		expr::Singular::arb_str(stringify!($name)).to_expr()
	};
	(& $name:ident) => { 
		expr::Singular::arb_str(stringify!($name)).to_expr()
	};
}


#[macro_export]
macro_rules! seq {
	(seq!($($stuff:tt)+)) => {
		seq!($($stuff)+)
	};
	(*{ $name:expr }) => { Into::<FreeSeq>::into($name).to_seq() };
	(&{ $name:expr }) => { Into::<ArbSeq>::into($name).to_seq() };
	({ $name:expr }) => { Into::<expr::SeqConst>::into($name).to_seq() };
	(*$name:ident..$ct:expr) => { 
		expr::SeqVar::free_str(stringify!($name), $ct)
	};
	(&$name:ident..$ct:expr) => { 
		expr::SeqVar::arb_str(stringify!($name), $ct)
	};
	($name:ident..$ct:expr) => { 
		expr::SeqVar::const_str(stringify!($name), $ct)
	};
}

#[allow(unused_macros)]
macro_rules! lambda {
	(lambda {$($s:tt)+} {$($body:tt)+}) => {
		expr::Lambda::<expr::Free>::new(s!($($body)+), free_var!($($s)+))
	};
	(lambdaseq {$($s:tt)+} {$($body:tt)+}) => {
		expr::LambdaSeq::new(s!($($body)+), free_seq_var!($($s)+))
	};
	({$e:expr}) => { $e }
}

#[macro_export]
macro_rules! s {
	(s!($($stuff:tt)+)) => {
		s!($($stuff)+)
	};
	(lambda {$($s:tt)+} {$($body:tt)+}) => {
		expr::Lambda::<expr::Free>::new(s!($($body)+), free_var!($($s)+))
	};
	(lambdaseq {$($s:tt)+} {$($body:tt)+}) => {
		expr::LambdaSeq::new(s!($($body)+), free_seq_var!($($s)+))
	};
	({$($f:tt)+} <- $v2:ident) => {
		expr::LambdaInst::<expr::Free>::new(lambda!($($f)+), s!($v2))
	};
	({$($f:tt)+} <- {$($stuff:tt)+}) => {
		expr::LambdaInst::<expr::Free>::new(lambda!($($f)+), s!($($stuff)+))
	};
	({$($f:tt)+} <= $v2:ident..$ct:expr) => {
		expr::LambdaSeqInst::new(lambda!($($f)+), seq!($v2..$ct))
	};
	({$($f:tt)+} <= {$($stuff:tt)+}) => {
		expr::LambdaSeqInst::new(lambda!($($f)+), seq!($($stuff)+))
	};
	({$name:expr}($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			expr::Singular::Composite($name.to_string(), v)
		}
	};
	($name:ident($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			expr::Singular::Composite(stringify!($name).to_string(), v)
		}
	};
	(*{ $name:expr }) => { 
		{
			let name = Into::into($name);
			expr::Free::from_cname(name).to_singular()
		}
	};
	(&{ $name:expr }) => { 
		{
			let name = Into::into($name);
			expr::Arb::from_cname(name).to_singular()
		}
	};
	({ $name:expr }) => { 
		{
			Into::<expr::Singular>::into($name)
		}
	};
	(*$name:ident) => { 
		expr::Singular::free_str(stringify!($name))
	};
	($name:ident) => {
		expr::Singular::arb_str(stringify!($name))
	};
	(& $name:ident) => { 
		expr::Singular::arb_str(stringify!($name))
	};
	($name:expr) => {
		Into::<expr::Singular>::into($name)
	}
}


#[macro_export]
macro_rules! f {
	(f!($($body:tt)+)) => {
		f!($($body)+)
	};
	(true) => { formula::Formula::True };
	(false) => { formula::Formula::False };
	(or({$($l:tt)+} {$($r:tt)+} $({$rest:tt})*)) => {
		get_or(ff!($($l)+), ff!($($r)+), &[$(ff!($rest),)*])
	};
	(and({$($l:tt)+} {$($r:tt)+} $({$rest:tt})*)) => {
		get_and(ff!($($l)+), ff!($($r)+), &[$(ff!($rest),)*])
	};
	(not($($l:tt)+)) => {
		formula::Not::new(ff!($($l)+))
	};	
	({$($f:tt)+}[$v:ident -> $v2:ident]) => {
		formula::ExpSubst::new(
			ff!($($f)+).ptr(),
			subst::Expr::sub_str(
				stringify!($v), 
				expr::Free::from_str(stringify!($v2)).to_singular()))
	};
	({$($f:tt)+}[$v:ident -> {$($s:tt)+}]) => {
		formula::ExpSubst::new(
			ff!($($f)+).ptr(),
			subst::Expr::sub_str(
				stringify!($v), 
				Into::<expr::Singular>::into(s!($($s)+))))
	};
	({$($f:tt)+}[{$sub:expr} -> {$($s:tt)+}]) => {
		formula::ExpSubst::new(
			ff!($($f)+).ptr(),
			subst::Expr::sub_free(
				Into::<expr::Free>::into($sub),
				Into::<expr::Singular>::into(s!($($s)+))))
	};
	({$($f:tt)+}[$v:ident => $v2:ident]) => {
		formula::FormSubst::new(
			ff!($($f)+),
			formula::Free::from_str(stringify!($v)),
			formula::Free::from_str(stringify!($v2)).to_form())
	};
	({$($f:tt)+}[$v:ident => {$($s:tt)+}]) => {
		formula::FormSubst::new(
			ff!($($f)+),
			formula::Free::from_str(stringify!($v)),
			ff!($($s)+))
	};
	({$($f:tt)+}[{$sub:expr} => {$($s:tt)+}]) => {
		formula::FormSubst::new(
			ff!($($f)+),
			Into::<formula::Free>::into($sub),
			ff!($($s)+))
	};
	({$($l:tt)+} -> {$($r:tt)+}) => {
		formula::Implies::new(ff!($($l)+), ff!($($r)+))
	};
	({$($l:tt)+} <-> {$($r:tt)+}) => {
		formula::IFF::new(ff!($($l)+), ff!($($r)+))
	};
	({$($l:tt)+} = {$($r:tt)+}) => {
		formula::Eq(s!($($l)+), s!($($r)+))
	};
	
	
	// Identifier list.
	(forall {$v:ident, $($rest:ident),+} { $($body:tt)+ }) => {
		{
			let f = formula::ForAll::from_str(stringify!($v), ff!($($body)+));
			[$(stringify!($rest),)+].iter().fold(f, |acc, &x| {
				formula::ForAll::from_str(x, acc.to_form())
			})
		}
	};
	(schema {$v:ident, $($rest:ident),+} { $($body:tt)+ }) => {
		{
			let f = formula::Schema::from_str(stringify!($v), ff!($($body)+));
			[$(stringify!($rest),)+].iter().fold(f, |acc, &x| {
				formula::Schema::from_str(x, acc.to_form())
			})
		}
	};
	(forallseq {$v:ident..$ct:expr, $($rest:ident..$ct2:expr),+} { $($body:tt)+ }) => 
	{
		{
			let f = formula::ForAllSeq::from_str(stringify!($v), $ct, ff!($($body)+));
			[$((stringify!($rest), $ct2),)+].iter().fold(f, |acc, &x| {
				formula::ForAllSeq::from_str(x.0, x.1, acc.to_form())
			})
		}
	};
	(exists {$v:ident, $($rest:ident),+} { $($body:tt)+ }) => {
		{
			let f = formula::Exists::from_str(stringify!($v), ff!($($body)+));
			[$(stringify!($rest),)+].iter().fold(f, |acc, &x| {
				formula::Exists::from_str(x, acc.to_form()).
			})
		}
	};
	// Expression  list.
	(forall {{$v:expr} $({$rest:expr}),+} { $($body:tt)+ }) => {
		{
			let f = formula::ForAll::from_free(
				Into::<expr::Free>::into($v), 
				f!($($body)+));
			[$(Into::<expr::Free>::into($rest),)+].iter().fold(f, |acc, x| {
				formula::ForAll::from_free(
					x.clone(), 
					acc.to_form())
			})
		}
	};
	(schema {{$v:expr} $({$rest:expr}),+} { $($body:tt)+ }) => {
		{
			let f = formula::Schema::from_free(
				Into::<formula::Free>::into($v), 
				f!($($body)+));
			[$(Into::<formula::Free>::into($rest),)+].iter().fold(f, |acc, x| {
				formula::Schema::from_free(
					x.clone(), 
					acc.to_form())
			})
		}
	};
	(forallseq {{$v:expr} $({$rest:expr}),+} { $($body:tt)+ }) => {
		{
			let f = formula::ForAllSeq::from_free(
				Into::<expr::FreeSeq>::into($v), 
				f!($($body)+));
			[$(Into::<expr::FreeSeq>::into($rest),)+].iter().fold(f, |acc, x| {
				formula::ForAllSeq::from_free(
					x.clone(), 
					acc.to_form())
			})
		}
	};
	(exists {{$v:expr} $({$rest:expr}),+} { $($body:tt)+ }) => {
		{
			let f = formula::Exists::from_free(
				Into::<expr::Free>::into($v), 
				f!($($body)+));
			[$(Into::<expr::Free>::into($rest),)+].iter().fold(f, |acc, x| {
				formula::Exists::from_free(
					x.clone(), 
					acc.to_form())
			})
		}
	};
	// Expression to String
	(forall {{$v:expr}} { $($body:tt)+ }) => {
		formula::ForAll::from_free(Into::<expr::Free>::into($v), ff!($($body)+))
	};
	(schema {{$v:expr}} { $($body:tt)+ }) => {
		formula::Schema::from_free(Into::<formula::Free>::into($v), ff!($($body)+))
	};
	(forallseq {{$v:expr}} { $($body:tt)+ }) => {
		formula::ForAllSeq::from_free(
			Into::<expr::FreeSeq>::into($v), 
			ff!($($body)+))
	};
	(exists {{$v:expr}} { $($body:tt)+ }) => {
		formula::Exists::from_free(Into::<expr::Free>::into($v), ff!($($body)+))
	};
	
	// Identifier to str.
	(forall {$v:ident} { $($body:tt)+ }) => {
		formula::ForAll::from_str(stringify!($v), ff!($($body)+))
	};
	(schema {$v:ident} { $($body:tt)+ }) => {
		formula::Schema::from_str(stringify!($v), ff!($($body)+))
	};
	(forallseq {$v:ident..$ct:expr} { $($body:tt)+ }) => {
		formula::ForAllSeq::from_str(stringify!($v), $ct, ff!($($body)+))
	};
	(exists {$v:ident} { $($body:tt)+ }) => {
		formula::Exists::from_str(stringify!($v), ff!($($body)+))
	};
	($name:ident($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			formula::Relation::new(stringify!($name).to_string(), v)
		}
	};
	({$name:expr}($($params:tt)+)) => {
		{
			let mut v = Vec::new();
			expr_list!(v; $($params)+);
			formula::Relation::new($name.to_string(), v)
		}
	};
	(&$f:ident) => { formula::Arb::from_str(stringify!($f)) };
	($f:ident) => { formula::Free::from_str(stringify!($f)) };
	(&{$f:expr}) => { Into::<formula::Arb>::into($f) };
	({$f:expr}) => { $f };
}

#[macro_export]
macro_rules! ff {
	($($t:tt)+) => ( f!($($t)+).to_form() )
}

#[macro_export]
macro_rules! d_seq {
	($s:expr; $($stuff:tt)+) =>  {{
		let w = dd!($($stuff)+);
		deduction::Sequence::cons($s.to_deduction(), w)
	}};
	($s:expr;) => { $s }
}

#[allow(unused_macros)]
macro_rules! free_var {
	($name:ident) => { Into::<expr::Free>::into(stringify!($name)) };
	({$name:expr}) => { Into::<expr::Free>::into($name) };
}

#[allow(unused_macros)]
macro_rules! free_seq_var {
	($name:ident..$ct:expr) => { 
		Into::<expr::FreeSeq>::into((stringify!($name), $ct))
	};
	({$name:expr}) => { Into::<expr::FreeSeq>::into($name) };
}

#[allow(unused_macros)]
macro_rules! arb_seq_var {
	($name:ident..$ct:expr) => { 
		Into::<expr::ArbSeq>::into((stringify!($name), $ct))
	};
	({$name:expr}) => { Into::<expr::ArbSeq>::into($name) };
}

#[allow(unused_macros)]
macro_rules! arb_var {
	($name:ident) => { 
		Into::<expr::Arb>::into(stringify!($name))
	};
	({$name:expr}) => { Into::<expr::Arb>::into($name) };
}

#[allow(unused_macros)]
macro_rules! const_var {
	($name:ident) => { 
		Into::<expr::Const>::into(stringify!($name))
	};
	({$name:expr}) => { Into::<expr::Const>::into($name) };
}

#[allow(unused_macros)]
macro_rules! arb_form {
	($name:ident) => { 
		Into::<formula::Arb>::into(stringify!($name))
	};
	({$name:expr}) => { Into::<formula::Arb>::into($name) };
}

#[macro_export]
macro_rules! d {
	(d!($($s:tt)+)) => {
		d!($($s)+)
	};
	(lambda_intro 
		{$($v:tt)+} 
		{$($lambda:tt)+} 
		{$($w:tt)+}
		$($stuff:tt)*) 
	=> {{
		let s = s!($($v)+);
		let l = s!($($lambda)+);
		let w = dd!($($w)+);
		d_seq!(deduction::LambdaInstIntro::new(s, l, w); $($stuff)*)
	}};
	(lambda_seq_intro 
		{$($v:tt)+} 
		{$($lambda:tt)+} 
		{$($w:tt)+}
		$($stuff:tt)*) 
	=> {{
		let s = s!($($v)+);
		let l = s!($($lambda)+);
		let w = dd!($($w)+);
		d_seq!(deduction::LambdaSeqInstIntro::new(s, l, w); $($stuff)*)
	}};
	(exists_extract 
		exists {$($c:tt)+} {$($f:tt)+} 
		{$($s:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(exists {$($c)+} {$($f)+});
		let s = const_var!($($s)+);
		let w = dd!($($w)+);
		d_seq!(deduction::ExistsExtract::new(thm, s, w); $($stuff)*)
	}};
	(schema_extract 
		schema {$($c:tt)+} {$($f:tt)+} 
		{$($thm:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(schema {$($c)+} {$($f)+});
		let s = ff!($($thm)+);
		let w = dd!($($w)+);
		d_seq!(deduction::SchemaExtract::new(thm, s, w); $($stuff)*)
	}};
	(schema_intro 
		schema {$($c:tt)+} {$($f:tt)+} 
		{$($thm:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(schema {$($c)+} {$($f)+});
		let s = arb_form!($($thm)+);
		let w = dd!($($w)+);
		d_seq!(deduction::SchemaIntro::new(thm, s, w); $($stuff)*)
	}};
	(forall_extract 
		forall {$($c:tt)+} {$($f:tt)+} 
		{$($s:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(forall {$($c)+} {$($f)+});
		let s = s!($($s)+);
		let w = dd!($($w)+);
		d_seq!(deduction::ForAllExtract::new(thm, s, w); $($stuff)*)
	}};
	(fseq_extract 
		forallseq {$($c:tt)+} {$($f:tt)+} 
		{$($s:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(forallseq {$($c)+} {$($f)+});
		let s = seq!($($s)+);
		let w = dd!($($w)+);
		d_seq!(deduction::ForAllSeqExtract::new(thm, s, w); $($stuff)*)
	}};
	(fseq_intro
		forallseq {$($c:tt)+} {$($f:tt)+} 
		{$($s:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(forallseq {$($c)+} {$($f)+});
		let s = arb_seq_var!($($s)+);
		let w = dd!($($w)+);
		d_seq!(deduction::ForAllSeqIntro::new(thm, s, w); $($stuff)*)
	}};
	(forall_intro
		forall {$($c:tt)+} {$($f:tt)+} 
		{$($s:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(forall {$($c)+} {$($f)+});
		let s = arb_var!($($s)+);
		let w = dd!($($w)+);
		d_seq!(deduction::ForAllIntro::new(thm, s, w); $($stuff)*)
	}};
	(exists_intro
		exists {$($c:tt)+} {$($f:tt)+} 
		{$($s:tt)+} 
		{$($w:tt)+} 
		$($stuff:tt)*) 
	=> {{
		let thm = f!(exists {$($c)+} {$($f)+});
		let s = s!($($s)+);
		let w = dd!($($w)+);
		d_seq!(deduction::ExistsIntro::new(thm, s, w); $($stuff)*)
	}};
	(sub 
		{$($s1:tt)+} 
		{$($s2:tt)+} 
		{$($c:tt)+} 
		{$($f:tt)+} 
		{$($w1:tt)+} 
		{$($w2:tt)+} 
		$($stuff:tt)*)
	=> {{
		let s1 = s!($($s1)+);
		let s2 = s!($($s2)+);
		let c = free_var!($($c)+);
		let f = ff!($($f)+);
		let w1 = dd!($($w1)+);
		let w2 = dd!($($w2)+);
		d_seq!(
			deduction::Substitution::new(s1, s2, c, f, w1, w2); 
			$($stuff)*)
	}};
	(eq_intro {$($s:tt)+} $($stuff:tt)*) => {{
		let s = s!($($s)+);
		d_seq!(deduction::EqualityIntro(s); $($stuff)*)
	}};
	(imply_intro 
		{$($i:tt)+}->{$($c:tt)+} 
		{ $($body:tt)+ } 
		$($stuff:tt)*) 
	=> {{
		let f = f!({$($i)+}->{$($c)+});
		let w1 = dd!($($body)+);
		d_seq!(deduction::ImplyIntro::new(f, w1); $($stuff)*)
	}};
	(and_intro and($($f:tt)+) { $($body:tt)+ } { $($body2:tt)+ } $($stuff:tt)*) 
	=> {{
		let f = f!(and($($f)+));
		let w1 = dd!($($body)+);
		let w2 = dd!($($body2)+);
		d_seq!(deduction::AndIntro::new(f, w1, w2); $($stuff)*)
	}};
	(not_extract not($($f:tt)+) { $($body:tt)+ } { $($body2:tt)+ } $($stuff:tt)*) 
	=> {{
		let f = f!(not($($f)+));
		let w1 = dd!($($body)+);
		let w2 = dd!($($body2)+);
		d_seq!(deduction::NegationExtract::new(f, w1, w2); $($stuff)*)
	}};
	(imply_extract 
		{$($i:tt)+}->{$($c:tt)+} 
		{ $($body:tt)+ } 
		{ $($body2:tt)+ }
		$($stuff:tt)*) 
	=> {{
		let f = f!({$($i)+}->{$($c)+});
		let w1 = dd!($($body)+);
		let w2 = dd!($($body2)+);
		d_seq!(deduction::ImplyExtract::new(f, w1, w2); $($stuff)*)
	}};
	(or_extract or($($f:tt)+)
		{$($form:tt)+}
		{ $($body:tt)+ } 
		{ $($body2:tt)+ }
		{ $($body3:tt)+ } 
		$($stuff:tt)*) 
	=> {{
		let f = f!(or($($f)+));
		let thm = ff!($($form)+);
		let w1 = dd!($($body)+);
		let w2 = dd!($($body2)+);
		let w3 = dd!($($body3)+);
		d_seq!(deduction::OrExtract::new(f, thm, w1, w2, w3); $($stuff)*)
	}};
	(and_extract and($($f:tt)+) { $($body:tt)+ } $($stuff:tt)*) 
	=> {{
		let f = f!(and($($f)+));
		let w1 = dd!($($body)+);
		d_seq!(deduction::AndExtract::new(f, w1); $($stuff)*)
	}};
	(or_intro or($($f:tt)+) { $($body:tt)+ } { $($body2:tt)+ } $($stuff:tt)*) 
	=> {{
		let f = f!(or($($f)+));
		let w1 = dd!($($body)+);
		let w2 = dd!($($body2)+);
		d_seq!(deduction::OrIntro::new(f, w1, w2); $($stuff)*)
	}};
	(subst_intro {$($f:tt)+}[$($def:tt)+] { $($body:tt)+ } $($stuff:tt)*) => {{
		let f = f!({$($f)+}[$($def)+]);
		let w = dd!($($body)+);
		d_seq!(deduction::SubstIntro::new(f, w); $($stuff)*)
	}};
	(form_redux {$($f:tt)+}[$($def:tt)+] { $($body:tt)+ } $($stuff:tt)*) => {{
		let f = f!({$($f)+}[$($def)+]);
		let w = dd!($($body)+);
		d_seq!(deduction::FormSubstReduction::new(f, w); $($stuff)*)
	}};
	(subst_redux {$($f:tt)+}[$($def:tt)+] { $($body:tt)+ } $($stuff:tt)*) => {{
		let f = f!({$($f)+}[$($def)+]);
		let w = dd!($($body)+);
		d_seq!(deduction::ExpSubstReduction::new(f, w); $($stuff)*)
	}};
	(subst_extract {$($f:tt)+}[$($def:tt)+] { $($body:tt)+ } $($stuff:tt)*) => {{
		let f = f!({$($f)+}[$($def)+]);
		let w = dd!($($body)+);
		d_seq!(deduction::SubstExtract::new(f, w); $($stuff)*)
	}};
	(not_intro not($($f:tt)+) { $($body:tt)+ } $($stuff:tt)*) => {{
		let f = f!(not($($f)+));
		let w = dd!($($body)+);
		d_seq!(deduction::NegationIntro::new(f, w); $($stuff)*)
	}};
	(iff_extract
		{$($l:tt)+} <-> {$($r:tt)+}
		{ $($b1:tt)+ } 
		$($more:tt)*) 
	=> {{
			let f = formula::IFF::new(ff!($($l)+), ff!($($r)+));
			let w1 = dd!($($b1)+);
			let d1 = deduction::IFFExtract::new(f, w1).to_deduction();
			d_seq!(d1; $($more)*)
		}
	};
	(iff_intro 
		{$($l:tt)+} <-> {$($r:tt)+}
		{ $($b1:tt)+ } 
		{ $($b2:tt)+ }
		$($more:tt)*) 
	=> {{
			let f = formula::IFF::new(ff!($($l)+), ff!($($r)+));
			let w1 = dd!($($b1)+);
			let w2 = dd!($($b2)+);
			let d1 = deduction::IFFIntro::new(f, w1, w2).to_deduction();
			//let d2 = dd!($($more)+);
			d_seq!(d1; $($more)*)
		}
	};
	(let $a:ident = {$($s:tt)+} { $($body:tt)+ } $($more:tt)*) => {{
		//let d1 = dd!($($more)+);		
		let d2 = deduction::Let::new(
				stringify!($a).to_string(), 
				s!($($s)+),
				dd!($($body)+))
			.to_deduction();
		d_seq!(d2; $($more)*)
	}};
	(_ $($rest:tt)+) => { 
		d!($($rest)+)
	};
	({ $d:expr }) => {
		$d
	};
	(_) => { deduction::Deduction::EmptyStep };
	() => { deduction::Deduction::EmptyStep };
}

#[macro_export]
macro_rules! dd {
	($($t:tt)+) => ( d!($($t)+).to_deduction() )
}


/*
pub fn test() {
	imports!();
	let _l = s!({lambdaseq {s..2} {s}} <= {{("b", 2)}});
	//let v = [var_list!(a, b, c, {"d"})];
	//let f = f!({true} -> {false});
	//let f = f!({true}[{"b"} => {true}]);	
	let _f: formula::And = f!(and({true} {false} {true}));
	let _f: formula::Not = f!(not(true));
	//let f = f!(schema {{"b"} {"c"}} {true});
	let _a = d!(
		lambda_seq_intro 
			{s} 
			{{lambdaseq {s..2} {s}} <= a..3} 
			{ _ }
		schema_intro schema {s} {true} { s } { _ }
		sub {a} {b} {c} {true} {_} {_}
		eq_intro {s}
		imply_extract {true} -> {false} {
			_
		} {
			{ deduction::Deduction::EmptyStep }
		}
		and_extract and({f!(true)} {false} {true}) {
			_
		}
		iff_extract {true} <-> {false} {
			_
		}
		not_extract not(false) {
			_
		} {
			_
		}
		_
		let a = {a} {
			_
		}
		subst_extract {true}[a -> {"b"}] {
			_
		}
		subst_redux {true}[a -> {"b"}] {
			_
		}
		form_redux {true}[a => {true}] {
			_
		}
		_
	);

	/*
	let p = proof!(
		thus { true }
		thus { false }
		therefore { false }
		assume {{Formula::True}} {
			thus { true }
			therefore { false }
		}
		let {a, {"b"}} {
			thus { true }
		}
		letf {a, {"b"}} {
			thus { false }
		}
	);
	*/
	/*
	let p = proof!(
		thus Formula::True;
		let a = s!(a);
		thus Formula::True;
		therefore Formula::True;
		thus Formula::True;
		therefore Formula::True;
		assume Formula::True; {
			therefore Formula::True;
			thus Formula::True;
			thus Formula::True;
			therefore Formula::True;
			thus Formula::True;
			therefore Formula::True;
		}
		thus Formula::True;
		let {a, {"b"}} {
			thus Formula::True;
		}
		letf {a, {"b"}} {
			thus Formula::True;
		}
		thus Formula::True;
	);
	*/
}
*/
