pub mod symmetry {
	imports!();
	pub fn thm() -> formula::Formula {
		ff!(forall {p, q} {
			{{p} = {q}} -> {{q} = {p}}
		})
	}

	pub fn proof() -> deduction::Deduction {
		dd!(forall_intro
			forall {p, q} {{{p} = {q}} -> {{q} = {p}}}
			{p} 
			{
				forall_intro
				forall {q} {{{&p} = {q}} -> {{q} = {&p}}}
				{q}
				{
					sub {&p} {&q} {y} {{*y} = {&p}}
					{
						eq_intro {&p}
					}
					{_}
				}
			}
		)
	}
}

pub mod transitivity {
	imports!();
	pub fn thm() -> formula::Formula {
		ff!(forall {p, q, r} {
			{and({{p} = {q}} {{q} = {r}})} -> {{p} = {r}}
		})
	}

	pub fn proof() -> deduction::Deduction {
		dd!(forall_intro
			forall {p, q, r} {{and({{p} = {q}} {{q} = {r}})} -> {{p} = {r}}}
			{p} 
			{
				forall_intro
				forall {q, r} {{and({{&p} = {q}} {{q} = {r}})} -> {{&p} = {r}}}
				{q}
				{
					forall_intro
					forall {r} {{and({{&p} = {&q}} {{&q} = {r}})} -> {{&p} = {r}}}
					{q}
					{
						sub {&q} {&r} {y} {{&p} = {*y}}	
						{
							and_extract and({{&p} = {&q}} {{&q} = {&r}}) {_}
						}
						{_}
					}
				}
			}
		)
	}
}