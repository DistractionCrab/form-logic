pub mod thm1 {
	imports!();
	pub fn thm() -> formula::Formula {
		ff!(schema {p, q} { 
			{not(or({p} {q}))} -> {and({not(p)} {not(q)})}
		})
	}

	pub fn proof() -> deduction::Deduction {
		dd!(schema_intro
			schema {p, q} {{not(or({p} {q}))} -> {and({not(p)} {not(q)})}}
			{p} 
			{
				schema_intro
				schema {q} {{not(or({&p} {q}))} -> {and({not(&p)} {not(q)})}}
				{q}
				{
					imply_intro {not(or({&p} {&q}))} -> {and({not(&p)} {not(&q)})} {
						and_intro and({not(&p)} {not(&q)}) 
						{
							not_intro not(&p) {
								or_intro or({&p} {&q}) {_} {_}
							}
						}
						{
							not_intro not(&q) {
								or_intro or({&p} {&q}) {_} {_}
							}
						}
					}
				}
			}
		)
	}
}

pub mod thm2 {
	imports!();
	pub fn thm() -> formula::Formula {
		ff!(schema {p, q} { 
			{and({not(p)} {not(q)})} -> {not(or({p} {q}))}
		})
	}

	pub fn proof() -> deduction::Deduction {
		dd!(schema_intro
			schema {p, q} {{and({not(p)} {not(q)})} -> {not(or({p} {q}))}}
			{p} 
			{
				schema_intro
				schema {q} {{and({not(&p)} {not(q)})} -> {not(or({&p} {q}))}}
				{q}
				{
					imply_intro {not(or({&p} {&q}))} -> {and({not(&p)} {not(&q)})}
					{
						not_intro not(or({&p} {&q})) {
							or_extract or({&p} {&q}) {false}
							{_}
							{
								not_extract not(&p) {
									and_extract and({not(&p)} {not(&q)}) {_}
								}
								{_}
							}
							{
								not_extract not(&q) {
									and_extract and({not(&p)} {not(&q)}) {_}
								}
								{_}
							}
						}
					}
				}
			}
		)
	}
}

pub mod thm3 {
	imports!();
	pub fn thm() -> formula::Formula {
		ff!(schema {p, q} { 
			{or({not(p)} {not(q)})} -> {not(and({p} {q}))}
		})
	}

	pub fn proof() -> deduction::Deduction {
		dd!(schema_intro
			schema {p, q} {{or({not(p)} {not(q)})} -> {not(and({p} {q}))}}
			{p} 
			{
				schema_intro
				schema {q} {{or({not(&p)} {not(q)})} -> {not(and({&p} {q}))}}
				{q}
				{
					imply_intro {or({not(&p)} {not(&q)})} -> {not(and({&p} {&q}))}
					{
						not_intro not(and({&p} {&q})) {
							or_extract or({not(&p)} {not(&q)}) {false}
							{_}
							{
								not_extract not(&p) {
									and_extract and({&p} {&q}) {_}
								}
								{_}
							}
							{
								not_extract not(&q) {
									and_extract and({&p} {&q}) {_}
								}
								{_}
							}
						}
					}
				}
			}
		)
	}
}