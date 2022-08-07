use formula::Formula;
use formula::Form;
use formula::ConstName;
use knowledge_base::ResultBase;
use knowledge_base::KnowledgeBase;
use Ptr;

pub type Work = Ptr<Deduction>;

pub enum Deduction {
	EmptyStep,
	IFFIntro((Form, Work), (Form, Work)),
	IFFExtract(Form, Form),
	SubstReduce(Form, ConstName, Form),
	AndIntro(Form, Form),
	AndExtract(Form, Form),
	OrIntro(Form, Form),	
	OrExtract((Form, Work), (Form, Work), Form),
	ImplyIntro(Form, Form, Work),
	ImplyExtract(Form, Form),
	NotIntro(Form, Work),
	NotExtract(Form),
	EqualityIntro(Form),
	Substitution(Form, Form, ConstName, Form),
	ForAllSeqExtract((u64, ConstName, Form), Vec<Formula>),
	ExistsIntro((ConstName, Form), Form),
	ExistsExtract((ConstName, Form), ConstName),
	ForAllExtract((ConstName, Form), Form),
	ForAllIntro((ConstName, Form), Work),
	Sequence(Vec<Deduction>),
	Let(ConstName, Vec<ConstName>, Form),
}

impl Deduction {
	pub fn deduced<K: KnowledgeBase>(&self, k: K, thm: &Formula) -> bool {
		let k = ResultBase::Root(Ptr::new(k));
		
		self.apply_work(k).contains(thm)
	}

	pub fn apply_work<K: KnowledgeBase>(&self, k: K) -> ResultBase<K> {
		self.apply_work_inner(ResultBase::new(k))
	}

	fn apply_work_inner<K: KnowledgeBase>(&self, k: ResultBase<K>) -> ResultBase<K> {		
		match self {
			Deduction::EmptyStep => k,
			Deduction::AndIntro(f1, f2) => self.and_intro(k, f1.clone(), f2.clone()),
			Deduction::AndExtract(f1, f2) => self.and_intro(k, f1.clone(), f2.clone()),
			Deduction::OrIntro(f1, f2) => self.or_intro(k, f1.clone(), f2.clone()),
			Deduction::OrExtract(f1, f2, f3) => self.or_extract(k, f1, f2, f3.clone()),
			Deduction::ImplyIntro(f1, f2, w) => self.implies_intro(k, f1.clone(), f2.clone(), w.clone()),
			Deduction::ImplyExtract(f1, f2) => self.implies_extract(k, f1.clone(), f2.clone()),
			Deduction::NotIntro(f1, w) => self.not_intro(k, f1.clone(), w.clone()),
			Deduction::NotExtract(f1) => self.not_extract(k, f1.clone()),
			Deduction::IFFIntro(f1, f2) => self.iff_intro(k, f1, f2),
			Deduction::IFFExtract(f1, f2) => self.iff_extract(k, f1.clone(), f2.clone()),
			Deduction::EqualityIntro(f) => self.equality_intro(k, f.clone()),
			Deduction::Substitution(f1, f2, c, sub) =>
				self.substitution(k, f1.clone(), f2.clone(), c, sub.clone()),
			Deduction::ForAllIntro(f, w) => self.forall_intro(k, f, w.clone()),
			Deduction::ForAllExtract(f, w) => self.forall_extract(k, f, w.clone()),
			Deduction::ForAllSeqExtract(f, w) => self.forallseq_extract(k, f, w.clone()),
			Deduction::ExistsIntro(f, w) => self.exists_intro(k, f, w.clone()),
			Deduction::ExistsExtract(f, w) => self.exists_extract(k, f, w.clone()),
			Deduction::Let(c, v, f) => self.alias(k, c, v, f.clone()),
			Deduction::Sequence(v) => self.sequence(k, v),
			Deduction::SubstReduce(f1, c, f2) => self.sub_reduce(k, f1.clone(), c, f2.clone()),
			//_ => panic!("")
		}
	}

	pub fn sub_reduce<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, c: &ConstName, f2: Form) 
	-> ResultBase<K> {
		let thm = Formula::Subst(f1.clone(), c.clone(), f2.clone());

		if k.contains(&thm) {
			k.result_form(f1.substitute(c, &f2))
		} else {
			ResultBase::Err(format!("SubReduce: Did not deduce theorem: {}", thm.to_string()))
		}
	}	

	pub fn sequence<K: KnowledgeBase>(&self, k: ResultBase<K>, work: &Vec<Deduction>) 
	-> ResultBase<K> {
		work.iter().fold(k, |r, d| d.apply_work_inner(r))
	}

	pub fn alias<K: KnowledgeBase>(
		&self, 
		k: ResultBase<K>, 
		c: &ConstName, 
		vars: &Vec<ConstName>,
		f1: Form) 
	-> ResultBase<K> {
		if !k.has_const(&c) {
			let thm = if vars.len() > 0 {				
				let vs = [&[c.clone()], vars.as_slice()].concat();
				let r = Formula::const_to_relation(&vs);
				let thm1 = Formula::Eq(r.ptr(), f1);
				vars.iter().fold(thm1, |acc, x| Formula::ForAll(x.clone(), acc.ptr()))
			} else {
				Formula::Eq(Formula::Const(c.clone()).ptr(), f1)			
			};
			k.result_const(c.clone()).result_form(thm)	
		} else {
			ResultBase::Err(format!("Alias: Cannot redefine constant {}", c.to_string()))
		}
	}

	pub fn equality_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form) 
	-> ResultBase<K> {
		k.result_form(Formula::Eq(f1.clone(), f1.clone()))
	}

	pub fn exists_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f: &(ConstName, Form), v: Form) 
	-> ResultBase<K>{
		let thm = f.1.substitute(&f.0, &v);

		if k.contains(&thm) {
			k.result_form(Formula::Exists(f.0.clone(), f.1.clone()))
		} else {
			ResultBase::Err(format!("ExistsIntro: Did not deduce formula {}", thm.to_string()))
		}
	}

	pub fn exists_extract<K: KnowledgeBase>(&self, k: ResultBase<K>, f: &(ConstName, Form), v: ConstName) 
	-> ResultBase<K>{

		if !k.has_const(&v) {
			let thm = f.1.substitute(&f.0, &Formula::Const(v.clone()));
			k.result_form(thm)
		} else {
			ResultBase::Err(format!("ExistsExtract: Cannot redefine constant {}", v.to_string()))
		}
	}

	pub fn forall_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f: &(ConstName, Form), w: Work) 
	-> ResultBase<K> {
		if !k.has_const(&f.0) {
			let assume = k.result_const(f.0.clone());
			let thm = f.1.substitute(&f.0, &Formula::Const(f.0.clone()));
			
			if w.deduced(assume, &thm) {
				k.result_form(Formula::ForAll(f.0.clone(), f.1.clone()))
			} else {
				ResultBase::Err(format!("ForAllIntro: Did not deduce formula {}", thm.to_string()))
			}
		} else {
			ResultBase::Err(format!("ForAllIntro: Cannot redefine constant: {}", f.0.to_string()))
		}
	}

	pub fn forall_extract<K: KnowledgeBase>(&self, k: ResultBase<K>, f: &(ConstName, Form), v: Form) 
	-> ResultBase<K> {
		let thm = Formula::ForAll(f.0.clone(), f.1.clone());

		if k.contains(&thm) {
			let r = f.1.substitute(&f.0, &v);
			k.result_form(r)
		} else {
			ResultBase::Err(format!("ForAllExtract: Did not deduce formula {}", thm.to_string()))
		}
	}

	pub fn forallseq_extract<K: KnowledgeBase>(&self, k: ResultBase<K>, f: &(u64, ConstName, Form), v: Vec<Formula>) 
	-> ResultBase<K> {
		let thm = Formula::ForAllSeq(f.0, f.1.clone(), f.2.clone());

		if k.contains(&thm) {
			let r = f.2.substitute_seq(f.0, &f.1, &v);
			k.result_form(r)
		} else {
			ResultBase::Err(format!("ForAllSeqExtract: Did not deduce formula {}", thm.to_string()))	
		}
	}

	pub fn substitution<K: KnowledgeBase>(&self, 
		k: ResultBase<K>, 
		f1: Form,
		f2: Form,
		c: &ConstName,
		sub: Form) 
	-> ResultBase<K> {
		let t1 = Formula::Eq(f1.clone(), f2.clone());
		let c1 = k.contains(&t1);

		if c1 {
			let t2 = sub.substitute(c, &f1);
			let c2 = k.contains(&t2);
			if c2 {
				k.result_form(sub.substitute(c, &f2))
			} else {
				ResultBase::Err(format!("Substitution: Did not deduced {}[{} \\ {}]",
					sub.to_string(),
					c.to_string(),
					f1.to_string()))
			}
		} else {
			ResultBase::Err(format!("Substitution: Did not deduced f1 == f2 = {} == {}", 
				f1.to_string(),
				f2.to_string()))
		}
	}

	pub fn and_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, f2: Form) 
	-> ResultBase<K> {
		let c1 = k.contains(&f1);
		let c2 = k.contains(&f2);
		if c1 && c2 {
			k.result_form(Formula::And(f1.clone(), f2.clone()))
		} else if !c1 {
			ResultBase::Err(format!("AndIntro: Did not deduced f1 = {}", f1.to_string()))
		} else {
			ResultBase::Err(format!("AndIntro: Did not deduced f2 = {}", f2.to_string()))
		}
	}

	pub fn and_extract<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, f2: Form) 
	-> ResultBase<K> {
		let f = Formula::And(f1.clone(), f2.clone());
		
		if k.contains(&f) {
			k.result_ptr(f1).result_ptr(f2)
		} else {
			ResultBase::Err(format!("AndExtract: Did not deduced f1&f2 = {} && {}", 
				f1.to_string(),
				f2.to_string()))
		}
	}

	pub fn or_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, f2: Form) 
	-> ResultBase<K> {
		let c1 = k.contains(&f1);
		let c2 = k.contains(&f2);
		if c1 || c2 {
			k.result_form(Formula::And(f1.clone(), f2.clone()))
		} else {
			ResultBase::Err(format!("OrIntro: Did not deduced either f1 = {} or f2 = {}", 
				f2.to_string(),
				f2.to_string()))
		}
	}

	pub fn or_extract<K: KnowledgeBase>(
		&self, k: ResultBase<K>, 
		f1: &(Form, Work), 
		f2: &(Form, Work), 
		f3: Form) 
	-> ResultBase<K> {
		let k1 = k.result_ptr(f1.0.clone());
		let k2 = k.result_ptr(f2.0.clone());
		let c1 = f1.1.deduced(k1, &f3);
		let c2 = f2.1.deduced(k2, &f3);
		if c1 && c2 {
			k.result_ptr(f3.clone())
		} else if !c1 {
			ResultBase::Err(format!("OrExtract: Did not deduced f1->f3 = {}", f2.0.to_string()))
		} else {
			ResultBase::Err(format!("OrExtract: Did not deduced f2->f3 = {}", f1.0.to_string()))
		}
	}

	pub fn not_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, work: Work) 
	-> ResultBase<K> {
		let assume = k.result_ptr(f1.clone());
		let c = work.deduced(assume, &Formula::False);

		if c {
			k.result_form(Formula::Not(f1))
		} else {
			ResultBase::Err(format!("NotIntro: Did not reach contradiction f1 = {}", f1.to_string()))
		}
	}

	pub fn not_extract<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form) 
	-> ResultBase<K> {
		let c1 = k.contains(&f1);
		let c2 = k.contains(&Formula::Not(f1.clone()));

		if c1 && c2 {
			k.result_form(Formula::False)
		} else {
			ResultBase::Err(format!("NotExtract: Did not reach contradiction f1 = {}", f1.to_string()))
		}
	}

	pub fn iff_extract<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, f2: Form) 
	-> ResultBase<K> {
		let thm = Formula::IFF(f1.clone(), f2.clone());
		let c  = k.contains(&thm);
		let c1 = k.contains(&f1);
		let c2 = k.contains(&f2);
		if c {
			if c1 {
				k.result_ptr(f2.clone())
			} else if c2 {
				k.result_ptr(f1.clone())
			} else {
				ResultBase::Err(format!("IFFExtract: Did not deduced either f1 = {} or f2 = {}", 
					f1.to_string(),
					f2.to_string()))
			}
		} else {
			ResultBase::Err(format!("IFFExtract: Did not deduced either f1 <=> f2 = {} <=> {}", 
					f1.to_string(),
					f2.to_string()))
		}
	}

	pub fn implies_extract<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, f2: Form) 
	-> ResultBase<K> {
		let thm = Formula::Implies(f1.clone(), f2.clone());
		let c1 = k.contains(&thm);
		let c2 = k.contains(&f1);
		if c1 {
			if c2 {
				k.result_ptr(f2.clone())
			} else {
				ResultBase::Err(format!("ImpliesExtract: Did not deduced either f1 = {}", f1.to_string()))
			}			
		} else {
			ResultBase::Err(format!("ImpliesExtract: Did not deduced either f1->f2 = {}->{}", 
				f1.to_string(),
				f2.to_string()))
		}
	}

	pub fn iff_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: &(Form, Work), f2: &(Form, Work)) 
	-> ResultBase<K> {
		let k1 = k.result_ptr(f1.0.clone());
		let k2 = k.result_ptr(f2.0.clone());
		let c1 = f1.1.deduced(k1, &f2.0);
		let c2 = f2.1.deduced(k2, &f1.0);

		if c1 && c2 {
			k.result_form(Formula::IFF(f1.0.clone(), f2.0.clone()))
		} else if !c1 {
			ResultBase::Err(format!("IFFIntro: Did not deduced f1->f2 = {}", f2.0.to_string()))
		} else {
			ResultBase::Err(format!("IFFIntro: Did not deduced f2->f1 = {}", f1.0.to_string()))
		}
	}

	pub fn implies_intro<K: KnowledgeBase>(&self, k: ResultBase<K>, f1: Form, f2: Form, w: Work) 
	-> ResultBase<K> {
		let k1 = k.result_ptr(f1.clone());
		let c1 = w.deduced(k1, &f2);

		if c1 {
			k.result_form(Formula::Implies(f1.clone(), f2.clone()))
		} else {
			ResultBase::Err(format!("ImpliesIntro: Did not deduced f2->f1 = {}", f1.to_string()))
		}
	}
}