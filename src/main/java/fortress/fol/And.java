/*
 * Copyright (c) 2016, Amirhossein Vakili
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *    1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package fortress.fol;

import fortress.Constants;
import fortress.fol.pterm.PTerm;
import fortress.fol.visitor.FormulaVisitor;
import fortress.lambda.Const;
import fortress.lambda.Term;
import fortress.lambda.Var;
import fortress.formats.smt.smtlib.ComExpr;
import fortress.formats.smt.smtlib.SExpr;
import fortress.formats.smt.smtlib.StrExpr;
import fortress.util.Pair;

import java.util.*;
import java.util.Map.Entry;

import static fortress.util.Errors.failIf;

/**
 * Created by amirhossein on 15/01/16.
 */
public class And extends Formula {

	private SortedSet<Formula> body;

	public And(SortedSet<Formula> body) {
		failIf(body == null);
		this.body = body;
	}

	public And(Formula... formulas) {
		failIf(formulas.length < 2);
		SortedSet<Formula> body = new TreeSet<Formula>();
		Collections.addAll(body, formulas);
		this.body = body;
	}

	public SortedSet<Formula> getBody() {
		return body;
	}

	@Override
	public boolean isAnd() {
		return true;
	}

	@Override
	public boolean is_quantifier_free() {
		for (Formula f : body)
			if (!f.is_quantifier_free())
				return false;
		return true;
	}

	@Override
	public String toString() {
		return Constants.AND_Str + body.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (o == this)
			return true;
		if (o == null)
			return false;
		if (getClass() != o.getClass())
			return false;
		And temp = ((And) o);
		return body.equals(temp.body);
	}

	@Override
	public int compareTo(Formula o) {
		failIf(o == null);
		if (o == this)
			return 0;
		Class oc = o.getClass();
		if (oc == False.class || oc == True.class || oc == Atomic.class || oc == Not.class)
			return 1;
		if (getClass() != o.getClass())
			return -1;
		And temp = ((And) o);
		Iterator<Formula> it1 = body.iterator();
		Iterator<Formula> it2 = temp.body.iterator();
		while (it1.hasNext() && it2.hasNext()) {
			Formula f1 = it1.next();
			Formula f2 = it2.next();
			int test = f1.compareTo(f2);
			if (test != 0)
				return test;
		}
		if (it1.hasNext())
			return 1;
		if (it2.hasNext())
			return -1;
		return 0;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + body.hashCode();
		return result;
	}

	@Override
	public <T> T accept(FormulaVisitor<T> v) {
		return v.visitAnd(this);
	}

	@Override
	public SExpr toSMTLIB() {
		List<SExpr> temp = new ArrayList<>();
		temp.add(new StrExpr(Constants.smtlibOf.getOrDefault(Constants.AND_Str, Constants.AND_Str)));
		for (Formula f : body)
			temp.add(f.toSMTLIB());
		return new ComExpr(temp);
	}

	@Override
	void fvH(Set<Var> acc) {
		for (Formula f : body)
			f.fvH(acc);
	}

	@Override
	public Formula substitute(Var v, Term t) {
		SortedSet<Formula> temp = new TreeSet<>();
		for (Formula f : body)
			temp.add(f.substitute(v, t));
		return new And(temp);
	}

	@Override
	public Formula substitute(Map<Var, Term> sub) {
		SortedSet<Formula> temp = new TreeSet<>();
		for (Formula f : body)
			temp.add(f.substitute(sub));
		return new And(temp);
	}

	@Override
	public Formula nnf() {
		SortedSet<Formula> temp = new TreeSet<>();
		for (Formula f : body)
			temp.add(f.nnf());
		return new And(temp);
	}

	@Override
	Formula simplify1() {
		if (body.contains(false_))
			return false_;
		body.remove(true_);
		if (body.size() == 0)
			return true_;
		if (body.size() == 1)
			return body.first();
		SortedSet<And> temp = new TreeSet<>();
		for (Formula f : body) {
			if (body.contains(new Not(f)))
				return false_;
			if (f.isAnd())
				temp.add((And) f);
		}
		for (And f : temp) {
			body.remove(f);
			for (Formula ff : f.body)
				body.add(ff);
		}
		return this;
		/*
		 * Map<PTerm, Var> sub = new HashMap<>(); SortedSet<Formula> tempForall = new
		 * TreeSet<>(); SortedSet<Var> tempVar = new TreeSet<>(); SortedSet<Formula>
		 * tempFormula = new TreeSet<>(); for (Formula f: body){ if (f.isForall()){
		 * Forall ff = (Forall) f; for (Var v: ff.getVars()){ if
		 * (sub.containsKey(v.getType())){ tempForall.add(ff.getBody().substitute(v,
		 * sub.get(v.getType()))); } else { tempVar.add(v); sub.put(v.getType(), v);
		 * tempForall.add(ff.getBody()); } } } else { tempFormula.add(f); } } if
		 * (tempVar.isEmpty()) return this; Forall f = new Forall(tempVar, new
		 * And(tempForall)); if (tempFormula.isEmpty()) return f; tempFormula.add(f);
		 * return new And(tempFormula);
		 */
	}

	@Override
	public Formula simplify() {
		SortedSet<Formula> s = new TreeSet<>();
		for (Formula f : body)
			s.add(f.simplify());
		return new And(s).simplify1();
	}

	@Override
	Pair<Formula, Integer> skolemizeH(int acc, List<Term> argumentList, List<PTerm> typeList, List<Const> skolemFunList) {
		SortedSet<Formula> temp = new TreeSet<>();
		int i = acc;
		for (Formula f : body) {
			Pair<Formula, Integer> p = f.skolemizeH(i, argumentList, typeList, skolemFunList);
			i = p.right;
			temp.add(p.left);
		}
		return new Pair<>(new And(temp), i);
	}

	@Override
	public Formula prenex() {
		SortedSet<Var> forallVar = new TreeSet<>();
		SortedSet<Var> existsVar = new TreeSet<>();
		SortedSet<Formula> temp = new TreeSet<>();
//		Map<PTerm, Var> sub = new HashMap<>();
//		SortedSet<Var> used = new TreeSet<>();
//		int freshCounter = 0;
//		boolean check;
		Map<PTerm, Integer> maxType = new HashMap<>();
		Map<PTerm, Var[]> maxVars = new HashMap<>();
		for (Formula f: body) {
			Formula ff = f.prenex();
			if (ff.isForall()) {
				Forall fa = (Forall) ff;
				Map<PTerm, Integer> typeCounter = new HashMap<>();
				Map<PTerm, Set<Var>> varHolder = new HashMap<>();
				for (Var v: fa.getVars()) {
					if (typeCounter.containsKey(v.getType())) {
						int container = typeCounter.get(v.getType());
						container++;
						typeCounter.remove(v.getType());
						typeCounter.put(v.getType(), container);
					} else {
						typeCounter.put(v.getType(), 1);
					}
					if (varHolder.containsKey(v.getType())) {
						Set<Var> tempVarHolder = new TreeSet<>();
						tempVarHolder = varHolder.get(v.getType());
						tempVarHolder.add(v);
						varHolder.remove(v.getType());
						varHolder.put(v.getType(), tempVarHolder);
					} else {
						Set<Var> tempVarHolder = new TreeSet<>();
						tempVarHolder.add(v);
						varHolder.put(v.getType(), tempVarHolder);
					}
				}
				for (Entry<PTerm, Integer> entry: typeCounter.entrySet()) {
					if (maxType.containsKey(entry.getKey())) {
						if (maxType.get(entry.getKey()) < entry.getValue()) {
							maxType.remove(entry.getKey());
							maxType.put(entry.getKey(), entry.getValue());
							maxVars.remove(entry.getKey());
							Set<Var> x = varHolder.get(entry.getKey());
							Object[] z = x.toArray();
							Var[] y = new Var[z.length];
							for (int i = 0; i < z.length; i++) 
								y[i] = (Var) z[i];
							maxVars.put(entry.getKey(), y);
						}
					} else {
						maxType.put(entry.getKey(), entry.getValue());
						Set<Var> x = varHolder.get(entry.getKey());
						Object[] z = x.toArray();
						Var[] y = new Var[z.length];
						for (int i = 0; i < z.length; i++) 
							y[i] = (Var) z[i];
						maxVars.put(entry.getKey(), y);
					}
				}
			}
		}
		for (Formula f : body) {
			Map<PTerm, Integer> varCount = new HashMap<>();
			Formula ff = f.prenex();
//			check = false;
			if (ff.isForall()) {
				Forall fa = (Forall) ff;
				Formula a = fa.getBody();
				for (Var v: fa.getVars()) {
					Var substitute;
					if (varCount.containsKey(v.getType())) {
						substitute = maxVars.get(v.getType())[varCount.get(v.getType())];
						int tempHolder = varCount.get(v.getType()) + 1;
						varCount.remove(v.getType());
						varCount.put(v.getType(), tempHolder);
					} else {
						substitute = maxVars.get(v.getType())[0];
						varCount.put(v.getType(), 1);
					}
					a = a.substitute(v, substitute);
					forallVar.add(substitute);
				}
//				for (Var v : fa.getVars()) {
//					boolean substituted = false;
//					if (sub.containsKey(v.getType()) && !check) {
//						a = a.substitute(v, sub.get(v.getType()));
//						check = true;
//						substituted = true;
//					} else {
//						sub.put(v.getType(), v);
//					}
//					if (used.contains(v)) {
//						Var tempFresh = new Var("fresh" + Integer.toString(freshCounter), v.getType());
//						freshCounter++;
//						forallVar.add(tempFresh);
//						a = a.substitute(v, tempFresh);
//					} else if (!substituted) {
//						used.add(v);
//						forallVar.add(v);
//					}
//				}
				temp.add(a);
			} else {
				if (ff.isExists()) {
					existsVar.addAll(((Exists) ff).getVars());
					temp.add(((Exists) ff).getBody());
				} else
					temp.add(ff);
			}
		}
		if (forallVar.isEmpty() && existsVar.isEmpty())
			return this;
		Formula f = (new And(temp)).prenex();
		if (f.isForall()) {
			forallVar.addAll(((Forall) f).getVars());
			f = ((Forall) f).getBody();
		}
		if (!forallVar.isEmpty()) {
			;
			f = new Forall(forallVar, f);
			// System.out.println(f);
		}
		if (!existsVar.isEmpty())
			f = new Exists(existsVar, f);
		return f;
	}

	@Override
	public Formula simplifyEQ(Map<Term, Formula> literlas, List<Set<Term>> pairwiseDistinct) {
		SortedSet<Formula> temp = new TreeSet<>();
		for (Formula f : body) {
			Formula fse = f.simplifyEQ(literlas, pairwiseDistinct);
			if (fse.equals(Formula.false_))
				return false_;
			if (fse.equals(Formula.true_))
				continue;
			temp.add(fse);
		}
		if (temp.isEmpty())
			return true_;
		if (temp.size() == 1)
			return temp.first();
		return new And(temp);
	}

}
