(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];

HOLTest`runTests["bool: TRUTH", Module[{},
  HOLTest`assertEq[isThm[TRUTH], True, "TRUTH is a thm"];
  HOLTest`assertEq[concl[TRUTH], mkConst["T", boolTy], "TRUTH conclusion is T"];
  HOLTest`assertEq[hyp[TRUTH], {}, "TRUTH has no hyps"];
]];

HOLTest`runTests["bool: EQTELIM", Module[{p, pEqT, th},
  p = mkVar["p", boolTy];
  pEqT = mkEq[p, mkConst["T", boolTy]];
  th = EQTELIM[ASSUME[pEqT]];
  HOLTest`assertEq[concl[th], p, "EQTELIM: p = T ⊢ p"];
  HOLTest`assertEq[hyp[th], {pEqT}, "EQTELIM preserves hyps"];
]];

HOLTest`runTests["bool: EQTINTRO", Module[{p, th},
  p = mkVar["p", boolTy];
  th = EQTINTRO[ASSUME[p]];
  HOLTest`assertEq[concl[th], mkEq[p, mkConst["T", boolTy]],
    "EQTINTRO: ⊢ p = T"];
  HOLTest`assertEq[hyp[th], {p}, "EQTINTRO preserves hyps"];
]];

HOLTest`runTests["bool: GEN basic", Module[{alpha, x, th, gen, expected},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  th = REFL[x];
  gen = GEN[x, th];
  expected = mkComb[
    mkConst["∀", tyFun[tyFun[alpha, boolTy], boolTy]],
    mkAbs[x, mkEq[x, x]]];
  HOLTest`assertEq[concl[gen], expected, "GEN: ⊢ ∀x. x = x"];
  HOLTest`assertEq[hyp[gen], {}, "GEN preserves empty hyps"];
]];

HOLTest`runTests["bool: GEN over bool", Module[{p, th, gen, expected},
  p = mkVar["p", boolTy];
  th = EQTINTRO[ASSUME[p]];  (* p ⊢ p = T *)
  gen = GEN[mkVar["q", boolTy], th];  (* q not free in hyps *)
  expected = mkComb[
    mkConst["∀", tyFun[tyFun[boolTy, boolTy], boolTy]],
    mkAbs[mkVar["q", boolTy], mkEq[p, mkConst["T", boolTy]]]];
  HOLTest`assertEq[concl[gen], expected, "GEN: ∀q. p = T (q fresh)"];
  HOLTest`assertEq[hyp[gen], {p}, "GEN preserves hyp p"];
]];

HOLTest`runTests["bool: GEN rejects free binder in hyps", Module[{p, th},
  p = mkVar["p", boolTy];
  th = EQTINTRO[ASSUME[p]];
  HOLTest`assertThrows[GEN[p, th], "rule",
    "GEN refuses binder that is free in hypotheses"];
]];

HOLTest`runTests["bool: SPEC basic", Module[{alpha, x, y, gen, spec},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  y = mkVar["y", alpha];
  gen = GEN[x, REFL[x]];
  spec = SPEC[y, gen];
  HOLTest`assertEq[concl[spec], mkEq[y, y], "SPEC: ∀x. x=x ⊢ y=y"];
  HOLTest`assertEq[hyp[spec], {}, "SPEC preserves empty hyps"];
]];

HOLTest`runTests["bool: SPEC at ground type", Module[{x, gen, spec, tConst},
  x = mkVar["x", boolTy];
  gen = GEN[x, REFL[x]];
  tConst = mkConst["T", boolTy];
  spec = SPEC[tConst, gen];
  HOLTest`assertEq[concl[spec], mkEq[tConst, tConst], "SPEC at T"];
]];

HOLTest`runTests["bool: SPEC type check", Module[{alpha, x, gen},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  gen = GEN[x, REFL[x]];
  HOLTest`assertThrows[SPEC[mkConst["T", boolTy], gen], "rule",
    "SPEC rejects wrong-type term"];
]];

HOLTest`runTests["bool: GEN/SPEC round-trip", Module[{alpha, x, t, gen, spec},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  gen = GEN[x, REFL[x]];
  spec = SPEC[x, gen];
  HOLTest`assertEq[concl[spec], mkEq[x, x], "GEN then SPEC at x recovers"];
]];

andTerm[p_, q_] := mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impliesTerm[p_, q_] := mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];

HOLTest`runTests["bool: CONJ basic", Module[{p, q, thp, thq, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  thp = ASSUME[p]; thq = ASSUME[q];
  th = CONJ[thp, thq];
  HOLTest`assertEq[concl[th], andTerm[p, q], "CONJ: ⊢ p ∧ q"];
  HOLTest`assertEq[hyp[th], Sort[{p, q}], "CONJ merges hypotheses"];
]];

HOLTest`runTests["bool: CONJ of TRUTH", Module[{th},
  th = CONJ[TRUTH, TRUTH];
  HOLTest`assertEq[concl[th], andTerm[mkConst["T", boolTy], mkConst["T", boolTy]],
    "⊢ T ∧ T"];
  HOLTest`assertEq[hyp[th], {}, "T ∧ T has no hyps"];
]];

HOLTest`runTests["bool: CONJUNCT1", Module[{p, q, conj, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  conj = CONJ[ASSUME[p], ASSUME[q]];
  th = CONJUNCT1[conj];
  HOLTest`assertEq[concl[th], p, "CONJUNCT1: ⊢ p"];
]];

HOLTest`runTests["bool: CONJUNCT2", Module[{p, q, conj, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  conj = CONJ[ASSUME[p], ASSUME[q]];
  th = CONJUNCT2[conj];
  HOLTest`assertEq[concl[th], q, "CONJUNCT2: ⊢ q"];
]];

HOLTest`runTests["bool: CONJUNCT rejects non-conj", Module[{p},
  p = ASSUME[mkVar["p", boolTy]];
  HOLTest`assertThrows[CONJUNCT1[p], "rule", "CONJUNCT1 rejects non-∧"];
  HOLTest`assertThrows[CONJUNCT2[p], "rule", "CONJUNCT2 rejects non-∧"];
]];

HOLTest`runTests["bool: MP basic", Module[{p, q, impTh, pTh, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  impTh = ASSUME[impliesTerm[p, q]];
  pTh = ASSUME[p];
  th = MP[impTh, pTh];
  HOLTest`assertEq[concl[th], q, "MP: ⊢ q"];
  HOLTest`assertEq[hyp[th], Sort[{impliesTerm[p, q], p}], "MP merges hyps"];
]];

HOLTest`runTests["bool: DISCH basic", Module[{p, th},
  p = mkVar["p", boolTy];
  th = DISCH[p, ASSUME[p]];
  HOLTest`assertEq[concl[th], impliesTerm[p, p], "DISCH: ⊢ p ⇒ p"];
  HOLTest`assertEq[hyp[th], {}, "DISCH removes p from hyps"];
]];

HOLTest`runTests["bool: UNDISCH basic", Module[{p, q, impTh, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  impTh = ASSUME[impliesTerm[p, q]];
  th = UNDISCH[impTh];
  HOLTest`assertEq[concl[th], q, "UNDISCH: ⊢ q"];
  HOLTest`assertEq[hyp[th], Sort[{impliesTerm[p, q], p}], "UNDISCH adds p"];
]];

HOLTest`runTests["bool: MP type check", Module[{p, q, badImp},
  p = mkVar["p", boolTy];
  q = mkVar["q", boolTy];
  HOLTest`assertThrows[MP[ASSUME[p], ASSUME[p]], "rule",
    "MP rejects non-implication"];
]];

notTerm[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
orTerm[p_, q_] := mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
existsTerm[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];

HOLTest`runTests["bool: NOTINTRO/NOTELIM round-trip", Module[{p, impTh, negTh, back},
  p = mkVar["p", boolTy];
  impTh = ASSUME[impliesTerm[p, mkConst["F", boolTy]]];
  negTh = NOTINTRO[impTh];
  HOLTest`assertEq[concl[negTh], notTerm[p], "NOTINTRO: ⊢ ¬ p"];
  back = NOTELIM[negTh];
  HOLTest`assertEq[concl[back], impliesTerm[p, mkConst["F", boolTy]],
    "NOTELIM: ⊢ p ⇒ F"];
]];

HOLTest`runTests["bool: NOTINTRO rejects non-⇒F", Module[{p},
  p = ASSUME[mkVar["p", boolTy]];
  HOLTest`assertThrows[NOTINTRO[p], "rule",
    "NOTINTRO rejects non-(p ⇒ F)"];
]];

HOLTest`runTests["bool: NOTELIM rejects non-¬", Module[{p},
  p = ASSUME[mkVar["p", boolTy]];
  HOLTest`assertThrows[NOTELIM[p], "rule",
    "NOTELIM rejects non-¬"];
]];

HOLTest`runTests["bool: CONTR from F", Module[{p, fAss, th},
  p = mkVar["p", boolTy];
  fAss = ASSUME[mkConst["F", boolTy]];
  th = CONTR[p, fAss];
  HOLTest`assertEq[concl[th], p, "CONTR: F ⊢ p"];
  HOLTest`assertEq[hyp[th], {mkConst["F", boolTy]}, "CONTR preserves F hyp"];
]];

HOLTest`runTests["bool: CONTR rejects non-F", Module[{pAss, q},
  pAss = ASSUME[mkVar["p", boolTy]];
  q = mkVar["q", boolTy];
  HOLTest`assertThrows[CONTR[q, pAss], "rule", "CONTR rejects non-F concl"];
]];

HOLTest`runTests["bool: EXISTS basic", Module[{alpha, x, c, existTm, th, ex},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  c = mkVar["c", alpha];
  existTm = existsTerm[x, mkEq[x, c]];
  th = REFL[c];
  ex = EXISTS[existTm, c, th];
  HOLTest`assertEq[concl[ex], existTm, "EXISTS: ⊢ ∃x. x = c"];
  HOLTest`assertEq[hyp[ex], {}, "EXISTS preserves empty hyps"];
]];

HOLTest`runTests["bool: EXISTS boolean witness", Module[{p, q, existTm, th, ex},
  p = mkVar["p", boolTy];
  q = mkVar["q", boolTy];
  existTm = existsTerm[q, mkEq[p, q]];
  th = REFL[p];
  ex = EXISTS[existTm, p, th];
  HOLTest`assertEq[concl[ex], existTm, "EXISTS: ⊢ ∃q. p = q"];
]];

HOLTest`runTests["bool: CHOOSE basic",
  Module[{alpha, x, y, v, c, existTm, exTh, bodyTm, bodyTh, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  v = mkVar["v", alpha];
  c = mkVar["c", alpha];
  existTm = existsTerm[x, mkEq[x, c]];
  exTh = EXISTS[existTm, c, REFL[c]];
  bodyTm = existsTerm[y, mkEq[y, c]];
  bodyTh = EXISTS[bodyTm, v, ASSUME[mkEq[v, c]]];
  th = CHOOSE[v, exTh, bodyTh];
  HOLTest`assertEq[concl[th], bodyTm, "CHOOSE: ⊢ ∃y. y = c"];
  HOLTest`assertEq[hyp[th], {}, "CHOOSE closes hypothesis"];
]];

HOLTest`runTests["bool: CHOOSE rejects v in concl",
  Module[{alpha, x, v, c, existTm, exTh, bodyTh},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  v = mkVar["v", alpha];
  c = mkVar["c", alpha];
  existTm = existsTerm[x, mkEq[x, c]];
  exTh = EXISTS[existTm, c, REFL[c]];
  bodyTh = ASSUME[mkEq[v, c]];
  HOLTest`assertThrows[CHOOSE[v, exTh, bodyTh], "rule",
    "CHOOSE rejects v free in concl"];
]];

HOLTest`runTests["bool: CHOOSE rejects wrong type",
  Module[{alpha, x, v, existTm, exTh, bodyTh},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  v = mkVar["v", boolTy];
  existTm = existsTerm[x, mkEq[x, mkVar["c", alpha]]];
  exTh = EXISTS[existTm, mkVar["c", alpha], REFL[mkVar["c", alpha]]];
  bodyTh = ASSUME[mkVar["p", boolTy]];
  HOLTest`assertThrows[CHOOSE[v, exTh, bodyTh], "rule",
    "CHOOSE rejects v of wrong type"];
]];

HOLTest`runTests["bool: DISJ1", Module[{p, q, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  th = DISJ1[ASSUME[p], q];
  HOLTest`assertEq[concl[th], orTerm[p, q], "DISJ1: ⊢ p ∨ q"];
  HOLTest`assertEq[hyp[th], {p}, "DISJ1 preserves p hyp"];
]];

HOLTest`runTests["bool: DISJ2", Module[{p, q, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  th = DISJ2[ASSUME[q], p];
  HOLTest`assertEq[concl[th], orTerm[p, q], "DISJ2: ⊢ p ∨ q"];
  HOLTest`assertEq[hyp[th], {q}, "DISJ2 preserves q hyp"];
]];

HOLTest`runTests["bool: DISJCASES basic", Module[{p, q, thOr, thPR, thQR, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  thOr = DISJ1[ASSUME[p], q];
  thPR = ASSUME[p];
  thQR = CONJUNCT1[CONJ[ASSUME[p], ASSUME[q]]];
  th = DISJCASES[thOr, thPR, thQR];
  HOLTest`assertEq[concl[th], p, "DISJCASES: ⊢ p"];
]];

HOLTest`runTests["bool: DISJCASES rejects non-∨", Module[{p, r1, r2},
  p = ASSUME[mkVar["p", boolTy]];
  r1 = ASSUME[mkVar["r", boolTy]];
  r2 = ASSUME[mkVar["r", boolTy]];
  HOLTest`assertThrows[DISJCASES[p, r1, r2], "rule",
    "DISJCASES rejects non-∨"];
]];

(* M4 acceptance test: ⊢ ∀x y. x = y ⇒ y = x *)
HOLTest`runTests["bool: M4 acceptance — symmetry of equality",
  Module[{alpha, x, y, xEqY, symTh, dischTh, innerGen, outerGen,
          forallTy, expected},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  xEqY = mkEq[x, y];
  symTh = SYM[ASSUME[xEqY]];
  dischTh = DISCH[xEqY, symTh];
  HOLTest`assertEq[concl[dischTh], impliesTerm[xEqY, mkEq[y, x]],
    "⊢ (x = y) ⇒ (y = x)"];
  HOLTest`assertEq[hyp[dischTh], {}, "discharged — no hyps"];
  innerGen = GEN[y, dischTh];
  outerGen = GEN[x, innerGen];
  forallTy = tyFun[tyFun[alpha, boolTy], boolTy];
  expected = mkComb[
    mkConst["∀", forallTy],
    mkAbs[x,
      mkComb[
        mkConst["∀", forallTy],
        mkAbs[y, impliesTerm[xEqY, mkEq[y, x]]]]]];
  HOLTest`assertEq[concl[outerGen], expected,
    "⊢ ∀x y. x = y ⇒ y = x"];
  HOLTest`assertEq[hyp[outerGen], {}, "closed theorem"];
]];
