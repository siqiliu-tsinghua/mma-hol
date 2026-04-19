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
