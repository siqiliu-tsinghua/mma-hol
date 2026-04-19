(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];

HOLTest`runTests["equal: SYM", Module[{alpha, x, y, eq, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  eq = ASSUME[mkEq[x, y]];
  th = SYM[eq];
  HOLTest`assertEq[concl[th], mkEq[y, x], "SYM swaps sides"];
  HOLTest`assertEq[hyp[th], {mkEq[x, y]}, "SYM preserves hypotheses"];
  HOLTest`assertEq[concl[SYM[REFL[x]]], mkEq[x, x], "SYM of REFL is REFL"];
  HOLTest`assertThrows[SYM[ASSUME[mkVar["p", boolTy]]], "rule",
    "SYM rejects non-equation"];
]];

HOLTest`runTests["equal: APTERM", Module[{alpha, beta, f, x, y, th},
  alpha = mkVarType["a"]; beta = mkVarType["b"];
  f = mkVar["f", tyFun[alpha, beta]];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  th = APTERM[f, ASSUME[mkEq[x, y]]];
  HOLTest`assertEq[concl[th], mkEq[mkComb[f, x], mkComb[f, y]],
    "APTERM: ⊢ f x = f y"];
  HOLTest`assertEq[hyp[th], {mkEq[x, y]}, "APTERM preserves hypotheses"];
]];

HOLTest`runTests["equal: APTHM", Module[{alpha, beta, f, g, x, th},
  alpha = mkVarType["a"]; beta = mkVarType["b"];
  f = mkVar["f", tyFun[alpha, beta]]; g = mkVar["g", tyFun[alpha, beta]];
  x = mkVar["x", alpha];
  th = APTHM[ASSUME[mkEq[f, g]], x];
  HOLTest`assertEq[concl[th], mkEq[mkComb[f, x], mkComb[g, x]],
    "APTHM: ⊢ f x = g x"];
  HOLTest`assertEq[hyp[th], {mkEq[f, g]}, "APTHM preserves hypotheses"];
]];

HOLTest`runTests["equal: BETACONV basic", Module[{alpha, x, y, idAbs, constAbs, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  idAbs = mkAbs[x, x];
  constAbs = mkAbs[x, y];
  th = BETACONV[mkComb[idAbs, y]];
  HOLTest`assertEq[concl[th], mkEq[mkComb[idAbs, y], y],
    "BETACONV: (λx.x) y = y"];
  HOLTest`assertEq[hyp[th], {}, "BETACONV has no hyps"];
  th = BETACONV[mkComb[constAbs, y]];
  HOLTest`assertEq[concl[th], mkEq[mkComb[constAbs, y], y],
    "BETACONV: (λx.y) y = y"];
]];

HOLTest`runTests["equal: BETACONV avoids capture", Module[{alpha, x, y, f, absTm, redex, th, expected},
  (* (λx. f x y) y   — the arg `y` is free in the body. BETACONV must not
     clash its fresh intermediate with y. Expected result: f y y. *)
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  y = mkVar["y", alpha];
  f = mkVar["f", tyFun[alpha, tyFun[alpha, alpha]]];
  absTm = mkAbs[x, mkComb[mkComb[f, x], y]];
  redex = mkComb[absTm, y];
  th = BETACONV[redex];
  expected = mkComb[mkComb[f, y], y];
  HOLTest`assertEq[concl[th], mkEq[redex, expected],
    "BETACONV: (λx. f x y) y = f y y"];
]];

HOLTest`runTests["equal: BETACONV non-trivial arg", Module[{alpha, beta, g, x, z, absTm, arg, redex, th, expected},
  (* (λx:α. g x) (g z)   where g : α→α *)
  alpha = mkVarType["a"];
  g = mkVar["g", tyFun[alpha, alpha]];
  x = mkVar["x", alpha];
  z = mkVar["z", alpha];
  absTm = mkAbs[x, mkComb[g, x]];
  arg = mkComb[g, z];
  redex = mkComb[absTm, arg];
  th = BETACONV[redex];
  expected = mkComb[g, mkComb[g, z]];
  HOLTest`assertEq[concl[th], mkEq[redex, expected],
    "BETACONV: (λx. g x) (g z) = g (g z)"];
]];

HOLTest`runTests["equal: BETACONV rejects non-redex", Module[{x},
  x = mkVar["x", boolTy];
  HOLTest`assertThrows[BETACONV[x], "rule", "BETACONV rejects var"];
  HOLTest`assertThrows[BETACONV[mkComb[mkVar["f", tyFun[boolTy, boolTy]], x]],
    "rule", "BETACONV rejects non-abs application"];
]];

HOLTest`runTests["equal: SYM on bootstrap definition", Module[{th, tTerm, xVar, body},
  (* Capstone ⊢ T reconstructed via the library SYM, not the inline symThm. *)
  xVar = mkVar["x", boolTy];
  body = mkAbs[xVar, xVar];
  tTerm = mkEq[body, body];
  th = SYM[tDef];
  HOLTest`assertEq[concl[th], mkEq[tTerm, mkConst["T", boolTy]],
    "SYM[tDef] swaps to (tTerm) = T"];
  HOLTest`assertEq[concl[EQMP[th, REFL[body]]], mkConst["T", boolTy],
    "⊢ T via SYM + REFL + EQMP"];
]];
