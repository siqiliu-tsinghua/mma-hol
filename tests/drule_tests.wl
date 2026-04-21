(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Drule`"];

HOLTest`runTests["drule: ALLCONV", Module[{x, th},
  x = mkVar["x", boolTy];
  th = ALLCONV[x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "ALLCONV[x] = REFL[x]"];
  HOLTest`assertEq[hyp[th], {}, "ALLCONV no hyps"];
]];

HOLTest`runTests["drule: NOCONV fails with conv tag", Module[{x},
  x = mkVar["x", boolTy];
  HOLTest`assertThrows[NOCONV[x], "conv", "NOCONV throws conv"];
]];

HOLTest`runTests["drule: THENC two ALLCONV", Module[{x, th},
  x = mkVar["x", boolTy];
  th = THENC[ALLCONV, ALLCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "THENC[ALLCONV, ALLCONV][x]"];
]];

HOLTest`runTests["drule: ORELSEC falls back", Module[{x, th},
  x = mkVar["x", boolTy];
  th = ORELSEC[NOCONV, ALLCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "ORELSEC tries second"];
]];

HOLTest`runTests["drule: ORELSEC first succeeds", Module[{x, th, c1},
  x = mkVar["x", boolTy];
  c1 = Function[t, REFL[t]];
  th = ORELSEC[c1, NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "ORELSEC picks first when it works"];
]];

HOLTest`runTests["drule: TRYCONV on failure", Module[{x, th},
  x = mkVar["x", boolTy];
  th = TRYCONV[NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "TRYCONV falls back to REFL"];
]];

HOLTest`runTests["drule: REPEATC on NOCONV", Module[{x, th},
  x = mkVar["x", boolTy];
  th = REPEATC[NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "REPEATC NOCONV = REFL"];
]];

HOLTest`runTests["drule: REPEATC one-shot BETA", Module[{x, y, redex, th},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  redex = mkComb[mkAbs[x, x], y];
  th = REPEATC[BETACONV][redex];
  HOLTest`assertEq[concl[th], mkEq[redex, y], "REPEATC reduces one β"];
]];

HOLTest`runTests["drule: SUBCONV comb", Module[{f, x, y, redex, th, fTy},
  fTy = tyFun[boolTy, boolTy];
  f = mkVar["f", fTy];
  x = mkVar["x", boolTy];
  y = mkVar["y", boolTy];
  redex = mkComb[f, mkComb[mkAbs[x, x], y]];
  (* SUBCONV[BETACONV][f ((λx. x) y)] should β-reduce the argument only. *)
  th = SUBCONV[BETACONV][redex];
  HOLTest`assertEq[concl[th], mkEq[redex, mkComb[f, y]], "SUBCONV reduces comb arg"];
]];

HOLTest`runTests["drule: SUBCONV abs", Module[{x, y, inner, outer, th, expected},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  inner = mkComb[mkAbs[x, x], y];
  outer = mkAbs[x, inner];
  (* SUBCONV[BETACONV][λx. (λx. x) y] reduces the inner β under the abs. *)
  th = SUBCONV[BETACONV][outer];
  expected = mkAbs[x, y];
  HOLTest`assertEq[concl[th][[2]], expected, "SUBCONV descends into abs"];
]];

HOLTest`runTests["drule: SUBCONV atomic fails", Module[{x},
  x = mkVar["x", boolTy];
  HOLTest`assertThrows[SUBCONV[ALLCONV][x], "conv",
    "SUBCONV on atom fails"];
]];

HOLTest`runTests["drule: DEPTHCONV nested β", Module[{x, y, inner, outer, th},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  inner = mkAbs[x, mkComb[mkAbs[x, x], x]];
  outer = mkComb[inner, y];
  th = DEPTHCONV[BETACONV][outer];
  HOLTest`assertEq[concl[th], mkEq[outer, y], "DEPTHCONV reduces nested β to y"];
]];

HOLTest`runTests["drule: DEPTHCONV no match returns REFL", Module[{x, th},
  x = mkVar["x", boolTy];
  th = DEPTHCONV[NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "DEPTHCONV NOCONV = REFL"];
]];

HOLTest`runTests["drule: REWRCONV identity on var", Module[{p, q, eqTh, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  eqTh = ASSUME[mkEq[p, q]];
  th = REWRCONV[eqTh][p];
  HOLTest`assertEq[concl[th], mkEq[p, q], "REWRCONV[p=q][p] = p=q"];
  HOLTest`assertEq[hyp[th], {mkEq[p, q]}, "preserves hyp"];
]];

HOLTest`runTests["drule: REWRCONV type-var instantiation",
  Module[{alpha, x, eqTh, bx, th},
    alpha = mkVarType["a"];
    x = mkVar["x", alpha];
    eqTh = REFL[x];
    bx = mkVar["x", boolTy];
    th = REWRCONV[eqTh][bx];
    HOLTest`assertEq[concl[th], mkEq[bx, bx], "REWRCONV instantiates type a := bool"];
]];

HOLTest`runTests["drule: REWRCONV rejects mismatch", Module[{p, q, r, eqTh},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  r = mkConst["T", boolTy];
  eqTh = ASSUME[mkEq[mkComb[mkAbs[p, p], p], q]];
  (* lhs = (λp. p) p : bool ; target = T : bool — lhs shape is a comb, T is a const. *)
  HOLTest`assertThrows[REWRCONV[eqTh][r], "conv", "REWRCONV rejects shape mismatch"];
]];

HOLTest`runTests["drule: REWRCONV rejects non-eq",
  Module[{p, th},
    p = mkVar["p", boolTy];
    th = ASSUME[p];
    HOLTest`assertThrows[REWRCONV[th][p], "conv", "REWRCONV demands equation"];
]];

HOLTest`runTests["drule: CONVRULE lifts", Module[{x, y, redex, th, rewTh},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  redex = mkComb[mkAbs[x, x], y];
  th = ASSUME[redex];
  rewTh = CONVRULE[BETACONV, th];
  HOLTest`assertEq[concl[rewTh], y, "CONVRULE β-reduces concl"];
  HOLTest`assertEq[hyp[rewTh], {redex}, "CONVRULE preserves hyps"];
]];

HOLTest`runTests["drule: ONCEREWRITERULE",
  Module[{p, q, notP, eqTh, andC, target, th, rewritten, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notP = mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
    eqTh = ASSUME[mkEq[notP, q]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[andC, notP], notP];
    th = ASSUME[target];
    rewritten = ONCEREWRITERULE[eqTh, th];
    expected = mkComb[mkComb[andC, q], notP];
    HOLTest`assertEq[concl[rewritten], expected,
      "ONCEREWRITERULE rewrites leftmost ¬p only"];
]];

HOLTest`runTests["drule: REWRITERULE rewrites all",
  Module[{p, q, notP, eqTh, andC, target, th, rewritten, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notP = mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
    eqTh = ASSUME[mkEq[notP, q]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[andC, notP], notP];
    th = ASSUME[target];
    rewritten = REWRITERULE[eqTh, th];
    expected = mkComb[mkComb[andC, q], q];
    HOLTest`assertEq[concl[rewritten], expected,
      "REWRITERULE rewrites both ¬p occurrences"];
]];
