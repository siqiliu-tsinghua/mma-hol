(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Pair`"];

(* ===== mkPair underlying constant ===== *)

HOLTest`runTests["pair: mkPair has correct generic type",
  Module[{ty, alpha, beta, expected},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[alpha, tyFun[beta, tyFun[alpha, tyFun[beta, boolTy]]]];
    ty = constType["mkPair"];
    HOLTest`assertEq[ty, expected,
      "mkPair : A → B → A → B → bool"];
]];

HOLTest`runTests["pair: mkPairDefThm is the expected equation",
  Module[{c, alpha, beta},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    c = concl[mkPairDefThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["mkPair", _]], _]],
      "concl is mkPair = <lambda>"];
    HOLTest`assertEq[hyp[mkPairDefThm], {},
      "definition has no hyps"];
]];

(* ===== prod type ===== *)

HOLTest`runTests["pair: prod type has arity 2",
  HOLTest`assertEq[typeArity["prod"], 2,
    "prod[A, B] takes two args"];
];

HOLTest`runTests["pair: prodTy[a, b] structure",
  Module[{alpha, beta, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    ty = prodTy[alpha, beta];
    HOLTest`assertEq[ty, tyApp["prod", {alpha, beta}],
      "prodTy builds tyApp[\"prod\", {α, β}]"];
]];

(* ===== ABS_prod / REP_prod ===== *)

HOLTest`runTests["pair: ABS_prod / REP_prod have correct generic types",
  Module[{alpha, beta, expectedAbs, expectedRep},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expectedAbs = tyFun[
      tyFun[alpha, tyFun[beta, boolTy]],
      tyApp["prod", {alpha, beta}]];
    expectedRep = tyFun[
      tyApp["prod", {alpha, beta}],
      tyFun[alpha, tyFun[beta, boolTy]]];
    HOLTest`assertEq[constType["ABS_prod"], expectedAbs,
      "ABS_prod : (A → B → bool) → prod[A, B]"];
    HOLTest`assertEq[constType["REP_prod"], expectedRep,
      "REP_prod : prod[A, B] → (A → B → bool)"];
]];

(* ===== bijection theorems ===== *)

HOLTest`runTests["pair: absRepProdThm is ABS_prod (REP_prod a) = a",
  Module[{c, lhs, rhs},
    c = concl[absRepProdThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _], _]],
      "concl is an equation"];
    lhs = c[[1, 2]]; rhs = c[[2]];
    HOLTest`assertTrue[
      MatchQ[lhs, comb[const["ABS_prod", _], comb[const["REP_prod", _], var["a", _]]]],
      "lhs is ABS_prod (REP_prod a)"];
    HOLTest`assertEq[rhs, var["a", tyApp["prod", {mkVarType["A"], mkVarType["B"]}]],
      "rhs is a"];
    HOLTest`assertEq[hyp[absRepProdThm], {},
      "no hyps"];
]];

(* ===== `,` constructor + injectivity ===== *)

HOLTest`runTests["pair: `,` has correct generic type",
  Module[{alpha, beta, expected, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[alpha, tyFun[beta, tyApp["prod", {alpha, beta}]]];
    ty = constType[","];
    HOLTest`assertEq[ty, expected,
      ", : A → B → prod[A, B]"];
]];

HOLTest`runTests["pair: pairCons builds a comb-of-comb term",
  Module[{alpha, beta, a, b, t},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    a = mkVar["a", alpha]; b = mkVar["b", beta];
    t = pairCons[a, b];
    HOLTest`assertEq[t,
      mkComb[mkComb[mkConst[",", constType[","]], a], b],
      "pairCons[a, b] = comb[comb[`,`, a], b]"];
]];

HOLTest`runTests["pair: destPair inverts pairCons",
  Module[{alpha, beta, a, b, parts},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    a = mkVar["a", alpha]; b = mkVar["b", beta];
    parts = destPair[pairCons[a, b]];
    HOLTest`assertEq[parts, {a, b}, "destPair[(a, b)] = {a, b}"];
]];

HOLTest`runTests["pair: pairConsDefThm is `,` = (λx y. ABS_prod (mkPair x y))",
  Module[{c, lhs},
    c = concl[pairConsDefThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const[",", _]], _]],
      "concl is `,` = <lambda>"];
    HOLTest`assertEq[hyp[pairConsDefThm], {},
      "no hyps"];
]];

HOLTest`runTests["pair: repPairThm is REP_prod (x, y) = mkPair x y",
  Module[{alpha, beta, x, y, c, expectedLhs, expectedRhs},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    x = mkVar["x", alpha]; y = mkVar["y", beta];
    expectedLhs = mkComb[
      mkConst["REP_prod", constType["REP_prod"]],
      pairCons[x, y]];
    expectedRhs = mkComb[mkComb[mkConst["mkPair", constType["mkPair"]], x], y];
    c = concl[repPairThm];
    HOLTest`assertEq[c, mkEq[expectedLhs, expectedRhs],
      "⊢ REP_prod (x, y) = mkPair x y"];
    HOLTest`assertEq[hyp[repPairThm], {},
      "no hyps"];
]];

HOLTest`runTests["pair: mkPairInjThm is (mkPair x y = mkPair xP yP) ⇒ (x = xP ∧ y = yP)",
  Module[{c, alpha, beta, x, y, xP, yP, ant, conseq},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    x = mkVar["x", alpha]; y = mkVar["y", beta];
    xP = mkVar["xP", alpha]; yP = mkVar["yP", beta];
    c = concl[mkPairInjThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["⇒", _], _], _]],
      "concl is an implication"];
    ant = c[[1, 2]];
    conseq = c[[2]];
    HOLTest`assertTrue[
      MatchQ[ant, comb[comb[const["=", _],
        comb[comb[const["mkPair", _], x_], y_]],
        comb[comb[const["mkPair", _], xP_], yP_]]],
      "antecedent is mkPair x y = mkPair xP yP"];
    HOLTest`assertTrue[
      MatchQ[conseq, comb[comb[const["∧", _], _], _]],
      "consequent is a conjunction"];
    HOLTest`assertEq[hyp[mkPairInjThm], {},
      "no hyps"];
]];

HOLTest`runTests["pair: pairInjThm is ((x, y) = (xP, yP)) ⇒ (x = xP ∧ y = yP)",
  Module[{c, alpha, beta, x, y, xP, yP, ant, conseq},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    x = mkVar["x", alpha]; y = mkVar["y", beta];
    xP = mkVar["xP", alpha]; yP = mkVar["yP", beta];
    c = concl[pairInjThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["⇒", _], _], _]],
      "concl is an implication"];
    ant = c[[1, 2]];
    conseq = c[[2]];
    HOLTest`assertEq[ant,
      mkEq[pairCons[x, y], pairCons[xP, yP]],
      "antecedent is (x, y) = (xP, yP)"];
    HOLTest`assertEq[conseq,
      mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]],
        mkEq[x, xP]],
        mkEq[y, yP]],
      "consequent is (x = xP) ∧ (y = yP)"];
    HOLTest`assertEq[hyp[pairInjThm], {},
      "no hyps"];
]];

(* ===== FST / SND projections + equation theorems ===== *)

HOLTest`runTests["pair: FST has correct generic type",
  Module[{alpha, beta, expected, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[tyApp["prod", {alpha, beta}], alpha];
    ty = constType["FST"];
    HOLTest`assertEq[ty, expected,
      "FST : prod[A, B] → A"];
]];

HOLTest`runTests["pair: SND has correct generic type",
  Module[{alpha, beta, expected, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[tyApp["prod", {alpha, beta}], beta];
    ty = constType["SND"];
    HOLTest`assertEq[ty, expected,
      "SND : prod[A, B] → B"];
]];

HOLTest`runTests["pair: fstDefThm and sndDefThm are equations",
  Module[{},
    HOLTest`assertTrue[
      MatchQ[concl[fstDefThm], comb[comb[const["=", _], const["FST", _]], _]],
      "fstDefThm concl is FST = <λ>"];
    HOLTest`assertTrue[
      MatchQ[concl[sndDefThm], comb[comb[const["=", _], const["SND", _]], _]],
      "sndDefThm concl is SND = <λ>"];
    HOLTest`assertEq[hyp[fstDefThm], {}, "fstDefThm has no hyps"];
    HOLTest`assertEq[hyp[sndDefThm], {}, "sndDefThm has no hyps"];
]];

HOLTest`runTests["pair: fstPairEqThm is FST (a, b) = a",
  Module[{alpha, beta, a, b, expected},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    a = mkVar["a", alpha]; b = mkVar["b", beta];
    expected = mkEq[
      mkComb[mkConst["FST", constType["FST"]], pairCons[a, b]],
      a];
    HOLTest`assertEq[concl[fstPairEqThm], expected,
      "⊢ FST (a, b) = a"];
    HOLTest`assertEq[hyp[fstPairEqThm], {}, "no hyps"];
]];

HOLTest`runTests["pair: sndPairEqThm is SND (a, b) = b",
  Module[{alpha, beta, a, b, expected},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    a = mkVar["a", alpha]; b = mkVar["b", beta];
    expected = mkEq[
      mkComb[mkConst["SND", constType["SND"]], pairCons[a, b]],
      b];
    HOLTest`assertEq[concl[sndPairEqThm], expected,
      "⊢ SND (a, b) = b"];
    HOLTest`assertEq[hyp[sndPairEqThm], {}, "no hyps"];
]];

HOLTest`runTests["pair: repAbsProdThm is (isPair r) = (REP_prod (ABS_prod r) = r)",
  Module[{c, lhs, rhs},
    c = concl[repAbsProdThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _], _]],
      "concl is an equation at bool"];
    lhs = c[[1, 2]]; rhs = c[[2]];
    (* lhs = (λp. ∃x y. p = mkPair x y) r *)
    HOLTest`assertTrue[
      MatchQ[lhs, comb[abs[bvar[0, _], _, _], var["r", _]]],
      "lhs is predicate applied to r"];
    (* rhs = REP_prod (ABS_prod r) = r *)
    HOLTest`assertTrue[
      MatchQ[rhs, comb[comb[const["=", _],
                comb[const["REP_prod", _],
                  comb[const["ABS_prod", _], var["r", _]]]], var["r", _]]],
      "rhs is REP_prod (ABS_prod r) = r"];
    HOLTest`assertEq[hyp[repAbsProdThm], {},
      "no hyps"];
]];
