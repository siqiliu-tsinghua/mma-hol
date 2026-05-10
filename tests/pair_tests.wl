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
