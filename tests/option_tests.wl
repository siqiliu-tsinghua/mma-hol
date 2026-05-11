(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Option`"];

(* ===== mkNone / mkSome ===== *)

HOLTest`runTests["option: mkNone has correct generic type",
  Module[{alpha, expected, ty},
    alpha = mkVarType["A"];
    expected = tyFun[alpha, boolTy];
    ty = constType["mkNone"];
    HOLTest`assertEq[ty, expected, "mkNone : A → bool"];
]];

HOLTest`runTests["option: mkSome has correct generic type",
  Module[{alpha, expected, ty},
    alpha = mkVarType["A"];
    expected = tyFun[alpha, tyFun[alpha, boolTy]];
    ty = constType["mkSome"];
    HOLTest`assertEq[ty, expected, "mkSome : A → A → bool"];
]];

HOLTest`runTests["option: mkNoneDefThm / mkSomeDefThm are equations",
  Module[{},
    HOLTest`assertTrue[
      MatchQ[concl[mkNoneDefThm], comb[comb[const["=", _], const["mkNone", _]], _]],
      "mkNone = <lambda>"];
    HOLTest`assertTrue[
      MatchQ[concl[mkSomeDefThm], comb[comb[const["=", _], const["mkSome", _]], _]],
      "mkSome = <lambda>"];
]];

(* ===== option type ===== *)

HOLTest`runTests["option: option type has arity 1",
  HOLTest`assertEq[typeArity["option"], 1,
    "option[A] takes one arg"];
];

HOLTest`runTests["option: optionTy[a] structure",
  Module[{alpha, ty},
    alpha = mkVarType["A"];
    ty = optionTy[alpha];
    HOLTest`assertEq[ty, tyApp["option", {alpha}],
      "optionTy[A] = tyApp[\"option\", {A}]"];
]];

(* ===== ABS_option / REP_option ===== *)

HOLTest`runTests["option: ABS_option / REP_option types",
  Module[{alpha, repTy, optionTyA, expectedAbs, expectedRep},
    alpha = mkVarType["A"];
    repTy = tyFun[alpha, boolTy];
    optionTyA = tyApp["option", {alpha}];
    expectedAbs = tyFun[repTy, optionTyA];
    expectedRep = tyFun[optionTyA, repTy];
    HOLTest`assertEq[constType["ABS_option"], expectedAbs,
      "ABS_option : (A → bool) → option[A]"];
    HOLTest`assertEq[constType["REP_option"], expectedRep,
      "REP_option : option[A] → (A → bool)"];
]];

HOLTest`runTests["option: absRepOptionThm is ABS_option (REP_option a) = a",
  Module[{c},
    c = concl[absRepOptionThm];
    HOLTest`assertTrue[
      MatchQ[c[[1, 2]],
        comb[const["ABS_option", _], comb[const["REP_option", _], var["a", _]]]],
      "lhs is ABS_option (REP_option a)"];
]];

(* ===== NONE / SOME constructors ===== *)

HOLTest`runTests["option: NONE has type option[A]",
  Module[{alpha, expected, ty},
    alpha = mkVarType["A"];
    expected = tyApp["option", {alpha}];
    ty = constType["NONE"];
    HOLTest`assertEq[ty, expected, "NONE : option[A]"];
]];

HOLTest`runTests["option: SOME has type A → option[A]",
  Module[{alpha, expected, ty},
    alpha = mkVarType["A"];
    expected = tyFun[alpha, tyApp["option", {alpha}]];
    ty = constType["SOME"];
    HOLTest`assertEq[ty, expected, "SOME : A → option[A]"];
]];

HOLTest`runTests["option: noneDefThm / someDefThm are equations",
  Module[{},
    HOLTest`assertTrue[
      MatchQ[concl[noneDefThm], comb[comb[const["=", _], const["NONE", _]], _]],
      "NONE = <body>"];
    HOLTest`assertTrue[
      MatchQ[concl[someDefThm], comb[comb[const["=", _], const["SOME", _]], _]],
      "SOME = <body>"];
    HOLTest`assertEq[hyp[noneDefThm], {}, "noneDefThm no hyps"];
    HOLTest`assertEq[hyp[someDefThm], {}, "someDefThm no hyps"];
]];

HOLTest`runTests["option: someTerm builds SOME a",
  Module[{alpha, a, t},
    alpha = mkVarType["A"];
    a = mkVar["a", alpha];
    t = someTerm[a];
    HOLTest`assertEq[t,
      mkComb[mkConst["SOME", constType["SOME"]], a],
      "someTerm[a] = SOME a"];
]];

(* ===== REP bridges ===== *)

HOLTest`runTests["option: repNoneThm is REP_option NONE = mkNone",
  Module[{c, expected},
    expected = mkEq[
      mkComb[mkConst["REP_option", constType["REP_option"]],
             mkConst["NONE", constType["NONE"]]],
      mkConst["mkNone", constType["mkNone"]]];
    c = concl[repNoneThm];
    HOLTest`assertEq[c, expected, "⊢ REP_option NONE = mkNone"];
    HOLTest`assertEq[hyp[repNoneThm], {}, "no hyps"];
]];

HOLTest`runTests["option: repSomeThm is REP_option (SOME x) = mkSome x",
  Module[{alpha, x, expected, c},
    alpha = mkVarType["A"];
    x = mkVar["x", alpha];
    expected = mkEq[
      mkComb[mkConst["REP_option", constType["REP_option"]], someTerm[x]],
      mkComb[mkConst["mkSome", constType["mkSome"]], x]];
    c = concl[repSomeThm];
    HOLTest`assertEq[c, expected, "⊢ REP_option (SOME x) = mkSome x"];
    HOLTest`assertEq[hyp[repSomeThm], {}, "no hyps"];
]];

(* ===== injectivity ===== *)

HOLTest`runTests["option: mkSomeInjThm is (mkSome x = mkSome xP) ⇒ (x = xP)",
  Module[{alpha, x, xP, expected, c},
    alpha = mkVarType["A"];
    x = mkVar["x", alpha]; xP = mkVar["xP", alpha];
    expected = mkComb[mkComb[
      mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[mkComb[mkConst["mkSome", constType["mkSome"]], x],
           mkComb[mkConst["mkSome", constType["mkSome"]], xP]]],
      mkEq[x, xP]];
    c = concl[mkSomeInjThm];
    HOLTest`assertEq[c, expected,
      "⊢ (mkSome x = mkSome xP) ⇒ (x = xP)"];
    HOLTest`assertEq[hyp[mkSomeInjThm], {}, "no hyps"];
]];

HOLTest`runTests["option: someInjThm is (SOME x = SOME xP) ⇒ (x = xP)",
  Module[{alpha, x, xP, expected, c},
    alpha = mkVarType["A"];
    x = mkVar["x", alpha]; xP = mkVar["xP", alpha];
    expected = mkComb[mkComb[
      mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[someTerm[x], someTerm[xP]]],
      mkEq[x, xP]];
    c = concl[someInjThm];
    HOLTest`assertEq[c, expected, "⊢ (SOME x = SOME xP) ⇒ (x = xP)"];
    HOLTest`assertEq[hyp[someInjThm], {}, "no hyps"];
]];

(* ===== disjointness ===== *)

HOLTest`runTests["option: noneNotEqSomeThm is ¬ (NONE = SOME x)",
  Module[{alpha, x, expected, c},
    alpha = mkVarType["A"];
    x = mkVar["x", alpha];
    expected = mkComb[
      mkConst["¬", tyFun[boolTy, boolTy]],
      mkEq[mkConst["NONE", constType["NONE"]], someTerm[x]]];
    c = concl[noneNotEqSomeThm];
    HOLTest`assertEq[c, expected, "⊢ ¬ (NONE = SOME x)"];
    HOLTest`assertEq[hyp[noneNotEqSomeThm], {}, "no hyps"];
]];
