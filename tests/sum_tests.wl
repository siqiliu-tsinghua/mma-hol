(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Sum`"];

(* ===== mkInl / mkInr underlying constants ===== *)

HOLTest`runTests["sum: mkInl has correct generic type",
  Module[{alpha, beta, expected, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[alpha,
      tyFun[alpha, tyFun[beta, tyFun[boolTy, boolTy]]]];
    ty = constType["mkInl"];
    HOLTest`assertEq[ty, expected,
      "mkInl : A → A → B → bool → bool"];
]];

HOLTest`runTests["sum: mkInr has correct generic type",
  Module[{alpha, beta, expected, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[beta,
      tyFun[alpha, tyFun[beta, tyFun[boolTy, boolTy]]]];
    ty = constType["mkInr"];
    HOLTest`assertEq[ty, expected,
      "mkInr : B → A → B → bool → bool"];
]];

HOLTest`runTests["sum: mkInlDefThm / mkInrDefThm are equations",
  Module[{},
    HOLTest`assertTrue[
      MatchQ[concl[mkInlDefThm], comb[comb[const["=", _], const["mkInl", _]], _]],
      "mkInl = <lambda>"];
    HOLTest`assertTrue[
      MatchQ[concl[mkInrDefThm], comb[comb[const["=", _], const["mkInr", _]], _]],
      "mkInr = <lambda>"];
]];

(* ===== sum type ===== *)

HOLTest`runTests["sum: sum type has arity 2",
  HOLTest`assertEq[typeArity["sum"], 2,
    "sum[A, B] takes two args"];
];

HOLTest`runTests["sum: sumTy[a, b] structure",
  Module[{alpha, beta, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    ty = sumTy[alpha, beta];
    HOLTest`assertEq[ty, tyApp["sum", {alpha, beta}],
      "sumTy builds tyApp[\"sum\", {α, β}]"];
]];

(* ===== ABS_sum / REP_sum ===== *)

HOLTest`runTests["sum: ABS_sum / REP_sum have correct generic types",
  Module[{alpha, beta, repTy, sumTyAB, expectedAbs, expectedRep},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    repTy = tyFun[alpha, tyFun[beta, tyFun[boolTy, boolTy]]];
    sumTyAB = tyApp["sum", {alpha, beta}];
    expectedAbs = tyFun[repTy, sumTyAB];
    expectedRep = tyFun[sumTyAB, repTy];
    HOLTest`assertEq[constType["ABS_sum"], expectedAbs,
      "ABS_sum : (A → B → bool → bool) → sum[A, B]"];
    HOLTest`assertEq[constType["REP_sum"], expectedRep,
      "REP_sum : sum[A, B] → (A → B → bool → bool)"];
]];

HOLTest`runTests["sum: absRepSumThm is ABS_sum (REP_sum a) = a",
  Module[{c},
    c = concl[absRepSumThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _], _]],
      "concl is an equation"];
    HOLTest`assertTrue[
      MatchQ[c[[1, 2]],
        comb[const["ABS_sum", _], comb[const["REP_sum", _], var["a", _]]]],
      "lhs is ABS_sum (REP_sum a)"];
    HOLTest`assertEq[hyp[absRepSumThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: repAbsSumThm is (isSum r) = (REP_sum (ABS_sum r) = r)",
  Module[{c},
    c = concl[repAbsSumThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _], _]],
      "concl is an equation"];
    HOLTest`assertTrue[
      MatchQ[c[[1, 2]], comb[abs[bvar[0, _], _, _], var["r", _]]],
      "lhs is (predicate) r"];
    HOLTest`assertTrue[
      MatchQ[c[[2]],
        comb[comb[const["=", _],
          comb[const["REP_sum", _], comb[const["ABS_sum", _], var["r", _]]]],
          var["r", _]]],
      "rhs is REP_sum (ABS_sum r) = r"];
]];

(* ===== INL / INR constructors ===== *)

HOLTest`runTests["sum: INL has correct generic type",
  Module[{alpha, beta, expected, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[alpha, tyApp["sum", {alpha, beta}]];
    ty = constType["INL"];
    HOLTest`assertEq[ty, expected,
      "INL : A → sum[A, B]"];
]];

HOLTest`runTests["sum: INR has correct generic type",
  Module[{alpha, beta, expected, ty},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    expected = tyFun[beta, tyApp["sum", {alpha, beta}]];
    ty = constType["INR"];
    HOLTest`assertEq[ty, expected,
      "INR : B → sum[A, B]"];
]];

HOLTest`runTests["sum: inlDefThm / inrDefThm are equations",
  Module[{},
    HOLTest`assertTrue[
      MatchQ[concl[inlDefThm], comb[comb[const["=", _], const["INL", _]], _]],
      "INL = <lambda>"];
    HOLTest`assertTrue[
      MatchQ[concl[inrDefThm], comb[comb[const["=", _], const["INR", _]], _]],
      "INR = <lambda>"];
    HOLTest`assertEq[hyp[inlDefThm], {}, "inlDefThm no hyps"];
    HOLTest`assertEq[hyp[inrDefThm], {}, "inrDefThm no hyps"];
]];

HOLTest`runTests["sum: inlTerm / inrTerm build comb terms",
  Module[{alpha, beta, a, b},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    a = mkVar["a", alpha]; b = mkVar["b", beta];
    HOLTest`assertEq[inlTerm[a],
      mkComb[mkConst["INL", constType["INL"]], a],
      "inlTerm[a] = INL a"];
    HOLTest`assertEq[inrTerm[b],
      mkComb[mkConst["INR", constType["INR"]], b],
      "inrTerm[b] = INR b"];
]];

(* ===== M7-1e: bridges + injectivity + disjointness ===== *)

HOLTest`runTests["sum: isSumWitnessInrThm is (predicate)(mkInr b₀)",
  Module[{c},
    c = concl[isSumWitnessInrThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[abs[bvar[0, _], _, _], comb[const["mkInr", _], var["b0", _]]]],
      "predicate applied to mkInr b₀"];
    HOLTest`assertEq[hyp[isSumWitnessInrThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: repInlThm is REP_sum (INL a) = mkInl a",
  Module[{alpha, beta, a, expectedLhs, expectedRhs, c},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    a = mkVar["a", alpha];
    expectedLhs = mkComb[
      mkConst["REP_sum", constType["REP_sum"]],
      inlTerm[a]];
    expectedRhs = mkComb[
      mkConst["mkInl", constType["mkInl"]], a];
    c = concl[repInlThm];
    HOLTest`assertEq[c, mkEq[expectedLhs, expectedRhs],
      "⊢ REP_sum (INL a) = mkInl a"];
    HOLTest`assertEq[hyp[repInlThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: repInrThm is REP_sum (INR b) = mkInr b",
  Module[{alpha, beta, b, expectedLhs, expectedRhs, c},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    b = mkVar["b", beta];
    expectedLhs = mkComb[
      mkConst["REP_sum", constType["REP_sum"]],
      inrTerm[b]];
    expectedRhs = mkComb[
      mkConst["mkInr", constType["mkInr"]], b];
    c = concl[repInrThm];
    HOLTest`assertEq[c, mkEq[expectedLhs, expectedRhs],
      "⊢ REP_sum (INR b) = mkInr b"];
    HOLTest`assertEq[hyp[repInrThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: mkInlInjThm is (mkInl a = mkInl aP) ⇒ (a = aP)",
  Module[{c, alpha, a, aP, expected},
    alpha = mkVarType["A"];
    a = mkVar["a", alpha]; aP = mkVar["aP", alpha];
    expected = mkComb[mkComb[
      mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[mkComb[mkConst["mkInl", constType["mkInl"]], a],
           mkComb[mkConst["mkInl", constType["mkInl"]], aP]]],
      mkEq[a, aP]];
    c = concl[mkInlInjThm];
    HOLTest`assertEq[c, expected,
      "⊢ (mkInl a = mkInl aP) ⇒ (a = aP)"];
    HOLTest`assertEq[hyp[mkInlInjThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: mkInrInjThm is (mkInr b = mkInr bP) ⇒ (b = bP)",
  Module[{c, beta, b, bP, expected},
    beta = mkVarType["B"];
    b = mkVar["b", beta]; bP = mkVar["bP", beta];
    expected = mkComb[mkComb[
      mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[mkComb[mkConst["mkInr", constType["mkInr"]], b],
           mkComb[mkConst["mkInr", constType["mkInr"]], bP]]],
      mkEq[b, bP]];
    c = concl[mkInrInjThm];
    HOLTest`assertEq[c, expected,
      "⊢ (mkInr b = mkInr bP) ⇒ (b = bP)"];
    HOLTest`assertEq[hyp[mkInrInjThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: inlInjThm is (INL a = INL aP) ⇒ (a = aP)",
  Module[{c, alpha, a, aP, expected},
    alpha = mkVarType["A"];
    a = mkVar["a", alpha]; aP = mkVar["aP", alpha];
    expected = mkComb[mkComb[
      mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[inlTerm[a], inlTerm[aP]]],
      mkEq[a, aP]];
    c = concl[inlInjThm];
    HOLTest`assertEq[c, expected, "⊢ (INL a = INL aP) ⇒ (a = aP)"];
    HOLTest`assertEq[hyp[inlInjThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: inrInjThm is (INR b = INR bP) ⇒ (b = bP)",
  Module[{c, beta, b, bP, expected},
    beta = mkVarType["B"];
    b = mkVar["b", beta]; bP = mkVar["bP", beta];
    expected = mkComb[mkComb[
      mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[inrTerm[b], inrTerm[bP]]],
      mkEq[b, bP]];
    c = concl[inrInjThm];
    HOLTest`assertEq[c, expected, "⊢ (INR b = INR bP) ⇒ (b = bP)"];
    HOLTest`assertEq[hyp[inrInjThm], {}, "no hyps"];
]];

HOLTest`runTests["sum: inlNotEqInrThm is ¬ (INL a = INR b)",
  Module[{c, alpha, beta, a, b, expected},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    a = mkVar["a", alpha]; b = mkVar["b", beta];
    expected = mkComb[
      mkConst["¬", tyFun[boolTy, boolTy]],
      mkEq[inlTerm[a], inrTerm[b]]];
    c = concl[inlNotEqInrThm];
    HOLTest`assertEq[c, expected, "⊢ ¬ (INL a = INR b)"];
    HOLTest`assertEq[hyp[inlNotEqInrThm], {}, "no hyps"];
]];
