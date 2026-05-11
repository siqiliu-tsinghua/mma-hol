(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Set`"];

(* ===== const types ===== *)

HOLTest`runTests["set: IN has correct generic type",
  Module[{alpha, setT, expected, ty},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    expected = tyFun[alpha, tyFun[setT, boolTy]];
    ty = constType["IN"];
    HOLTest`assertEq[ty, expected, "IN : A → (A → bool) → bool"];
]];

HOLTest`runTests["set: SUBSET / UNION / INTER / DIFF binary types",
  Module[{alpha, setT, binBool, binSet},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    binBool = tyFun[setT, tyFun[setT, boolTy]];
    binSet  = tyFun[setT, tyFun[setT, setT]];
    HOLTest`assertEq[constType["SUBSET"], binBool, "SUBSET : set → set → bool"];
    HOLTest`assertEq[constType["UNION"],  binSet,  "UNION  : set → set → set"];
    HOLTest`assertEq[constType["INTER"],  binSet,  "INTER  : set → set → set"];
    HOLTest`assertEq[constType["DIFF"],   binSet,  "DIFF   : set → set → set"];
]];

HOLTest`runTests["set: EMPTY / UNIV are set-typed",
  Module[{alpha, setT},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    HOLTest`assertEq[constType["EMPTY"], setT, "EMPTY : set"];
    HOLTest`assertEq[constType["UNIV"],  setT, "UNIV : set"];
]];

(* ===== def thm shapes ===== *)

HOLTest`runTests["set: def thms are equations with no hyps",
  Module[{},
    Scan[
      Function[{pair},
        HOLTest`assertTrue[
          MatchQ[concl[pair[[1]]],
            comb[comb[const["=", _], const[pair[[2]], _]], _]],
          pair[[2]] <> " is a defining equation"];
        HOLTest`assertEq[hyp[pair[[1]]], {},
          pair[[2]] <> " has no hyps"];
      ],
      {{inDefThm, "IN"}, {subsetDefThm, "SUBSET"},
       {unionDefThm, "UNION"}, {interDefThm, "INTER"},
       {diffDefThm, "DIFF"}, {emptyDefThm, "EMPTY"},
       {univDefThm, "UNIV"}}];
]];

(* ===== term builders ===== *)

HOLTest`runTests["set: term builders construct the right comb shapes",
  Module[{alpha, x, A, B, setT},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    x = mkVar["x", alpha];
    A = mkVar["A", setT]; B = mkVar["B", setT];
    HOLTest`assertEq[inTerm[x, A],
      mkComb[mkComb[mkConst["IN", constType["IN"]], x], A],
      "inTerm[x, A] = IN x A"];
    HOLTest`assertEq[unionTerm[A, B],
      mkComb[mkComb[mkConst["UNION", constType["UNION"]], A], B],
      "unionTerm[A, B] = UNION A B"];
    HOLTest`assertEq[interTerm[A, B],
      mkComb[mkComb[mkConst["INTER", constType["INTER"]], A], B],
      "interTerm[A, B] = INTER A B"];
    HOLTest`assertEq[diffTerm[A, B],
      mkComb[mkComb[mkConst["DIFF", constType["DIFF"]], A], B],
      "diffTerm[A, B] = DIFF A B"];
    HOLTest`assertEq[subsetTerm[A, B],
      mkComb[mkComb[mkConst["SUBSET", constType["SUBSET"]], A], B],
      "subsetTerm[A, B] = SUBSET A B"];
]];

(* ===== membership theorems ===== *)

HOLTest`runTests["set: inUnionThm — x ∈ A ∪ B = x ∈ A ∨ x ∈ B",
  Module[{alpha, setT, x, A, B, orC, expected, c},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    x = mkVar["x", alpha];
    A = mkVar["A", setT]; B = mkVar["B", setT];
    orC = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    expected = mkEq[
      inTerm[x, unionTerm[A, B]],
      mkComb[mkComb[orC, inTerm[x, A]], inTerm[x, B]]];
    c = concl[inUnionThm];
    HOLTest`assertEq[c, expected, "⊢ x ∈ A ∪ B = (x ∈ A) ∨ (x ∈ B)"];
    HOLTest`assertEq[hyp[inUnionThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inInterThm — x ∈ A ∩ B = x ∈ A ∧ x ∈ B",
  Module[{alpha, setT, x, A, B, andC, expected, c},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    x = mkVar["x", alpha];
    A = mkVar["A", setT]; B = mkVar["B", setT];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    expected = mkEq[
      inTerm[x, interTerm[A, B]],
      mkComb[mkComb[andC, inTerm[x, A]], inTerm[x, B]]];
    c = concl[inInterThm];
    HOLTest`assertEq[c, expected, "⊢ x ∈ A ∩ B = (x ∈ A) ∧ (x ∈ B)"];
    HOLTest`assertEq[hyp[inInterThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inDiffThm — x ∈ A ∖ B = x ∈ A ∧ ¬ x ∈ B",
  Module[{alpha, setT, x, A, B, andC, notC, expected, c},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    x = mkVar["x", alpha];
    A = mkVar["A", setT]; B = mkVar["B", setT];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    expected = mkEq[
      inTerm[x, diffTerm[A, B]],
      mkComb[mkComb[andC, inTerm[x, A]],
        mkComb[notC, inTerm[x, B]]]];
    c = concl[inDiffThm];
    HOLTest`assertEq[c, expected,
      "⊢ x ∈ A ∖ B = (x ∈ A) ∧ ¬ (x ∈ B)"];
    HOLTest`assertEq[hyp[inDiffThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inEmptyThm — x ∈ EMPTY = F",
  Module[{alpha, x, F, expected, c},
    alpha = mkVarType["A"]; x = mkVar["x", alpha];
    F = mkConst["F", boolTy];
    expected = mkEq[inTerm[x, mkConst["EMPTY", constType["EMPTY"]]], F];
    c = concl[inEmptyThm];
    HOLTest`assertEq[c, expected, "⊢ x ∈ EMPTY = F"];
    HOLTest`assertEq[hyp[inEmptyThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inUnivThm — x ∈ UNIV = T",
  Module[{alpha, x, T, expected, c},
    alpha = mkVarType["A"]; x = mkVar["x", alpha];
    T = mkConst["T", boolTy];
    expected = mkEq[inTerm[x, mkConst["UNIV", constType["UNIV"]]], T];
    c = concl[inUnivThm];
    HOLTest`assertEq[c, expected, "⊢ x ∈ UNIV = T"];
    HOLTest`assertEq[hyp[inUnivThm], {}, "no hyps"];
]];
