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

(* ===== SUBSET theorems ===== *)

HOLTest`runTests["set: subsetReflThm — A ⊆ A",
  Module[{alpha, setT, A, expected, c},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    A = mkVar["A", setT];
    expected = subsetTerm[A, A];
    c = concl[subsetReflThm];
    HOLTest`assertEq[c, expected, "⊢ A ⊆ A"];
    HOLTest`assertEq[hyp[subsetReflThm], {}, "no hyps"];
]];

HOLTest`runTests["set: subsetTransThm — A ⊆ B ⇒ B ⊆ C ⇒ A ⊆ C",
  Module[{alpha, setT, A, B, C, impC, expected, c},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    A = mkVar["A", setT]; B = mkVar["B", setT]; C = mkVar["C", setT];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    expected = mkComb[mkComb[impC, subsetTerm[A, B]],
      mkComb[mkComb[impC, subsetTerm[B, C]], subsetTerm[A, C]]];
    c = concl[subsetTransThm];
    HOLTest`assertEq[c, expected,
      "⊢ A ⊆ B ⇒ B ⊆ C ⇒ A ⊆ C"];
    HOLTest`assertEq[hyp[subsetTransThm], {}, "no hyps"];
]];

HOLTest`runTests["set: unionSubsetLeftThm / unionSubsetRightThm",
  Module[{alpha, setT, A, B, leftExpected, rightExpected},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    A = mkVar["A", setT]; B = mkVar["B", setT];
    leftExpected  = subsetTerm[A, unionTerm[A, B]];
    rightExpected = subsetTerm[B, unionTerm[A, B]];
    HOLTest`assertEq[concl[unionSubsetLeftThm],  leftExpected,
      "⊢ A ⊆ A ∪ B"];
    HOLTest`assertEq[concl[unionSubsetRightThm], rightExpected,
      "⊢ B ⊆ A ∪ B"];
    HOLTest`assertEq[hyp[unionSubsetLeftThm], {}, "left no hyps"];
    HOLTest`assertEq[hyp[unionSubsetRightThm], {}, "right no hyps"];
]];

HOLTest`runTests["set: interSubsetLeftThm / interSubsetRightThm",
  Module[{alpha, setT, A, B, leftExpected, rightExpected},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    A = mkVar["A", setT]; B = mkVar["B", setT];
    leftExpected  = subsetTerm[interTerm[A, B], A];
    rightExpected = subsetTerm[interTerm[A, B], B];
    HOLTest`assertEq[concl[interSubsetLeftThm],  leftExpected,
      "⊢ A ∩ B ⊆ A"];
    HOLTest`assertEq[concl[interSubsetRightThm], rightExpected,
      "⊢ A ∩ B ⊆ B"];
    HOLTest`assertEq[hyp[interSubsetLeftThm], {}, "left no hyps"];
    HOLTest`assertEq[hyp[interSubsetRightThm], {}, "right no hyps"];
]];

HOLTest`runTests["set: emptySubsetThm — EMPTY ⊆ A",
  Module[{alpha, setT, A, expected},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    A = mkVar["A", setT];
    expected = subsetTerm[mkConst["EMPTY", constType["EMPTY"]], A];
    HOLTest`assertEq[concl[emptySubsetThm], expected, "⊢ EMPTY ⊆ A"];
    HOLTest`assertEq[hyp[emptySubsetThm], {}, "no hyps"];
]];

HOLTest`runTests["set: subsetUnivThm — A ⊆ UNIV",
  Module[{alpha, setT, A, expected},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    A = mkVar["A", setT];
    expected = subsetTerm[A, mkConst["UNIV", constType["UNIV"]]];
    HOLTest`assertEq[concl[subsetUnivThm], expected, "⊢ A ⊆ UNIV"];
    HOLTest`assertEq[hyp[subsetUnivThm], {}, "no hyps"];
]];

(* ===== POW / IMAGE / PREIMAGE: types + def thms ===== *)

HOLTest`runTests["set: POW / IMAGE / PREIMAGE have correct generic types",
  Module[{alpha, beta, setT, setB, powTyExpect, imageTyExpect, preimageTyExpect},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    setT = tyFun[alpha, boolTy]; setB = tyFun[beta, boolTy];
    powTyExpect      = tyFun[setT, tyFun[setT, boolTy]];
    imageTyExpect    = tyFun[tyFun[alpha, beta], tyFun[setT, setB]];
    preimageTyExpect = tyFun[tyFun[alpha, beta], tyFun[setB, setT]];
    HOLTest`assertEq[constType["POW"], powTyExpect,
      "POW : set → (set → bool)"];
    HOLTest`assertEq[constType["IMAGE"], imageTyExpect,
      "IMAGE : (α → β) → α-set → β-set"];
    HOLTest`assertEq[constType["PREIMAGE"], preimageTyExpect,
      "PREIMAGE : (α → β) → β-set → α-set"];
]];

HOLTest`runTests["set: def thms for POW / IMAGE / PREIMAGE",
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
      {{powDefThm, "POW"}, {imageDefThm, "IMAGE"},
       {preimageDefThm, "PREIMAGE"}}];
]];

(* ===== POW / IMAGE / PREIMAGE: term builders ===== *)

HOLTest`runTests["set: term builders for POW / IMAGE / PREIMAGE",
  Module[{alpha, beta, setT, setB, f, S, T},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    setT = tyFun[alpha, boolTy]; setB = tyFun[beta, boolTy];
    f = mkVar["f", tyFun[alpha, beta]];
    S = mkVar["S", setT]; T = mkVar["T", setB];
    HOLTest`assertEq[powTerm[S],
      mkComb[mkConst["POW", constType["POW"]], S],
      "powTerm[S] = POW S"];
    HOLTest`assertEq[imageTerm[f, S],
      mkComb[mkComb[mkConst["IMAGE", constType["IMAGE"]], f], S],
      "imageTerm[f, S] = IMAGE f S"];
    HOLTest`assertEq[preimageTerm[f, T],
      mkComb[mkComb[mkConst["PREIMAGE", constType["PREIMAGE"]], f], T],
      "preimageTerm[f, T] = PREIMAGE f T"];
]];

(* ===== Membership theorems ===== *)

HOLTest`runTests["set: inPowThm — T ∈ POW S = T ⊆ S",
  Module[{alpha, setT, S, T, expected},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT]; T = mkVar["T", setT];
    expected = mkEq[inTerm[T, powTerm[S]], subsetTerm[T, S]];
    HOLTest`assertEq[concl[inPowThm], expected,
      "⊢ T ∈ POW S = T ⊆ S"];
    HOLTest`assertEq[hyp[inPowThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inImageThm — y ∈ IMAGE f S = ∃x. x ∈ S ∧ y = f x",
  Module[{alpha, beta, setT, f, S, y, x, andCop, expected},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    setT = tyFun[alpha, boolTy];
    f = mkVar["f", tyFun[alpha, beta]];
    S = mkVar["S", setT];
    y = mkVar["y", beta]; x = mkVar["x", alpha];
    andCop = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    expected = mkEq[
      inTerm[y, imageTerm[f, S]],
      mkComb[
        mkConst["∃", tyFun[tyFun[alpha, boolTy], boolTy]],
        mkAbs[x,
          mkComb[mkComb[andCop, inTerm[x, S]],
            mkEq[y, mkComb[f, x]]]]]];
    HOLTest`assertEq[concl[inImageThm], expected,
      "⊢ y ∈ IMAGE f S = ∃x. x ∈ S ∧ y = f x"];
    HOLTest`assertEq[hyp[inImageThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inPreimageThm — x ∈ PREIMAGE f T = f x ∈ T",
  Module[{alpha, beta, setB, f, T, x, expected},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    setB = tyFun[beta, boolTy];
    f = mkVar["f", tyFun[alpha, beta]];
    T = mkVar["T", setB]; x = mkVar["x", alpha];
    expected = mkEq[
      inTerm[x, preimageTerm[f, T]],
      inTerm[mkComb[f, x], T]];
    HOLTest`assertEq[concl[inPreimageThm], expected,
      "⊢ x ∈ PREIMAGE f T = f x ∈ T"];
    HOLTest`assertEq[hyp[inPreimageThm], {}, "no hyps"];
]];

(* ===== M7-2-d: bounded quantifiers + COMPOSE / I + INJ/SURJ/BIJ ===== *)

HOLTest`runTests["set: BALL / BEX have correct generic types",
  Module[{alpha, setT, predT, expectedTy},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    predT = tyFun[alpha, boolTy];
    expectedTy = tyFun[setT, tyFun[predT, boolTy]];
    HOLTest`assertEq[constType["BALL"], expectedTy,
      "BALL : set → (α → bool) → bool"];
    HOLTest`assertEq[constType["BEX"], expectedTy,
      "BEX : set → (α → bool) → bool"];
]];

HOLTest`runTests["set: ballDefThm / bexDefThm are equations",
  Module[{},
    Scan[
      Function[{pair},
        HOLTest`assertTrue[
          MatchQ[concl[pair[[1]]],
            comb[comb[const["=", _], const[pair[[2]], _]], _]],
          pair[[2]] <> " = <lambda>"];
        HOLTest`assertEq[hyp[pair[[1]]], {},
          pair[[2]] <> " no hyps"];
      ],
      {{ballDefThm, "BALL"}, {bexDefThm, "BEX"}}];
]];

HOLTest`runTests["set: ballTerm / bexTerm builders",
  Module[{alpha, setT, predT, S, P},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy]; predT = setT;
    S = mkVar["S", setT]; P = mkVar["P", predT];
    HOLTest`assertEq[ballTerm[S, P],
      mkComb[mkComb[mkConst["BALL", constType["BALL"]], S], P],
      "ballTerm[S, P] = BALL S P"];
    HOLTest`assertEq[bexTerm[S, P],
      mkComb[mkComb[mkConst["BEX", constType["BEX"]], S], P],
      "bexTerm[S, P] = BEX S P"];
]];

(* ===== I and COMPOSE ===== *)

HOLTest`runTests["set: I has type α → α; COMPOSE has the right shape",
  Module[{alpha, beta, gamma, idTyExpect, composeTyExpect},
    alpha = mkVarType["A"]; beta = mkVarType["B"]; gamma = mkVarType["C"];
    idTyExpect = tyFun[alpha, alpha];
    composeTyExpect = tyFun[tyFun[beta, gamma],
      tyFun[tyFun[alpha, beta], tyFun[alpha, gamma]]];
    HOLTest`assertEq[constType["I"], idTyExpect, "I : A → A"];
    HOLTest`assertEq[constType["COMPOSE"], composeTyExpect,
      "COMPOSE : (B → C) → (A → B) → (A → C)"];
]];

HOLTest`runTests["set: idApplyThm — I x = x",
  Module[{alpha, x, expected},
    alpha = mkVarType["A"]; x = mkVar["x", alpha];
    expected = mkEq[mkComb[mkConst["I", constType["I"]], x], x];
    HOLTest`assertEq[concl[idApplyThm], expected, "⊢ I x = x"];
    HOLTest`assertEq[hyp[idApplyThm], {}, "no hyps"];
]];

HOLTest`runTests["set: composeApplyThm — COMPOSE f g x = f (g x)",
  Module[{alpha, beta, gamma, f, g, x, expected},
    alpha = mkVarType["A"]; beta = mkVarType["B"]; gamma = mkVarType["C"];
    f = mkVar["f", tyFun[beta, gamma]];
    g = mkVar["g", tyFun[alpha, beta]];
    x = mkVar["x", alpha];
    expected = mkEq[
      mkComb[mkComb[mkComb[mkConst["COMPOSE", constType["COMPOSE"]], f], g], x],
      mkComb[f, mkComb[g, x]]];
    HOLTest`assertEq[concl[composeApplyThm], expected,
      "⊢ COMPOSE f g x = f (g x)"];
    HOLTest`assertEq[hyp[composeApplyThm], {}, "no hyps"];
]];

(* ===== INJ / SURJ / BIJ ===== *)

HOLTest`runTests["set: INJ / SURJ / BIJ have correct generic types",
  Module[{alpha, beta, setT, setB, expectedTy},
    alpha = mkVarType["A"]; beta = mkVarType["B"];
    setT = tyFun[alpha, boolTy]; setB = tyFun[beta, boolTy];
    expectedTy = tyFun[tyFun[alpha, beta],
      tyFun[setT, tyFun[setB, boolTy]]];
    HOLTest`assertEq[constType["INJ"], expectedTy,
      "INJ : (α → β) → α-set → β-set → bool"];
    HOLTest`assertEq[constType["SURJ"], expectedTy, "SURJ same shape"];
    HOLTest`assertEq[constType["BIJ"], expectedTy, "BIJ same shape"];
]];

HOLTest`runTests["set: INJ / SURJ / BIJ def thms are equations",
  Module[{},
    Scan[
      Function[{pair},
        HOLTest`assertTrue[
          MatchQ[concl[pair[[1]]],
            comb[comb[const["=", _], const[pair[[2]], _]], _]],
          pair[[2]] <> " = <lambda>"];
        HOLTest`assertEq[hyp[pair[[1]]], {},
          pair[[2]] <> " no hyps"];
      ],
      {{injDefThm, "INJ"}, {surjDefThm, "SURJ"}, {bijDefThm, "BIJ"}}];
]];

(* ===== INSERT / SING / DELETE ===== *)

HOLTest`runTests["set: inInsertThm — y ∈ (x INSERT S) = (y = x) ∨ y ∈ S",
  Module[{alpha, setT, x, y, S, orC, expected},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    x = mkVar["x", alpha]; y = mkVar["y", alpha]; S = mkVar["S", setT];
    orC = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    expected = mkEq[
      inTerm[y, insertTerm[x, S]],
      mkComb[mkComb[orC, mkEq[y, x]], inTerm[y, S]]];
    HOLTest`assertEq[concl[inInsertThm], expected,
      "⊢ y ∈ (x INSERT S) = (y = x) ∨ (y ∈ S)"];
    HOLTest`assertEq[hyp[inInsertThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inSingThm — y ∈ SING x = (y = x)",
  Module[{alpha, x, y, expected},
    alpha = mkVarType["A"];
    x = mkVar["x", alpha]; y = mkVar["y", alpha];
    expected = mkEq[inTerm[y, singTerm[x]], mkEq[y, x]];
    HOLTest`assertEq[concl[inSingThm], expected, "⊢ y ∈ SING x = (y = x)"];
    HOLTest`assertEq[hyp[inSingThm], {}, "no hyps"];
]];

HOLTest`runTests["set: inDeleteThm — y ∈ DELETE S x = y ∈ S ∧ ¬(y = x)",
  Module[{alpha, setT, x, y, S, andC, notC, expected},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    x = mkVar["x", alpha]; y = mkVar["y", alpha]; S = mkVar["S", setT];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    expected = mkEq[
      inTerm[y, deleteTerm[S, x]],
      mkComb[mkComb[andC, inTerm[y, S]], mkComb[notC, mkEq[y, x]]]];
    HOLTest`assertEq[concl[inDeleteThm], expected,
      "⊢ y ∈ DELETE S x = (y ∈ S) ∧ ¬ (y = x)"];
    HOLTest`assertEq[hyp[inDeleteThm], {}, "no hyps"];
]];
