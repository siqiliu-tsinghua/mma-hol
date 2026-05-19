(* ::Package:: *)

(* M7-4-a.1 list tests: type creation + NIL shape. *)

BeginPackage["HOLListTests`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOLTest`",
  "HOL`Stdlib`Num`", "HOL`Stdlib`Option`", "HOL`Stdlib`List`"
}];

Begin["`Private`"];

αTy = mkVarType["A"];
numTy = mkType["num", {}];
optionATy = HOL`Stdlib`Option`optionTy[αTy];
carrierTy = tyFun[numTy, optionATy];
listATy = HOL`Stdlib`List`listTy[αTy];

HOLTest`runTests["stdlib/List: isListP has type (num → α option) → bool",
  Module[{ty},
    ty = HOL`Kernel`constType["isListP"];
    HOLTest`assertEq[ty, tyFun[carrierTy, boolTy],
      "isListP : (num → α option) → bool"];
]];

HOLTest`runTests["stdlib/List: isListPDefThm — concl `isListP = …` with no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`isListPDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["isListP", _]], _]],
      "concl shape ⊢ isListP = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: list type has arity 1",
  HOLTest`assertEq[HOL`Kernel`typeArity["list"], 1, "list has arity 1"];
];

HOLTest`runTests["stdlib/List: ABS_list has type (num → α option) → α list",
  Module[{ty},
    ty = HOL`Kernel`constType["ABS_list"];
    HOLTest`assertEq[ty, tyFun[carrierTy, listATy],
      "ABS_list : (num → α option) → α list"];
]];

HOLTest`runTests["stdlib/List: REP_list has type α list → (num → α option)",
  Module[{ty},
    ty = HOL`Kernel`constType["REP_list"];
    HOLTest`assertEq[ty, tyFun[listATy, carrierTy],
      "REP_list : α list → (num → α option)"];
]];

HOLTest`runTests["stdlib/List: absRepListThm — ⊢ ABS_list (REP_list a) = a, no hyps",
  Module[{c, expected, aV},
    aV = mkVar["a", listATy];
    expected = mkEq[
      mkComb[HOL`Stdlib`List`absListConst[],
        mkComb[HOL`Stdlib`List`repListConst[], aV]],
      aV];
    c = concl[HOL`Stdlib`List`absRepListThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "ABS_list (REP_list a) = a"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`absRepListThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: NIL has type α list",
  Module[{ty},
    ty = HOL`Kernel`constType["NIL"];
    HOLTest`assertEq[ty, listATy, "NIL : α list"];
]];

HOLTest`runTests["stdlib/List: nilDefThm — concl `NIL = ABS_list (λi. NONE)`, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`nilDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["NIL", _]],
              comb[const["ABS_list", _], abs[_, _, _]]]],
      "concl shape ⊢ NIL = ABS_list (λi. NONE)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: repNilThm — ⊢ REP_list NIL = (λi. NONE), no hyps",
  Module[{c, dThm, iV, expected, noneTm},
    dThm = HOL`Stdlib`List`repNilThm;
    c = concl[dThm];
    iV = mkVar["i", numTy];
    noneTm = mkConst["NONE", optionATy];
    expected = mkEq[
      mkComb[HOL`Stdlib`List`repListConst[], HOL`Stdlib`List`nilConst[]],
      mkAbs[iV, noneTm]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "REP_list NIL = (λi. NONE)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-4-a.2 tests: CONS def + helper lemmas ===== *)

HOLTest`runTests["stdlib/List: CONS has type α → α list → α list",
  Module[{ty},
    ty = HOL`Kernel`constType["CONS"];
    HOLTest`assertEq[ty, tyFun[αTy, tyFun[listATy, listATy]],
      "CONS : α → α list → α list"];
]];

HOLTest`runTests["stdlib/List: consDefThm — concl `CONS = …`, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`consDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["CONS", _]], _]],
      "concl shape ⊢ CONS = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: leqSucMonoCancelThm — ⊢ ∀a b. (SUC a ≤ SUC b) = (a ≤ b), no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`leqSucMonoCancelThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _],
        abs[bvar[0, tyApp["num", {}]],
          comb[const["∀", _],
            abs[bvar[0, tyApp["num", {}]],
              comb[comb[const["=", _], _], _], _]], _]]],
      "shape: ∀a. ∀b. (SUC a ≤ SUC b) = (a ≤ b)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: isListPOfRepListThm — ⊢ isListPLambda (REP_list l), no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`isListPOfRepListThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[abs[_, _, "f"],
        comb[const["REP_list", _], var["l", _]]]],
      "shape: (λf. …) (REP_list l) — isListP-lambda applied to REP_list l"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* Smoke test: invoke the consFAt*Thm function helpers and check shape. *)
HOLTest`runTests["stdlib/List: consFAtZeroThm[x, l] — concl `(λi. ε y. …) 0 = SOME x`, no hyps",
  Module[{xV, lV, thm, c},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listATy];
    thm = HOL`Stdlib`List`Private`consFAtZeroThm[xV, lV];
    c = concl[thm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _],
                     comb[const["SOME", _], var["x", _]]]],
      "RHS is SOME x"];
    HOLTest`assertEq[hyp[thm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: consFAtSucThm[x, l, j] — concl `(λi. ε y. …) (SUC j) = REP_list l j`, no hyps",
  Module[{xV, lV, jV, thm, c},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listATy];
    jV = mkVar["j", numTy];
    thm = HOL`Stdlib`List`Private`consFAtSucThm[xV, lV, jV];
    c = concl[thm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _],
                     comb[comb[const["REP_list", _], var["l", _]], var["j", _]]]],
      "RHS is REP_list l j"];
    HOLTest`assertEq[hyp[thm], {}, "no hyps"];
]];

(* ===== M7-4-a.3 tests: repConsHead/Tail + aux ===== *)

HOLTest`runTests["stdlib/List: ltSucMonoCancelThm — ⊢ ∀a b. (SUC a < SUC b) = (a < b), no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`ltSucMonoCancelThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _],
        abs[bvar[0, tyApp["num", {}]],
          comb[const["∀", _],
            abs[bvar[0, tyApp["num", {}]],
              comb[comb[const["=", _], _], _], _]], _]]],
      "shape: ∀a. ∀b. (SUC a < SUC b) = (a < b)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: zeroLtSucThm — ⊢ ∀n. 0 < SUC n, no hyps",
  Module[{c, expected, nV, zeroC, sucC, ltC, forallC},
    nV = mkVar["n", numTy];
    zeroC = mkConst["0", numTy];
    sucC = mkConst["SUC", tyFun[numTy, numTy]];
    ltC = mkConst["<", tyFun[numTy, tyFun[numTy, boolTy]]];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    expected = mkComb[forallC,
      mkAbs[nV, mkComb[mkComb[ltC, zeroC], mkComb[sucC, nV]]]];
    c = concl[HOL`Stdlib`List`zeroLtSucThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀n. 0 < SUC n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`zeroLtSucThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: someNotEqNoneThm — ⊢ ∀x. ¬(SOME x = NONE), no hyps",
  Module[{c, expected, xV, someC, noneC, notC, forallC},
    xV = mkVar["x", αTy];
    someC = mkConst["SOME", tyFun[αTy, optionATy]];
    noneC = mkConst["NONE", optionATy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    forallC = mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]];
    expected = mkComb[forallC,
      mkAbs[xV, mkComb[notC, mkEq[mkComb[someC, xV], noneC]]]];
    c = concl[HOL`Stdlib`List`someNotEqNoneThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀x. ¬(SOME x = NONE)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`someNotEqNoneThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: repConsHeadThm — ⊢ REP_list (CONS x l) 0 = SOME x, no hyps",
  Module[{c, dThm, xV, lV, zeroC, expected,
          someC, repListC, consC},
    dThm = HOL`Stdlib`List`repConsHeadThm;
    c = concl[dThm];
    xV = mkVar["x", αTy];
    lV = mkVar["l", listATy];
    zeroC = mkConst["0", numTy];
    someC = mkConst["SOME", tyFun[αTy, optionATy]];
    repListC = HOL`Stdlib`List`repListConst[];
    consC = HOL`Stdlib`List`consConst[];
    expected = mkEq[
      mkComb[mkComb[repListC, mkComb[mkComb[consC, xV], lV]], zeroC],
      mkComb[someC, xV]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "REP_list (CONS x l) 0 = SOME x"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: repConsTailThm — ⊢ ∀i. REP_list (CONS x l) (SUC i) = REP_list l i, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`repConsTailThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _],
        abs[bvar[0, tyApp["num", {}]],
          comb[comb[const["=", _], _], _], _]]],
      "shape ⊢ ∀i. _ = _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-4-a.4 tests: CONS injectivity + NIL/CONS disjointness ===== *)

HOLTest`runTests["stdlib/List: consInjThm — ⊢ ∀x xP l lP. CONS x l = CONS xP lP ⇒ x = xP ∧ l = lP, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`consInjThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _],
        abs[bvar[0, _],
          comb[const["∀", _],
            abs[bvar[0, _],
              comb[const["∀", _],
                abs[bvar[0, _],
                  comb[const["∀", _],
                    abs[bvar[0, _],
                      comb[comb[const["⇒", _], _], _], _]], _]], _]], _]]],
      "shape: ∀x xP l lP. _ ⇒ _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: nilNotEqConsThm — ⊢ ∀x l. ¬(NIL = CONS x l), no hyps",
  Module[{c, dThm, expected, xV, lV, nilC, consC, notC, forallC},
    dThm = HOL`Stdlib`List`nilNotEqConsThm;
    c = concl[dThm];
    xV = mkVar["x", αTy];
    lV = mkVar["l", listATy];
    nilC = HOL`Stdlib`List`nilConst[];
    consC = HOL`Stdlib`List`consConst[];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    forallC = mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]];
    expected = mkComb[forallC,
      mkAbs[xV, mkComb[mkConst["∀", tyFun[tyFun[listATy, boolTy], boolTy]],
        mkAbs[lV, mkComb[notC,
          mkEq[nilC, mkComb[mkComb[consC, xV], lV]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀x l. ¬(NIL = CONS x l)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-4-a.5 tests: option cases + tail/shift toolkit ===== *)

HOLTest`runTests["stdlib/List: optionCasesThm — ⊢ ∀y. y = NONE ∨ ∃x. y = SOME x, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`optionCasesThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _],
        abs[bvar[0, _],
          comb[comb[const["∨", _], _], _], _]]],
      "shape ⊢ ∀y. _ ∨ _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* Smoke test: invoke notNoneImpliesSome[⊢ ¬(y = NONE)] for a concrete y. *)
HOLTest`runTests["stdlib/List: notNoneImpliesSome smoke test",
  Module[{yV, notNoneTm, thm, c, optionATyLocal},
    optionATyLocal = HOL`Stdlib`Option`optionTy[αTy];
    yV = mkVar["y", optionATyLocal];
    notNoneTm = mkComb[mkConst["¬", tyFun[boolTy, boolTy]],
      mkEq[yV, mkConst["NONE", optionATyLocal]]];
    thm = HOL`Stdlib`List`notNoneImpliesSome[ASSUME[notNoneTm]];
    c = concl[thm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∃", _], abs[bvar[0, _], _, _]]],
      "concl is ∃x. _"];
    HOLTest`assertEq[hyp[thm], {notNoneTm}, "hyp = {¬(y = NONE)}"];
]];

(* Smoke test: invoke consHeadTailEqLThm at a free l with explicit witness hyp. *)
HOLTest`runTests["stdlib/List: consHeadTailEqLThm smoke test",
  Module[{lV, nPrimeV, iV, witTm, witThm, thm, c},
    lV = mkVar["l", listATy];
    nPrimeV = mkVar["nP", numTy];
    iV = mkVar["i", numTy];
    (* witTm = ∀i. (REP_list l i = NONE) ⇔ ¬(i < SUC nP) *)
    witTm = mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[iV, mkEq[
        mkEq[
          mkComb[mkComb[HOL`Stdlib`List`repListConst[], lV], iV],
          mkConst["NONE", HOL`Stdlib`Option`optionTy[αTy]]],
        mkComb[mkConst["¬", tyFun[boolTy, boolTy]],
          mkComb[mkComb[mkConst["<", tyFun[numTy, tyFun[numTy, boolTy]]], iV],
            mkComb[mkConst["SUC", tyFun[numTy, numTy]], nPrimeV]]]]]];
    witThm = ASSUME[witTm];
    thm = HOL`Stdlib`List`consHeadTailEqLThm[lV, nPrimeV, witThm];
    c = concl[thm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _], var["l", _]]],
      "concl is _ = l"];
    HOLTest`assertEq[hyp[thm], {witTm}, "single hyp = witTm"];
]];

(* ===== M7-4-a.6 tests: list induction ===== *)

HOLTest`runTests["stdlib/List: listInductionThm — ⊢ ∀P. P NIL ∧ (∀x l. P l ⇒ P (CONS x l)) ⇒ ∀l. P l, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`listInductionThm;
    c = concl[dThm];
    (* Shape: ∀P. (P NIL ∧ stepHyp) ⇒ (∀l. P l) *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _],
        abs[bvar[0, _],
          comb[comb[const["⇒", _], _], _], _]]],
      "shape: ∀P. _ ⇒ _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

End[];
EndPackage[];
