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

(* ===== M7-4-b.1 tests: LENGTH ===== *)

HOLTest`runTests["stdlib/List: LENGTH has type α list → num",
  HOLTest`assertEq[HOL`Kernel`constType["LENGTH"], tyFun[listATy, numTy],
    "LENGTH : α list → num"];
];

HOLTest`runTests["stdlib/List: ltExtThm — ⊢ ∀m n. (∀i. ¬(i<m)=¬(i<n)) ⇒ m=n, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`ltExtThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[comb[const["⇒", _], _], _], _]], _]]],
      "shape: ∀m n. _ ⇒ _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: lengthNilThm — ⊢ LENGTH NIL = 0, no hyps",
  Module[{c, dThm, expected},
    dThm = HOL`Stdlib`List`lengthNilThm;
    c = concl[dThm];
    expected = mkEq[
      mkComb[HOL`Stdlib`List`lengthConst[], HOL`Stdlib`List`nilConst[]],
      mkConst["0", numTy]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "LENGTH NIL = 0"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: lengthConsThm — ⊢ ∀x l. LENGTH (CONS x l) = SUC (LENGTH l), no hyps",
  Module[{c, dThm, expected, xV, lV, lenC, consC, sucC},
    dThm = HOL`Stdlib`List`lengthConsThm;
    c = concl[dThm];
    xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    lenC = HOL`Stdlib`List`lengthConst[];
    consC = HOL`Stdlib`List`consConst[];
    sucC = mkConst["SUC", tyFun[numTy, numTy]];
    expected = mkComb[mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]],
      mkAbs[xV, mkComb[mkConst["∀", tyFun[tyFun[listATy, boolTy], boolTy]],
        mkAbs[lV, mkEq[
          mkComb[lenC, mkComb[mkComb[consC, xV], lV]],
          mkComb[sucC, mkComb[lenC, lV]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀x l. LENGTH (CONS x l) = SUC (LENGTH l)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-4-b.2 tests: HD, TL ===== *)

HOLTest`runTests["stdlib/List: HD has type α list → α, TL has type α list → α list",
  (HOLTest`assertEq[HOL`Kernel`constType["HD"], tyFun[listATy, αTy], "HD : α list → α"];
   HOLTest`assertEq[HOL`Kernel`constType["TL"], tyFun[listATy, listATy], "TL : α list → α list"];)
];

HOLTest`runTests["stdlib/List: hdConsThm — ⊢ ∀x l. HD (CONS x l) = x, no hyps",
  Module[{c, dThm, expected, xV, lV, hdC, consC},
    dThm = HOL`Stdlib`List`hdConsThm;
    c = concl[dThm];
    xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    hdC = HOL`Stdlib`List`hdConst[];
    consC = HOL`Stdlib`List`consConst[];
    expected = mkComb[mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]],
      mkAbs[xV, mkComb[mkConst["∀", tyFun[tyFun[listATy, boolTy], boolTy]],
        mkAbs[lV, mkEq[mkComb[hdC, mkComb[mkComb[consC, xV], lV]], xV]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀x l. HD (CONS x l) = x"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: tlConsThm — ⊢ ∀x l. TL (CONS x l) = l, no hyps",
  Module[{c, dThm, expected, xV, lV, tlC, consC},
    dThm = HOL`Stdlib`List`tlConsThm;
    c = concl[dThm];
    xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    tlC = HOL`Stdlib`List`tlConst[];
    consC = HOL`Stdlib`List`consConst[];
    expected = mkComb[mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]],
      mkAbs[xV, mkComb[mkConst["∀", tyFun[tyFun[listATy, boolTy], boolTy]],
        mkAbs[lV, mkEq[mkComb[tlC, mkComb[mkComb[consC, xV], lV]], lV]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀x l. TL (CONS x l) = l"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-4-c.1 tests: list iteration graph toolbox ===== *)

HOLTest`runTests["stdlib/List: LIST_ITER_GRAPH has type β → (α→β→β) → α list → β → bool",
  Module[{ty, βTy, fTy},
    βTy = mkVarType["B"];
    fTy = tyFun[αTy, tyFun[βTy, βTy]];
    ty = HOL`Kernel`constType["LIST_ITER_GRAPH"];
    HOLTest`assertEq[ty,
      tyFun[βTy, tyFun[fTy, tyFun[listATy, tyFun[βTy, boolTy]]]],
      "LIST_ITER_GRAPH : β → (α→β→β) → α list → β → bool"];
]];

HOLTest`runTests["stdlib/List: graphNilThm — ⊢ G NIL e, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`graphNilThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[comb[comb[const["LIST_ITER_GRAPH", _],
        var["e", _]], var["f", _]], const["NIL", _]], var["e", _]]],
      "shape: LIST_ITER_GRAPH e f NIL e"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: graphConsThm — shape ∀x t y. G t y ⇒ G (CONS x t)(f x y), no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`graphConsThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _],
            comb[comb[const["⇒", _], _], _], _]], _]], _]]],
      "shape: ∀x t y. _ ⇒ _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: graphExistsThm — shape ∀l. ∃z. G l z, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`graphExistsThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∃", _], abs[bvar[0, _], _, _]], _]]],
      "shape: ∀l. ∃z. _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: graphNilValThm — shape ∀z. G NIL z ⇒ z = e, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`graphNilValThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], _],
          comb[comb[const["=", _], bvar[0, _]], var["e", _]]], _]]],
      "shape: ∀z. _ ⇒ z = e"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: graphInversionThm — shape ∀x l z. G (CONS x l) z ⇒ ∃y. …, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`graphInversionThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _],
            comb[comb[const["⇒", _], _],
              comb[const["∃", _], abs[bvar[0, _], _, _]]], _]], _]], _]]],
      "shape: ∀x l z. _ ⇒ ∃y. _"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-4-c.2 tests: uniqueness + listIterationThm ===== *)

HOLTest`runTests["stdlib/List: graphUniqueThm — shape ∀l z z'. G l z ⇒ G l z' ⇒ z = z', no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`graphUniqueThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _],
            comb[comb[const["⇒", _], _],
              comb[comb[const["⇒", _], _],
                comb[comb[const["=", _], bvar[1, _]], bvar[0, _]]]], _]], _]], _]]],
      "shape: ∀l z z'. _ ⇒ _ ⇒ z = z'"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: listIterationThm — ⊢ ∀e f. ∃g. g NIL = e ∧ ∀x l. g (CONS x l) = f x (g l), no hyps",
  Module[{c, dThm, βTy},
    βTy = mkVarType["B"];
    dThm = HOL`Stdlib`List`listIterationThm;
    c = concl[dThm];
    (* ∀e. ∀f. ∃g. (g NIL = e) ∧ (∀x l. ...) *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∃", _], abs[bvar[0, _],
            comb[comb[const["∧", _],
              comb[comb[const["=", _], comb[bvar[0, _], const["NIL", _]]], _]],
              comb[const["∀", _], _]], _]], _]], _]]],
      "shape: ∀e f. ∃g. (g NIL = e) ∧ ∀x l. …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-4-d tests: FOLDR / APPEND / MAP / FILTER / FOLDL ===== *)

forallAt[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
consAtTy[ty_] := mkConst["CONS",
  tyFun[ty, tyFun[HOL`Stdlib`List`listTy[ty], HOL`Stdlib`List`listTy[ty]]]];
nilAtTy[ty_]  := mkConst["NIL", HOL`Stdlib`List`listTy[ty]];
ap2[f_, x_, y_] := mkComb[mkComb[f, x], y];

HOLTest`runTests["stdlib/List: foldrNilThm / foldrConsThm",
  Module[{βTy, fTy, fV, eV, xV, lV, foldrC, consC, nilC, expN, expC},
    βTy = mkVarType["B"]; fTy = tyFun[αTy, tyFun[βTy, βTy]];
    fV = mkVar["f", fTy]; eV = mkVar["e", βTy];
    xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    foldrC = HOL`Stdlib`List`foldrConst[];
    consC = HOL`Stdlib`List`consConst[]; nilC = HOL`Stdlib`List`nilConst[];
    expN = mkComb[forallAt[fTy], mkAbs[fV, mkComb[forallAt[βTy], mkAbs[eV,
      mkEq[mkComb[ap2[foldrC, fV, eV], nilC], eV]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`foldrNilThm], expN],
      "∀f e. FOLDR f e NIL = e"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`foldrNilThm], {}, "foldrNil no hyps"];
    expC = mkComb[forallAt[fTy], mkAbs[fV, mkComb[forallAt[βTy], mkAbs[eV,
      mkComb[forallAt[αTy], mkAbs[xV, mkComb[forallAt[listATy], mkAbs[lV,
        mkEq[
          mkComb[ap2[foldrC, fV, eV], ap2[consC, xV, lV]],
          ap2[fV, xV, mkComb[ap2[foldrC, fV, eV], lV]]]]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`foldrConsThm], expC],
      "∀f e x l. FOLDR f e (CONS x l) = f x (FOLDR f e l)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`foldrConsThm], {}, "foldrCons no hyps"];
]];

HOLTest`runTests["stdlib/List: appendNilThm / appendConsThm",
  Module[{xV, l1V, l2V, appC, consC, nilC, expN, expC},
    xV = mkVar["x", αTy];
    l1V = mkVar["l1", listATy]; l2V = mkVar["l2", listATy];
    appC = HOL`Stdlib`List`appendConst[];
    consC = HOL`Stdlib`List`consConst[]; nilC = HOL`Stdlib`List`nilConst[];
    expN = mkComb[forallAt[listATy], mkAbs[l2V,
      mkEq[ap2[appC, nilC, l2V], l2V]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`appendNilThm], expN],
      "∀l. APPEND NIL l = l"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`appendNilThm], {}, "appendNil no hyps"];
    expC = mkComb[forallAt[αTy], mkAbs[xV, mkComb[forallAt[listATy], mkAbs[l1V,
      mkComb[forallAt[listATy], mkAbs[l2V,
        mkEq[ap2[appC, ap2[consC, xV, l1V], l2V],
             ap2[consC, xV, ap2[appC, l1V, l2V]]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`appendConsThm], expC],
      "∀x l1 l2. APPEND (CONS x l1) l2 = CONS x (APPEND l1 l2)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`appendConsThm], {}, "appendCons no hyps"];
]];

HOLTest`runTests["stdlib/List: mapNilThm / mapConsThm",
  Module[{βTy, listBTy, hTy, hV, xV, lV, mapC, consA, nilA, consB, nilB,
          expN, expC},
    βTy = mkVarType["B"]; listBTy = listTy[βTy]; hTy = tyFun[αTy, βTy];
    hV = mkVar["h", hTy]; xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    mapC = HOL`Stdlib`List`mapConst[];
    consA = HOL`Stdlib`List`consConst[]; nilA = HOL`Stdlib`List`nilConst[];
    consB = consAtTy[βTy]; nilB = nilAtTy[βTy];
    expN = mkComb[forallAt[hTy], mkAbs[hV,
      mkEq[ap2[mapC, hV, nilA], nilB]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`mapNilThm], expN],
      "∀h. MAP h NIL = NIL"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`mapNilThm], {}, "mapNil no hyps"];
    expC = mkComb[forallAt[hTy], mkAbs[hV, mkComb[forallAt[αTy], mkAbs[xV,
      mkComb[forallAt[listATy], mkAbs[lV,
        mkEq[ap2[mapC, hV, ap2[consA, xV, lV]],
             ap2[consB, mkComb[hV, xV], ap2[mapC, hV, lV]]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`mapConsThm], expC],
      "∀h x l. MAP h (CONS x l) = CONS (h x) (MAP h l)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`mapConsThm], {}, "mapCons no hyps"];
]];

HOLTest`runTests["stdlib/List: filterNilThm / filterConsThm",
  Module[{pTy, pV, xV, lV, filC, consC, nilC, condC, px, recCall, expN, expC},
    pTy = tyFun[αTy, boolTy];
    pV = mkVar["p", pTy]; xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    filC = HOL`Stdlib`List`filterConst[];
    consC = HOL`Stdlib`List`consConst[]; nilC = HOL`Stdlib`List`nilConst[];
    condC = HOL`Bool`condConst[listATy];
    px = mkComb[pV, xV]; recCall = ap2[filC, pV, lV];
    expN = mkComb[forallAt[pTy], mkAbs[pV,
      mkEq[ap2[filC, pV, nilC], nilC]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`filterNilThm], expN],
      "∀p. FILTER p NIL = NIL"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`filterNilThm], {}, "filterNil no hyps"];
    expC = mkComb[forallAt[pTy], mkAbs[pV, mkComb[forallAt[αTy], mkAbs[xV,
      mkComb[forallAt[listATy], mkAbs[lV,
        mkEq[ap2[filC, pV, ap2[consC, xV, lV]],
             ap2[mkComb[condC, px], ap2[consC, xV, recCall], recCall]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`filterConsThm], expC],
      "∀p x l. FILTER p (CONS x l) = COND (p x) (CONS x (FILTER p l)) (FILTER p l)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`filterConsThm], {}, "filterCons no hyps"];
]];

HOLTest`runTests["stdlib/List: foldlNilThm / foldlConsThm",
  Module[{βTy, fTy, fV, eV, xV, lV, foldlC, consC, nilC, expN, expC},
    βTy = mkVarType["B"]; fTy = tyFun[βTy, tyFun[αTy, βTy]];
    fV = mkVar["f", fTy]; eV = mkVar["e", βTy];
    xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    foldlC = HOL`Stdlib`List`foldlConst[];
    consC = HOL`Stdlib`List`consConst[]; nilC = HOL`Stdlib`List`nilConst[];
    expN = mkComb[forallAt[fTy], mkAbs[fV, mkComb[forallAt[βTy], mkAbs[eV,
      mkEq[mkComb[ap2[foldlC, fV, eV], nilC], eV]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`foldlNilThm], expN],
      "∀f e. FOLDL f e NIL = e"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`foldlNilThm], {}, "foldlNil no hyps"];
    expC = mkComb[forallAt[fTy], mkAbs[fV, mkComb[forallAt[βTy], mkAbs[eV,
      mkComb[forallAt[αTy], mkAbs[xV, mkComb[forallAt[listATy], mkAbs[lV,
        mkEq[
          mkComb[ap2[foldlC, fV, eV], ap2[consC, xV, lV]],
          mkComb[ap2[foldlC, fV, ap2[fV, eV, xV]], lV]]]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`foldlConsThm], expC],
      "∀f e x l. FOLDL f e (CONS x l) = FOLDL f (f e x) l"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`foldlConsThm], {}, "foldlCons no hyps"];
]];

HOLTest`runTests["stdlib/List: allNilThm / allConsThm",
  Module[{pTy, pV, xV, lV, allC, consC, nilC, andC, px, recCall,
          expN, expC},
    pTy = tyFun[αTy, boolTy];
    pV = mkVar["p", pTy]; xV = mkVar["x", αTy]; lV = mkVar["l", listATy];
    allC = HOL`Stdlib`List`allConst[];
    consC = HOL`Stdlib`List`consConst[]; nilC = HOL`Stdlib`List`nilConst[];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    px = mkComb[pV, xV]; recCall = ap2[allC, pV, lV];
    expN = mkComb[forallAt[pTy], mkAbs[pV,
      mkEq[ap2[allC, pV, nilC], mkConst["T", boolTy]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`allNilThm], expN],
      "∀p. ALL p NIL = T"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`allNilThm], {}, "allNil no hyps"];
    expC = mkComb[forallAt[pTy], mkAbs[pV, mkComb[forallAt[αTy], mkAbs[xV,
      mkComb[forallAt[listATy], mkAbs[lV,
        mkEq[ap2[allC, pV, ap2[consC, xV, lV]],
             ap2[andC, px, recCall]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`allConsThm], expC],
      "∀p x l. ALL p (CONS x l) = p x ∧ ALL p l"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`allConsThm], {}, "allCons no hyps"];
]];

HOLTest`runTests["stdlib/List: memNilThm / memConsThm",
  Module[{xV, yV, lV, memC, consC, nilC, orC, expN, expC},
    xV = mkVar["x", αTy]; yV = mkVar["y", αTy]; lV = mkVar["l", listATy];
    memC = HOL`Stdlib`List`memConst[];
    consC = HOL`Stdlib`List`consConst[]; nilC = HOL`Stdlib`List`nilConst[];
    orC = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    expN = mkComb[forallAt[αTy], mkAbs[xV,
      mkEq[ap2[memC, xV, nilC], mkConst["F", boolTy]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`memNilThm], expN],
      "∀x. MEM x NIL = F"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`memNilThm], {}, "memNil no hyps"];
    expC = mkComb[forallAt[αTy], mkAbs[xV, mkComb[forallAt[αTy], mkAbs[yV,
      mkComb[forallAt[listATy], mkAbs[lV,
        mkEq[ap2[memC, xV, ap2[consC, yV, lV]],
             ap2[orC, mkEq[xV, yV], ap2[memC, xV, lV]]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`memConsThm], expC],
      "∀x y l. MEM x (CONS y l) = (x = y ∨ MEM x l)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`memConsThm], {}, "memCons no hyps"];
]];

HOLTest`runTests["stdlib/List: foldrAppendThm / allAppendThm",
  Module[{βTy, fTy, fV, eV, l1V, l2V, foldrC, appendC, allC, andC,
          pTy, pV, expFoldrAppend, expAllAppend},
    βTy = mkVarType["B"]; fTy = tyFun[αTy, tyFun[βTy, βTy]];
    fV = mkVar["f", fTy]; eV = mkVar["e", βTy];
    l1V = mkVar["l1", listATy]; l2V = mkVar["l2", listATy];
    foldrC = HOL`Stdlib`List`foldrConst[];
    appendC = HOL`Stdlib`List`appendConst[];
    allC = HOL`Stdlib`List`allConst[];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    pTy = tyFun[αTy, boolTy]; pV = mkVar["p", pTy];

    expFoldrAppend = mkComb[forallAt[fTy], mkAbs[fV,
      mkComb[forallAt[βTy], mkAbs[eV,
        mkComb[forallAt[listATy], mkAbs[l1V,
          mkComb[forallAt[listATy], mkAbs[l2V,
            mkEq[
              mkComb[ap2[foldrC, fV, eV], ap2[appendC, l1V, l2V]],
              mkComb[ap2[foldrC, fV, mkComb[ap2[foldrC, fV, eV], l2V]], l1V]
            ]]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`foldrAppendThm],
      expFoldrAppend],
      "∀f e l1 l2. FOLDR f e (APPEND l1 l2) = FOLDR f (FOLDR f e l2) l1"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`foldrAppendThm], {},
      "foldrAppend no hyps"];

    expAllAppend = mkComb[forallAt[pTy], mkAbs[pV,
      mkComb[forallAt[listATy], mkAbs[l1V,
        mkComb[forallAt[listATy], mkAbs[l2V,
          mkEq[
            ap2[allC, pV, ap2[appendC, l1V, l2V]],
            ap2[andC, ap2[allC, pV, l1V], ap2[allC, pV, l2V]]
          ]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[HOL`Stdlib`List`allAppendThm],
      expAllAppend],
      "∀p l1 l2. ALL p (APPEND l1 l2) = ALL p l1 ∧ ALL p l2"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`allAppendThm], {},
      "allAppend no hyps"];
]];

End[];
EndPackage[];
