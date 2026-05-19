(* ::Package:: *)

(* M7-4-a.{1,2,3,4,5} stdlib/List — list type, NIL, CONS, induction prep.

   Encode α list as the subtype of carrier `num → α option` whose elements
   are supported on an initial segment [0, n):

     isListP f  ⇔  ∃n. ∀i. (f i = NONE) ⇔ ¬ (i < n)

   newBasicTypeDefinition carves out `α list` with ABS_list / REP_list.

   NIL = ABS_list (λi. NONE) — the unique list of length 0.

   CONS x l = ABS_list (λi. ε y. (i = 0 ⇒ y = SOME x) ∧
                                  (∀j. i = SUC j ⇒ y = REP_list l j))
   — head at position 0, tail at SUC.

   Round-trip theorems (M7-4-a.3):
     repConsHeadThm: ⊢ REP_list (CONS x l) 0 = SOME x
     repConsTailThm: ⊢ ∀i. REP_list (CONS x l) (SUC i) = REP_list l i

   Peano-like theorems (M7-4-a.4):
     consInjThm:      ⊢ ∀x xP l lP. CONS x l = CONS xP lP ⇒ x = xP ∧ l = lP
     nilNotEqConsThm: ⊢ ∀x l. ¬(NIL = CONS x l)

   Induction-prep toolkit (M7-4-a.5):
     optionCasesThm:        ⊢ ∀y. y = NONE ∨ ∃x. y = SOME x
     notNoneImpliesSome:    helper from ¬(y = NONE) to ∃x. y = SOME x
     shiftedFn[l]:          term `λj. REP_list l (SUC j)`
     tailFnOf[l]:           term `ABS_list (shiftedFn[l])`
     headTermOf[l]:         term `ε x. REP_list l 0 = SOME x`
     shiftedIsListPThm:     witHyp-driven proof that shiftedFn[l] has
                            length n' when l has length SUC n'
     repTailEqShiftedThm:   ⊢ REP_list (tailFnOf l) = shiftedFn[l]
     tailLengthThm:         IH-ready length-n' witness for tailFnOf l
     consHeadTailEqLThm:    ⊢ CONS (headTermOf l) (tailFnOf l) = l

   List induction defers to M7-4-a.6. *)

BeginPackage["HOL`Stdlib`List`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`",
  "HOL`Stdlib`Num`", "HOL`Stdlib`Option`"
}];

isListPConst::usage    = "isListPConst[] — isListP : (num → α option) → bool. Carrier predicate carving out finitely-supported sequences.";
isListPDefThm::usage   = "isListPDefThm — ⊢ isListP = (λf. ∃n. ∀i. (f i = NONE) ⇔ ¬ (i < n)).";

isListPLambdaTerm::usage  = "isListPLambdaTerm[] — closed λ-term for the carrier predicate.";
isListPWitnessThm::usage  = "isListPWitnessThm — ⊢ isListPLambda (λi. NONE); the DISJ1-style witness via n = 0.";

listTy::usage = "listTy[a] — list type tyApp[\"list\", {a}].";

absListConst::usage = "absListConst[] — ABS_list : (num → α option) → α list.";
repListConst::usage = "repListConst[] — REP_list : α list → (num → α option).";

absRepListThm::usage = "absRepListThm — ⊢ ABS_list (REP_list l) = l (round-trip on list).";
repAbsListThm::usage = "repAbsListThm — ⊢ isListPLambda r = (REP_list (ABS_list r) = r).";

nilConst::usage  = "nilConst[] — NIL : α list. The empty list.";
nilDefThm::usage = "nilDefThm — ⊢ NIL = ABS_list (λi. NONE).";

repNilThm::usage = "repNilThm — ⊢ REP_list NIL = (λi. NONE).";

consConst::usage    = "consConst[] — CONS : α → α list → α list.";
consDefThm::usage   = "consDefThm — ⊢ CONS = (λx l. ABS_list (λi. ε y. (i = 0 ⇒ y = SOME x) ∧ (∀j. i = SUC j ⇒ y = REP_list l j))).";

leqSucMonoCancelThm::usage =
  "leqSucMonoCancelThm — ⊢ ∀a b. (SUC a ≤ SUC b) = (a ≤ b). Auxiliary num lemma needed for the upcoming isListP-for-CONS proof.";
isListPOfRepListThm::usage =
  "isListPOfRepListThm — ⊢ isListPLambda (REP_list l). REP_list always lands in the isListP carrier subset (via absRepListThm + repAbsListThm round-trip).";

ltSucMonoCancelThm::usage =
  "ltSucMonoCancelThm — ⊢ ∀a b. (SUC a < SUC b) = (a < b). Derived from leqSucMonoCancel via ltDefThm.";
zeroLtSucThm::usage =
  "zeroLtSucThm — ⊢ ∀n. 0 < SUC n.";
someNotEqNoneThm::usage =
  "someNotEqNoneThm — ⊢ ∀x. ¬(SOME x = NONE). Symmetric form of Option's noneNotEqSomeThm.";

repConsHeadThm::usage =
  "repConsHeadThm — ⊢ REP_list (CONS x l) 0 = SOME x.";
repConsTailThm::usage =
  "repConsTailThm — ⊢ ∀i. REP_list (CONS x l) (SUC i) = REP_list l i.";

consInjThm::usage =
  "consInjThm — ⊢ ∀x xP l lP. CONS x l = CONS xP lP ⇒ x = xP ∧ l = lP.";
nilNotEqConsThm::usage =
  "nilNotEqConsThm — ⊢ ∀x l. ¬ (NIL = CONS x l).";

optionCasesThm::usage =
  "optionCasesThm — ⊢ ∀y. y = NONE ∨ ∃x. y = SOME x. Option case analysis via isOption REP-roundtrip + bridges.";
notNoneImpliesSome::usage =
  "notNoneImpliesSome[thNotNone] — from Γ ⊢ ¬(y = NONE), derive Γ ⊢ ∃x. y = SOME x.";

shiftedFn::usage =
  "shiftedFn[lTm] — Wolfram term builder for `λj. REP_list lTm (SUC j)`. Used as the carrier for the tail of a non-empty list.";
tailFnOf::usage =
  "tailFnOf[lTm] — Wolfram term builder for `ABS_list (shiftedFn[lTm])`. The list term for tail-of-l.";
shiftedIsListPThm::usage =
  "shiftedIsListPThm[lTm, nPrimeTm, witHypThm] — given a length-SUC-n' witness `(witHyp) ⊢ ∀i. REP_list l i = NONE ⇔ ¬(i < SUC n')`, derive `(witHyp) ⊢ isListPLambda (shiftedFn[l])`.";
repTailEqShiftedThm::usage =
  "repTailEqShiftedThm[lTm, nPrimeTm, witHypThm] — given the length-SUC-n' witness, derive `(witHyp) ⊢ REP_list (tailFnOf[l]) = shiftedFn[l]`.";
tailLengthThm::usage =
  "tailLengthThm[lTm, nPrimeTm, witHypThm] — given the length-SUC-n' witness, derive `(witHyp) ⊢ ∀i. REP_list (tailFnOf[l]) i = NONE ⇔ ¬(i < nPrimeTm)`.";
headTermOf::usage =
  "headTermOf[lTm] — Wolfram term builder for `ε x. REP_list l 0 = SOME x`.";
consHeadTailEqLThm::usage =
  "consHeadTailEqLThm[lTm, nPrimeTm, witHypThm] — given the length-SUC-n' witness, derive `(witHyp) ⊢ CONS (headTermOf l) (tailFnOf l) = l`.";

Begin["`Private`"];

(* ============================================================ *)
(* Local type vars + helpers                                    *)
(* ============================================================ *)

αTy = mkVarType["A"];

(* Num.wl's numTy is HOL`Stdlib`Num`Private`numTy — not visible here. *)
numTy = mkType["num", {}];

optionATy   = HOL`Stdlib`Option`optionTy[αTy];
carrierTy   = tyFun[numTy, optionATy];
predTy      = tyFun[carrierTy, boolTy];

noneAt[ty_] := mkConst["NONE", HOL`Stdlib`Option`optionTy[ty]];
someAt[ty_] := mkConst["SOME", tyFun[ty, HOL`Stdlib`Option`optionTy[ty]]];
selectC[ty_] := mkConst["@", tyFun[tyFun[ty, boolTy], ty]];

andC[]       := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
impC[]       := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notC[]       := mkConst["¬", tyFun[boolTy, boolTy]];
forallC[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
existsC[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];

andTm[a_, b_] := mkComb[mkComb[andC[], a], b];
impTm[a_, b_] := mkComb[mkComb[impC[], a], b];

(* Local num-term builders (Num.wl's ltTm/plusTm/etc. are Private). *)
ltTmLocal[aTm_, bTm_] :=
  mkComb[mkComb[HOL`Stdlib`Num`ltConst[], aTm], bTm];
sucTm[nTm_] := mkComb[HOL`Stdlib`Num`sucConst[], nTm];

(* ============================================================ *)
(* isListP predicate                                            *)
(*   λf. ∃n. ∀i. (f i = NONE) ⇔ ¬ (i < n)                       *)
(* ============================================================ *)

isListPLambdaTerm[] :=
  Module[{fV, iV, nV, fAti, noneOption, ltIn, eqFiNone,
          notLtIn, iffBody, forallI, existsN},
    fV = mkVar["f", carrierTy];
    iV = mkVar["i", numTy];
    nV = mkVar["n", numTy];
    fAti = mkComb[fV, iV];
    noneOption = noneAt[αTy];
    ltIn = ltTmLocal[iV, nV];
    eqFiNone = mkEq[fAti, noneOption];
    notLtIn = mkComb[notC[], ltIn];
    iffBody = mkEq[eqFiNone, notLtIn];
    forallI = mkComb[forallC[numTy], mkAbs[iV, iffBody]];
    existsN = mkComb[existsC[numTy], mkAbs[nV, forallI]];
    mkAbs[fV, existsN]
  ];

isListPDefThm = newDefinition[mkEq[
  mkVar["isListP", predTy],
  isListPLambdaTerm[]
]];

isListPConst[] := mkConst["isListP", predTy];

(* ============================================================ *)
(* Witness theorem: ⊢ isListPLambda (λi. NONE)                  *)
(*                                                              *)
(* Take n = 0:                                                  *)
(*   ∀i. ((λi. NONE) i = NONE) ⇔ ¬ (i < 0).                     *)
(*   - LHS reduces to NONE = NONE = T (via inverse BETA over    *)
(*     REFL[NONE]).                                              *)
(*   - RHS = ¬(i < 0) = T (via notLtZeroThm + EQTINTRO).         *)
(*   - TRANS the two T-equalities → LHS = RHS.                   *)
(* GEN i, EXISTS at n = 0, then EQMP via SYM[BETACONV of         *)
(* (predLam (λi. NONE))].                                        *)
(* ============================================================ *)

isListPWitnessThm =
  Module[{iV, nV, nilFunc, noneOption, refl, lhsBeta,
          lhsEqT, notLtAti, notLtEqT, iffEq, genI,
          existsBodyTm, existsAt0,
          predLam, predApplied, betaTh},
    iV = mkVar["i", numTy];
    nV = mkVar["n", numTy];
    nilFunc = mkAbs[iV, noneAt[αTy]];
    (* λi. NONE *)
    noneOption = noneAt[αTy];

    refl = REFL[noneOption];
    (* ⊢ NONE = NONE *)

    lhsBeta = BETACONV[mkComb[nilFunc, iV]];
    (* ⊢ (λi. NONE) i = NONE *)
    lhsEqT = HOL`Bool`EQTINTRO[lhsBeta];
    (* ⊢ ((λi. NONE) i = NONE) = T *)

    notLtAti = HOL`Bool`SPEC[iV, HOL`Stdlib`Num`notLtZeroThm];
    (* ⊢ ¬ (i < 0) *)
    notLtEqT = HOL`Bool`EQTINTRO[notLtAti];
    (* ⊢ (¬ (i < 0)) = T *)

    iffEq = TRANS[lhsEqT, HOL`Equal`SYM[notLtEqT]];
    (* ⊢ ((λi. NONE) i = NONE) = ¬ (i < 0) *)

    genI = HOL`Bool`GEN[iV, iffEq];
    (* ⊢ ∀i. ((λi. NONE) i = NONE) = ¬ (i < 0) *)

    existsBodyTm = mkComb[existsC[numTy],
      mkAbs[nV, mkComb[forallC[numTy], mkAbs[iV,
        mkEq[mkEq[mkComb[nilFunc, iV], noneOption],
             mkComb[notC[], ltTmLocal[iV, nV]]]]]]];
    existsAt0 = HOL`Bool`EXISTS[existsBodyTm, zeroConst[], genI];
    (* ⊢ ∃n. ∀i. ((λi. NONE) i = NONE) = ¬ (i < n) *)

    predLam = isListPLambdaTerm[];
    predApplied = mkComb[predLam, nilFunc];
    betaTh = BETACONV[predApplied];
    (* ⊢ isListPLambda (λi. NONE) = ∃n. ∀i. ((λi. NONE) i = NONE) = ¬ (i < n) *)

    EQMP[HOL`Equal`SYM[betaTh], existsAt0]
    (* ⊢ isListPLambda (λi. NONE) *)
  ];

(* ============================================================ *)
(* Introduce the list type via newBasicTypeDefinition           *)
(* ============================================================ *)

{absRepListThm, repAbsListThm} =
  newBasicTypeDefinition["list", "ABS_list", "REP_list",
    isListPWitnessThm];

listTy[a_] := mkType["list", {a}];

absListConst[] :=
  mkConst["ABS_list", tyFun[carrierTy, listTy[αTy]]];
repListConst[] :=
  mkConst["REP_list", tyFun[listTy[αTy], carrierTy]];

(* ============================================================ *)
(* NIL constructor: ABS_list (λi. NONE)                         *)
(* ============================================================ *)

nilTy = listTy[αTy];

nilDefBody[] :=
  Module[{iV},
    iV = mkVar["i", numTy];
    mkComb[absListConst[], mkAbs[iV, noneAt[αTy]]]
  ];

nilDefThm = newDefinition[
  mkEq[mkVar["NIL", nilTy], nilDefBody[]]
];

nilConst[] := mkConst["NIL", nilTy];

(* ============================================================ *)
(* repNilThm : ⊢ REP_list NIL = (λi. NONE)                       *)
(*                                                              *)
(* APTERM REP_list onto nilDefThm: REP_list NIL = REP_list      *)
(* (ABS_list (λi. NONE)). Then EQMP repAbsListThm instantiated  *)
(* at r = (λi. NONE) (the witness term, where isListPLambda      *)
(* holds) gives REP_list (ABS_list (λi. NONE)) = (λi. NONE).     *)
(* ============================================================ *)

repNilThm =
  Module[{iV, nilFunc, applyRep, repAbsAtNilFunc,
          forwardEqHyp, swapDir, chained},
    iV = mkVar["i", numTy];
    nilFunc = mkAbs[iV, noneAt[αTy]];

    applyRep = HOL`Equal`APTERM[repListConst[], nilDefThm];
    (* ⊢ REP_list NIL = REP_list (ABS_list (λi. NONE)) *)

    (* repAbsListThm : ⊢ isListPLambda r = (REP_list (ABS_list r) = r)
       INST r → nilFunc, apply the witness to extract RHS. *)
    repAbsAtNilFunc = HOL`Kernel`INST[
      {mkVar["r", carrierTy] -> nilFunc}, repAbsListThm];
    (* ⊢ isListPLambda (λi. NONE) = (REP_list (ABS_list (λi. NONE)) = (λi. NONE)) *)

    forwardEqHyp = EQMP[repAbsAtNilFunc, isListPWitnessThm];
    (* ⊢ REP_list (ABS_list (λi. NONE)) = (λi. NONE) *)

    chained = TRANS[applyRep, forwardEqHyp]
    (* ⊢ REP_list NIL = (λi. NONE) *)
  ];

(* ============================================================ *)
(* CONS constructor                                              *)
(*                                                              *)
(* CONS x l = ABS_list (λi. ε y. (i = 0 ⇒ y = SOME x)            *)
(*                              ∧ (∀j. i = SUC j ⇒ y =           *)
(*                                  REP_list l j)).               *)
(*                                                              *)
(* Uses Hilbert ε for a case-by-i selector — head at 0, tail at  *)
(* SUC j. Avoids defining COND / PRE as separate constants.       *)
(* ============================================================ *)

consTy = tyFun[αTy, tyFun[listTy[αTy], listTy[αTy]]];

(* Wolfram helper: predicate body P[x, l, i, y] under ε's λy.    *)
(*   (i = 0 ⇒ y = SOME x) ∧ (∀j. i = SUC j ⇒ y = REP_list l j)   *)
consPredBodyTerm[xTm_, lTm_, iTm_, yTm_, jVForBuild_] :=
  Module[{someX, repLj, leftImp, rightForall},
    someX = mkComb[someAt[αTy], xTm];
    repLj = mkComb[mkComb[repListConst[], lTm], jVForBuild];
    leftImp = impTm[mkEq[iTm, zeroConst[]], mkEq[yTm, someX]];
    rightForall = mkComb[forallC[numTy], mkAbs[jVForBuild,
      impTm[mkEq[iTm, sucTm[jVForBuild]], mkEq[yTm, repLj]]]];
    andTm[leftImp, rightForall]
  ];

consDefBody[] :=
  Module[{xV, lV, iV, jV, yV, predLam, epsTm, indexedFn},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listTy[αTy]];
    iV = mkVar["i", numTy];
    jV = mkVar["jBnd", numTy];
    yV = mkVar["y", optionATy];
    predLam = mkAbs[yV, consPredBodyTerm[xV, lV, iV, yV, jV]];
    epsTm = mkComb[selectC[optionATy], predLam];
    indexedFn = mkAbs[iV, epsTm];
    mkAbs[xV, mkAbs[lV, mkComb[absListConst[], indexedFn]]]
  ];

consDefThm = newDefinition[
  mkEq[mkVar["CONS", consTy], consDefBody[]]
];

consConst[] := mkConst["CONS", consTy];

(* ============================================================ *)
(* Helper: unfold CONS x l to ABS_list (consF x l) via APTHM     *)
(*         on consDefThm, then BETACONV twice (for x and l).     *)
(* Returns ⊢ CONS x l = ABS_list (consF x l).                    *)
(* ============================================================ *)

unfoldCons[xTm_, lTm_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[consDefThm, xTm];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, lTm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ============================================================ *)
(* consF x l : λi. ε y. (i = 0 ⇒ y = SOME x) ∧                   *)
(*                     (∀j. i = SUC j ⇒ y = REP_list l j)         *)
(* Wolfram helper returning the carrier-side λ-term.              *)
(* ============================================================ *)

consFTerm[xTm_, lTm_] :=
  Module[{iV, jV, yV, predLam, epsTm},
    iV = mkVar["i", numTy];
    jV = mkVar["jBnd", numTy];
    yV = mkVar["y", optionATy];
    predLam = mkAbs[yV, consPredBodyTerm[xTm, lTm, iV, yV, jV]];
    epsTm = mkComb[selectC[optionATy], predLam];
    mkAbs[iV, epsTm]
  ];

(* ============================================================ *)
(* consPredExistsThm[x, l, i, witness]                           *)
(*   helpers that build ⊢ ∃y. predBody[x, l, i, y]                *)
(* using the witness (SOME x for i = 0, REP_list l j for          *)
(* i = SUC j). Both via CONJ + EXISTS.                            *)
(* ============================================================ *)

(* Case i = 0, witness y = SOME x.                              *)
(*   first  : (0 = 0) ⇒ (SOME x = SOME x) — DISCH REFL.          *)
(*   second : ∀j. (0 = SUC j) ⇒ (SOME x = REP_list l j) —          *)
(*            ASSUME 0 = SUC j, SYM gives SUC j = 0, contradicts  *)
(*            sucNotZeroThm, CONTR + DISCH + GEN.                 *)
consExistsAtZeroThm[xTm_, lTm_] :=
  Module[{iV, jV, yV, someX, repLj,
          conj1, jHypTm, jHyp, symEq, sucNotZeroAtJ, fContra,
          targetEq, contrThm, dischJ, genJ, conj2,
          predBodyAtSx, predLam, predLamY, existsTm},
    iV = mkVar["i", numTy];
    jV = mkVar["jBnd", numTy];
    yV = mkVar["y", optionATy];
    someX = mkComb[someAt[αTy], xTm];
    repLj = mkComb[mkComb[repListConst[], lTm], jV];

    (* conj1 : ⊢ (0 = 0) ⇒ (SOME x = SOME x) *)
    conj1 = HOL`Bool`DISCH[mkEq[zeroConst[], zeroConst[]], REFL[someX]];

    (* conj2 : ⊢ ∀j. (0 = SUC j) ⇒ (SOME x = REP_list l j) *)
    jHypTm = mkEq[zeroConst[], sucTm[jV]];
    jHyp = ASSUME[jHypTm];
    symEq = HOL`Equal`SYM[jHyp];
    (* (0=SUC j) ⊢ SUC j = 0 *)
    sucNotZeroAtJ = HOL`Bool`SPEC[jV, HOL`Stdlib`Num`sucNotZeroThm];
    fContra = HOL`Bool`MP[HOL`Bool`NOTELIM[sucNotZeroAtJ], symEq];
    (* (0=SUC j) ⊢ F *)
    targetEq = mkEq[someX, repLj];
    contrThm = HOL`Bool`CONTR[targetEq, fContra];
    (* (0=SUC j) ⊢ SOME x = REP_list l j *)
    dischJ = HOL`Bool`DISCH[jHypTm, contrThm];
    genJ = HOL`Bool`GEN[jV, dischJ];
    conj2 = genJ;

    predBodyAtSx = HOL`Bool`CONJ[conj1, conj2];
    (* ⊢ (0 = 0 ⇒ SOME x = SOME x) ∧ (∀j. 0 = SUC j ⇒ SOME x = REP_list l j)
       which is consPredBodyTerm[x, l, 0, SOME x, j] *)

    predLam = mkAbs[yV, consPredBodyTerm[xTm, lTm, zeroConst[], yV, jV]];
    existsTm = mkComb[existsC[optionATy], predLam];
    HOL`Bool`EXISTS[existsTm, someX, predBodyAtSx]
    (* ⊢ ∃y. predBody[x, l, 0, y] *)
  ];

(* Case i = SUC jconc (jconc is a free-var term), witness y =     *)
(* REP_list l jconc.                                              *)
(*   first  : (SUC jconc = 0) ⇒ ... — vacuous via sucNotZero.     *)
(*   second : ∀j. (SUC jconc = SUC j) ⇒                           *)
(*              REP_list l jconc = REP_list l j — sucInj + APTERM. *)
consExistsAtSucThm[xTm_, lTm_, jcTm_] :=
  Module[{iV, jV, yV, someX, repLjc, repLj,
          iEq0Tm, iEq0Hyp, sucNotZeroAtJc, fContra1,
          conj1Target, contrThm1, dischI0, conj1,
          jHypTm, jHyp, sucInjAtJcJ, jcEqJ, apTermRep, contrThm2,
          dischJ, genJ, conj2,
          predBodyAtRl, predLam, existsTm},
    iV = mkVar["i", numTy];
    jV = mkVar["jBnd", numTy];
    yV = mkVar["y", optionATy];
    someX = mkComb[someAt[αTy], xTm];
    repLjc = mkComb[mkComb[repListConst[], lTm], jcTm];
    repLj  = mkComb[mkComb[repListConst[], lTm], jV];

    (* conj1 : ⊢ (SUC jc = 0) ⇒ (REP_list l jc = SOME x).       *)
    iEq0Tm = mkEq[sucTm[jcTm], zeroConst[]];
    iEq0Hyp = ASSUME[iEq0Tm];
    sucNotZeroAtJc = HOL`Bool`SPEC[jcTm, HOL`Stdlib`Num`sucNotZeroThm];
    fContra1 = HOL`Bool`MP[HOL`Bool`NOTELIM[sucNotZeroAtJc], iEq0Hyp];
    conj1Target = mkEq[repLjc, someX];
    contrThm1 = HOL`Bool`CONTR[conj1Target, fContra1];
    dischI0 = HOL`Bool`DISCH[iEq0Tm, contrThm1];
    conj1 = dischI0;

    (* conj2 : ⊢ ∀j. (SUC jc = SUC j) ⇒ REP_list l jc = REP_list l j *)
    jHypTm = mkEq[sucTm[jcTm], sucTm[jV]];
    jHyp = ASSUME[jHypTm];
    sucInjAtJcJ = HOL`Bool`SPEC[jV, HOL`Bool`SPEC[jcTm,
                    HOL`Stdlib`Num`sucInjThm]];
    (* ⊢ SUC jc = SUC j ⇒ jc = j *)
    jcEqJ = HOL`Bool`MP[sucInjAtJcJ, jHyp];
    (* (SUC jc = SUC j) ⊢ jc = j *)
    apTermRep = HOL`Equal`APTERM[mkComb[repListConst[], lTm], jcEqJ];
    (* (SUC jc = SUC j) ⊢ REP_list l jc = REP_list l j *)
    dischJ = HOL`Bool`DISCH[jHypTm, apTermRep];
    genJ = HOL`Bool`GEN[jV, dischJ];
    conj2 = genJ;

    predBodyAtRl = HOL`Bool`CONJ[conj1, conj2];

    (* Build predicate λy. predBody[x, l, SUC jc, y, j] manually
       — the witness substitutes y = REP_list l jc. *)
    predLam = mkAbs[yV, consPredBodyTerm[xTm, lTm, sucTm[jcTm], yV, jV]];
    existsTm = mkComb[existsC[optionATy], predLam];
    HOL`Bool`EXISTS[existsTm, repLjc, predBodyAtRl]
    (* ⊢ ∃y. predBody[x, l, SUC jc, y] *)
  ];

(* ============================================================ *)
(* consF x l 0 = SOME x  and  consF x l (SUC j) = REP_list l j   *)
(*                                                              *)
(* For each i case: build ∃-thm via consExistsAt*; selectOfExists *)
(* gives predBody[..., @predLam]; extract the relevant conjunct, *)
(* MP with REFL to get @predLam = witness; BETACONV chain        *)
(* converts (consF x l) i form to ε form.                        *)
(* ============================================================ *)

consFAtZeroThm[xTm_, lTm_] :=
  Module[{iV, jV, yV, predLam, existsThZero,
          predBodyAtAt, conj1, atEpsEqSomeX,
          consFTerm0, betaConsF0, fullChain},
    iV = mkVar["i", numTy];
    jV = mkVar["jBnd", numTy];
    yV = mkVar["y", optionATy];
    predLam = mkAbs[yV, consPredBodyTerm[xTm, lTm, zeroConst[], yV, jV]];

    existsThZero = consExistsAtZeroThm[xTm, lTm];
    (* ⊢ ∃y. predBody[x, l, 0, y] *)
    predBodyAtAt = HOL`Stdlib`Num`selectOfExists[predLam, existsThZero];
    (* ⊢ (0 = 0 ⇒ @predLam = SOME x) ∧ (∀j. 0 = SUC j ⇒ @predLam = REP_list l j) *)
    conj1 = HOL`Bool`CONJUNCT1[predBodyAtAt];
    (* ⊢ (0 = 0) ⇒ @predLam = SOME x *)
    atEpsEqSomeX = HOL`Bool`MP[conj1, REFL[zeroConst[]]];
    (* ⊢ @predLam = SOME x
       where @predLam = ε y. predBody[x, l, 0, y]. *)

    (* consFTerm[x, l] 0 = ε y. predBody[x, l, 0, y] via BETA. *)
    consFTerm0 = mkComb[consFTerm[xTm, lTm], zeroConst[]];
    betaConsF0 = BETACONV[consFTerm0];
    (* ⊢ (λi. ε y. predBody[x, l, i, y]) 0 = ε y. predBody[x, l, 0, y] *)

    fullChain = TRANS[betaConsF0, atEpsEqSomeX]
    (* ⊢ consFTerm[x, l] 0 = SOME x *)
  ];

consFAtSucThm[xTm_, lTm_, jcTm_] :=
  Module[{iV, jV, yV, predLam, existsThSuc,
          predBodyAtAt, conj2, conj2AtJc, atEpsEqRepLjc,
          consFTermSuc, betaConsFSuc, fullChain},
    iV = mkVar["i", numTy];
    jV = mkVar["jBnd", numTy];
    yV = mkVar["y", optionATy];
    predLam = mkAbs[yV, consPredBodyTerm[xTm, lTm, sucTm[jcTm], yV, jV]];

    existsThSuc = consExistsAtSucThm[xTm, lTm, jcTm];
    (* ⊢ ∃y. predBody[x, l, SUC jc, y] *)
    predBodyAtAt = HOL`Stdlib`Num`selectOfExists[predLam, existsThSuc];
    conj2 = HOL`Bool`CONJUNCT2[predBodyAtAt];
    (* ⊢ ∀j. (SUC jc = SUC j) ⇒ @predLam = REP_list l j *)
    conj2AtJc = HOL`Bool`SPEC[jcTm, conj2];
    (* ⊢ (SUC jc = SUC jc) ⇒ @predLam = REP_list l jc *)
    atEpsEqRepLjc = HOL`Bool`MP[conj2AtJc, REFL[sucTm[jcTm]]];
    (* ⊢ @predLam = REP_list l jc *)

    consFTermSuc = mkComb[consFTerm[xTm, lTm], sucTm[jcTm]];
    betaConsFSuc = BETACONV[consFTermSuc];
    (* ⊢ consFTerm[x, l] (SUC jc) = ε y. predBody[x, l, SUC jc, y] *)

    fullChain = TRANS[betaConsFSuc, atEpsEqRepLjc]
    (* ⊢ consFTerm[x, l] (SUC jc) = REP_list l jc *)
  ];

(* ============================================================ *)
(* Auxiliary num lemma: ⊢ ∀a b. (SUC a ≤ SUC b) = (a ≤ b)        *)
(*                                                              *)
(* Each direction via leqDefThm: unfold both sides to ∃k. _+_=_, *)
(* manipulate via addLeftSuc + sucInj. Wrapped in DEDUCTANTISYM. *)
(* ============================================================ *)

leqSucMonoCancelThm =
  Module[{aV, bV, kV, leqC,
          sucALeqSucBTm, sucALeqSucBHyp, sucALeqSucBExists,
          aPlusKEqBHyp, sucChain, akEqB, existsAkEqB, aLeqB,
          aLeqBTm, aLeqBHyp, aLeqBExists, kHyp,
          sucAPlusKEqSucB, sucALeqSucB,
          forwardImpl, backwardImpl, deductRes, genB, genA},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    kV = mkVar["k", numTy];
    leqC = HOL`Stdlib`Num`leqConst[];

    (* === Forward: SUC a ≤ SUC b ⇒ a ≤ b === *)
    sucALeqSucBTm = mkComb[mkComb[leqC, sucTm[aV]], sucTm[bV]];
    sucALeqSucBHyp = ASSUME[sucALeqSucBTm];
    sucALeqSucBExists = EQMP[
      Module[{ap1, ap2},
        ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, sucTm[aV]];
        ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
        ap2 = HOL`Equal`APTHM[ap1, sucTm[bV]];
        TRANS[ap2, BETACONV[concl[ap2][[2]]]]
      ],
      sucALeqSucBHyp];
    (* (SUC a ≤ SUC b) ⊢ ∃k. SUC a + k = SUC b *)
    aPlusKEqBHyp = ASSUME[
      mkEq[mkComb[mkComb[HOL`Stdlib`Num`plusConst[], sucTm[aV]], kV],
           sucTm[bV]]];
    (* (SUC a + k = SUC b) ⊢ SUC a + k = SUC b *)
    sucChain = HOL`Bool`SPEC[kV,
      HOL`Bool`SPEC[aV, HOL`Stdlib`Num`addLeftSucThm]];
    (* ⊢ SUC a + k = SUC (a + k) *)
    akEqB = HOL`Bool`MP[
      HOL`Bool`SPEC[bV,
        HOL`Bool`SPEC[mkComb[mkComb[HOL`Stdlib`Num`plusConst[], aV], kV],
          HOL`Stdlib`Num`sucInjThm]],
      TRANS[HOL`Equal`SYM[sucChain], aPlusKEqBHyp]];
    (* (SUC a + k = SUC b) ⊢ a + k = b *)
    existsAkEqB = HOL`Bool`EXISTS[
      mkComb[existsC[numTy], mkAbs[kV,
        mkEq[mkComb[mkComb[HOL`Stdlib`Num`plusConst[], aV], kV], bV]]],
      kV, akEqB];
    (* (SUC a + k = SUC b) ⊢ ∃k. a + k = b *)
    aLeqB = EQMP[
      HOL`Equal`SYM[Module[{ap1, ap2},
        ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, aV];
        ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
        ap2 = HOL`Equal`APTHM[ap1, bV];
        TRANS[ap2, BETACONV[concl[ap2][[2]]]]
      ]],
      existsAkEqB];
    (* (SUC a + k = SUC b) ⊢ a ≤ b *)
    forwardImpl = HOL`Bool`DISCH[sucALeqSucBTm,
      HOL`Bool`CHOOSE[kV, sucALeqSucBExists, aLeqB]];
    (* ⊢ (SUC a ≤ SUC b) ⇒ (a ≤ b) *)

    (* === Backward: a ≤ b ⇒ SUC a ≤ SUC b === *)
    aLeqBTm = mkComb[mkComb[leqC, aV], bV];
    aLeqBHyp = ASSUME[aLeqBTm];
    aLeqBExists = EQMP[
      Module[{ap1, ap2},
        ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, aV];
        ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
        ap2 = HOL`Equal`APTHM[ap1, bV];
        TRANS[ap2, BETACONV[concl[ap2][[2]]]]
      ],
      aLeqBHyp];
    (* (a ≤ b) ⊢ ∃k. a + k = b *)
    kHyp = ASSUME[
      mkEq[mkComb[mkComb[HOL`Stdlib`Num`plusConst[], aV], kV], bV]];
    (* (a + k = b) ⊢ a + k = b *)
    sucAPlusKEqSucB = Module[{apSucEq, sucAddLeft, transAll, existsTm2, foldedRes},
      apSucEq = HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], kHyp];
      (* (a+k=b) ⊢ SUC (a + k) = SUC b *)
      sucAddLeft = HOL`Bool`SPEC[kV,
        HOL`Bool`SPEC[aV, HOL`Stdlib`Num`addLeftSucThm]];
      (* ⊢ SUC a + k = SUC (a + k) *)
      transAll = TRANS[sucAddLeft, apSucEq];
      (* (a+k=b) ⊢ SUC a + k = SUC b *)
      existsTm2 = mkComb[existsC[numTy], mkAbs[kV,
        mkEq[mkComb[mkComb[HOL`Stdlib`Num`plusConst[], sucTm[aV]], kV],
             sucTm[bV]]]];
      foldedRes = HOL`Bool`EXISTS[existsTm2, kV, transAll];
      (* (a+k=b) ⊢ ∃k. SUC a + k = SUC b *)
      EQMP[
        HOL`Equal`SYM[Module[{ap1, ap2},
          ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, sucTm[aV]];
          ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
          ap2 = HOL`Equal`APTHM[ap1, sucTm[bV]];
          TRANS[ap2, BETACONV[concl[ap2][[2]]]]
        ]],
        foldedRes]
      (* (a+k=b) ⊢ SUC a ≤ SUC b *)
    ];
    sucALeqSucB = HOL`Bool`CHOOSE[kV, aLeqBExists, sucAPlusKEqSucB];
    (* (a ≤ b) ⊢ SUC a ≤ SUC b *)
    backwardImpl = HOL`Bool`DISCH[aLeqBTm, sucALeqSucB];
    (* ⊢ (a ≤ b) ⇒ (SUC a ≤ SUC b) *)

    (* === Combine via DEDUCTANTISYM ===                          *)
    (* DEDUCTANTISYM[thm1, thm2] returns ⊢ p = q where             *)
    (*   p = concl(thm1), q = concl(thm2).                          *)
    (* For (SUC a ≤ SUC b) = (a ≤ b) we want                        *)
    (*   thm1: (a ≤ b) ⊢ SUC a ≤ SUC b   (p = SUC a ≤ SUC b)        *)
    (*   thm2: (SUC a ≤ SUC b) ⊢ a ≤ b   (q = a ≤ b)                *)
    deductRes = HOL`Kernel`DEDUCTANTISYM[
      HOL`Bool`MP[backwardImpl, aLeqBHyp],
      HOL`Bool`MP[forwardImpl, sucALeqSucBHyp]];
    genB = HOL`Bool`GEN[bV, deductRes];
    genA = HOL`Bool`GEN[aV, genB]
  ];

(* ============================================================ *)
(* ⊢ isListPLambda (REP_list l) — REP_list always lands in the   *)
(* carrier subset. APTERM-loop through absRepListThm +          *)
(* repAbsListThm inverted.                                       *)
(* ============================================================ *)

isListPOfRepListThm =
  Module[{lV, absRepAtL, applyRepBothSides, repAbsAtRepL},
    lV = mkVar["l", listTy[αTy]];
    absRepAtL = HOL`Kernel`INST[
      {mkVar["a", listTy[αTy]] -> lV}, absRepListThm];
    (* ⊢ ABS_list (REP_list l) = l *)
    applyRepBothSides = HOL`Equal`APTERM[repListConst[], absRepAtL];
    (* ⊢ REP_list (ABS_list (REP_list l)) = REP_list l *)
    repAbsAtRepL = HOL`Kernel`INST[
      {mkVar["r", carrierTy] -> mkComb[repListConst[], lV]},
      repAbsListThm];
    EQMP[HOL`Equal`SYM[repAbsAtRepL], applyRepBothSides]
  ];

(* ============================================================ *)
(* Small derived rules used by the isListP-for-CONS proof.       *)
(* ============================================================ *)

(* From Γ ⊢ ¬p derive Γ ⊢ p = F. *)
eqfIntroLocal[thNotP_] :=
  Module[{p, pToF, fToP, fConst},
    fConst = mkConst["F", boolTy];
    p = concl[thNotP][[2]];
    pToF = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], ASSUME[p]];
    fToP = HOL`Bool`CONTR[p, ASSUME[fConst]];
    HOL`Kernel`DEDUCTANTISYM[fToP, pToF]
  ];

(* From Γ ⊢ p derive Γ ⊢ ¬¬p. *)
notNotIntroLocal[thP_] :=
  Module[{notP, notPHyp, fThm, dischNotP},
    notP = mkComb[notC[], concl[thP]];
    notPHyp = ASSUME[notP];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notPHyp], thP];
    dischNotP = HOL`Bool`DISCH[notP, fThm];
    HOL`Bool`NOTINTRO[dischNotP]
  ];

(* ============================================================ *)
(* someNotEqNoneThm : ⊢ ∀x. ¬(SOME x = NONE)                     *)
(* Symmetric of Option's noneNotEqSomeThm.                       *)
(* ============================================================ *)

someNotEqNoneThm =
  Module[{xV, someX, noneOpt, hypTm, hypAssum, symEq,
          contradF, dischHyp, notEq, genX},
    xV = mkVar["x", αTy];
    someX = mkComb[someAt[αTy], xV];
    noneOpt = noneAt[αTy];
    hypTm = mkEq[someX, noneOpt];
    hypAssum = ASSUME[hypTm];
    symEq = HOL`Equal`SYM[hypAssum];
    (* (SOME x = NONE) ⊢ NONE = SOME x *)
    (* noneNotEqSomeThm is already ⊢ ¬(NONE = SOME x) at free x. *)
    contradF = HOL`Bool`MP[
      HOL`Bool`NOTELIM[HOL`Stdlib`Option`noneNotEqSomeThm], symEq];
    dischHyp = HOL`Bool`DISCH[hypTm, contradF];
    notEq = HOL`Bool`NOTINTRO[dischHyp];
    genX = HOL`Bool`GEN[xV, notEq]
  ];

(* ============================================================ *)
(* ltSucMonoCancelThm : ⊢ ∀a b. (SUC a < SUC b) = (a < b)        *)
(* SUC a < SUC b  ⇔  SUC (SUC a) ≤ SUC b  ⇔  SUC a ≤ b  ⇔  a < b. *)
(* ============================================================ *)

ltSucMonoCancelThm =
  Module[{aV, bV, lhsUnfold, monoCancelAt, rhsUnfold, chainEq, genB, genA},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];

    lhsUnfold = Module[{ap1, ap2},
      ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, sucTm[aV]];
      ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
      ap2 = HOL`Equal`APTHM[ap1, sucTm[bV]];
      TRANS[ap2, BETACONV[concl[ap2][[2]]]]
    ];
    (* ⊢ (SUC a < SUC b) = (SUC (SUC a) ≤ SUC b) *)
    monoCancelAt = HOL`Bool`SPEC[bV,
      HOL`Bool`SPEC[sucTm[aV], leqSucMonoCancelThm]];
    (* ⊢ (SUC (SUC a) ≤ SUC b) = (SUC a ≤ b) *)
    rhsUnfold = Module[{ap1, ap2},
      ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, aV];
      ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
      ap2 = HOL`Equal`APTHM[ap1, bV];
      TRANS[ap2, BETACONV[concl[ap2][[2]]]]
    ];
    (* ⊢ (a < b) = (SUC a ≤ b) *)
    chainEq = TRANS[TRANS[lhsUnfold, monoCancelAt], HOL`Equal`SYM[rhsUnfold]];
    (* ⊢ (SUC a < SUC b) = (a < b) *)
    genB = HOL`Bool`GEN[bV, chainEq];
    genA = HOL`Bool`GEN[aV, genB]
  ];

(* ============================================================ *)
(* zeroLtSucThm : ⊢ ∀n. 0 < SUC n                                *)
(* 0 < SUC n  ⇔  SUC 0 ≤ SUC n  ⇔  0 ≤ n  (always true).         *)
(* ============================================================ *)

zeroLtSucThm =
  Module[{nV, zeroLeqN, monoCancelAt, sucZeroLeqSucN, foldLt, genN},
    nV = mkVar["n", numTy];
    zeroLeqN = HOL`Bool`SPEC[nV, HOL`Stdlib`Num`leqZeroThm];
    (* ⊢ 0 ≤ n *)
    monoCancelAt = HOL`Bool`SPEC[nV,
      HOL`Bool`SPEC[zeroConst[], leqSucMonoCancelThm]];
    (* ⊢ (SUC 0 ≤ SUC n) = (0 ≤ n) *)
    sucZeroLeqSucN = EQMP[HOL`Equal`SYM[monoCancelAt], zeroLeqN];
    (* ⊢ SUC 0 ≤ SUC n *)
    foldLt = EQMP[
      HOL`Equal`SYM[Module[{ap1, ap2},
        ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, zeroConst[]];
        ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
        ap2 = HOL`Equal`APTHM[ap1, sucTm[nV]];
        TRANS[ap2, BETACONV[concl[ap2][[2]]]]
      ]],
      sucZeroLeqSucN];
    (* ⊢ 0 < SUC n *)
    genN = HOL`Bool`GEN[nV, foldLt]
  ];

(* ============================================================ *)
(* consCarrierIsListPThm[x, l]                                   *)
(*   ⊢ isListPLambdaTerm[] (consFTerm[x, l])                     *)
(*                                                              *)
(* Witness n = SUC n_l where n_l comes from isListP (REP_list l). *)
(* For each i: numCases on i.                                    *)
(*   i = 0: consF x l 0 = SOME x; (SOME x = NONE) is F;          *)
(*          0 < SUC n_l is T so ¬(0 < SUC n_l) is F; F = F.       *)
(*   i = SUC j: consF x l (SUC j) = REP_list l j;                *)
(*              (REP_list l j = NONE) ⇔ ¬(j < n_l) from witHyp;   *)
(*              ¬(j < n_l) = ¬(SUC j < SUC n_l) via               *)
(*              ltSucMonoCancel SYM.                              *)
(* ============================================================ *)

consCarrierIsListPThm[xTm_, lTm_] :=
  Module[{nLV, iV, jBndV,
          isListPRepL, betaUnfold, existsBodyThm, witInnerTm, witHyp,
          consFXL, eqC,
          caseZeroBranch, caseSucBranch, perI,
          numCasesAtI, iEqZeroBranch, iEqSucBranch, perIGenI,
          existsAtSucNL, foldUnfold, chosenNL},

    nLV = mkVar["nL", numTy];
    iV = mkVar["i", numTy];
    (* "jSplit" — name distinct from consFAtSucThm's internal "jBnd" *)
    jBndV = mkVar["jSplit", numTy];

    consFXL = consFTerm[xTm, lTm];
    eqC = mkConst["=", tyFun[optionATy, tyFun[optionATy, boolTy]]];

    (* === Step 1+2: ⊢ ∃n_l. ∀i. (REP_list l i = NONE) ⇔ ¬(i < n_l) === *)
    isListPRepL = HOL`Kernel`INST[
      {mkVar["l", listTy[αTy]] -> lTm}, isListPOfRepListThm];
    betaUnfold = BETACONV[
      mkComb[isListPLambdaTerm[], mkComb[repListConst[], lTm]]];
    existsBodyThm = EQMP[betaUnfold, isListPRepL];

    (* === Step 3: CHOOSE n_l, ASSUME the inner ∀i body === *)
    witInnerTm = mkComb[forallC[numTy], mkAbs[iV,
      mkEq[mkEq[mkComb[mkComb[repListConst[], lTm], iV], noneAt[αTy]],
           mkComb[notC[], ltTmLocal[iV, nLV]]]]];
    witHyp = ASSUME[witInnerTm];
    (* (witHyp) ⊢ ∀i. (REP_list l i = NONE) ⇔ ¬(i < n_l) *)

    (* === Step 4: For arbitrary i, derive
              ⊢ (consF x l i = NONE) = ¬(i < SUC n_l) === *)
    numCasesAtI = HOL`Bool`SPEC[iV, HOL`Stdlib`Num`numCasesThm];
    (* ⊢ i = 0 ∨ ∃j. i = SUC j *)

    (* Sub-case i = 0. *)
    iEqZeroBranch = Module[{iEqZeroTm, iEqZeroHyp, consFAtZ,
                            consFAtZAti, lhsRewrite, lhsRewriteAtI,
                            someXEqNoneEqF, lhsEqF,
                            zeroLtSucNLAt, notNotZLtSucNL,
                            notZeroLtSucNLEqF, rhsAtI, rhsAtIeqF,
                            lhsEqRhs},
      iEqZeroTm = mkEq[iV, zeroConst[]];
      iEqZeroHyp = ASSUME[iEqZeroTm];
      consFAtZ = consFAtZeroThm[xTm, lTm];
      (* ⊢ consFXL 0 = SOME x *)

      (* Build (consFXL i = NONE) = (consFXL 0 = NONE) via APTHM+APTERM on i=0. *)
      lhsRewrite = HOL`Equal`APTHM[
        HOL`Equal`APTERM[eqC,
          HOL`Equal`APTERM[consFXL, iEqZeroHyp]],
        noneAt[αTy]];
      (* (i=0) ⊢ (consFXL i = NONE) = (consFXL 0 = NONE) *)
      (* Now (consFXL 0 = NONE) = (SOME x = NONE) via consFAtZ. *)
      lhsRewriteAtI = TRANS[lhsRewrite,
        HOL`Equal`APTHM[HOL`Equal`APTERM[eqC, consFAtZ], noneAt[αTy]]];
      (* (i=0) ⊢ (consFXL i = NONE) = (SOME x = NONE) *)
      someXEqNoneEqF = eqfIntroLocal[HOL`Bool`SPEC[xTm, someNotEqNoneThm]];
      (* ⊢ (SOME x = NONE) = F *)
      lhsEqF = TRANS[lhsRewriteAtI, someXEqNoneEqF];
      (* (i=0) ⊢ (consFXL i = NONE) = F *)

      (* RHS side: ¬(i < SUC n_l).  Under (i=0), this is ¬(0 < SUC n_l).
         ¬(0 < SUC n_l) = F via eqfIntro[¬¬(0 < SUC n_l)] which needs
         ¬¬(0 < SUC n_l). Build via notNotIntroLocal[0 < SUC n_l]. *)
      zeroLtSucNLAt = HOL`Bool`SPEC[nLV, zeroLtSucThm];
      (* ⊢ 0 < SUC n_l *)
      notNotZLtSucNL = notNotIntroLocal[zeroLtSucNLAt];
      (* ⊢ ¬¬(0 < SUC n_l) *)
      notZeroLtSucNLEqF = eqfIntroLocal[notNotZLtSucNL];
      (* ⊢ ¬(0 < SUC n_l) = F *)
      (* Build (¬(i < SUC n_l)) = (¬(0 < SUC n_l)) via i=0 rewrite. *)
      rhsAtI = HOL`Equal`APTERM[notC[],
        HOL`Equal`APTHM[
          HOL`Equal`APTERM[HOL`Stdlib`Num`ltConst[], iEqZeroHyp],
          sucTm[nLV]]];
      (* (i=0) ⊢ ¬(i < SUC n_l) = ¬(0 < SUC n_l) *)
      rhsAtIeqF = TRANS[rhsAtI, notZeroLtSucNLEqF];
      (* (i=0) ⊢ ¬(i < SUC n_l) = F *)

      lhsEqRhs = TRANS[lhsEqF, HOL`Equal`SYM[rhsAtIeqF]];
      (* (i=0) ⊢ (consFXL i = NONE) = ¬(i < SUC n_l) *)
      lhsEqRhs
    ];

    (* Sub-case ∃j. i = SUC j. *)
    iEqSucBranch = Module[{exJTm, exJHyp, iEqSucJTm, iEqSucJHyp,
                           consFAtS, lhsRewrite1, lhsRewrite2, lhsEqRepLj,
                           witHypAtJ, repLjEqNotLt,
                           rhsRewrite1, ltSucMCAtJN, rhsRewrite2,
                           rhsRewrite3, finalIff, choseJ},
      exJTm = mkComb[existsC[numTy],
        mkAbs[jBndV, mkEq[iV, sucTm[jBndV]]]];
      exJHyp = ASSUME[exJTm];
      iEqSucJTm = mkEq[iV, sucTm[jBndV]];
      iEqSucJHyp = ASSUME[iEqSucJTm];

      consFAtS = consFAtSucThm[xTm, lTm, jBndV];
      (* ⊢ consFXL (SUC jBnd) = REP_list l jBnd *)

      (* LHS rewrites:
         (consFXL i = NONE) → (consFXL (SUC jBnd) = NONE) via i=SUC jBnd.
         → (REP_list l jBnd = NONE) via consFAtS. *)
      lhsRewrite1 = HOL`Equal`APTHM[
        HOL`Equal`APTERM[eqC,
          HOL`Equal`APTERM[consFXL, iEqSucJHyp]],
        noneAt[αTy]];
      (* (i=SUC jBnd) ⊢ (consFXL i = NONE) = (consFXL (SUC jBnd) = NONE) *)
      lhsRewrite2 = HOL`Equal`APTHM[
        HOL`Equal`APTERM[eqC, consFAtS], noneAt[αTy]];
      (* ⊢ (consFXL (SUC jBnd) = NONE) = (REP_list l jBnd = NONE) *)
      lhsEqRepLj = TRANS[lhsRewrite1, lhsRewrite2];
      (* (i=SUC jBnd) ⊢ (consFXL i = NONE) = (REP_list l jBnd = NONE) *)

      witHypAtJ = HOL`Bool`SPEC[jBndV, witHyp];
      (* (witHyp) ⊢ (REP_list l jBnd = NONE) = ¬(jBnd < n_l) *)
      repLjEqNotLt = TRANS[lhsEqRepLj, witHypAtJ];
      (* (witHyp, i=SUC jBnd) ⊢ (consFXL i = NONE) = ¬(jBnd < n_l) *)

      (* RHS rewrites:
         ¬(i < SUC n_l) → ¬(SUC jBnd < SUC n_l) via i=SUC jBnd.
         → ¬(jBnd < n_l) via ltSucMonoCancel. *)
      rhsRewrite1 = HOL`Equal`APTERM[notC[],
        HOL`Equal`APTHM[
          HOL`Equal`APTERM[HOL`Stdlib`Num`ltConst[], iEqSucJHyp],
          sucTm[nLV]]];
      (* (i=SUC jBnd) ⊢ ¬(i < SUC n_l) = ¬(SUC jBnd < SUC n_l) *)
      ltSucMCAtJN = HOL`Bool`SPEC[nLV,
        HOL`Bool`SPEC[jBndV, ltSucMonoCancelThm]];
      (* ⊢ (SUC jBnd < SUC n_l) = (jBnd < n_l) *)
      rhsRewrite2 = HOL`Equal`APTERM[notC[], ltSucMCAtJN];
      (* ⊢ ¬(SUC jBnd < SUC n_l) = ¬(jBnd < n_l) *)
      rhsRewrite3 = TRANS[rhsRewrite1, rhsRewrite2];
      (* (i=SUC jBnd) ⊢ ¬(i < SUC n_l) = ¬(jBnd < n_l) *)

      finalIff = TRANS[repLjEqNotLt, HOL`Equal`SYM[rhsRewrite3]];
      (* (witHyp, i=SUC jBnd) ⊢ (consFXL i = NONE) = ¬(i < SUC n_l) *)
      choseJ = HOL`Bool`CHOOSE[jBndV, exJHyp, finalIff];
      (* (witHyp, ∃j. i=SUC j) ⊢ (consFXL i = NONE) = ¬(i < SUC n_l) *)
      choseJ
    ];

    perI = HOL`Bool`DISJCASES[numCasesAtI, iEqZeroBranch, iEqSucBranch];
    (* (witHyp) ⊢ (consFXL i = NONE) = ¬(i < SUC n_l) *)
    perIGenI = HOL`Bool`GEN[iV, perI];
    (* (witHyp) ⊢ ∀i. (consFXL i = NONE) = ¬(i < SUC n_l) *)

    (* === Step 5: EXISTS at SUC n_l === *)
    existsAtSucNL = HOL`Bool`EXISTS[
      mkComb[existsC[numTy], mkAbs[nLV,
        mkComb[forallC[numTy], mkAbs[iV,
          mkEq[mkEq[mkComb[consFXL, iV], noneAt[αTy]],
               mkComb[notC[], ltTmLocal[iV, nLV]]]]]]],
      sucTm[nLV], perIGenI];
    (* (witHyp) ⊢ ∃n. ∀i. (consFXL i = NONE) = ¬(i < n) *)

    (* CHOOSE n_l from the existsBodyThm: discharges witHyp. *)
    chosenNL = HOL`Bool`CHOOSE[nLV, existsBodyThm, existsAtSucNL];
    (* ⊢ ∃n. ∀i. (consFXL i = NONE) = ¬(i < n) *)

    (* === Step 6: fold back to isListPLambdaTerm[] (consFXL) === *)
    foldUnfold = BETACONV[mkComb[isListPLambdaTerm[], consFXL]];
    (* ⊢ isListPLambdaTerm[] (consFXL) = ∃n. ∀i. (consFXL i = NONE) = ¬(i < n) *)
    EQMP[HOL`Equal`SYM[foldUnfold], chosenNL]
    (* ⊢ isListPLambdaTerm[] (consFXL) *)
  ];

(* ============================================================ *)
(* repConsEqThm[x, l] — ⊢ REP_list (CONS x l) = consFTerm[x, l]   *)
(* Compose unfoldCons + repAbsListThm INST'd at consF.            *)
(* ============================================================ *)

repConsEqThm[xTm_, lTm_] :=
  Module[{unfold, consFXL, applyRep, isListPConsXL,
          repAbsAtConsF, eqREP},
    unfold = unfoldCons[xTm, lTm];
    (* ⊢ CONS x l = ABS_list (consFXL) *)
    consFXL = consFTerm[xTm, lTm];
    applyRep = HOL`Equal`APTERM[repListConst[], unfold];
    (* ⊢ REP_list (CONS x l) = REP_list (ABS_list consFXL) *)
    isListPConsXL = consCarrierIsListPThm[xTm, lTm];
    (* ⊢ isListPLambdaTerm[] (consFXL) *)
    repAbsAtConsF = HOL`Kernel`INST[
      {mkVar["r", carrierTy] -> consFXL}, repAbsListThm];
    (* ⊢ isListPLambdaTerm[] consFXL = (REP_list (ABS_list consFXL) = consFXL) *)
    eqREP = EQMP[repAbsAtConsF, isListPConsXL];
    (* ⊢ REP_list (ABS_list consFXL) = consFXL *)
    TRANS[applyRep, eqREP]
    (* ⊢ REP_list (CONS x l) = consFXL *)
  ];

(* ============================================================ *)
(* repConsHeadThm : ⊢ REP_list (CONS x l) 0 = SOME x             *)
(* repConsTailThm : ⊢ ∀i. REP_list (CONS x l) (SUC i) = REP_list l i *)
(*                                                              *)
(* Free x, l (and i for tail). APTHM repConsEqThm at the index +  *)
(* compose with consFAtZero/SucThm.                               *)
(* ============================================================ *)

repConsHeadThm =
  Module[{xV, lV, repEq, applyZero, consFAtZ},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listTy[αTy]];
    repEq = repConsEqThm[xV, lV];
    (* ⊢ REP_list (CONS x l) = consFTerm[x, l] *)
    applyZero = HOL`Equal`APTHM[repEq, zeroConst[]];
    (* ⊢ REP_list (CONS x l) 0 = consFTerm[x, l] 0 *)
    consFAtZ = consFAtZeroThm[xV, lV];
    (* ⊢ consFTerm[x, l] 0 = SOME x *)
    TRANS[applyZero, consFAtZ]
    (* ⊢ REP_list (CONS x l) 0 = SOME x *)
  ];

repConsTailThm =
  Module[{xV, lV, iV, repEq, applySucI, consFAtS, perI, genI},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listTy[αTy]];
    iV = mkVar["i", numTy];
    repEq = repConsEqThm[xV, lV];
    applySucI = HOL`Equal`APTHM[repEq, sucTm[iV]];
    (* ⊢ REP_list (CONS x l) (SUC i) = consFTerm[x, l] (SUC i) *)
    consFAtS = consFAtSucThm[xV, lV, iV];
    (* ⊢ consFTerm[x, l] (SUC i) = REP_list l i *)
    perI = TRANS[applySucI, consFAtS];
    (* ⊢ REP_list (CONS x l) (SUC i) = REP_list l i *)
    genI = HOL`Bool`GEN[iV, perI]
  ];

(* ============================================================ *)
(* CONS injectivity                                              *)
(*   ⊢ ∀x xP l lP. CONS x l = CONS xP lP ⇒ x = xP ∧ l = lP        *)
(*                                                              *)
(* APTERM REP_list both sides.                                    *)
(*   At index 0: repConsHead gives SOME x and SOME xP, then       *)
(*               someInj gives x = xP.                            *)
(*   At index SUC i (any i): repConsTail gives                    *)
(*               REP_list l i = REP_list l' i.                    *)
(*               GEN i; funcExt via ABS + etaAx → REP_list l =    *)
(*               REP_list l'. APTERM ABS_list + absRepListThm     *)
(*               twice → l = l'.                                  *)
(* ============================================================ *)

consInjThm =
  Module[{xV, xpV, lV, lpV, iV, consXL, consXpLp,
          hypTm, hypAssum, applyRep,
          atZero, repConsHeadAtXL, repConsHeadAtXpLp, someXEqSomeXp,
          someInjAtXXp, xEqXp,
          atSucI, repConsTailAtXL, repConsTailAtXpLp, repLEqRepLpAtI,
          genI, specI, absI, etaAtRepL, etaAtRepLp, repLEqRepLp,
          applyAbsList, absRepAtL, absRepAtLp, lEqLp,
          conjResult, dischHyp, genLp, genL, genXp, genX},
    xV = mkVar["x", αTy];
    xpV = mkVar["xP", αTy];
    lV = mkVar["l", listTy[αTy]];
    lpV = mkVar["lP", listTy[αTy]];
    iV = mkVar["i", numTy];

    consXL = mkComb[mkComb[consConst[], xV], lV];
    consXpLp = mkComb[mkComb[consConst[], xpV], lpV];
    hypTm = mkEq[consXL, consXpLp];
    hypAssum = ASSUME[hypTm];
    applyRep = HOL`Equal`APTERM[repListConst[], hypAssum];
    (* (hyp) ⊢ REP_list (CONS x l) = REP_list (CONS xP lP) *)

    (* === x = xP === *)
    atZero = HOL`Equal`APTHM[applyRep, zeroConst[]];
    repConsHeadAtXL = repConsHeadThm;
    (* ⊢ REP_list (CONS x l) 0 = SOME x — already at xV, lV *)
    repConsHeadAtXpLp = HOL`Kernel`INST[
      {mkVar["x", αTy] -> xpV, mkVar["l", listTy[αTy]] -> lpV},
      repConsHeadThm];
    (* ⊢ REP_list (CONS xP lP) 0 = SOME xP *)
    someXEqSomeXp = TRANS[TRANS[HOL`Equal`SYM[repConsHeadAtXL], atZero],
                          repConsHeadAtXpLp];
    (* (hyp) ⊢ SOME x = SOME xP *)
    someInjAtXXp = HOL`Stdlib`Option`someInjThm;
    (* ⊢ (SOME x = SOME xP) ⇒ (x = xP) — Option's names match *)
    xEqXp = HOL`Bool`MP[someInjAtXXp, someXEqSomeXp];
    (* (hyp) ⊢ x = xP *)

    (* === l = lP via per-i + funcExt === *)
    atSucI = HOL`Equal`APTHM[applyRep, sucTm[iV]];
    repConsTailAtXL = HOL`Bool`SPEC[iV, repConsTailThm];
    (* ⊢ REP_list (CONS x l) (SUC i) = REP_list l i *)
    repConsTailAtXpLp = HOL`Bool`SPEC[iV, HOL`Kernel`INST[
      {mkVar["x", αTy] -> xpV, mkVar["l", listTy[αTy]] -> lpV},
      repConsTailThm]];
    (* ⊢ REP_list (CONS xP lP) (SUC i) = REP_list lP i *)
    repLEqRepLpAtI = TRANS[TRANS[HOL`Equal`SYM[repConsTailAtXL], atSucI],
                            repConsTailAtXpLp];
    (* (hyp) ⊢ REP_list l i = REP_list lP i *)
    genI = HOL`Bool`GEN[iV, repLEqRepLpAtI];
    (* (hyp) ⊢ ∀i. REP_list l i = REP_list lP i *)

    (* funcExt step: from genI derive REP_list l = REP_list lP. *)
    specI = HOL`Bool`SPEC[iV, genI];
    (* (hyp) ⊢ REP_list l i = REP_list lP i *)
    absI = HOL`Kernel`ABS[iV, specI];
    (* (hyp) ⊢ (λi. REP_list l i) = (λi. REP_list lP i) *)
    etaAtRepL = HOL`Bool`ISPEC[
      mkComb[repListConst[], lV], HOL`Bootstrap`etaAx];
    (* ⊢ (λx. REP_list l x) = REP_list l *)
    etaAtRepLp = HOL`Bool`ISPEC[
      mkComb[repListConst[], lpV], HOL`Bootstrap`etaAx];
    repLEqRepLp = TRANS[TRANS[HOL`Equal`SYM[etaAtRepL], absI], etaAtRepLp];
    (* (hyp) ⊢ REP_list l = REP_list lP *)

    applyAbsList = HOL`Equal`APTERM[absListConst[], repLEqRepLp];
    (* (hyp) ⊢ ABS_list (REP_list l) = ABS_list (REP_list lP) *)
    absRepAtL = HOL`Kernel`INST[
      {mkVar["a", listTy[αTy]] -> lV}, absRepListThm];
    absRepAtLp = HOL`Kernel`INST[
      {mkVar["a", listTy[αTy]] -> lpV}, absRepListThm];
    lEqLp = TRANS[TRANS[HOL`Equal`SYM[absRepAtL], applyAbsList], absRepAtLp];
    (* (hyp) ⊢ l = lP *)

    conjResult = HOL`Bool`CONJ[xEqXp, lEqLp];
    dischHyp = HOL`Bool`DISCH[hypTm, conjResult];
    genLp = HOL`Bool`GEN[lpV, dischHyp];
    genL = HOL`Bool`GEN[lV, genLp];
    genXp = HOL`Bool`GEN[xpV, genL];
    genX = HOL`Bool`GEN[xV, genXp]
  ];

(* ============================================================ *)
(* NIL ≠ CONS disjointness                                       *)
(*   ⊢ ∀x l. ¬(NIL = CONS x l)                                   *)
(*                                                              *)
(* APTERM REP_list, APTHM at 0:                                   *)
(*   repNilThm + BETA: REP_list NIL 0 = NONE.                     *)
(*   repConsHead: REP_list (CONS x l) 0 = SOME x.                 *)
(*   TRANS chain: NONE = SOME x.                                  *)
(* noneNotEqSomeThm: ¬(NONE = SOME x). Contradiction.             *)
(* DISCH + NOTINTRO + GEN.                                        *)
(* ============================================================ *)

nilNotEqConsThm =
  Module[{xV, lV, consXL, hypTm, hypAssum, applyRep, atZero,
          repNilAt0Beta, repNilAt0, repConsHeadAt,
          noneEqSomeX, noneNotEqAt, contradF, dischHyp, notEq, genL, genX},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listTy[αTy]];
    consXL = mkComb[mkComb[consConst[], xV], lV];

    hypTm = mkEq[nilConst[], consXL];
    hypAssum = ASSUME[hypTm];
    applyRep = HOL`Equal`APTERM[repListConst[], hypAssum];
    (* (NIL = CONS x l) ⊢ REP_list NIL = REP_list (CONS x l) *)
    atZero = HOL`Equal`APTHM[applyRep, zeroConst[]];
    (* (...) ⊢ REP_list NIL 0 = REP_list (CONS x l) 0 *)

    (* REP_list NIL 0 = NONE via repNilThm + BETACONV. *)
    repNilAt0Beta = HOL`Equal`APTHM[repNilThm, zeroConst[]];
    (* ⊢ REP_list NIL 0 = (λi. NONE) 0 *)
    repNilAt0 = TRANS[repNilAt0Beta,
      BETACONV[concl[repNilAt0Beta][[2]]]];
    (* ⊢ REP_list NIL 0 = NONE *)

    (* REP_list (CONS x l) 0 = SOME x (already at xV, lV). *)
    repConsHeadAt = repConsHeadThm;
    (* ⊢ REP_list (CONS x l) 0 = SOME x *)

    noneEqSomeX = TRANS[TRANS[HOL`Equal`SYM[repNilAt0], atZero],
                        repConsHeadAt];
    (* (NIL = CONS x l) ⊢ NONE = SOME x *)

    noneNotEqAt = HOL`Stdlib`Option`noneNotEqSomeThm;
    (* ⊢ ¬(NONE = SOME x) — already at xV *)
    contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[noneNotEqAt], noneEqSomeX];
    (* (NIL = CONS x l) ⊢ F *)
    dischHyp = HOL`Bool`DISCH[hypTm, contradF];
    notEq = HOL`Bool`NOTINTRO[dischHyp];
    (* ⊢ ¬(NIL = CONS x l) *)
    genL = HOL`Bool`GEN[lV, notEq];
    genX = HOL`Bool`GEN[xV, genL]
  ];

(* ============================================================ *)
(* M7-4-a.5: Option case analysis + tail/shift toolkit            *)
(*           preparing M7-4-a.6 list induction.                   *)
(* ============================================================ *)

(* ============================================================ *)
(* optionCasesThm : ⊢ ∀y. y = NONE ∨ ∃x. y = SOME x               *)
(*                                                              *)
(* Build isOption (REP_option y) via the standard REP-roundtrip   *)
(* argument; BETACONV unfolds to (REP y = mkNone) ∨ (∃x. REP y =  *)
(* mkSome x). DISJCASES converts each disjunct into the y-form    *)
(* via APTERM ABS_option + absRepOptionThm and the noneDefThm /    *)
(* someDefThm bridges.                                            *)
(* ============================================================ *)

optionCasesThm =
  Module[{yV, optAlphaTy, repC, absC, mkNoneC, mkSomeC,
          carrierTyOpt, absRepAtY,
          applyRepY, repAbsAtRepY, isOptForRepY, isOptUnfold,
          disjThm,
          leftBranch, rightBranch, mergedDisj, genY,
          existsTargetTm, leftDisjShape, rightDisjShape},
    optAlphaTy = HOL`Stdlib`Option`optionTy[αTy];
    yV = mkVar["y", optAlphaTy];
    repC = HOL`Stdlib`Option`repOptionConst[];
    absC = HOL`Stdlib`Option`absOptionConst[];
    mkNoneC = HOL`Stdlib`Option`mkNoneConst[];
    mkSomeC = HOL`Stdlib`Option`mkSomeConst[];
    carrierTyOpt = tyFun[αTy, boolTy];

    (* ⊢ isOption (REP_option y) — same trick as isListPOfRepList. *)
    absRepAtY = HOL`Kernel`INST[
      {mkVar["a", optAlphaTy] -> yV},
      HOL`Stdlib`Option`absRepOptionThm];
    (* ⊢ ABS_option (REP_option y) = y *)
    applyRepY = HOL`Equal`APTERM[repC, absRepAtY];
    (* ⊢ REP_option (ABS_option (REP_option y)) = REP_option y *)
    repAbsAtRepY = HOL`Kernel`INST[
      {mkVar["r", carrierTyOpt] -> mkComb[repC, yV]},
      HOL`Stdlib`Option`repAbsOptionThm];
    (* ⊢ isOption (REP_option y) =
         (REP_option (ABS_option (REP_option y)) = REP_option y) *)
    isOptForRepY = EQMP[HOL`Equal`SYM[repAbsAtRepY], applyRepY];
    (* ⊢ isOption (REP_option y) — predicate applied form *)

    isOptUnfold = BETACONV[
      mkComb[HOL`Stdlib`Option`isOptionPredicate[], mkComb[repC, yV]]];
    (* ⊢ isOption (REP_option y) = (REP_option y = mkNone)
                                   ∨ (∃x. REP_option y = mkSome x) *)
    disjThm = EQMP[isOptUnfold, isOptForRepY];
    (* ⊢ (REP_option y = mkNone) ∨ (∃x. REP_option y = mkSome x) *)

    (* Target shapes for both disjuncts of the final disjunction. *)
    existsTargetTm = mkComb[existsC[αTy],
      mkAbs[mkVar["x", αTy],
        mkEq[yV, mkComb[HOL`Stdlib`Option`someConst[], mkVar["x", αTy]]]]];
    leftDisjShape = mkEq[yV, HOL`Stdlib`Option`noneConst[]];
    rightDisjShape = existsTargetTm;

    (* Left branch: REP_option y = mkNone ⇒ y = NONE. *)
    leftBranch = Module[{leftHyp, leftHypAssum, absLeft, noneDefSym,
                         yEqNoneStep, yEqNone, disj1},
      leftHyp = mkEq[mkComb[repC, yV], mkNoneC];
      leftHypAssum = ASSUME[leftHyp];
      absLeft = HOL`Equal`APTERM[absC, leftHypAssum];
      (* (...) ⊢ ABS_option (REP_option y) = ABS_option mkNone *)
      noneDefSym = HOL`Equal`SYM[HOL`Stdlib`Option`noneDefThm];
      (* ⊢ ABS_option mkNone = NONE *)
      yEqNoneStep = TRANS[absLeft, noneDefSym];
      (* (REP_option y = mkNone) ⊢ ABS_option (REP_option y) = NONE *)
      yEqNone = TRANS[HOL`Equal`SYM[absRepAtY], yEqNoneStep];
      (* (REP_option y = mkNone) ⊢ y = NONE *)
      disj1 = HOL`Bool`DISJ1[yEqNone, rightDisjShape];
      disj1
    ];

    (* Right branch: ∃x. REP_option y = mkSome x ⇒ ∃x. y = SOME x. *)
    rightBranch = Module[{xV, xHyp, xHypTm, xHypAssum, exRepHyp, exRepHypAssum,
                          absRight, someDefAtX, someDefAtXBeta, ySomeEq,
                          existsYSome, choseX, disj2},
      xV = mkVar["x", αTy];
      xHypTm = mkEq[mkComb[repC, yV], mkComb[mkSomeC, xV]];
      xHypAssum = ASSUME[xHypTm];
      exRepHyp = mkComb[existsC[αTy],
        mkAbs[xV, mkEq[mkComb[repC, yV], mkComb[mkSomeC, xV]]]];
      exRepHypAssum = ASSUME[exRepHyp];

      absRight = HOL`Equal`APTERM[absC, xHypAssum];
      (* (REP_option y = mkSome x) ⊢ ABS_option (REP_option y)
                                       = ABS_option (mkSome x) *)
      (* someDefThm: ⊢ SOME = (λx. ABS_option (mkSome x)).
         APTHM + BETACONV → ⊢ SOME x = ABS_option (mkSome x). *)
      someDefAtX = HOL`Equal`APTHM[HOL`Stdlib`Option`someDefThm, xV];
      someDefAtXBeta = TRANS[someDefAtX, BETACONV[concl[someDefAtX][[2]]]];
      (* ⊢ SOME x = ABS_option (mkSome x) *)
      ySomeEq = TRANS[HOL`Equal`SYM[absRepAtY],
                      TRANS[absRight, HOL`Equal`SYM[someDefAtXBeta]]];
      (* (REP_option y = mkSome x) ⊢ y = SOME x *)
      existsYSome = HOL`Bool`EXISTS[existsTargetTm, xV, ySomeEq];
      (* (REP_option y = mkSome x) ⊢ ∃x. y = SOME x *)
      choseX = HOL`Bool`CHOOSE[xV, exRepHypAssum, existsYSome];
      (* (∃x. REP_option y = mkSome x) ⊢ ∃x. y = SOME x *)
      disj2 = HOL`Bool`DISJ2[choseX, leftDisjShape];
      disj2
    ];

    mergedDisj = HOL`Bool`DISJCASES[disjThm, leftBranch, rightBranch];
    (* ⊢ (y = NONE) ∨ (∃x. y = SOME x) *)
    genY = HOL`Bool`GEN[yV, mergedDisj]
  ];

(* ============================================================ *)
(* notNoneImpliesSome[thNotNone] : Γ ⊢ ¬(y = NONE) → Γ ⊢ ∃x. y = SOME x *)
(* SPEC optionCasesThm at y; DISJCASES with the NONE-case        *)
(* contradicting via NOTELIM + MP.                                *)
(* ============================================================ *)

notNoneImpliesSome[thNotNone_] :=
  Module[{notNoneTm, yTm, casesAtY, leftCase, rightCase, choseDisj,
          existsTarget, xV},
    notNoneTm = concl[thNotNone];   (* shape: ¬(y = NONE) *)
    (* notNoneTm = comb[¬, comb[comb[=, y], NONE]] *)
    yTm = notNoneTm[[2, 1, 2]];     (* extract y *)
    xV = mkVar["x", αTy];
    existsTarget = mkComb[existsC[αTy],
      mkAbs[xV,
        mkEq[yTm, mkComb[HOL`Stdlib`Option`someConst[], xV]]]];
    casesAtY = HOL`Bool`SPEC[yTm, optionCasesThm];
    (* ⊢ y = NONE ∨ ∃x. y = SOME x *)

    leftCase = Module[{yEqNoneHyp, contradF},
      yEqNoneHyp = ASSUME[mkEq[yTm, HOL`Stdlib`Option`noneConst[]]];
      contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotNone], yEqNoneHyp];
      HOL`Bool`CONTR[existsTarget, contradF]
    ];

    rightCase = Module[{exYSomeHyp},
      exYSomeHyp = ASSUME[existsTarget];
      exYSomeHyp
    ];

    HOL`Bool`DISJCASES[casesAtY, leftCase, rightCase]
    (* (Γ_thNotNone) ⊢ ∃x. y = SOME x *)
  ];

(* ============================================================ *)
(* shiftedFn / tailFnOf — Wolfram term builders                  *)
(* ============================================================ *)

shiftedFn[lTm_] :=
  Module[{jShV},
    jShV = mkVar["jShift", numTy];
    mkAbs[jShV, mkComb[mkComb[repListConst[], lTm], sucTm[jShV]]]
  ];

tailFnOf[lTm_] := mkComb[absListConst[], shiftedFn[lTm]];

headTermOf[lTm_] :=
  Module[{xHV},
    xHV = mkVar["xHead", αTy];
    mkComb[selectC[αTy], mkAbs[xHV,
      mkEq[mkComb[mkComb[repListConst[], lTm], zeroConst[]],
           mkComb[someAt[αTy], xHV]]]]
  ];

(* ============================================================ *)
(* shiftedIsListPThm — isListP for the shifted function           *)
(* ============================================================ *)

shiftedIsListPThm[lTm_, nPrimeTm_, witHypThm_] :=
  Module[{shfFn, iV, nV, eqC, shfFnAtI, witAtSucI,
          ltSucMCAt, notLtSucMC, witAtSucI2,
          lhsEqMid, iffThm, genIThm,
          existsTm, existsAt, foldUnfold},
    shfFn = shiftedFn[lTm];
    iV = mkVar["i", numTy];
    nV = mkVar["n", numTy];
    eqC = mkConst["=", tyFun[optionATy, tyFun[optionATy, boolTy]]];

    shfFnAtI = BETACONV[mkComb[shfFn, iV]];
    (* ⊢ shfFn i = REP_list lTm (SUC i) *)
    witAtSucI = HOL`Bool`SPEC[sucTm[iV], witHypThm];
    (* (witHyp) ⊢ (REP_list lTm (SUC i) = NONE) = ¬(SUC i < SUC n') *)
    ltSucMCAt = HOL`Bool`SPEC[nPrimeTm,
      HOL`Bool`SPEC[iV, ltSucMonoCancelThm]];
    (* ⊢ (SUC i < SUC n') = (i < n') *)
    notLtSucMC = HOL`Equal`APTERM[notC[], ltSucMCAt];
    (* ⊢ ¬(SUC i < SUC n') = ¬(i < n') *)
    witAtSucI2 = TRANS[witAtSucI, notLtSucMC];
    (* (witHyp) ⊢ (REP_list lTm (SUC i) = NONE) = ¬(i < n') *)

    lhsEqMid = HOL`Equal`APTHM[
      HOL`Equal`APTERM[eqC, shfFnAtI], noneAt[αTy]];
    (* ⊢ (shfFn i = NONE) = (REP_list lTm (SUC i) = NONE) *)
    iffThm = TRANS[lhsEqMid, witAtSucI2];
    (* (witHyp) ⊢ (shfFn i = NONE) = ¬(i < n') *)
    genIThm = HOL`Bool`GEN[iV, iffThm];
    (* (witHyp) ⊢ ∀i. (shfFn i = NONE) = ¬(i < n') *)

    existsTm = mkComb[existsC[numTy], mkAbs[nV,
      mkComb[forallC[numTy], mkAbs[iV,
        mkEq[mkEq[mkComb[shfFn, iV], noneAt[αTy]],
             mkComb[notC[], ltTmLocal[iV, nV]]]]]]];
    existsAt = HOL`Bool`EXISTS[existsTm, nPrimeTm, genIThm];
    (* (witHyp) ⊢ ∃n. ∀i. (shfFn i = NONE) = ¬(i < n) *)
    foldUnfold = BETACONV[mkComb[isListPLambdaTerm[], shfFn]];
    EQMP[HOL`Equal`SYM[foldUnfold], existsAt]
    (* (witHyp) ⊢ isListPLambda shfFn *)
  ];

(* ============================================================ *)
(* repTailEqShiftedThm — ⊢ REP_list (tailFnOf l) = shiftedFn[l]   *)
(* via repAbsListThm INST'd at shiftedFn[l]                       *)
(* ============================================================ *)

repTailEqShiftedThm[lTm_, nPrimeTm_, witHypThm_] :=
  Module[{shfFn, isListPshfFn, repAbsAtShfFn},
    shfFn = shiftedFn[lTm];
    isListPshfFn = shiftedIsListPThm[lTm, nPrimeTm, witHypThm];
    repAbsAtShfFn = HOL`Kernel`INST[
      {mkVar["r", carrierTy] -> shfFn}, repAbsListThm];
    (* ⊢ isListPLambda shfFn = (REP_list (ABS_list shfFn) = shfFn) *)
    EQMP[repAbsAtShfFn, isListPshfFn]
    (* (witHyp) ⊢ REP_list (tailFnOf[l]) = shiftedFn[l] *)
  ];

(* ============================================================ *)
(* tailLengthThm — ⊢ ∀i. REP_list (tail l) i = NONE ⇔ ¬(i < n')  *)
(* The "length n' witness" for the tail, IH-ready.                *)
(* ============================================================ *)

tailLengthThm[lTm_, nPrimeTm_, witHypThm_] :=
  Module[{shfFn, iV, repTailEq, shfFnAtI, repTailAtI,
          witAtSucI, ltSucMCAt, notLtSucMC, witAtSucI2,
          eqC, lhsEqMid, iffThm, genIThm},
    shfFn = shiftedFn[lTm];
    iV = mkVar["i", numTy];
    eqC = mkConst["=", tyFun[optionATy, tyFun[optionATy, boolTy]]];

    repTailEq = repTailEqShiftedThm[lTm, nPrimeTm, witHypThm];
    (* (witHyp) ⊢ REP_list (tailFnOf l) = shiftedFn[l] *)

    (* REP_list (tail l) i = shfFn i via APTHM at i. *)
    repTailAtI = HOL`Equal`APTHM[repTailEq, iV];
    (* (witHyp) ⊢ REP_list (tailFnOf l) i = shfFn i *)
    shfFnAtI = BETACONV[mkComb[shfFn, iV]];
    (* ⊢ shfFn i = REP_list lTm (SUC i) *)

    witAtSucI = HOL`Bool`SPEC[sucTm[iV], witHypThm];
    ltSucMCAt = HOL`Bool`SPEC[nPrimeTm,
      HOL`Bool`SPEC[iV, ltSucMonoCancelThm]];
    notLtSucMC = HOL`Equal`APTERM[notC[], ltSucMCAt];
    witAtSucI2 = TRANS[witAtSucI, notLtSucMC];
    (* (witHyp) ⊢ (REP_list lTm (SUC i) = NONE) = ¬(i < n') *)

    (* (REP_list tail l i = NONE) = (shfFn i = NONE) via repTailAtI. *)
    lhsEqMid = HOL`Equal`APTHM[
      HOL`Equal`APTERM[eqC, TRANS[repTailAtI, shfFnAtI]], noneAt[αTy]];
    (* (witHyp) ⊢ (REP_list (tailFnOf l) i = NONE)
                  = (REP_list lTm (SUC i) = NONE) *)
    iffThm = TRANS[lhsEqMid, witAtSucI2];
    (* (witHyp) ⊢ (REP_list (tailFnOf l) i = NONE) = ¬(i < n') *)
    genIThm = HOL`Bool`GEN[iV, iffThm]
    (* (witHyp) ⊢ ∀i. (REP_list (tailFnOf l) i = NONE) = ¬(i < n') *)
  ];

(* ============================================================ *)
(* consHeadTailEqLThm — ⊢ CONS (headTermOf l) (tailFnOf l) = l    *)
(*                                                              *)
(* Strategy: derive REP_list (CONS h tail) = REP_list l per index *)
(* via numCases, then funcExt + ABS_list both sides + absRep.     *)
(* ============================================================ *)

consHeadTailEqLThm[lTm_, nPrimeTm_, witHypThm_] :=
  Module[{iV, jShV, nV, hTm, tailTm,
          eqC, witAt0, zeroLtSucNL, repListLAt0NotNone,
          existsSome, atSelect, repL0EqSomeH,
          consHTl, repCHT, repCHTAt0, repCHTAtSucJ,
          shfFn, shfFnAtJ, repTailEq, repTailAtJ,
          repCHTAtSucJ2, repLAtSucJ, perIeq, perI,
          numCasesAtI, iEqZeroBranch, iEqSucBranch, perIThm,
          genIThm, specI, absI, etaAtRepCHT, etaAtRepL,
          repCHTEqRepL, applyAbs, absRepAtCHT, absRepAtL2,
          finalEq},
    iV = mkVar["i", numTy];
    jShV = mkVar["jShift", numTy];
    nV = mkVar["n", numTy];
    eqC = mkConst["=", tyFun[optionATy, tyFun[optionATy, boolTy]]];

    hTm = headTermOf[lTm];
    tailTm = tailFnOf[lTm];
    consHTl = mkComb[mkComb[consConst[], hTm], tailTm];

    (* === Derive ⊢ REP_list l 0 = SOME h via notNoneImpliesSome. === *)
    witAt0 = HOL`Bool`SPEC[zeroConst[], witHypThm];
    (* (witHyp) ⊢ (REP_list l 0 = NONE) = ¬(0 < SUC n') *)
    zeroLtSucNL = HOL`Bool`SPEC[nPrimeTm, zeroLtSucThm];
    (* ⊢ 0 < SUC n' *)
    repListLAt0NotNone = Module[{nnIntro, eqfNotLt, eqfSym, repListEqNoneEqF,
                                  repNeqNone},
      nnIntro = notNotIntroLocal[zeroLtSucNL];
      (* ⊢ ¬¬(0 < SUC n') *)
      eqfNotLt = eqfIntroLocal[nnIntro];
      (* ⊢ ¬(0 < SUC n') = F *)
      repListEqNoneEqF = TRANS[witAt0, eqfNotLt];
      (* (witHyp) ⊢ (REP_list l 0 = NONE) = F *)
      (* From p = F, derive ¬p. *)
      Module[{pEqFHyp, pHyp, fThm, dischp},
        pHyp = ASSUME[mkEq[mkComb[mkComb[repListConst[], lTm], zeroConst[]],
                           noneAt[αTy]]];
        fThm = EQMP[repListEqNoneEqF, pHyp];
        (* (witHyp, REP l 0 = NONE) ⊢ F *)
        dischp = HOL`Bool`DISCH[
          mkEq[mkComb[mkComb[repListConst[], lTm], zeroConst[]],
               noneAt[αTy]], fThm];
        HOL`Bool`NOTINTRO[dischp]
        (* (witHyp) ⊢ ¬(REP_list l 0 = NONE) *)
      ]
    ];

    existsSome = notNoneImpliesSome[repListLAt0NotNone];
    (* (witHyp) ⊢ ∃x. REP_list l 0 = SOME x *)

    (* selectOfExists: gives REP_list l 0 = SOME (@x. ...).
       The @x term = headTermOf l. *)
    atSelect = HOL`Stdlib`Num`selectOfExists[
      mkAbs[mkVar["xHead", αTy],
        mkEq[mkComb[mkComb[repListConst[], lTm], zeroConst[]],
             mkComb[someAt[αTy], mkVar["xHead", αTy]]]],
      existsSome];
    (* (witHyp) ⊢ REP_list l 0 = SOME (headTermOf l) *)
    repL0EqSomeH = atSelect;

    (* === Per-index proof: REP_list (CONS h tail) i = REP_list l i. === *)
    (* numCases on i. *)
    numCasesAtI = HOL`Bool`SPEC[iV, HOL`Stdlib`Num`numCasesThm];

    (* Case i = 0:
       REP_list (CONS h tail) 0 = SOME h (repConsHead INST'd).
       REP_list l 0 = SOME h (atSelect).
       Hence equal. *)
    iEqZeroBranch = Module[{iEqZeroHyp, applyZeroL, applyZeroR,
                            repCHAtZero, equation},
      iEqZeroHyp = ASSUME[mkEq[iV, zeroConst[]]];
      (* (i=0) ⊢ i = 0 *)
      repCHAtZero = HOL`Kernel`INST[
        {mkVar["x", αTy] -> hTm, mkVar["l", listTy[αTy]] -> tailTm},
        repConsHeadThm];
      (* ⊢ REP_list (CONS h tail) 0 = SOME h *)
      applyZeroL = HOL`Equal`APTERM[
        mkComb[repListConst[], consHTl], iEqZeroHyp];
      (* (i=0) ⊢ REP_list (CONS h tail) i = REP_list (CONS h tail) 0 *)
      applyZeroR = HOL`Equal`APTERM[
        mkComb[repListConst[], lTm], iEqZeroHyp];
      (* (i=0) ⊢ REP_list l i = REP_list l 0 *)
      equation = TRANS[applyZeroL,
        TRANS[repCHAtZero,
          TRANS[HOL`Equal`SYM[repL0EqSomeH],
            HOL`Equal`SYM[applyZeroR]]]];
      (* (witHyp, i=0) ⊢ REP_list (CONS h tail) i = REP_list l i *)
      equation
    ];

    (* Case ∃j. i = SUC j:
       REP_list (CONS h tail) (SUC j) = REP_list tail j = shfFn j
         = REP_list l (SUC j) = REP_list l i. *)
    iEqSucBranch = Module[{exJTm, exJHyp, iEqSucJ, iEqSucJHyp,
                           repConsTailAt, repCSAt,
                           repTailEq, repTailAtJ, shfAtJ,
                           applySucL, applySucR, equation, choseJ, jBindV},
      jBindV = mkVar["jBnd2", numTy];
      exJTm = mkComb[existsC[numTy], mkAbs[jBindV, mkEq[iV, sucTm[jBindV]]]];
      exJHyp = ASSUME[exJTm];
      iEqSucJ = mkEq[iV, sucTm[jBindV]];
      iEqSucJHyp = ASSUME[iEqSucJ];

      repConsTailAt = HOL`Bool`SPEC[jBindV, HOL`Kernel`INST[
        {mkVar["x", αTy] -> hTm, mkVar["l", listTy[αTy]] -> tailTm},
        repConsTailThm]];
      (* ⊢ REP_list (CONS h tail) (SUC jBnd2) = REP_list tail jBnd2 *)
      repTailEq = repTailEqShiftedThm[lTm, nPrimeTm, witHypThm];
      (* (witHyp) ⊢ REP_list (tailFnOf l) = shiftedFn[l] *)
      repTailAtJ = HOL`Equal`APTHM[repTailEq, jBindV];
      (* (witHyp) ⊢ REP_list tail jBnd2 = shfFn jBnd2 *)
      shfAtJ = BETACONV[mkComb[shiftedFn[lTm], jBindV]];
      (* ⊢ shfFn jBnd2 = REP_list l (SUC jBnd2) *)

      applySucL = HOL`Equal`APTERM[
        mkComb[repListConst[], consHTl], iEqSucJHyp];
      (* (i=SUC jBnd2) ⊢ REP_list (CONS h tail) i
                          = REP_list (CONS h tail) (SUC jBnd2) *)
      applySucR = HOL`Equal`APTERM[
        mkComb[repListConst[], lTm], iEqSucJHyp];
      (* (i=SUC jBnd2) ⊢ REP_list l i = REP_list l (SUC jBnd2) *)
      equation = TRANS[applySucL,
        TRANS[repConsTailAt,
          TRANS[repTailAtJ,
            TRANS[shfAtJ, HOL`Equal`SYM[applySucR]]]]];
      (* (witHyp, i=SUC jBnd2) ⊢ REP_list (CONS h tail) i = REP_list l i *)
      choseJ = HOL`Bool`CHOOSE[jBindV, exJHyp, equation];
      (* (witHyp, ∃j. i=SUC j) ⊢ REP_list (CONS h tail) i = REP_list l i *)
      choseJ
    ];

    perIThm = HOL`Bool`DISJCASES[numCasesAtI, iEqZeroBranch, iEqSucBranch];
    (* (witHyp) ⊢ REP_list (CONS h tail) i = REP_list l i *)
    genIThm = HOL`Bool`GEN[iV, perIThm];
    (* (witHyp) ⊢ ∀i. REP_list (CONS h tail) i = REP_list l i *)

    (* funcExt: REP_list (CONS h tail) = REP_list l. *)
    specI = HOL`Bool`SPEC[iV, genIThm];
    absI = HOL`Kernel`ABS[iV, specI];
    (* (witHyp) ⊢ (λi. REP_list (CONS h tail) i) = (λi. REP_list l i) *)
    etaAtRepCHT = HOL`Bool`ISPEC[
      mkComb[repListConst[], consHTl], HOL`Bootstrap`etaAx];
    etaAtRepL = HOL`Bool`ISPEC[
      mkComb[repListConst[], lTm], HOL`Bootstrap`etaAx];
    repCHTEqRepL = TRANS[
      TRANS[HOL`Equal`SYM[etaAtRepCHT], absI], etaAtRepL];
    (* (witHyp) ⊢ REP_list (CONS h tail) = REP_list l *)

    applyAbs = HOL`Equal`APTERM[absListConst[], repCHTEqRepL];
    (* (witHyp) ⊢ ABS_list (REP_list (CONS h tail)) = ABS_list (REP_list l) *)
    absRepAtCHT = HOL`Kernel`INST[
      {mkVar["a", listTy[αTy]] -> consHTl}, absRepListThm];
    absRepAtL2 = HOL`Kernel`INST[
      {mkVar["a", listTy[αTy]] -> lTm}, absRepListThm];
    finalEq = TRANS[HOL`Equal`SYM[absRepAtCHT],
                    TRANS[applyAbs, absRepAtL2]]
    (* (witHyp) ⊢ CONS (headTermOf l) (tailFnOf l) = l *)
  ];

End[];
EndPackage[];
