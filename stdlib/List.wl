(* ::Package:: *)

(* M7-4-a.{1,2,3} stdlib/List — list type, NIL, CONS, round-trip thms.

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

   Injectivity, disjointness, list induction defer to M7-4-a.4+. *)

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

End[];
EndPackage[];
