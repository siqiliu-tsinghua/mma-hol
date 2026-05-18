(* ::Package:: *)

(* M7-4-a.1 stdlib/List — list type definition + NIL constructor.

   Encode α list as the subtype of carrier `num → α option` whose elements
   are supported on an initial segment [0, n):

     isListP f  ⇔  ∃n. ∀i. (f i = NONE) ⇔ ¬ (i < n)

   newBasicTypeDefinition carves out `α list` with ABS_list / REP_list.

   NIL = ABS_list (λi. NONE) — the unique list of length 0.

   CONS, injectivity, disjointness, induction defer to M7-4-a.2. *)

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

andC[]       := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notC[]       := mkConst["¬", tyFun[boolTy, boolTy]];
forallC[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
existsC[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];

andTm[a_, b_] := mkComb[mkComb[andC[], a], b];

(* Local num-term builders (Num.wl's ltTm/plusTm/etc. are Private). *)
ltTmLocal[aTm_, bTm_] :=
  mkComb[mkComb[HOL`Stdlib`Num`ltConst[], aTm], bTm];

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

End[];
EndPackage[];
