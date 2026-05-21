(* ::Package:: *)

(* M7-4-a.{1..6} stdlib/List — list type, NIL, CONS, list induction.

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

   List induction (M7-4-a.6):
     funcExtThm:       Wolfram helper, ⊢ ∀x. f x = g x → ⊢ f = g
     listInductionThm: ⊢ ∀P. P NIL ∧ (∀x l. P l ⇒ P (CONS x l)) ⇒ ∀l. P l

   M7-4-a is the foundation slice. M7-4-b adds LENGTH (b.1) and
   HD/TL (b.2). M7-4-c builds the list iteration theorem: c.1 is
   the LIST_ITER_GRAPH toolbox (closed/exists/nilVal/inversion);
   c.2 adds uniqueness + listIterationThm
     ⊢ ∀e f. ∃g. g NIL = e ∧ ∀x l. g (CONS x l) = f x (g l),
   the enabler for APPEND/MAP/FILTER/FOLD (M7-4-d). *)

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

funcExtThm::usage =
  "funcExtThm[fTm, gTm, perITh] — from Γ ⊢ ∀x. fTm x = gTm x, derive Γ ⊢ fTm = gTm. Inline SPEC + ABS + etaAx chain.";
listInductionThm::usage =
  "listInductionThm — ⊢ ∀P. P NIL ∧ (∀x l. P l ⇒ P (CONS x l)) ⇒ ∀l. P l.";

ltNotReflThm::usage =
  "ltNotReflThm — ⊢ ∀m. ¬(m < m).";
ltExtThm::usage =
  "ltExtThm — ⊢ ∀m n. (∀i. ¬(i < m) = ¬(i < n)) ⇒ m = n.";

lengthConst::usage =
  "lengthConst[] — LENGTH : α list → num. LENGTH l = ε n. ∀i. REP_list l i = NONE ⇔ ¬(i < n).";
lengthDefThm::usage =
  "lengthDefThm — ⊢ LENGTH = (λl. ε n. ∀i. REP_list l i = NONE ⇔ ¬(i < n)).";
lengthSpecThm::usage =
  "lengthSpecThm — ⊢ ∀l. ∀i. REP_list l i = NONE ⇔ ¬(i < LENGTH l).";
lengthUniqueThm::usage =
  "lengthUniqueThm — ⊢ ∀l n. (∀i. REP_list l i = NONE ⇔ ¬(i < n)) ⇒ LENGTH l = n.";
lengthNilThm::usage =
  "lengthNilThm — ⊢ LENGTH NIL = 0.";
lengthConsThm::usage =
  "lengthConsThm — ⊢ ∀x l. LENGTH (CONS x l) = SUC (LENGTH l).";

hdConst::usage =
  "hdConst[] — HD : α list → α. HD l = ε x. REP_list l 0 = SOME x (head; unspecified ε at NIL).";
hdDefThm::usage =
  "hdDefThm — ⊢ HD = (λl. ε x. REP_list l 0 = SOME x).";
hdConsThm::usage =
  "hdConsThm — ⊢ ∀x l. HD (CONS x l) = x.";

tlConst::usage =
  "tlConst[] — TL : α list → α list. TL l = ABS_list (λj. REP_list l (SUC j)).";
tlDefThm::usage =
  "tlDefThm — ⊢ TL = (λl. ABS_list (λj. REP_list l (SUC j))).";
tlConsThm::usage =
  "tlConsThm — ⊢ ∀x l. TL (CONS x l) = l.";

listIterGraphConst::usage =
  "listIterGraphConst[] — LIST_ITER_GRAPH : β → (α→β→β) → α list → β → bool. Smallest relation R with R NIL e and (R t y ⇒ R (CONS x t) (f x y)).";
listIterGraphDefThm::usage =
  "listIterGraphDefThm — ⊢ LIST_ITER_GRAPH = (λe f l z. ∀R. (R NIL e ∧ (∀x t y. R t y ⇒ R (CONS x t) (f x y))) ⇒ R l z).";
graphNilThm::usage =
  "graphNilThm — ⊢ LIST_ITER_GRAPH e f NIL e (graph closed at NIL).";
graphConsThm::usage =
  "graphConsThm — ⊢ ∀x t y. LIST_ITER_GRAPH e f t y ⇒ LIST_ITER_GRAPH e f (CONS x t) (f x y).";
graphExistsThm::usage =
  "graphExistsThm — ⊢ ∀l. ∃z. LIST_ITER_GRAPH e f l z.";
graphNilValThm::usage =
  "graphNilValThm — ⊢ ∀z. LIST_ITER_GRAPH e f NIL z ⇒ z = e.";
graphInversionThm::usage =
  "graphInversionThm — ⊢ ∀x l z. LIST_ITER_GRAPH e f (CONS x l) z ⇒ ∃y. LIST_ITER_GRAPH e f l y ∧ z = f x y.";
graphUniqueThm::usage =
  "graphUniqueThm — ⊢ ∀l z z'. LIST_ITER_GRAPH e f l z ⇒ LIST_ITER_GRAPH e f l z' ⇒ z = z'.";
listIterationThm::usage =
  "listIterationThm — ⊢ ∀e f. ∃g. g NIL = e ∧ ∀x l. g (CONS x l) = f x (g l). List iteration principle (analogue of numIterationThm).";

foldrConst::usage =
  "foldrConst[] — FOLDR : (α→β→β) → β → α list → β. Right fold; FOLDR f e [x1,…,xn] = f x1 (… (f xn e)).";
foldrDefThm::usage = "foldrDefThm — ⊢ FOLDR = (λf e. ε g. g NIL = e ∧ ∀x l. g (CONS x l) = f x (g l)).";
foldrNilThm::usage = "foldrNilThm — ⊢ ∀f e. FOLDR f e NIL = e.";
foldrConsThm::usage = "foldrConsThm — ⊢ ∀f e x l. FOLDR f e (CONS x l) = f x (FOLDR f e l).";

appendConst::usage =
  "appendConst[] — APPEND : α list → α list → α list. List concatenation.";
appendDefThm::usage = "appendDefThm — ⊢ APPEND = (λl1 l2. (ε g. …) l1) recursing on l1 with base l2.";
appendNilThm::usage = "appendNilThm — ⊢ ∀l. APPEND NIL l = l.";
appendConsThm::usage = "appendConsThm — ⊢ ∀x l1 l2. APPEND (CONS x l1) l2 = CONS x (APPEND l1 l2).";

mapConst::usage =
  "mapConst[] — MAP : (α→β) → α list → β list. Map a function over a list.";
mapDefThm::usage = "mapDefThm — ⊢ MAP = (λh l. (ε g. …) l).";
mapNilThm::usage = "mapNilThm — ⊢ ∀h. MAP h NIL = NIL.";
mapConsThm::usage = "mapConsThm — ⊢ ∀h x l. MAP h (CONS x l) = CONS (h x) (MAP h l).";

filterConst::usage =
  "filterConst[] — FILTER : (α→bool) → α list → α list. Keep elements satisfying the predicate.";
filterDefThm::usage = "filterDefThm — ⊢ FILTER = (λp l. (ε g. …) l).";
filterNilThm::usage = "filterNilThm — ⊢ ∀p. FILTER p NIL = NIL.";
filterConsThm::usage = "filterConsThm — ⊢ ∀p x l. FILTER p (CONS x l) = COND (p x) (CONS x (FILTER p l)) (FILTER p l).";

foldlConst::usage =
  "foldlConst[] — FOLDL : (β→α→β) → β → α list → β. Left fold; FOLDL f e [x1,…,xn] = f (… (f e x1) …) xn. Defined via FOLDR at target type β→β.";
foldlDefThm::usage = "foldlDefThm — ⊢ FOLDL = (λf e l. FOLDR (λx r a. r (f a x)) (λa. a) l e).";
foldlNilThm::usage = "foldlNilThm — ⊢ ∀f e. FOLDL f e NIL = e.";
foldlConsThm::usage = "foldlConsThm — ⊢ ∀f e x l. FOLDL f e (CONS x l) = FOLDL f (f e x) l.";

Begin["`Private`"];

(* ============================================================ *)
(* Local type vars + helpers                                    *)
(* ============================================================ *)

αTy = mkVarType["A"];
βTy = mkVarType["B"];

(* Num.wl's numTy is HOL`Stdlib`Num`Private`numTy — not visible here. *)
numTy = mkType["num", {}];

optionATy   = HOL`Stdlib`Option`optionTy[αTy];
carrierTy   = tyFun[numTy, optionATy];
predTy      = tyFun[carrierTy, boolTy];

(* Iteration target type β; step f : α → β → β. *)
iterFnTy = tyFun[αTy, tyFun[βTy, βTy]];

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
leqTmLocal[aTm_, bTm_] :=
  mkComb[mkComb[HOL`Stdlib`Num`leqConst[], aTm], bTm];
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

(* ============================================================ *)
(* M7-4-a.6 : list induction theorem.                            *)
(* ============================================================ *)

(* funcExtThm[fTm, gTm, perITh] : Γ ⊢ ∀x. fTm x = gTm x → Γ ⊢ fTm = gTm *)
funcExtThm[fTm_, gTm_, perITh_] :=
  Module[{fTy, dom, xV, specXth, absXth, etaAtF, etaAtG},
    fTy = typeOf[fTm];
    dom = fTy[[2, 1]];
    xV = mkVar["xFE", dom];
    specXth = HOL`Bool`SPEC[xV, perITh];
    (* Γ ⊢ fTm xFE = gTm xFE *)
    absXth = HOL`Kernel`ABS[xV, specXth];
    (* Γ ⊢ (λxFE. fTm xFE) = (λxFE. gTm xFE) *)
    etaAtF = HOL`Bool`ISPEC[fTm, HOL`Bootstrap`etaAx];
    etaAtG = HOL`Bool`ISPEC[gTm, HOL`Bootstrap`etaAx];
    TRANS[TRANS[HOL`Equal`SYM[etaAtF], absXth], etaAtG]
    (* Γ ⊢ fTm = gTm *)
  ];

(* ============================================================ *)
(* listInductionThm                                              *)
(*   ⊢ ∀P. P NIL ∧ (∀x l. P l ⇒ P (CONS x l)) ⇒ ∀l. P l          *)
(*                                                              *)
(* Num induction on the length witness n from isListP (REP_list l). *)
(* Predicate Q n = ∀l'. (∀i. REP_list l' i = NONE ⇔ ¬(i < n)) ⇒ P l'.*)
(*   Q 0:    REP_list l' = (λi. NONE) = REP_list NIL → l' = NIL →   *)
(*           P l' from P NIL.                                       *)
(*   Q(SUC n): consHeadTailEqL gives CONS h (tail l') = l';         *)
(*           tailLengthThm gives the n-witness for tail l';         *)
(*           Q n SPEC at tail l' + MP → P (tail l');                *)
(*           step hyp SPEC at h, tail l' + MP → P (CONS h tail);    *)
(*           rewrite via consHeadTailEqL → P l'.                    *)
(* ============================================================ *)

listInductionThm =
  Module[{pV, lV, lpV, nV, iV, xV2,
          stepXV, stepLV, pNilTm, stepImpTm, stepInner, stepTm,
          conjTm, conjHyp, pNil, stepHyp,
          qLamBody, qLam,
          baseTh, stepTh, indResult,
          isListPRepL, unfoldIsListPRepL, existsN,
          witInnerTm, witHyp, qAtN, qAtNAtL, plUnderWit,
          chooseN, genL, dischConj, genP,
          repListLTy},
    pV = mkVar["P", tyFun[listTy[αTy], boolTy]];
    lV = mkVar["l", listTy[αTy]];
    lpV = mkVar["lP", listTy[αTy]];
    nV = mkVar["n", numTy];
    iV = mkVar["i", numTy];
    stepXV = mkVar["x", αTy];
    stepLV = mkVar["lS", listTy[αTy]];
    repListLTy = listTy[αTy];

    (* === Hyps. === *)
    pNilTm = mkComb[pV, nilConst[]];
    stepInner = impTm[
      mkComb[pV, stepLV],
      mkComb[pV, mkComb[mkComb[consConst[], stepXV], stepLV]]];
    stepImpTm = mkComb[forallC[αTy], mkAbs[stepXV,
      mkComb[forallC[repListLTy], mkAbs[stepLV, stepInner]]]];
    stepTm = stepImpTm;
    conjTm = andTm[pNilTm, stepTm];
    conjHyp = ASSUME[conjTm];
    pNil = HOL`Bool`CONJUNCT1[conjHyp];
    (* (conjHyp) ⊢ P NIL *)
    stepHyp = HOL`Bool`CONJUNCT2[conjHyp];
    (* (conjHyp) ⊢ ∀x lS. P lS ⇒ P (CONS x lS) *)

    (* === Induction predicate Q n. === *)
    qLamBody[nTm_] :=
      mkComb[forallC[repListLTy], mkAbs[lpV,
        impTm[
          mkComb[forallC[numTy], mkAbs[iV,
            mkEq[
              mkEq[mkComb[mkComb[repListConst[], lpV], iV], noneAt[αTy]],
              mkComb[notC[], ltTmLocal[iV, nTm]]]]],
          mkComb[pV, lpV]]]];
    qLam = mkAbs[nV, qLamBody[nV]];

    (* === Base case ⊢ qLamBody[0]. === *)
    baseTh = Module[{lpHyp, witTm, witHyp1, perI, repLpEqNone, funExtNil,
                     repNilSymTh, repLpEqRepNil, applyAbsCH, absRepAtLp2,
                     absRepAtNil2, lpEqNil, pNilEqPLp, plpTh,
                     dischWit, genLp},
      witTm = mkComb[forallC[numTy], mkAbs[iV,
        mkEq[
          mkEq[mkComb[mkComb[repListConst[], lpV], iV], noneAt[αTy]],
          mkComb[notC[], ltTmLocal[iV, zeroConst[]]]]]];
      witHyp1 = ASSUME[witTm];
      (* (wit) ⊢ ∀i. (REP_list lP i = NONE) = ¬(i < 0) *)

      (* For arbitrary i, derive REP_list lP i = NONE. *)
      perI = Module[{specAtI, symEq, notLtZero, repLpAtI},
        specAtI = HOL`Bool`SPEC[iV, witHyp1];
        (* (wit) ⊢ (REP_list lP i = NONE) = ¬(i < 0) *)
        symEq = HOL`Equal`SYM[specAtI];
        (* (wit) ⊢ ¬(i < 0) = (REP_list lP i = NONE) *)
        notLtZero = HOL`Bool`SPEC[iV, HOL`Stdlib`Num`notLtZeroThm];
        (* ⊢ ¬(i < 0) *)
        repLpAtI = EQMP[symEq, notLtZero];
        (* (wit) ⊢ REP_list lP i = NONE *)
        repLpAtI
      ];
      (* Need ∀i. REP_list lP i = NONE = (λi. NONE) i.                *)
      (* Build perITh : ⊢ ∀i. REP_list lP i = (λi. NONE) i.            *)
      Module[{nilFunc, betaNilFnAtI, repLpEqLamNone, genIThm},
        nilFunc = mkAbs[iV, noneAt[αTy]];
        betaNilFnAtI = BETACONV[mkComb[nilFunc, iV]];
        (* ⊢ (λi. NONE) i = NONE *)
        repLpEqLamNone = TRANS[perI, HOL`Equal`SYM[betaNilFnAtI]];
        (* (wit) ⊢ REP_list lP i = (λi. NONE) i *)
        genIThm = HOL`Bool`GEN[iV, repLpEqLamNone];
        (* (wit) ⊢ ∀i. REP_list lP i = (λi. NONE) i *)
        repLpEqNone = funcExtThm[
          mkComb[repListConst[], lpV], nilFunc, genIThm]
        (* (wit) ⊢ REP_list lP = (λi. NONE) *)
      ];

      (* repNilThm : ⊢ REP_list NIL = (λi. NONE). SYM and TRANS. *)
      repNilSymTh = HOL`Equal`SYM[repNilThm];
      (* ⊢ (λi. NONE) = REP_list NIL *)
      repLpEqRepNil = TRANS[repLpEqNone, repNilSymTh];
      (* (wit) ⊢ REP_list lP = REP_list NIL *)
      applyAbsCH = HOL`Equal`APTERM[absListConst[], repLpEqRepNil];
      (* (wit) ⊢ ABS_list (REP_list lP) = ABS_list (REP_list NIL) *)
      absRepAtLp2 = HOL`Kernel`INST[
        {mkVar["a", repListLTy] -> lpV}, absRepListThm];
      absRepAtNil2 = HOL`Kernel`INST[
        {mkVar["a", repListLTy] -> nilConst[]}, absRepListThm];
      lpEqNil = TRANS[HOL`Equal`SYM[absRepAtLp2],
                      TRANS[applyAbsCH, absRepAtNil2]];
      (* (wit) ⊢ lP = NIL *)

      (* Use P NIL → P lP. APTERM P on SYM[lpEqNil] : NIL = lP gives
         P NIL = P lP; EQMP P NIL → P lP. *)
      pNilEqPLp = HOL`Equal`APTERM[pV, HOL`Equal`SYM[lpEqNil]];
      (* (wit) ⊢ P NIL = P lP *)
      plpTh = EQMP[pNilEqPLp, pNil];
      (* (conjHyp, wit) ⊢ P lP *)
      dischWit = HOL`Bool`DISCH[witTm, plpTh];
      (* (conjHyp) ⊢ (∀i. ...) ⇒ P lP *)
      genLp = HOL`Bool`GEN[lpV, dischWit]
      (* (conjHyp) ⊢ ∀lP. (∀i. ...) ⇒ P lP    — i.e. qLamBody[0] *)
    ];

    (* === Step case ⊢ ∀n. qLamBody[n] ⇒ qLamBody[SUC n]. === *)
    stepTh = Module[{ihTm, ihHyp, witTm, witHyp2,
                     consHTeqL, tailLenWit, qNAtTail, ihAtTail, ihMP,
                     pTail, stepAtH, stepAtHL, pConsHTail,
                     pConsEqPL, pLp,
                     dischWit, genLp, dischIh, genN, lpHypTm},
      ihTm = qLamBody[nV];
      ihHyp = ASSUME[ihTm];
      (* (ih) ⊢ ∀lP. (∀i. REP_list lP i = NONE = ¬(i < n)) ⇒ P lP *)

      witTm = mkComb[forallC[numTy], mkAbs[iV,
        mkEq[
          mkEq[mkComb[mkComb[repListConst[], lpV], iV], noneAt[αTy]],
          mkComb[notC[], ltTmLocal[iV, sucTm[nV]]]]]];
      witHyp2 = ASSUME[witTm];
      (* (wit) ⊢ ∀i. REP_list lP i = NONE = ¬(i < SUC n) *)

      consHTeqL = consHeadTailEqLThm[lpV, nV, witHyp2];
      (* (wit) ⊢ CONS (headTermOf lP) (tailFnOf lP) = lP *)
      tailLenWit = tailLengthThm[lpV, nV, witHyp2];
      (* (wit) ⊢ ∀i. REP_list (tailFnOf lP) i = NONE = ¬(i < n) *)

      qNAtTail = HOL`Bool`SPEC[tailFnOf[lpV], ihHyp];
      (* (ih) ⊢ (∀i. ...) ⇒ P (tailFnOf lP) *)
      pTail = HOL`Bool`MP[qNAtTail, tailLenWit];
      (* (ih, wit) ⊢ P (tailFnOf lP) *)

      stepAtH = HOL`Bool`SPEC[headTermOf[lpV], stepHyp];
      (* (conjHyp) ⊢ ∀lS. P lS ⇒ P (CONS (headTermOf lP) lS) *)
      stepAtHL = HOL`Bool`SPEC[tailFnOf[lpV], stepAtH];
      (* (conjHyp) ⊢ P (tailFnOf lP)
                     ⇒ P (CONS (headTermOf lP) (tailFnOf lP)) *)
      pConsHTail = HOL`Bool`MP[stepAtHL, pTail];
      (* (conjHyp, ih, wit) ⊢ P (CONS (headTermOf lP) (tailFnOf lP)) *)

      (* Rewrite via consHTeqL. *)
      pConsEqPL = HOL`Equal`APTERM[pV, consHTeqL];
      (* (wit) ⊢ P (CONS (headTermOf lP) (tailFnOf lP)) = P lP *)
      pLp = EQMP[pConsEqPL, pConsHTail];
      (* (conjHyp, ih, wit) ⊢ P lP *)

      dischWit = HOL`Bool`DISCH[witTm, pLp];
      (* (conjHyp, ih) ⊢ (∀i. ...) ⇒ P lP *)
      genLp = HOL`Bool`GEN[lpV, dischWit];
      (* (conjHyp, ih) ⊢ qLamBody[SUC n] *)
      dischIh = HOL`Bool`DISCH[ihTm, genLp];
      (* (conjHyp) ⊢ qLamBody[n] ⇒ qLamBody[SUC n] *)
      genN = HOL`Bool`GEN[nV, dischIh]
      (* (conjHyp) ⊢ ∀n. qLamBody[n] ⇒ qLamBody[SUC n] *)
    ];

    indResult = HOL`Stdlib`Num`Private`numInductBy[qLam, baseTh, stepTh];
    (* (conjHyp) ⊢ ∀n. qLamBody[n] *)

    (* Apply at our l. *)
    isListPRepL = HOL`Kernel`INST[
      {mkVar["l", repListLTy] -> lV}, isListPOfRepListThm];
    unfoldIsListPRepL = BETACONV[
      mkComb[isListPLambdaTerm[], mkComb[repListConst[], lV]]];
    existsN = EQMP[unfoldIsListPRepL, isListPRepL];
    (* ⊢ ∃n. ∀i. REP_list l i = NONE = ¬(i < n) *)

    witInnerTm = mkComb[forallC[numTy], mkAbs[iV,
      mkEq[
        mkEq[mkComb[mkComb[repListConst[], lV], iV], noneAt[αTy]],
        mkComb[notC[], ltTmLocal[iV, nV]]]]];
    witHyp = ASSUME[witInnerTm];
    (* (wit) ⊢ ∀i. REP_list l i = NONE = ¬(i < n) *)

    qAtN = HOL`Bool`SPEC[nV, indResult];
    (* (conjHyp) ⊢ qLamBody[n] = ∀l'. (∀i. ...) ⇒ P l' *)
    qAtNAtL = HOL`Bool`SPEC[lV, qAtN];
    (* (conjHyp) ⊢ (∀i. REP_list l i = NONE = ¬(i < n)) ⇒ P l *)
    plUnderWit = HOL`Bool`MP[qAtNAtL, witHyp];
    (* (conjHyp, wit) ⊢ P l *)

    chooseN = HOL`Bool`CHOOSE[nV, existsN, plUnderWit];
    (* (conjHyp) ⊢ P l *)
    genL = HOL`Bool`GEN[lV, chooseN];
    dischConj = HOL`Bool`DISCH[conjTm, genL];
    genP = HOL`Bool`GEN[pV, dischConj]
  ];

(* ============================================================ *)
(* M7-4-b.1 : LENGTH                                             *)
(* ============================================================ *)

(* ltNotReflThm : ⊢ ∀m. ¬(m < m) *)
ltNotReflThm =
  Module[{mV, mLtMTm, mLtMHyp, notMEqM, contradF, dischLt, genM},
    mV = mkVar["m", numTy];
    mLtMTm = ltTmLocal[mV, mV];
    mLtMHyp = ASSUME[mLtMTm];
    notMEqM = HOL`Bool`MP[
      HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, HOL`Stdlib`Num`ltImpliesNotEqThm]],
      mLtMHyp];
    (* (m<m) ⊢ ¬(m = m) *)
    contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[notMEqM], REFL[mV]];
    (* (m<m) ⊢ F *)
    dischLt = HOL`Bool`DISCH[mLtMTm, contradF];
    genM = HOL`Bool`GEN[mV, HOL`Bool`NOTINTRO[dischLt]]
  ];

(* ltExtThm : ⊢ ∀m n. (∀i. ¬(i < m) = ¬(i < n)) ⇒ m = n          *)
(* Instantiate at i=m and i=n; ¬(m<m), ¬(n<n) collapse via       *)
(* EQTINTRO/EQTELIM to give ¬(m<n) and ¬(n<m); leqTotal +         *)
(* leqCaseEqLt then forces m = n.                                 *)
ltExtThm =
  Module[{mV, nV, iV, hypTm, hypHyp, hypAtM, hypAtN,
          notMLtM, notNLtN, notMLtN, notNLtM, mEqN,
          dischHyp, genN, genM},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy]; iV = mkVar["i", numTy];
    hypTm = mkComb[forallC[numTy], mkAbs[iV,
      mkEq[mkComb[notC[], ltTmLocal[iV, mV]],
           mkComb[notC[], ltTmLocal[iV, nV]]]]];
    hypHyp = ASSUME[hypTm];

    hypAtM = HOL`Bool`SPEC[mV, hypHyp];
    (* ⊢ ¬(m<m) = ¬(m<n) *)
    notMLtM = HOL`Bool`SPEC[mV, ltNotReflThm];
    (* ⊢ ¬(m<m) *)
    notMLtN = HOL`Bool`EQTELIM[
      TRANS[HOL`Equal`SYM[hypAtM], HOL`Bool`EQTINTRO[notMLtM]]];
    (* ⊢ ¬(m<n) *)

    hypAtN = HOL`Bool`SPEC[nV, hypHyp];
    (* ⊢ ¬(n<m) = ¬(n<n) *)
    notNLtN = HOL`Bool`SPEC[nV, ltNotReflThm];
    notNLtM = HOL`Bool`EQTELIM[
      TRANS[hypAtN, HOL`Bool`EQTINTRO[notNLtN]]];
    (* ⊢ ¬(n<m) *)

    mEqN = Module[{leqTotalAt, caseMLeqN, caseNLeqM},
      leqTotalAt = HOL`Bool`SPEC[nV,
        HOL`Bool`SPEC[mV, HOL`Stdlib`Num`leqTotalThm]];
      caseMLeqN = Module[{mLeqNHyp, mEqNOrLt, mEqNCase, mLtNCase},
        mLeqNHyp = ASSUME[leqTmLocal[mV, nV]];
        mEqNOrLt = HOL`Bool`MP[
          HOL`Bool`SPEC[nV,
            HOL`Bool`SPEC[mV, HOL`Stdlib`Num`leqCaseEqLtThm]],
          mLeqNHyp];
        (* ⊢ m = n ∨ m < n *)
        mEqNCase = ASSUME[mkEq[mV, nV]];
        mLtNCase = HOL`Bool`CONTR[mkEq[mV, nV],
          HOL`Bool`MP[HOL`Bool`NOTELIM[notMLtN],
            ASSUME[ltTmLocal[mV, nV]]]];
        HOL`Bool`DISJCASES[mEqNOrLt, mEqNCase, mLtNCase]
      ];
      caseNLeqM = Module[{nLeqMHyp, nEqMOrLt, nEqMCase, nLtMCase},
        nLeqMHyp = ASSUME[leqTmLocal[nV, mV]];
        nEqMOrLt = HOL`Bool`MP[
          HOL`Bool`SPEC[mV,
            HOL`Bool`SPEC[nV, HOL`Stdlib`Num`leqCaseEqLtThm]],
          nLeqMHyp];
        (* ⊢ n = m ∨ n < m *)
        nEqMCase = HOL`Equal`SYM[ASSUME[mkEq[nV, mV]]];
        nLtMCase = HOL`Bool`CONTR[mkEq[mV, nV],
          HOL`Bool`MP[HOL`Bool`NOTELIM[notNLtM],
            ASSUME[ltTmLocal[nV, mV]]]];
        HOL`Bool`DISJCASES[nEqMOrLt, nEqMCase, nLtMCase]
      ];
      HOL`Bool`DISJCASES[leqTotalAt, caseMLeqN, caseNLeqM]
      (* ⊢ m = n *)
    ];
    dischHyp = HOL`Bool`DISCH[hypTm, mEqN];
    genN = HOL`Bool`GEN[nV, dischHyp];
    genM = HOL`Bool`GEN[mV, genN]
  ];

(* ============================================================ *)
(* LENGTH = λl. ε n. ∀i. REP_list l i = NONE ⇔ ¬(i < n)          *)
(* ============================================================ *)

lengthTy = tyFun[listTy[αTy], numTy];

lengthPredLam[lTm_] :=
  Module[{nV, iV},
    nV = mkVar["n", numTy];
    iV = mkVar["i", numTy];
    mkAbs[nV, mkComb[forallC[numTy], mkAbs[iV,
      mkEq[
        mkEq[mkComb[mkComb[repListConst[], lTm], iV], noneAt[αTy]],
        mkComb[notC[], ltTmLocal[iV, nV]]]]]]
  ];

lengthDefBody[] :=
  Module[{lV},
    lV = mkVar["l", listTy[αTy]];
    mkAbs[lV, mkComb[selectC[numTy], lengthPredLam[lV]]]
  ];

lengthDefThm = newDefinition[
  mkEq[mkVar["LENGTH", lengthTy], lengthDefBody[]]];
lengthConst[] := mkConst["LENGTH", lengthTy];
lengthTm[lTm_] := mkComb[lengthConst[], lTm];

unfoldLength[lTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[lengthDefThm, lTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* lengthSpecAt[l] : ⊢ ∀i. REP_list l i = NONE ⇔ ¬(i < LENGTH l)  *)
lengthSpecAt[lTm_] :=
  Module[{predLam, isListPRepL, betaUnfold, existsN, atSelect},
    predLam = lengthPredLam[lTm];
    isListPRepL = HOL`Kernel`INST[
      {mkVar["l", listTy[αTy]] -> lTm}, isListPOfRepListThm];
    betaUnfold = BETACONV[
      mkComb[isListPLambdaTerm[], mkComb[repListConst[], lTm]]];
    existsN = EQMP[betaUnfold, isListPRepL];
    (* ⊢ ∃n. ∀i. REP_list l i = NONE ⇔ ¬(i < n) *)
    atSelect = HOL`Stdlib`Num`selectOfExists[predLam, existsN];
    (* ⊢ ∀i. REP_list l i = NONE ⇔ ¬(i < @predLam) *)
    HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[
        HOL`Drule`REWRCONV[HOL`Equal`SYM[unfoldLength[lTm]]]],
      atSelect]
    (* ⊢ ∀i. REP_list l i = NONE ⇔ ¬(i < LENGTH l) *)
  ];

lengthSpecThm =
  Module[{lV},
    lV = mkVar["l", listTy[αTy]];
    HOL`Bool`GEN[lV, lengthSpecAt[lV]]
  ];

(* lengthUniqueThm : ⊢ ∀l n. (∀i. REP_list l i = NONE ⇔ ¬(i < n)) *)
(*                          ⇒ LENGTH l = n                         *)
lengthUniqueThm =
  Module[{lV, nV, iV, hypTm, hypHyp, lenSpec,
          notIffTm, perI, genI, ltExtAt, nEqLen,
          dischHyp, genN, genL},
    lV = mkVar["l", listTy[αTy]];
    nV = mkVar["n", numTy];
    iV = mkVar["i", numTy];
    hypTm = mkComb[forallC[numTy], mkAbs[iV,
      mkEq[
        mkEq[mkComb[mkComb[repListConst[], lV], iV], noneAt[αTy]],
        mkComb[notC[], ltTmLocal[iV, nV]]]]];
    hypHyp = ASSUME[hypTm];
    lenSpec = lengthSpecAt[lV];
    (* ⊢ ∀i. REP_list l i = NONE ⇔ ¬(i < LENGTH l) *)

    (* For each i: ¬(i < n) = ¬(i < LENGTH l). *)
    perI = Module[{hypAtI, lenAtI},
      hypAtI = HOL`Bool`SPEC[iV, hypHyp];
      (* ⊢ (REP_list l i = NONE) = ¬(i < n) *)
      lenAtI = HOL`Bool`SPEC[iV, lenSpec];
      (* ⊢ (REP_list l i = NONE) = ¬(i < LENGTH l) *)
      TRANS[HOL`Equal`SYM[hypAtI], lenAtI]
      (* ⊢ ¬(i < n) = ¬(i < LENGTH l) *)
    ];
    genI = HOL`Bool`GEN[iV, perI];
    (* ⊢ ∀i. ¬(i < n) = ¬(i < LENGTH l) *)
    ltExtAt = HOL`Bool`SPEC[lengthTm[lV],
      HOL`Bool`SPEC[nV, ltExtThm]];
    (* ⊢ (∀i. ¬(i < n) = ¬(i < LENGTH l)) ⇒ n = LENGTH l *)
    nEqLen = HOL`Bool`MP[ltExtAt, genI];
    (* ⊢ n = LENGTH l *)
    dischHyp = HOL`Bool`DISCH[hypTm, HOL`Equal`SYM[nEqLen]];
    (* ⊢ (∀i. …) ⇒ LENGTH l = n *)
    genN = HOL`Bool`GEN[nV, dischHyp];
    genL = HOL`Bool`GEN[lV, genN]
  ];

(* lengthNilThm : ⊢ LENGTH NIL = 0                               *)
(* lengthUnique at (NIL, 0): need ∀i. REP_list NIL i = NONE ⇔     *)
(* ¬(i < 0). REP_list NIL i = NONE always (repNil + beta);        *)
(* ¬(i < 0) always (notLtZero). Both T.                           *)
lengthNilThm =
  Module[{iV, repNilAtI, repNilEqNone, notLtZeroAtI,
          iffAtI, genI, uniqAtNil0},
    iV = mkVar["i", numTy];
    repNilAtI = HOL`Equal`APTHM[repNilThm, iV];
    (* ⊢ REP_list NIL i = (λi. NONE) i *)
    repNilEqNone = TRANS[repNilAtI, BETACONV[concl[repNilAtI][[2]]]];
    (* ⊢ REP_list NIL i = NONE *)
    notLtZeroAtI = HOL`Bool`SPEC[iV, HOL`Stdlib`Num`notLtZeroThm];
    (* ⊢ ¬(i < 0) *)
    iffAtI = TRANS[HOL`Bool`EQTINTRO[repNilEqNone],
                   HOL`Equal`SYM[HOL`Bool`EQTINTRO[notLtZeroAtI]]];
    (* ⊢ (REP_list NIL i = NONE) = ¬(i < 0) *)
    genI = HOL`Bool`GEN[iV, iffAtI];
    (* ⊢ ∀i. (REP_list NIL i = NONE) = ¬(i < 0) *)
    uniqAtNil0 = HOL`Bool`SPEC[zeroConst[],
      HOL`Bool`SPEC[nilConst[], lengthUniqueThm]];
    (* ⊢ (∀i. REP_list NIL i = NONE ⇔ ¬(i < 0)) ⇒ LENGTH NIL = 0 *)
    HOL`Bool`MP[uniqAtNil0, genI]
    (* ⊢ LENGTH NIL = 0 *)
  ];

(* consLengthWitnessAt[x, l] :                                    *)
(*   ⊢ ∀i. REP_list (CONS x l) i = NONE ⇔ ¬(i < SUC (LENGTH l))   *)
(* Per-index, mirroring consCarrierIsListP but with n' = LENGTH l *)
(* supplied by lengthSpecAt[l].                                   *)
consLengthWitnessAt[xTm_, lTm_] :=
  Module[{iV, jLenV, eqC, consXL, lenSpecL, numCasesAtI,
          iEqZeroBranch, iEqSucBranch, perI, genI},
    iV = mkVar["i", numTy];
    jLenV = mkVar["jLen", numTy];
    eqC = mkConst["=", tyFun[optionATy, tyFun[optionATy, boolTy]]];
    consXL = mkComb[mkComb[consConst[], xTm], lTm];
    lenSpecL = lengthSpecAt[lTm];
    (* ⊢ ∀i. REP_list l i = NONE ⇔ ¬(i < LENGTH l) *)
    numCasesAtI = HOL`Bool`SPEC[iV, HOL`Stdlib`Num`numCasesThm];

    iEqZeroBranch = Module[{iEqZeroHyp, repCHAt0, lhsRw, lhsEqF,
                            zeroLtSucLen, notNot, notZeroLtEqF, rhsRw, rhsEqF},
      iEqZeroHyp = ASSUME[mkEq[iV, zeroConst[]]];
      repCHAt0 = HOL`Kernel`INST[
        {mkVar["x", αTy] -> xTm, mkVar["l", listTy[αTy]] -> lTm},
        repConsHeadThm];
      (* ⊢ REP_list (CONS x l) 0 = SOME x *)
      lhsRw = TRANS[
        HOL`Equal`APTHM[HOL`Equal`APTERM[eqC,
          HOL`Equal`APTERM[mkComb[repListConst[], consXL], iEqZeroHyp]],
          noneAt[αTy]],
        HOL`Equal`APTHM[HOL`Equal`APTERM[eqC, repCHAt0], noneAt[αTy]]];
      (* (i=0) ⊢ (REP_list (CONS x l) i = NONE) = (SOME x = NONE) *)
      lhsEqF = TRANS[lhsRw,
        eqfIntroLocal[HOL`Bool`SPEC[xTm, someNotEqNoneThm]]];
      (* (i=0) ⊢ (REP_list (CONS x l) i = NONE) = F *)
      zeroLtSucLen = HOL`Bool`SPEC[lengthTm[lTm], zeroLtSucThm];
      (* ⊢ 0 < SUC (LENGTH l) *)
      notNot = notNotIntroLocal[zeroLtSucLen];
      notZeroLtEqF = eqfIntroLocal[notNot];
      (* ⊢ ¬(0 < SUC (LENGTH l)) = F *)
      rhsRw = HOL`Equal`APTERM[notC[],
        HOL`Equal`APTHM[
          HOL`Equal`APTERM[HOL`Stdlib`Num`ltConst[], iEqZeroHyp],
          sucTm[lengthTm[lTm]]]];
      (* (i=0) ⊢ ¬(i < SUC (LENGTH l)) = ¬(0 < SUC (LENGTH l)) *)
      rhsEqF = TRANS[rhsRw, notZeroLtEqF];
      (* (i=0) ⊢ ¬(i < SUC (LENGTH l)) = F *)
      TRANS[lhsEqF, HOL`Equal`SYM[rhsEqF]]
      (* (i=0) ⊢ (REP_list (CONS x l) i = NONE) = ¬(i < SUC (LENGTH l)) *)
    ];

    iEqSucBranch = Module[{exJTm, exJHyp, iEqSucJ, iEqSucJHyp,
                           repCTAt, lhsRw, lenAtJ, lhsEqNotLt,
                           ltSucMC, rhsRw1, rhsRw2, rhsRw3, finalIff, choseJ},
      exJTm = mkComb[existsC[numTy], mkAbs[jLenV, mkEq[iV, sucTm[jLenV]]]];
      exJHyp = ASSUME[exJTm];
      iEqSucJ = mkEq[iV, sucTm[jLenV]];
      iEqSucJHyp = ASSUME[iEqSucJ];
      repCTAt = HOL`Bool`SPEC[jLenV, HOL`Kernel`INST[
        {mkVar["x", αTy] -> xTm, mkVar["l", listTy[αTy]] -> lTm},
        repConsTailThm]];
      (* ⊢ REP_list (CONS x l) (SUC jLen) = REP_list l jLen *)
      lhsRw = TRANS[
        HOL`Equal`APTHM[HOL`Equal`APTERM[eqC,
          HOL`Equal`APTERM[mkComb[repListConst[], consXL], iEqSucJHyp]],
          noneAt[αTy]],
        HOL`Equal`APTHM[HOL`Equal`APTERM[eqC, repCTAt], noneAt[αTy]]];
      (* (i=SUC jLen) ⊢ (REP_list (CONS x l) i = NONE)
                        = (REP_list l jLen = NONE) *)
      lenAtJ = HOL`Bool`SPEC[jLenV, lenSpecL];
      (* ⊢ (REP_list l jLen = NONE) = ¬(jLen < LENGTH l) *)
      lhsEqNotLt = TRANS[lhsRw, lenAtJ];
      (* (i=SUC jLen) ⊢ (REP_list (CONS x l) i = NONE)
                        = ¬(jLen < LENGTH l) *)
      ltSucMC = HOL`Bool`SPEC[lengthTm[lTm],
        HOL`Bool`SPEC[jLenV, ltSucMonoCancelThm]];
      (* ⊢ (SUC jLen < SUC (LENGTH l)) = (jLen < LENGTH l) *)
      rhsRw1 = HOL`Equal`APTERM[notC[],
        HOL`Equal`APTHM[
          HOL`Equal`APTERM[HOL`Stdlib`Num`ltConst[], iEqSucJHyp],
          sucTm[lengthTm[lTm]]]];
      (* (i=SUC jLen) ⊢ ¬(i < SUC (LENGTH l))
                        = ¬(SUC jLen < SUC (LENGTH l)) *)
      rhsRw2 = HOL`Equal`APTERM[notC[], ltSucMC];
      (* ⊢ ¬(SUC jLen < SUC (LENGTH l)) = ¬(jLen < LENGTH l) *)
      rhsRw3 = TRANS[rhsRw1, rhsRw2];
      (* (i=SUC jLen) ⊢ ¬(i < SUC (LENGTH l)) = ¬(jLen < LENGTH l) *)
      finalIff = TRANS[lhsEqNotLt, HOL`Equal`SYM[rhsRw3]];
      (* (i=SUC jLen) ⊢ (REP_list (CONS x l) i = NONE)
                        = ¬(i < SUC (LENGTH l)) *)
      choseJ = HOL`Bool`CHOOSE[jLenV, exJHyp, finalIff];
      choseJ
    ];

    perI = HOL`Bool`DISJCASES[numCasesAtI, iEqZeroBranch, iEqSucBranch];
    genI = HOL`Bool`GEN[iV, perI]
    (* ⊢ ∀i. REP_list (CONS x l) i = NONE ⇔ ¬(i < SUC (LENGTH l)) *)
  ];

(* lengthConsThm : ⊢ ∀x l. LENGTH (CONS x l) = SUC (LENGTH l)    *)
lengthConsThm =
  Module[{xV, lV, consXL, witCons, uniqAtCons, lenEq, genL, genX},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listTy[αTy]];
    consXL = mkComb[mkComb[consConst[], xV], lV];
    witCons = consLengthWitnessAt[xV, lV];
    (* ⊢ ∀i. REP_list (CONS x l) i = NONE ⇔ ¬(i < SUC (LENGTH l)) *)
    uniqAtCons = HOL`Bool`SPEC[sucTm[lengthTm[lV]],
      HOL`Bool`SPEC[consXL, lengthUniqueThm]];
    (* ⊢ (∀i. …) ⇒ LENGTH (CONS x l) = SUC (LENGTH l) *)
    lenEq = HOL`Bool`MP[uniqAtCons, witCons];
    (* ⊢ LENGTH (CONS x l) = SUC (LENGTH l) *)
    genL = HOL`Bool`GEN[lV, lenEq];
    genX = HOL`Bool`GEN[xV, genL]
  ];

(* ============================================================ *)
(* M7-4-b.2 : HD, TL                                             *)
(* ============================================================ *)

(* HD = λl. ε x. REP_list l 0 = SOME x                          *)

hdTy = tyFun[listTy[αTy], αTy];

hdDefBody[] :=
  Module[{lV, zV},
    lV = mkVar["l", listTy[αTy]];
    zV = mkVar["zHd", αTy];
    mkAbs[lV, mkComb[selectC[αTy], mkAbs[zV,
      mkEq[mkComb[mkComb[repListConst[], lV], zeroConst[]],
           mkComb[someAt[αTy], zV]]]]]
  ];

hdDefThm = newDefinition[mkEq[mkVar["HD", hdTy], hdDefBody[]]];
hdConst[] := mkConst["HD", hdTy];
hdTm[lTm_] := mkComb[hdConst[], lTm];

unfoldHd[lTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[hdDefThm, lTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* hdConsThm : ⊢ ∀x l. HD (CONS x l) = x                        *)
hdConsThm =
  Module[{xV, lV, zV, consXL, repCH, predLam, existsZ, atSelect,
          hdEqSome, someEq, someInjAt, hdEqX, genL, genX},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listTy[αTy]];
    zV = mkVar["zHd", αTy];
    consXL = mkComb[mkComb[consConst[], xV], lV];

    repCH = HOL`Kernel`INST[
      {mkVar["x", αTy] -> xV, mkVar["l", listTy[αTy]] -> lV},
      repConsHeadThm];
    (* ⊢ REP_list (CONS x l) 0 = SOME x *)
    predLam = mkAbs[zV,
      mkEq[mkComb[mkComb[repListConst[], consXL], zeroConst[]],
           mkComb[someAt[αTy], zV]]];
    existsZ = HOL`Bool`EXISTS[
      mkComb[existsC[αTy], predLam], xV, repCH];
    (* ⊢ ∃z. REP_list (CONS x l) 0 = SOME z *)
    atSelect = HOL`Stdlib`Num`selectOfExists[predLam, existsZ];
    (* ⊢ REP_list (CONS x l) 0 = SOME (@predLam) *)
    hdEqSome = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[
        HOL`Drule`REWRCONV[HOL`Equal`SYM[unfoldHd[consXL]]]],
      atSelect];
    (* ⊢ REP_list (CONS x l) 0 = SOME (HD (CONS x l)) *)
    someEq = TRANS[HOL`Equal`SYM[hdEqSome], repCH];
    (* ⊢ SOME (HD (CONS x l)) = SOME x *)
    someInjAt = HOL`Kernel`INST[
      {mkVar["x", αTy] -> hdTm[consXL], mkVar["xP", αTy] -> xV},
      HOL`Stdlib`Option`someInjThm];
    (* ⊢ (SOME (HD (CONS x l)) = SOME x) ⇒ (HD (CONS x l) = x) *)
    hdEqX = HOL`Bool`MP[someInjAt, someEq];
    (* ⊢ HD (CONS x l) = x *)
    genL = HOL`Bool`GEN[lV, hdEqX];
    genX = HOL`Bool`GEN[xV, genL]
  ];

(* TL = λl. ABS_list (λj. REP_list l (SUC j))                   *)

tlTy = tyFun[listTy[αTy], listTy[αTy]];

tlDefBody[] :=
  Module[{lV, jV},
    lV = mkVar["l", listTy[αTy]];
    jV = mkVar["jTl", numTy];
    mkAbs[lV, mkComb[absListConst[],
      mkAbs[jV, mkComb[mkComb[repListConst[], lV], sucTm[jV]]]]]
  ];

tlDefThm = newDefinition[mkEq[mkVar["TL", tlTy], tlDefBody[]]];
tlConst[] := mkConst["TL", tlTy];
tlTm[lTm_] := mkComb[tlConst[], lTm];

unfoldTl[lTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[tlDefThm, lTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* tlConsThm : ⊢ ∀x l. TL (CONS x l) = l                        *)
tlConsThm =
  Module[{xV, lV, jV, consXL, unfoldTlCons, repCTAtJ, absJ,
          etaRepL, shfEqRepL, applyAbs, absRepL, tlEqL, genL, genX},
    xV = mkVar["x", αTy];
    lV = mkVar["l", listTy[αTy]];
    jV = mkVar["jTl", numTy];
    consXL = mkComb[mkComb[consConst[], xV], lV];

    unfoldTlCons = unfoldTl[consXL];
    (* ⊢ TL (CONS x l) = ABS_list (λj. REP_list (CONS x l) (SUC j)) *)
    repCTAtJ = HOL`Bool`SPEC[jV, HOL`Kernel`INST[
      {mkVar["x", αTy] -> xV, mkVar["l", listTy[αTy]] -> lV},
      repConsTailThm]];
    (* ⊢ REP_list (CONS x l) (SUC j) = REP_list l j *)
    absJ = HOL`Kernel`ABS[jV, repCTAtJ];
    (* ⊢ (λj. REP_list (CONS x l) (SUC j)) = (λj. REP_list l j) *)
    etaRepL = HOL`Bool`ISPEC[
      mkComb[repListConst[], lV], HOL`Bootstrap`etaAx];
    (* ⊢ (λj. REP_list l j) = REP_list l *)
    shfEqRepL = TRANS[absJ, etaRepL];
    (* ⊢ (λj. REP_list (CONS x l) (SUC j)) = REP_list l *)
    applyAbs = HOL`Equal`APTERM[absListConst[], shfEqRepL];
    (* ⊢ ABS_list (λj. REP_list (CONS x l) (SUC j)) = ABS_list (REP_list l) *)
    absRepL = HOL`Kernel`INST[
      {mkVar["a", listTy[αTy]] -> lV}, absRepListThm];
    (* ⊢ ABS_list (REP_list l) = l *)
    tlEqL = TRANS[unfoldTlCons, TRANS[applyAbs, absRepL]];
    (* ⊢ TL (CONS x l) = l *)
    genL = HOL`Bool`GEN[lV, tlEqL];
    genX = HOL`Bool`GEN[xV, genL]
  ];

(* ============================================================ *)
(* M7-4-c.1 : list iteration graph + toolbox                     *)
(*                                                              *)
(* LIST_ITER_GRAPH e f = smallest R : α list → β → bool with     *)
(*   R NIL e   and   (∀x t y. R t y ⇒ R (CONS x t) (f x y)).     *)
(* Encoded as the intersection of all such closed R:            *)
(*   LIST_ITER_GRAPH e f l z = ∀R. closed[R] ⇒ R l z.            *)
(* Mirrors Num.wl's ITER_GRAPH.                                  *)
(* ============================================================ *)

graphRelTy = tyFun[listTy[αTy], tyFun[βTy, boolTy]];
listIterGraphTy =
  tyFun[βTy, tyFun[iterFnTy, tyFun[listTy[αTy], tyFun[βTy, boolTy]]]];

(* closed[R] = R NIL e ∧ (∀x t y. R t y ⇒ R (CONS x t) (f x y))   *)
closedRelTm[eTm_, fTm_, rTm_] :=
  Module[{xV, tV, yV, rNilE, stepBody, stepForall},
    rNilE = mkComb[mkComb[rTm, nilConst[]], eTm];
    xV = mkVar["x", αTy];
    tV = mkVar["t", listTy[αTy]];
    yV = mkVar["y", βTy];
    stepBody = impTm[
      mkComb[mkComb[rTm, tV], yV],
      mkComb[mkComb[rTm, mkComb[mkComb[consConst[], xV], tV]],
             mkComb[mkComb[fTm, xV], yV]]];
    stepForall = mkComb[forallC[αTy], mkAbs[xV,
      mkComb[forallC[listTy[αTy]], mkAbs[tV,
        mkComb[forallC[βTy], mkAbs[yV, stepBody]]]]]];
    andTm[rNilE, stepForall]
  ];

graphDefBody[] :=
  Module[{eVl, fVl, lVl, zVl, rV},
    eVl = mkVar["e", βTy];
    fVl = mkVar["f", iterFnTy];
    lVl = mkVar["l", listTy[αTy]];
    zVl = mkVar["z", βTy];
    rV = mkVar["R", graphRelTy];
    mkAbs[eVl, mkAbs[fVl, mkAbs[lVl, mkAbs[zVl,
      mkComb[forallC[graphRelTy], mkAbs[rV,
        impTm[closedRelTm[eVl, fVl, rV],
              mkComb[mkComb[rV, lVl], zVl]]]]]]]]
  ];

listIterGraphDefThm = newDefinition[
  mkEq[mkVar["LIST_ITER_GRAPH", listIterGraphTy], graphDefBody[]]];
listIterGraphConst[] := mkConst["LIST_ITER_GRAPH", listIterGraphTy];

graphAppTm[eTm_, fTm_, lTm_, zTm_] :=
  mkComb[mkComb[mkComb[mkComb[listIterGraphConst[], eTm], fTm], lTm], zTm];

(* ⊢ LIST_ITER_GRAPH e f l z = ∀R. closed[R] ⇒ R l z *)
unfoldGraphApp[eTm_, fTm_, lTm_, zTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[listIterGraphDefThm, eTm];
    ap = TRANS[ap, BETACONV[concl[ap][[2]]]];
    ap = HOL`Equal`APTHM[ap, fTm];
    ap = TRANS[ap, BETACONV[concl[ap][[2]]]];
    ap = HOL`Equal`APTHM[ap, lTm];
    ap = TRANS[ap, BETACONV[concl[ap][[2]]]];
    ap = HOL`Equal`APTHM[ap, zTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* list-induction helper (mirrors numInductBy) *)
listInductBy[pLam_, baseTh_, stepTh_] :=
  Module[{premise, indSpec, indBeta},
    premise = HOL`Bool`CONJ[baseTh, stepTh];
    indSpec = HOL`Bool`SPEC[pLam, listInductionThm];
    indBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], indSpec];
    HOL`Bool`MP[indBeta, premise]
  ];

(* === Lemma 1a : ⊢ G NIL e === *)
graphNilThm =
  Module[{eV, fV, rV, closedTm, closedHyp, rNilE, dischClosed, genR},
    eV = mkVar["e", βTy]; fV = mkVar["f", iterFnTy];
    rV = mkVar["R", graphRelTy];
    closedTm = closedRelTm[eV, fV, rV];
    closedHyp = ASSUME[closedTm];
    rNilE = HOL`Bool`CONJUNCT1[closedHyp];
    (* (closed R) ⊢ R NIL e *)
    dischClosed = HOL`Bool`DISCH[closedTm, rNilE];
    genR = HOL`Bool`GEN[rV, dischClosed];
    (* ⊢ ∀R. closed[R] ⇒ R NIL e *)
    EQMP[HOL`Equal`SYM[unfoldGraphApp[eV, fV, nilConst[], eV]], genR]
    (* ⊢ G NIL e *)
  ];

(* === Lemma 1b : ⊢ ∀x t y. G t y ⇒ G (CONS x t) (f x y) === *)
graphConsThm =
  Module[{eV, fV, xV, tV, yV, rV, gTYTm, gTYHyp, gTYUnf,
          closedTm, closedHyp, specR, rTY, stepConj, stepAt, rConsApp,
          dischClosed, genR, foldGraph, dischGTY, genY, genT, genX},
    eV = mkVar["e", βTy]; fV = mkVar["f", iterFnTy];
    xV = mkVar["x", αTy]; tV = mkVar["t", listTy[αTy]]; yV = mkVar["y", βTy];
    rV = mkVar["R", graphRelTy];

    gTYTm = graphAppTm[eV, fV, tV, yV];
    gTYHyp = ASSUME[gTYTm];
    gTYUnf = EQMP[unfoldGraphApp[eV, fV, tV, yV], gTYHyp];
    (* (G t y) ⊢ ∀R. closed[R] ⇒ R t y *)

    closedTm = closedRelTm[eV, fV, rV];
    closedHyp = ASSUME[closedTm];
    specR = HOL`Bool`SPEC[rV, gTYUnf];
    rTY = HOL`Bool`MP[specR, closedHyp];
    (* (G t y, closed R) ⊢ R t y *)
    stepConj = HOL`Bool`CONJUNCT2[closedHyp];
    stepAt = HOL`Bool`SPEC[yV,
      HOL`Bool`SPEC[tV, HOL`Bool`SPEC[xV, stepConj]]];
    (* (closed R) ⊢ R t y ⇒ R (CONS x t) (f x y) *)
    rConsApp = HOL`Bool`MP[stepAt, rTY];
    (* (G t y, closed R) ⊢ R (CONS x t) (f x y) *)
    dischClosed = HOL`Bool`DISCH[closedTm, rConsApp];
    genR = HOL`Bool`GEN[rV, dischClosed];
    foldGraph = EQMP[
      HOL`Equal`SYM[unfoldGraphApp[eV, fV,
        mkComb[mkComb[consConst[], xV], tV],
        mkComb[mkComb[fV, xV], yV]]],
      genR];
    (* (G t y) ⊢ G (CONS x t) (f x y) *)
    dischGTY = HOL`Bool`DISCH[gTYTm, foldGraph];
    genY = HOL`Bool`GEN[yV, dischGTY];
    genT = HOL`Bool`GEN[tV, genY];
    genX = HOL`Bool`GEN[xV, genT]
  ];

(* === Lemma 2 (existence) : ⊢ ∀l. ∃z. G l z === *)
graphExistsThm =
  Module[{eV, fV, lV, zV, xV, z0V, existsBodyAt, pLam, baseTh, stepTh},
    eV = mkVar["e", βTy]; fV = mkVar["f", iterFnTy];
    lV = mkVar["l", listTy[αTy]]; zV = mkVar["z", βTy];
    xV = mkVar["x", αTy]; z0V = mkVar["z0", βTy];
    existsBodyAt[lTm_] := mkComb[existsC[βTy],
      mkAbs[zV, graphAppTm[eV, fV, lTm, zV]]];
    pLam = mkAbs[lV, existsBodyAt[lV]];

    baseTh = HOL`Bool`EXISTS[existsBodyAt[nilConst[]], eV, graphNilThm];
    (* ⊢ ∃z. G NIL z *)

    stepTh = Module[{exTm, exHyp, z0Tm, z0Hyp, gConsAt, existsRes,
                     choseZ0, dischEx, genL, genX, consXL},
      consXL = mkComb[mkComb[consConst[], xV], lV];
      exTm = existsBodyAt[lV];
      exHyp = ASSUME[exTm];
      z0Hyp = ASSUME[graphAppTm[eV, fV, lV, z0V]];
      gConsAt = HOL`Bool`MP[
        HOL`Bool`SPEC[z0V,
          HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV, graphConsThm]]],
        z0Hyp];
      (* (G l z0) ⊢ G (CONS x l) (f x z0) *)
      existsRes = HOL`Bool`EXISTS[existsBodyAt[consXL],
        mkComb[mkComb[fV, xV], z0V], gConsAt];
      (* (G l z0) ⊢ ∃z. G (CONS x l) z *)
      choseZ0 = HOL`Bool`CHOOSE[z0V, exHyp, existsRes];
      (* (∃z. G l z) ⊢ ∃z. G (CONS x l) z *)
      dischEx = HOL`Bool`DISCH[exTm, choseZ0];
      genL = HOL`Bool`GEN[lV, dischEx];
      genX = HOL`Bool`GEN[xV, genL]
    ];

    listInductBy[pLam, baseTh, stepTh]
  ];

(* === Lemma 3 (nilVal) : ⊢ ∀z. G NIL z ⇒ z = e === *)
(* Instantiate ∀R at R₀ = λl' w. (l' = NIL ⇒ w = e); beta. *)
graphNilValThm =
  Module[{eV, fV, zV, lpV, wV, xV, tV, yV, r0Tm,
          gNilZTm, gNilZHyp, gNilZUnf, specR0, specR0Beta,
          closedR0, r0NilZ, zEqE, dischGNilZ, genZ},
    eV = mkVar["e", βTy]; fV = mkVar["f", iterFnTy];
    zV = mkVar["z", βTy];
    lpV = mkVar["lp", listTy[αTy]]; wV = mkVar["w", βTy];
    xV = mkVar["x", αTy]; tV = mkVar["t", listTy[αTy]]; yV = mkVar["y", βTy];
    r0Tm = mkAbs[lpV, mkAbs[wV,
      impTm[mkEq[lpV, nilConst[]], mkEq[wV, eV]]]];

    gNilZTm = graphAppTm[eV, fV, nilConst[], zV];
    gNilZHyp = ASSUME[gNilZTm];
    gNilZUnf = EQMP[unfoldGraphApp[eV, fV, nilConst[], zV], gNilZHyp];
    (* (G NIL z) ⊢ ∀R. closed[R] ⇒ R NIL z *)
    specR0 = HOL`Bool`SPEC[r0Tm, gNilZUnf];
    specR0Beta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specR0];
    (* (G NIL z) ⊢ closedBeta[R₀] ⇒ (NIL = NIL ⇒ z = e) *)

    (* closedBeta[R₀] = (NIL=NIL ⇒ e=e)
                      ∧ ∀x t y. (t=NIL ⇒ y=e) ⇒ (CONS x t=NIL ⇒ f x y=e) *)
    closedR0 = Module[{conj1, conj2},
      conj1 = HOL`Bool`DISCH[mkEq[nilConst[], nilConst[]], REFL[eV]];
      conj2 = Module[{outerHypTm, innerHypTm, innerHyp, nilNotConsAt,
                      contradF, fxyEqE, dischCons, dischOuter, gY, gT, gX},
        outerHypTm = impTm[mkEq[tV, nilConst[]], mkEq[yV, eV]];
        innerHypTm = mkEq[mkComb[mkComb[consConst[], xV], tV], nilConst[]];
        innerHyp = ASSUME[innerHypTm];
        nilNotConsAt = HOL`Bool`SPEC[tV,
          HOL`Bool`SPEC[xV, nilNotEqConsThm]];
        (* ⊢ ¬(NIL = CONS x t) *)
        contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[nilNotConsAt],
          HOL`Equal`SYM[innerHyp]];
        (* (CONS x t = NIL) ⊢ F *)
        fxyEqE = HOL`Bool`CONTR[
          mkEq[mkComb[mkComb[fV, xV], yV], eV], contradF];
        (* (CONS x t = NIL) ⊢ f x y = e *)
        dischCons = HOL`Bool`DISCH[innerHypTm, fxyEqE];
        dischOuter = HOL`Bool`DISCH[outerHypTm, dischCons];
        gY = HOL`Bool`GEN[yV, dischOuter];
        gT = HOL`Bool`GEN[tV, gY];
        gX = HOL`Bool`GEN[xV, gT]
      ];
      HOL`Bool`CONJ[conj1, conj2]
    ];
    r0NilZ = HOL`Bool`MP[specR0Beta, closedR0];
    (* (G NIL z) ⊢ NIL = NIL ⇒ z = e *)
    zEqE = HOL`Bool`MP[r0NilZ, REFL[nilConst[]]];
    (* (G NIL z) ⊢ z = e *)
    dischGNilZ = HOL`Bool`DISCH[gNilZTm, zEqE];
    genZ = HOL`Bool`GEN[zV, dischGNilZ]
  ];

(* === Lemma 4 (inversion) :                                     *)
(*   ⊢ ∀x l z. G (CONS x l) z ⇒ ∃y. G l y ∧ z = f x y            *)
(* Instantiate ∀R at                                             *)
(*   R₂ = λl'' w. G l'' w ∧ (∀a t. l''=CONS a t ⇒ ∃y. G t y ∧ w=f a y) *)
(* ============================================================ *)
graphInversionThm =
  Module[{eV, fV, xV, lV, zV, lppV, wV, aV, tV, yV, ypV, r2Tm,
          gConsZTm, gConsZHyp, gConsZUnf, specR2, specR2Beta,
          closedR2, r2ConsZ, secondConj, invAt, dischGConsZ,
          genZ, genL, genX,
          invBody, consXL},
    eV = mkVar["e", βTy]; fV = mkVar["f", iterFnTy];
    xV = mkVar["x", αTy]; lV = mkVar["l", listTy[αTy]]; zV = mkVar["z", βTy];
    lppV = mkVar["lpp", listTy[αTy]]; wV = mkVar["w", βTy];
    aV = mkVar["a", αTy]; tV = mkVar["t", listTy[αTy]]; yV = mkVar["y", βTy];
    consXL = mkComb[mkComb[consConst[], xV], lV];

    (* inversion-body[lTm, wTm] = ∀a t. lTm = CONS a t
                                    ⇒ ∃y. G t y ∧ wTm = f a y *)
    invBody[lTm_, wTm_] := mkComb[forallC[αTy], mkAbs[aV,
      mkComb[forallC[listTy[αTy]], mkAbs[tV,
        impTm[
          mkEq[lTm, mkComb[mkComb[consConst[], aV], tV]],
          mkComb[existsC[βTy], mkAbs[yV,
            andTm[graphAppTm[eV, fV, tV, yV],
                  mkEq[wTm, mkComb[mkComb[fV, aV], yV]]]]]]]]]];

    r2Tm = mkAbs[lppV, mkAbs[wV,
      andTm[graphAppTm[eV, fV, lppV, wV], invBody[lppV, wV]]]];

    gConsZTm = graphAppTm[eV, fV, consXL, zV];
    gConsZHyp = ASSUME[gConsZTm];
    gConsZUnf = EQMP[unfoldGraphApp[eV, fV, consXL, zV], gConsZHyp];
    (* (G (CONS x l) z) ⊢ ∀R. closed[R] ⇒ R (CONS x l) z *)
    specR2 = HOL`Bool`SPEC[r2Tm, gConsZUnf];
    specR2Beta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specR2];
    (* (G (CONS x l) z) ⊢ closedBeta[R₂]
                          ⇒ (G (CONS x l) z ∧ invBody[CONS x l, z]) *)

    closedR2 = Module[{r2NilBeta, r2StepBeta},
      (* R₂ NIL e (beta) = G NIL e ∧ invBody[NIL, e] *)
      r2NilBeta = Module[{invNil, gNilE},
        gNilE = graphNilThm;
        invNil = Module[{aHypTm, aHyp, nilNotConsAt, contradF,
                         exTm, exFromF, dischA, gT2, gA2},
          aHypTm = mkEq[nilConst[], mkComb[mkComb[consConst[], aV], tV]];
          aHyp = ASSUME[aHypTm];
          nilNotConsAt = HOL`Bool`SPEC[tV,
            HOL`Bool`SPEC[aV, nilNotEqConsThm]];
          (* ⊢ ¬(NIL = CONS a t) *)
          contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[nilNotConsAt], aHyp];
          (* (NIL = CONS a t) ⊢ F *)
          exTm = mkComb[existsC[βTy], mkAbs[yV,
            andTm[graphAppTm[eV, fV, tV, yV],
                  mkEq[eV, mkComb[mkComb[fV, aV], yV]]]]];
          exFromF = HOL`Bool`CONTR[exTm, contradF];
          dischA = HOL`Bool`DISCH[aHypTm, exFromF];
          gT2 = HOL`Bool`GEN[tV, dischA];
          gA2 = HOL`Bool`GEN[aV, gT2]
        ];
        HOL`Bool`CONJ[gNilE, invNil]
      ];
      (* R₂-step (beta): ∀x' l'' y'.
           (G l'' y' ∧ invBody[l'', y'])
           ⇒ (G (CONS x' l'') (f x' y') ∧ invBody[CONS x' l'', f x' y']) *)
      r2StepBeta = Module[{xpV, lppV2, ypV2, hypTm, hypHyp, gLppYp,
                           gConsStep, invStep, conjGoal, dischHyp,
                           gYp, gLpp, gXp},
        xpV = mkVar["x", αTy];
        lppV2 = mkVar["lpp", listTy[αTy]];
        ypV2 = mkVar["yp", βTy];
        hypTm = andTm[graphAppTm[eV, fV, lppV2, ypV2],
                      invBody[lppV2, ypV2]];
        hypHyp = ASSUME[hypTm];
        gLppYp = HOL`Bool`CONJUNCT1[hypHyp];
        (* (hyp) ⊢ G lpp yp *)
        gConsStep = HOL`Bool`MP[
          HOL`Bool`SPEC[ypV2,
            HOL`Bool`SPEC[lppV2, HOL`Bool`SPEC[xpV, graphConsThm]]],
          gLppYp];
        (* (hyp) ⊢ G (CONS x' lpp) (f x' yp) *)
        invStep = Module[{aHypTm, aHyp, consInjAt, xpEqA, lppEqT,
                          gTyp, gLppEq, fEq, conjY, existsY, dischA, gT3, gA3},
          aHypTm = mkEq[mkComb[mkComb[consConst[], xpV], lppV2],
                        mkComb[mkComb[consConst[], aV], tV]];
          aHyp = ASSUME[aHypTm];
          consInjAt = HOL`Bool`MP[
            HOL`Bool`SPEC[tV,
              HOL`Bool`SPEC[lppV2,
                HOL`Bool`SPEC[aV, HOL`Bool`SPEC[xpV, consInjThm]]]],
            aHyp];
          (* (CONS x' lpp = CONS a t) ⊢ x' = a ∧ lpp = t *)
          xpEqA = HOL`Bool`CONJUNCT1[consInjAt];
          lppEqT = HOL`Bool`CONJUNCT2[consInjAt];
          (* G t yp from G lpp yp + lpp = t *)
          gLppEq = HOL`Equal`APTHM[
            HOL`Equal`APTERM[
              mkComb[mkComb[listIterGraphConst[], eV], fV], lppEqT],
            ypV2];
          (* ⊢ (G lpp yp) = (G t yp) *)
          gTyp = EQMP[gLppEq, gLppYp];
          (* (hyp, CONS…=CONS…) ⊢ G t yp *)
          (* f x' yp = f a yp from x' = a *)
          fEq = HOL`Equal`APTHM[
            HOL`Equal`APTERM[fV, xpEqA], ypV2];
          (* ⊢ (f x' yp) = (f a yp) *)
          conjY = HOL`Bool`CONJ[gTyp, fEq];
          (* (hyp, …) ⊢ G t yp ∧ f x' yp = f a yp *)
          existsY = HOL`Bool`EXISTS[
            mkComb[existsC[βTy], mkAbs[yV,
              andTm[graphAppTm[eV, fV, tV, yV],
                    mkEq[mkComb[mkComb[fV, xpV], ypV2],
                         mkComb[mkComb[fV, aV], yV]]]]],
            ypV2, conjY];
          (* (hyp, …) ⊢ ∃y. G t y ∧ f x' yp = f a y *)
          dischA = HOL`Bool`DISCH[aHypTm, existsY];
          gT3 = HOL`Bool`GEN[tV, dischA];
          gA3 = HOL`Bool`GEN[aV, gT3]
          (* (hyp) ⊢ invBody[CONS x' lpp, f x' yp] *)
        ];
        conjGoal = HOL`Bool`CONJ[gConsStep, invStep];
        dischHyp = HOL`Bool`DISCH[hypTm, conjGoal];
        gYp = HOL`Bool`GEN[ypV2, dischHyp];
        gLpp = HOL`Bool`GEN[lppV2, gYp];
        gXp = HOL`Bool`GEN[xpV, gLpp]
      ];
      HOL`Bool`CONJ[r2NilBeta, r2StepBeta]
    ];
    r2ConsZ = HOL`Bool`MP[specR2Beta, closedR2];
    (* (G (CONS x l) z) ⊢ G (CONS x l) z ∧ invBody[CONS x l, z] *)
    secondConj = HOL`Bool`CONJUNCT2[r2ConsZ];
    (* (G (CONS x l) z) ⊢ ∀a t. CONS x l = CONS a t
                            ⇒ ∃y. G t y ∧ z = f a y *)
    invAt = HOL`Bool`MP[
      HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV, secondConj]],
      REFL[consXL]];
    (* (G (CONS x l) z) ⊢ ∃y. G l y ∧ z = f x y *)
    dischGConsZ = HOL`Bool`DISCH[gConsZTm, invAt];
    genZ = HOL`Bool`GEN[zV, dischGConsZ];
    genL = HOL`Bool`GEN[lV, genZ];
    genX = HOL`Bool`GEN[xV, genL]
  ];

(* ============================================================ *)
(* M7-4-c.2 : uniqueness + list iteration theorem                *)
(* ============================================================ *)

(* === Lemma 5 (uniqueness) :                                    *)
(*   ⊢ ∀l z z'. G l z ⇒ G l z' ⇒ z = z'                          *)
(* Rule induction: take Φ = λl z. ∀z'. G l z' ⇒ z = z'.          *)
(* closed[Φ] via graphNilValThm (NIL clause) and                 *)
(* graphInversionThm (CONS clause); minimality (instantiate ∀R   *)
(* at Φ) gives G ⊆ Φ, i.e. uniqueness.                            *)
(* ============================================================ *)
graphUniqueThm =
  Module[{eV, fV, lV, zV, zpV, phiTm,
          gLZTm, gLZHyp, gLZUnf, specPhi, specPhiBeta,
          closedPhi, phiLZBeta, specZp, dischGLZ, genZp2, genZ, genL},
    eV = mkVar["e", βTy]; fV = mkVar["f", iterFnTy];
    lV = mkVar["l", listTy[αTy]]; zV = mkVar["z", βTy];
    zpV = mkVar["zp", βTy];

    (* Φ = λl z. ∀z'. G l z' ⇒ z = z' *)
    phiTm = mkAbs[lV, mkAbs[zV,
      mkComb[forallC[βTy], mkAbs[zpV,
        impTm[graphAppTm[eV, fV, lV, zpV], mkEq[zV, zpV]]]]]];

    (* closed[Φ] (beta-normal). *)
    closedPhi = Module[{conj1, conj2},
      (* conj1 = Φ NIL e beta = ∀z'. G NIL z' ⇒ e = z' *)
      conj1 = Module[{zp, gNilZpHyp, nilValAt, zpEqE, dischG, genZpC1},
        zp = mkVar["zp", βTy];
        gNilZpHyp = ASSUME[graphAppTm[eV, fV, nilConst[], zp]];
        nilValAt = HOL`Bool`SPEC[zp, graphNilValThm];
        (* ⊢ G NIL zp ⇒ zp = e *)
        zpEqE = HOL`Bool`MP[nilValAt, gNilZpHyp];
        (* (G NIL zp) ⊢ zp = e *)
        dischG = HOL`Bool`DISCH[graphAppTm[eV, fV, nilConst[], zp],
          HOL`Equal`SYM[zpEqE]];
        (* ⊢ G NIL zp ⇒ e = zp *)
        genZpC1 = HOL`Bool`GEN[zp, dischG]
        (* ⊢ ∀z'. G NIL z' ⇒ e = z' *)
      ];
      (* conj2 = Φ-step beta:
         ∀x t y. (∀z'. G t z' ⇒ y = z')
                  ⇒ (∀z'. G (CONS x t) z' ⇒ f x y = z') *)
      conj2 = Module[{xV, tV, yV, phiTYTm, phiTYHyp, zp, consXT,
                      gConsZpTm, gConsZpHyp, invMP, ypV, gTypEqTm,
                      gTypEqHyp, gTyp, zpEqFxyp, phiAtYp, yEqYp,
                      fxyEqFxyp, fxyEqZp, choseYp, dischGCons, genZpC2,
                      dischPhiTY, genY, genT, genX},
        xV = mkVar["x", αTy]; tV = mkVar["t", listTy[αTy]];
        yV = mkVar["y", βTy]; zp = mkVar["zp", βTy]; ypV = mkVar["yp", βTy];
        consXT = mkComb[mkComb[consConst[], xV], tV];
        phiTYTm = mkComb[forallC[βTy], mkAbs[zp,
          impTm[graphAppTm[eV, fV, tV, zp], mkEq[yV, zp]]]];
        phiTYHyp = ASSUME[phiTYTm];
        (* (Φ t y) ⊢ ∀z'. G t z' ⇒ y = z' *)
        gConsZpTm = graphAppTm[eV, fV, consXT, zp];
        gConsZpHyp = ASSUME[gConsZpTm];
        invMP = HOL`Bool`MP[
          HOL`Bool`SPEC[zp,
            HOL`Bool`SPEC[tV, HOL`Bool`SPEC[xV, graphInversionThm]]],
          gConsZpHyp];
        (* (G (CONS x t) zp) ⊢ ∃y. G t y ∧ zp = f x y *)
        gTypEqTm = andTm[graphAppTm[eV, fV, tV, ypV],
                         mkEq[zp, mkComb[mkComb[fV, xV], ypV]]];
        gTypEqHyp = ASSUME[gTypEqTm];
        gTyp = HOL`Bool`CONJUNCT1[gTypEqHyp];
        (* (G t yp ∧ zp = f x yp) ⊢ G t yp *)
        zpEqFxyp = HOL`Bool`CONJUNCT2[gTypEqHyp];
        (* (…) ⊢ zp = f x yp *)
        phiAtYp = HOL`Bool`SPEC[ypV, phiTYHyp];
        (* (Φ t y) ⊢ G t yp ⇒ y = yp *)
        yEqYp = HOL`Bool`MP[phiAtYp, gTyp];
        (* (Φ t y, …) ⊢ y = yp *)
        fxyEqFxyp = HOL`Equal`APTERM[mkComb[fV, xV], yEqYp];
        (* (…) ⊢ f x y = f x yp *)
        fxyEqZp = TRANS[fxyEqFxyp, HOL`Equal`SYM[zpEqFxyp]];
        (* (Φ t y, G t yp ∧ zp = f x yp) ⊢ f x y = zp *)
        choseYp = HOL`Bool`CHOOSE[ypV, invMP, fxyEqZp];
        (* (Φ t y, G (CONS x t) zp) ⊢ f x y = zp *)
        dischGCons = HOL`Bool`DISCH[gConsZpTm, choseYp];
        (* (Φ t y) ⊢ G (CONS x t) zp ⇒ f x y = zp *)
        genZpC2 = HOL`Bool`GEN[zp, dischGCons];
        (* (Φ t y) ⊢ ∀z'. G (CONS x t) z' ⇒ f x y = z' *)
        dischPhiTY = HOL`Bool`DISCH[phiTYTm, genZpC2];
        genY = HOL`Bool`GEN[yV, dischPhiTY];
        genT = HOL`Bool`GEN[tV, genY];
        genX = HOL`Bool`GEN[xV, genT]
      ];
      HOL`Bool`CONJ[conj1, conj2]
    ];

    (* Minimality: instantiate ∀R at Φ. *)
    gLZTm = graphAppTm[eV, fV, lV, zV];
    gLZHyp = ASSUME[gLZTm];
    gLZUnf = EQMP[unfoldGraphApp[eV, fV, lV, zV], gLZHyp];
    (* (G l z) ⊢ ∀R. closed[R] ⇒ R l z *)
    specPhi = HOL`Bool`SPEC[phiTm, gLZUnf];
    specPhiBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specPhi];
    (* (G l z) ⊢ closedBeta[Φ] ⇒ (∀z'. G l z' ⇒ z = z') *)
    phiLZBeta = HOL`Bool`MP[specPhiBeta, closedPhi];
    (* (G l z) ⊢ ∀z'. G l z' ⇒ z = z' *)
    specZp = HOL`Bool`SPEC[zpV, phiLZBeta];
    (* (G l z) ⊢ G l z' ⇒ z = z' *)
    dischGLZ = HOL`Bool`DISCH[gLZTm, specZp];
    (* ⊢ G l z ⇒ G l z' ⇒ z = z' *)
    genZp2 = HOL`Bool`GEN[zpV, dischGLZ];
    genZ = HOL`Bool`GEN[zV, genZp2];
    genL = HOL`Bool`GEN[lV, genZ]
  ];

(* === listIterationThm : assemble g = λl. ε z. G l z === *)
listIterationThm =
  Module[{eV, fV, lV, zV, xV, gVarBndr, gTermVal, gAppTm, gGraphAt,
          gNilEq, gConsEq, genConsEq, exBody, exTm, conjEqs,
          existsG, genF, genE},
    eV = mkVar["e", βTy]; fV = mkVar["f", iterFnTy];
    lV = mkVar["l", listTy[αTy]]; zV = mkVar["z", βTy]; xV = mkVar["x", αTy];

    (* g = λl. ε z. G l z *)
    gTermVal = mkAbs[lV, mkComb[selectC[βTy],
      mkAbs[zV, graphAppTm[eV, fV, lV, zV]]]];
    gAppTm[lTm_] := mkComb[gTermVal, lTm];

    (* gGraphAt[l] : ⊢ G l (g l) *)
    gGraphAt[lTm_] := Module[{existsAtL, predLam, atSelect, betaGL, rewriteEq},
      existsAtL = HOL`Bool`SPEC[lTm, graphExistsThm];
      (* ⊢ ∃z. G l z *)
      predLam = mkAbs[zV, graphAppTm[eV, fV, lTm, zV]];
      atSelect = HOL`Stdlib`Num`selectOfExists[predLam, existsAtL];
      (* ⊢ G l (ε z. G l z) *)
      betaGL = BETACONV[gAppTm[lTm]];
      (* ⊢ g l = ε z. G l z *)
      rewriteEq = HOL`Equal`APTERM[
        mkComb[mkComb[mkComb[listIterGraphConst[], eV], fV], lTm],
        HOL`Equal`SYM[betaGL]];
      (* ⊢ G l (ε z. G l z) = G l (g l) *)
      EQMP[rewriteEq, atSelect]
      (* ⊢ G l (g l) *)
    ];

    (* g NIL = e *)
    gNilEq = HOL`Bool`MP[
      HOL`Bool`SPEC[gAppTm[nilConst[]], graphNilValThm],
      gGraphAt[nilConst[]]];
    (* ⊢ g NIL = e *)

    (* g (CONS x l) = f x (g l) *)
    gConsEq = Module[{consXL, gGraphCons, invMP, ypV, gLypEqTm, gLypEqHyp,
                      gLyp, gConsEqFxyp, gGraphL, uniqAt, ypEqGL,
                      fxGLeq, fxyEqGCons, choseYp},
      consXL = mkComb[mkComb[consConst[], xV], lV];
      gGraphCons = gGraphAt[consXL];
      (* ⊢ G (CONS x l) (g (CONS x l)) *)
      invMP = HOL`Bool`MP[
        HOL`Bool`SPEC[gAppTm[consXL],
          HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV, graphInversionThm]]],
        gGraphCons];
      (* ⊢ ∃y. G l y ∧ g (CONS x l) = f x y *)
      ypV = mkVar["yp", βTy];
      gLypEqTm = andTm[graphAppTm[eV, fV, lV, ypV],
                       mkEq[gAppTm[consXL], mkComb[mkComb[fV, xV], ypV]]];
      gLypEqHyp = ASSUME[gLypEqTm];
      gLyp = HOL`Bool`CONJUNCT1[gLypEqHyp];
      (* (G l yp ∧ g (CONS x l) = f x yp) ⊢ G l yp *)
      gConsEqFxyp = HOL`Bool`CONJUNCT2[gLypEqHyp];
      (* (…) ⊢ g (CONS x l) = f x yp *)
      gGraphL = gGraphAt[lV];
      (* ⊢ G l (g l) *)
      uniqAt = HOL`Bool`SPEC[gAppTm[lV],
        HOL`Bool`SPEC[ypV, HOL`Bool`SPEC[lV, graphUniqueThm]]];
      (* ⊢ G l yp ⇒ G l (g l) ⇒ yp = g l *)
      ypEqGL = HOL`Bool`MP[HOL`Bool`MP[uniqAt, gLyp], gGraphL];
      (* (G l yp ∧ …) ⊢ yp = g l *)
      fxGLeq = HOL`Equal`APTERM[mkComb[fV, xV], ypEqGL];
      (* (…) ⊢ f x yp = f x (g l) *)
      fxyEqGCons = TRANS[gConsEqFxyp, fxGLeq];
      (* (G l yp ∧ g (CONS x l) = f x yp) ⊢ g (CONS x l) = f x (g l) *)
      choseYp = HOL`Bool`CHOOSE[ypV, invMP, fxyEqGCons]
      (* ⊢ g (CONS x l) = f x (g l) *)
    ];

    genConsEq = HOL`Bool`GEN[xV, HOL`Bool`GEN[lV, gConsEq]];
    (* ⊢ ∀x l. g (CONS x l) = f x (g l) *)
    conjEqs = HOL`Bool`CONJ[gNilEq, genConsEq];
    (* ⊢ g NIL = e ∧ ∀x l. g (CONS x l) = f x (g l) *)

    gVarBndr = mkVar["g", tyFun[listTy[αTy], βTy]];
    exBody = andTm[
      mkEq[mkComb[gVarBndr, nilConst[]], eV],
      mkComb[forallC[αTy], mkAbs[xV,
        mkComb[forallC[listTy[αTy]], mkAbs[lV,
          mkEq[mkComb[gVarBndr, mkComb[mkComb[consConst[], xV], lV]],
               mkComb[mkComb[fV, xV], mkComb[gVarBndr, lV]]]]]]]];
    exTm = mkComb[existsC[tyFun[listTy[αTy], βTy]], mkAbs[gVarBndr, exBody]];
    existsG = HOL`Bool`EXISTS[exTm, gTermVal, conjEqs];
    (* ⊢ ∃g. g NIL = e ∧ ∀x l. g (CONS x l) = f x (g l) *)
    genF = HOL`Bool`GEN[fV, existsG];
    genE = HOL`Bool`GEN[eV, genF]
  ];

(* ============================================================ *)
(* M7-4-d : APPEND / MAP / FILTER / FOLDR / FOLDL                *)
(* ============================================================ *)

nilAt[ty_]  := mkConst["NIL", listTy[ty]];
consAt[ty_] := mkConst["CONS", tyFun[ty, tyFun[listTy[ty], listTy[ty]]]];
consApp[ty_, xTm_, lTm_] := mkComb[mkComb[consAt[ty], xTm], lTm];

(* listRecExists[elemTy, eTm, fTm] — instantiate listIterationThm at  *)
(* (A:=elemTy, B:=typeOf[eTm]), specialize e,f, then select a witness *)
(* g. Returns {satThm, selTerm} where selTerm = ε g. P g (the chosen  *)
(* function) and satThm ⊢ selTerm NIL = e ∧ ∀x l. selTerm (CONS x l)  *)
(* = f x (selTerm l). NIL/CONS in the recursion are at elemTy.        *)
(* selectOfExists β-reduces the predicate-application internally, so   *)
(* the existsTh handed to it must already be β-normal — otherwise a     *)
(* lambda step f (MAP/FILTER) leaves f x (g l) unreduced in existsTh    *)
(* but reduced in the CHOOSE body, the hyp fails to discharge, and the  *)
(* leftover hyp (carrying f's free vars) later blocks GEN. Normalize.   *)
listRecExists[elemTy_, eTm_, fTm_] :=
  Module[{bTy, gTy, instThm, specEF, specNorm, predLam, selTerm, satThm},
    bTy = typeOf[eTm];
    gTy = tyFun[listTy[elemTy], bTy];
    instThm = INSTTYPE[{αTy -> elemTy, βTy -> bTy}, listIterationThm];
    specEF = HOL`Bool`SPEC[fTm, HOL`Bool`SPEC[eTm, instThm]];
    specNorm = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specEF];
    predLam = concl[specNorm][[2]];
    selTerm = mkComb[selectC[gTy], predLam];
    satThm = HOL`Stdlib`Num`selectOfExists[predLam, specNorm];
    {satThm, selTerm}
  ];

(* ---- FOLDR ------------------------------------------------- *)

foldrTy = tyFun[iterFnTy, tyFun[βTy, tyFun[listTy[αTy], βTy]]];

Module[{fV, eV, selTerm, foldrBody},
  fV = mkVar["f", iterFnTy]; eV = mkVar["e", βTy];
  selTerm = listRecExists[αTy, eV, fV][[2]];
  foldrBody = mkAbs[fV, mkAbs[eV, selTerm]];
  foldrDefThm = newDefinition[mkEq[mkVar["FOLDR", foldrTy], foldrBody]];
];

foldrConst[] := mkConst["FOLDR", foldrTy];

(* foldrAppEq[fTm, eTm] — ⊢ FOLDR f e = (ε g. …) (the witness g). *)
foldrAppEq[fTm_, eTm_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[foldrDefThm, fTm];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, eTm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

{foldrNilThm, foldrConsThm} =
  Module[{fV, eV, xV, lV, satThm, selTerm, appEq, gNilEq,
          foldrNilBase, consXL, gConsSpec, gLEq, lhsCons, fxGL,
          foldrConsBase},
    fV = mkVar["f", iterFnTy]; eV = mkVar["e", βTy];
    xV = mkVar["x", αTy]; lV = mkVar["l", listTy[αTy]];
    {satThm, selTerm} = listRecExists[αTy, eV, fV];
    appEq = foldrAppEq[fV, eV];
    (* ⊢ FOLDR f e = selTerm *)

    gNilEq = HOL`Bool`CONJUNCT1[satThm];
    (* ⊢ selTerm NIL = e *)
    foldrNilBase = TRANS[HOL`Equal`APTHM[appEq, nilConst[]], gNilEq];
    (* ⊢ FOLDR f e NIL = e *)

    consXL = mkComb[mkComb[consConst[], xV], lV];
    gConsSpec = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV,
      HOL`Bool`CONJUNCT2[satThm]]];
    (* ⊢ selTerm (CONS x l) = f x (selTerm l) *)
    lhsCons = TRANS[HOL`Equal`APTHM[appEq, consXL], gConsSpec];
    (* ⊢ FOLDR f e (CONS x l) = f x (selTerm l) *)
    gLEq = HOL`Equal`SYM[HOL`Equal`APTHM[appEq, lV]];
    (* ⊢ selTerm l = FOLDR f e l *)
    fxGL = HOL`Equal`APTERM[mkComb[fV, xV], gLEq];
    (* ⊢ f x (selTerm l) = f x (FOLDR f e l) *)
    foldrConsBase = TRANS[lhsCons, fxGL];
    (* ⊢ FOLDR f e (CONS x l) = f x (FOLDR f e l) *)

    {HOL`Bool`GEN[fV, HOL`Bool`GEN[eV, foldrNilBase]],
     HOL`Bool`GEN[fV, HOL`Bool`GEN[eV, HOL`Bool`GEN[xV,
       HOL`Bool`GEN[lV, foldrConsBase]]]]}
  ];

(* ---- APPEND ------------------------------------------------ *)
(* APPEND l1 l2 recurses on l1 with base l2, step CONS.          *)

appendTy = tyFun[listTy[αTy], tyFun[listTy[αTy], listTy[αTy]]];

Module[{l1V, l2V, selTerm, appendBody},
  l1V = mkVar["l1", listTy[αTy]]; l2V = mkVar["l2", listTy[αTy]];
  selTerm = listRecExists[αTy, l2V, consConst[]][[2]];
  appendBody = mkAbs[l1V, mkAbs[l2V, mkComb[selTerm, l1V]]];
  appendDefThm = newDefinition[mkEq[mkVar["APPEND", appendTy], appendBody]];
];

appendConst[] := mkConst["APPEND", appendTy];

appendAppEq[l1Tm_, l2Tm_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[appendDefThm, l1Tm];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, l2Tm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

{appendNilThm, appendConsThm} =
  Module[{xV, l1V, l2V, satThm, selTerm, gNilEq, nilBase,
          consXL1, gConsSpec, stepThm, eqRec, consBase},
    xV = mkVar["x", αTy];
    l1V = mkVar["l1", listTy[αTy]]; l2V = mkVar["l2", listTy[αTy]];
    {satThm, selTerm} = listRecExists[αTy, l2V, consConst[]];

    gNilEq = HOL`Bool`CONJUNCT1[satThm];
    (* ⊢ selTerm NIL = l2 *)
    nilBase = TRANS[appendAppEq[nilConst[], l2V], gNilEq];
    (* ⊢ APPEND NIL l2 = l2 *)

    consXL1 = mkComb[mkComb[consConst[], xV], l1V];
    gConsSpec = HOL`Bool`SPEC[l1V, HOL`Bool`SPEC[xV,
      HOL`Bool`CONJUNCT2[satThm]]];
    (* ⊢ selTerm (CONS x l1) = CONS x (selTerm l1) *)
    stepThm = TRANS[appendAppEq[consXL1, l2V], gConsSpec];
    (* ⊢ APPEND (CONS x l1) l2 = CONS x (selTerm l1) *)
    eqRec = HOL`Equal`SYM[appendAppEq[l1V, l2V]];
    (* ⊢ selTerm l1 = APPEND l1 l2 *)
    consBase = HOL`Drule`SUBS[{eqRec}, stepThm];
    (* ⊢ APPEND (CONS x l1) l2 = CONS x (APPEND l1 l2) *)

    {HOL`Bool`GEN[l2V, nilBase],
     HOL`Bool`GEN[xV, HOL`Bool`GEN[l1V, HOL`Bool`GEN[l2V, consBase]]]}
  ];

(* ---- MAP --------------------------------------------------- *)
(* MAP h l recurses on l; base NIL:β list, step λx r. CONS(h x) r. *)

Module[{hTy, hV, lV, xV, rV, fMap, eMap, selTerm, mapTy, mapBody},
  hTy = tyFun[αTy, βTy];
  hV = mkVar["h", hTy]; lV = mkVar["l", listTy[αTy]];
  xV = mkVar["x", αTy]; rV = mkVar["r", listTy[βTy]];
  fMap = mkAbs[xV, mkAbs[rV, consApp[βTy, mkComb[hV, xV], rV]]];
  eMap = nilAt[βTy];
  selTerm = listRecExists[αTy, eMap, fMap][[2]];
  mapTy = tyFun[hTy, tyFun[listTy[αTy], listTy[βTy]]];
  mapBody = mkAbs[hV, mkAbs[lV, mkComb[selTerm, lV]]];
  mapDefThm = newDefinition[mkEq[mkVar["MAP", mapTy], mapBody]];
];

mapConst[] := mkConst["MAP", tyFun[tyFun[αTy, βTy],
  tyFun[listTy[αTy], listTy[βTy]]]];

mapAppEq[hTm_, lTm_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[mapDefThm, hTm];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, lTm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

{mapNilThm, mapConsThm} =
  Module[{hTy, hV, lV, xV, fMap, eMap, satThm, selTerm, gNilEq, nilBase,
          consXL, gConsSpec, stepThm, eqRec, consBase},
    hTy = tyFun[αTy, βTy];
    hV = mkVar["h", hTy]; lV = mkVar["l", listTy[αTy]]; xV = mkVar["x", αTy];
    fMap = mkAbs[xV, mkAbs[mkVar["r", listTy[βTy]],
      consApp[βTy, mkComb[hV, xV], mkVar["r", listTy[βTy]]]]];
    eMap = nilAt[βTy];
    {satThm, selTerm} = listRecExists[αTy, eMap, fMap];

    gNilEq = HOL`Bool`CONJUNCT1[satThm];
    (* ⊢ selTerm NIL = NIL *)
    nilBase = TRANS[mapAppEq[hV, nilConst[]], gNilEq];
    (* ⊢ MAP h NIL = NIL *)

    consXL = mkComb[mkComb[consConst[], xV], lV];
    gConsSpec = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV,
      HOL`Bool`CONJUNCT2[satThm]]];
    (* ⊢ selTerm (CONS x l) = CONS (h x) (selTerm l) *)
    stepThm = TRANS[mapAppEq[hV, consXL], gConsSpec];
    (* ⊢ MAP h (CONS x l) = CONS (h x) (selTerm l) *)
    eqRec = HOL`Equal`SYM[mapAppEq[hV, lV]];
    (* ⊢ selTerm l = MAP h l *)
    consBase = HOL`Drule`SUBS[{eqRec}, stepThm];
    (* ⊢ MAP h (CONS x l) = CONS (h x) (MAP h l) *)

    {HOL`Bool`GEN[hV, nilBase],
     HOL`Bool`GEN[hV, HOL`Bool`GEN[xV, HOL`Bool`GEN[lV, consBase]]]}
  ];

(* ---- FILTER ------------------------------------------------ *)
(* step λx r. COND (p x) (CONS x r) r ; base NIL.                *)

filterTy = tyFun[tyFun[αTy, boolTy], tyFun[listTy[αTy], listTy[αTy]]];

filterStep[pV_] :=
  Module[{xV, rV, condTm},
    xV = mkVar["x", αTy]; rV = mkVar["r", listTy[αTy]];
    condTm = HOL`Bool`condConst[listTy[αTy]];
    mkAbs[xV, mkAbs[rV,
      mkComb[mkComb[mkComb[condTm, mkComb[pV, xV]],
        consApp[αTy, xV, rV]], rV]]]
  ];

Module[{pV, selTerm, filterBody},
  pV = mkVar["p", tyFun[αTy, boolTy]];
  selTerm = listRecExists[αTy, nilConst[], filterStep[pV]][[2]];
  filterBody = mkAbs[pV, mkAbs[mkVar["l", listTy[αTy]],
    mkComb[selTerm, mkVar["l", listTy[αTy]]]]];
  filterDefThm = newDefinition[mkEq[mkVar["FILTER", filterTy], filterBody]];
];

filterConst[] := mkConst["FILTER", filterTy];

filterAppEq[pTm_, lTm_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[filterDefThm, pTm];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, lTm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

{filterNilThm, filterConsThm} =
  Module[{pV, lV, xV, satThm, selTerm, gNilEq, nilBase,
          consXL, gConsSpec, stepThm, eqRec, consBase},
    pV = mkVar["p", tyFun[αTy, boolTy]];
    lV = mkVar["l", listTy[αTy]]; xV = mkVar["x", αTy];
    {satThm, selTerm} = listRecExists[αTy, nilConst[], filterStep[pV]];

    gNilEq = HOL`Bool`CONJUNCT1[satThm];
    nilBase = TRANS[filterAppEq[pV, nilConst[]], gNilEq];
    (* ⊢ FILTER p NIL = NIL *)

    consXL = mkComb[mkComb[consConst[], xV], lV];
    gConsSpec = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV,
      HOL`Bool`CONJUNCT2[satThm]]];
    (* ⊢ selTerm (CONS x l) = COND (p x) (CONS x (selTerm l)) (selTerm l) *)
    stepThm = TRANS[filterAppEq[pV, consXL], gConsSpec];
    eqRec = HOL`Equal`SYM[filterAppEq[pV, lV]];
    (* ⊢ selTerm l = FILTER p l *)
    consBase = HOL`Drule`SUBS[{eqRec}, stepThm];
    (* ⊢ FILTER p (CONS x l)
         = COND (p x) (CONS x (FILTER p l)) (FILTER p l) *)

    {HOL`Bool`GEN[pV, nilBase],
     HOL`Bool`GEN[pV, HOL`Bool`GEN[xV, HOL`Bool`GEN[lV, consBase]]]}
  ];

(* ---- FOLDL ------------------------------------------------- *)
(* FOLDL f e l = FOLDR (λx rec a. rec (f a x)) (λa. a) l e,       *)
(* the inner FOLDR at target type β→β.                           *)

bbTy = tyFun[βTy, βTy];
foldlFnTy = tyFun[βTy, tyFun[αTy, βTy]];
foldlTy = tyFun[foldlFnTy, tyFun[βTy, tyFun[listTy[αTy], βTy]]];
foldrInstTy = tyFun[tyFun[αTy, tyFun[bbTy, bbTy]],
  tyFun[bbTy, tyFun[listTy[αTy], bbTy]]];

foldlStep[fTm_] :=
  Module[{xV, recV, aV},
    xV = mkVar["x", αTy]; recV = mkVar["rec", bbTy]; aV = mkVar["a", βTy];
    mkAbs[xV, mkAbs[recV, mkAbs[aV,
      mkComb[recV, mkComb[mkComb[fTm, aV], xV]]]]]
  ];

foldlBase[] := mkAbs[mkVar["a", βTy], mkVar["a", βTy]];

Module[{fV, eV, lV, foldrInst, foldrApplied, foldlInner, foldlBody},
  fV = mkVar["f", foldlFnTy]; eV = mkVar["e", βTy];
  lV = mkVar["l", listTy[αTy]];
  foldrInst = mkConst["FOLDR", foldrInstTy];
  foldrApplied = mkComb[mkComb[mkComb[foldrInst, foldlStep[fV]],
    foldlBase[]], lV];
  foldlInner = mkComb[foldrApplied, eV];
  foldlBody = mkAbs[fV, mkAbs[eV, mkAbs[lV, foldlInner]]];
  foldlDefThm = newDefinition[mkEq[mkVar["FOLDL", foldlTy], foldlBody]];
];

foldlConst[] := mkConst["FOLDL", foldlTy];

foldlAppEq[fTm_, eTm_, lTm_] :=
  Module[{ap1, e1, ap2, e2, ap3},
    ap1 = HOL`Equal`APTHM[foldlDefThm, fTm];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, eTm];
    e2 = TRANS[ap2, BETACONV[concl[ap2][[2]]]];
    ap3 = HOL`Equal`APTHM[e2, lTm];
    TRANS[ap3, BETACONV[concl[ap3][[2]]]]
  ];

{foldlNilThm, foldlConsThm} =
  Module[{fV, eV, xV, lV, foldrNilInst, foldrConsInst, step, base,
          foldrNilAt, applyE, baseEbeta, nilBase, consXL, foldrConsAt,
          applyEcons, reducedRhs, foldlAppCons, recCall, consBase},
    fV = mkVar["f", foldlFnTy]; eV = mkVar["e", βTy];
    xV = mkVar["x", αTy]; lV = mkVar["l", listTy[αTy]];
    step = foldlStep[fV]; base = foldlBase[];
    foldrNilInst = INSTTYPE[{βTy -> bbTy}, foldrNilThm];
    foldrConsInst = INSTTYPE[{βTy -> bbTy}, foldrConsThm];

    (* NIL clause *)
    foldrNilAt = HOL`Bool`SPEC[base, HOL`Bool`SPEC[step, foldrNilInst]];
    (* ⊢ FOLDR step base NIL = base *)
    applyE = HOL`Equal`APTHM[foldrNilAt, eV];
    (* ⊢ (FOLDR step base NIL) e = base e *)
    baseEbeta = BETACONV[concl[applyE][[2]]];
    (* ⊢ base e = e *)
    nilBase = TRANS[foldlAppEq[fV, eV, nilConst[]],
      TRANS[applyE, baseEbeta]];
    (* ⊢ FOLDL f e NIL = e *)

    (* CONS clause *)
    consXL = mkComb[mkComb[consConst[], xV], lV];
    foldrConsAt = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV,
      HOL`Bool`SPEC[base, HOL`Bool`SPEC[step, foldrConsInst]]]];
    (* ⊢ FOLDR step base (CONS x l) = step x (FOLDR step base l) *)
    applyEcons = HOL`Equal`APTHM[foldrConsAt, eV];
    (* ⊢ (FOLDR step base (CONS x l)) e = (step x (FOLDR step base l)) e *)
    reducedRhs = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], applyEcons];
    (* ⊢ (FOLDR step base (CONS x l)) e = (FOLDR step base l) (f e x) *)
    foldlAppCons = foldlAppEq[fV, eV, consXL];
    (* ⊢ FOLDL f e (CONS x l) = (FOLDR step base (CONS x l)) e *)
    recCall = HOL`Equal`SYM[
      foldlAppEq[fV, mkComb[mkComb[fV, eV], xV], lV]];
    (* ⊢ (FOLDR step base l) (f e x) = FOLDL f (f e x) l *)
    consBase = TRANS[foldlAppCons, TRANS[reducedRhs, recCall]];
    (* ⊢ FOLDL f e (CONS x l) = FOLDL f (f e x) l *)

    {HOL`Bool`GEN[fV, HOL`Bool`GEN[eV, nilBase]],
     HOL`Bool`GEN[fV, HOL`Bool`GEN[eV, HOL`Bool`GEN[xV,
       HOL`Bool`GEN[lV, consBase]]]]}
  ];

End[];
EndPackage[];
