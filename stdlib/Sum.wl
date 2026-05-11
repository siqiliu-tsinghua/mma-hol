(* ::Package:: *)

(* M7-1d stdlib/Sum — sum type α + β (type-introduction stage).

   Following HOL Light sum.ml: encode α + β as α → β → bool → bool
   functions of one of two forms:

     mkInl a = λa' b' p'. (a = a') ∧ p'
     mkInr b = λa' b' p'. (b = b') ∧ ¬p'

   The bool argument acts as a tag: the function returns true only when
   the "right" side matches. The closed predicate

     isSum P = (∃a. P = mkInl a) ∨ (∃b. P = mkInr b)

   carves out exactly these characteristic functions; newBasicTypeDefinition
   gives the type `sum` together with ABS_sum / REP_sum.

   This first cut builds the type and the INL / INR constructors. Mkinl /
   mkInr extensional injectivity, INL / INR injectivity, disjointness,
   and the outl / outr destructors come in M7-1e.

   Public API:
     - mkInlConst[], mkInrConst[]
     - mkInlDefThm, mkInrDefThm
     - sumTy[a, b]
     - absSumConst[], repSumConst[]
     - absRepSumThm, repAbsSumThm
     - inlConst[], inrConst[]
     - inlDefThm, inrDefThm
     - inlTerm[a], inrTerm[b]
*)

BeginPackage["HOL`Stdlib`Sum`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`"
}];

mkInlConst::usage =
  "mkInlConst[] — underlying `mkInl : α → α → β → bool → bool` such " <>
  "that `mkInl a = λa' b' p'. (a = a') ∧ p'`.";

mkInrConst::usage =
  "mkInrConst[] — underlying `mkInr : β → α → β → bool → bool` such " <>
  "that `mkInr b = λa' b' p'. (b = b') ∧ ¬p'`.";

mkInlDefThm::usage = "mkInlDefThm — defining equation of mkInl.";
mkInrDefThm::usage = "mkInrDefThm — defining equation of mkInr.";

sumTy::usage = "sumTy[a, b] — the sum type tyApp[\"sum\", {a, b}].";

absSumConst::usage = "absSumConst[] — ABS_sum constant from newBasicTypeDefinition.";
repSumConst::usage = "repSumConst[] — REP_sum constant from newBasicTypeDefinition.";

absRepSumThm::usage = "absRepSumThm — ⊢ ABS_sum (REP_sum a) = a.";
repAbsSumThm::usage =
  "repAbsSumThm — ⊢ (λP. (∃a. P = mkInl a) ∨ (∃b. P = mkInr b)) r ⇔ " <>
  "(REP_sum (ABS_sum r) = r).";

isSumPredicate::usage =
  "isSumPredicate[] — the closed predicate λP. (∃a. P = mkInl a) ∨ " <>
  "(∃b. P = mkInr b) used to carve out the sum type. Returned as a "  <>
  "term, not a constant.";

isSumWitnessThm::usage =
  "isSumWitnessThm — ⊢ (predicate) (mkInl a₀). The DISJ1 witness used " <>
  "by newBasicTypeDefinition.";

inlConst::usage = "inlConst[] — constructor INL : α → α + β.";
inrConst::usage = "inrConst[] — constructor INR : β → α + β.";

inlDefThm::usage = "inlDefThm — ⊢ INL = (λa. ABS_sum (mkInl a)).";
inrDefThm::usage = "inrDefThm — ⊢ INR = (λb. ABS_sum (mkInr b)).";

inlTerm::usage = "inlTerm[a] — build the term `INL a`.";
inrTerm::usage = "inrTerm[b] — build the term `INR b`.";

isSumWitnessInrThm::usage =
  "isSumWitnessInrThm — ⊢ (predicate) (mkInr b₀). Companion of " <>
  "isSumWitnessThm (which covers the INL case); needed to bridge "  <>
  "REP_sum (INR b) = mkInr b through repAbsSumThm.";

repInlThm::usage = "repInlThm — ⊢ REP_sum (INL a) = mkInl a.";
repInrThm::usage = "repInrThm — ⊢ REP_sum (INR b) = mkInr b.";

mkInlInjThm::usage =
  "mkInlInjThm — ⊢ (mkInl a = mkInl aP) ⇒ (a = aP). Extensional " <>
  "injectivity of the underlying mkInl, derived by applying both "  <>
  "sides at (a, bDummy, T).";

mkInrInjThm::usage =
  "mkInrInjThm — ⊢ (mkInr b = mkInr bP) ⇒ (b = bP). Mirror of "    <>
  "mkInlInjThm, applied at (aDummy, b, F).";

inlInjThm::usage =
  "inlInjThm — ⊢ (INL a = INL aP) ⇒ (a = aP). Chain: APTERM " <>
  "REP_sum + repInlThm bridges + mkInlInjThm.";

inrInjThm::usage =
  "inrInjThm — ⊢ (INR b = INR bP) ⇒ (b = bP). Mirror of inlInjThm.";

inlNotEqInrThm::usage =
  "inlNotEqInrThm — ⊢ ¬ (INL a = INR b). Disjointness: apply REP_sum " <>
  "to both sides, evaluate at (a, b, T), giving T = F contradiction.";

Begin["`Private`"];

(* ============================================================ *)
(* Type vars / canonical bool consts                            *)
(* ============================================================ *)

αTy = mkVarType["A"];
βTy = mkVarType["B"];

repSumTy = tyFun[αTy, tyFun[βTy, tyFun[boolTy, boolTy]]];
mkInlTy = tyFun[αTy, repSumTy];
mkInrTy = tyFun[βTy, repSumTy];

andC[]      := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
orC[]       := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notC[]      := mkConst["¬", tyFun[boolTy, boolTy]];
existsC[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];

(* ============================================================ *)
(* mkInl, mkInr definitions                                     *)
(* ============================================================ *)

mkInlLambdaTerm[] :=
  Module[{a, aP, bP, pP, body},
    a  = mkVar["a", αTy];
    aP = mkVar["aP", αTy];
    bP = mkVar["bP", βTy];
    pP = mkVar["pP", boolTy];
    body = mkComb[mkComb[andC[], mkEq[a, aP]], pP];
    mkAbs[a, mkAbs[aP, mkAbs[bP, mkAbs[pP, body]]]]
  ];

mkInrLambdaTerm[] :=
  Module[{b, aP, bP, pP, body},
    b  = mkVar["b", βTy];
    aP = mkVar["aP", αTy];
    bP = mkVar["bP", βTy];
    pP = mkVar["pP", boolTy];
    body = mkComb[mkComb[andC[], mkEq[b, bP]], mkComb[notC[], pP]];
    mkAbs[b, mkAbs[aP, mkAbs[bP, mkAbs[pP, body]]]]
  ];

mkInlDefThm = newDefinition[
  mkEq[mkVar["mkInl", mkInlTy], mkInlLambdaTerm[]]];
mkInrDefThm = newDefinition[
  mkEq[mkVar["mkInr", mkInrTy], mkInrLambdaTerm[]]];

mkInlConst[] := mkConst["mkInl", mkInlTy];
mkInrConst[] := mkConst["mkInr", mkInrTy];

(* ============================================================ *)
(* isSum predicate                                              *)
(*   isSum P = (∃a. P = mkInl a) ∨ (∃b. P = mkInr b)            *)
(* ============================================================ *)

isSumPredicateTerm[] :=
  Module[{pV, aV, bV, mInl, mInr,
          leftEq, leftLam, leftEx,
          rightEq, rightLam, rightEx,
          disj},
    pV = mkVar["P", repSumTy];
    aV = mkVar["a", αTy]; bV = mkVar["b", βTy];
    mInl = mkInlConst[]; mInr = mkInrConst[];
    leftEq  = mkEq[pV, mkComb[mInl, aV]];
    leftLam = mkAbs[aV, leftEq];
    leftEx  = mkComb[existsC[αTy], leftLam];
    rightEq  = mkEq[pV, mkComb[mInr, bV]];
    rightLam = mkAbs[bV, rightEq];
    rightEx  = mkComb[existsC[βTy], rightLam];
    disj = mkComb[mkComb[orC[], leftEx], rightEx];
    mkAbs[pV, disj]
  ];

isSumPredicate[] := isSumPredicateTerm[];

(* ============================================================ *)
(* Witness theorem ⊢ (predicate) (mkInl a₀)                     *)
(*                                                              *)
(* Strategy: prove the LEFT disjunct ∃a. mkInl a₀ = mkInl a via *)
(* REFL + EXISTS, then DISJ1 to get the full disjunction, then  *)
(* un-beta via SYM[BETACONV] + EQMP.                            *)
(* ============================================================ *)

isSumWitnessThm =
  Module[{a0, mInl, witnessTm, refl,
          aV, leftEq, leftLam, leftExTm, existsA,
          bV, mInr, rightEq, rightLam, rightExTm,
          disj1Th,
          predLambda, predApplied, betaTh},
    a0 = mkVar["a0", αTy];
    mInl = mkInlConst[];
    witnessTm = mkComb[mInl, a0];           (* mkInl a₀ *)
    refl = REFL[witnessTm];                  (* ⊢ mkInl a₀ = mkInl a₀ *)

    aV = mkVar["a", αTy];
    leftEq  = mkEq[witnessTm, mkComb[mInl, aV]];
    leftLam = mkAbs[aV, leftEq];
    leftExTm = mkComb[existsC[αTy], leftLam];
    existsA = HOL`Bool`EXISTS[leftExTm, a0, refl];
    (* existsA : ⊢ ∃a. mkInl a₀ = mkInl a *)

    bV = mkVar["b", βTy];
    mInr = mkInrConst[];
    rightEq  = mkEq[witnessTm, mkComb[mInr, bV]];
    rightLam = mkAbs[bV, rightEq];
    rightExTm = mkComb[existsC[βTy], rightLam];

    disj1Th = HOL`Bool`DISJ1[existsA, rightExTm];
    (* disj1Th : ⊢ (∃a. mkInl a₀ = mkInl a) ∨ (∃b. mkInl a₀ = mkInr b) *)

    predLambda = isSumPredicateTerm[];
    predApplied = mkComb[predLambda, witnessTm];
    betaTh = BETACONV[predApplied];
    EQMP[SYM[betaTh], disj1Th]
  ];

(* ============================================================ *)
(* Introduce the sum type                                       *)
(* ============================================================ *)

{absRepSumThm, repAbsSumThm} =
  newBasicTypeDefinition["sum", "ABS_sum", "REP_sum", isSumWitnessThm];

sumTy[a_, b_] := mkType["sum", {a, b}];

absSumConst[] :=
  mkConst["ABS_sum", tyFun[repSumTy, sumTy[αTy, βTy]]];
repSumConst[] :=
  mkConst["REP_sum", tyFun[sumTy[αTy, βTy], repSumTy]];

(* ============================================================ *)
(* INL, INR constructors                                        *)
(*                                                              *)
(*   INL = λa. ABS_sum (mkInl a)                                *)
(*   INR = λb. ABS_sum (mkInr b)                                *)
(* ============================================================ *)

inlTy = tyFun[αTy, sumTy[αTy, βTy]];
inrTy = tyFun[βTy, sumTy[αTy, βTy]];

inlDefBody[] :=
  Module[{a},
    a = mkVar["a", αTy];
    mkAbs[a, mkComb[absSumConst[], mkComb[mkInlConst[], a]]]
  ];

inrDefBody[] :=
  Module[{b},
    b = mkVar["b", βTy];
    mkAbs[b, mkComb[absSumConst[], mkComb[mkInrConst[], b]]]
  ];

inlDefThm = newDefinition[mkEq[mkVar["INL", inlTy], inlDefBody[]]];
inrDefThm = newDefinition[mkEq[mkVar["INR", inrTy], inrDefBody[]]];

inlConst[] := mkConst["INL", inlTy];
inrConst[] := mkConst["INR", inrTy];

inlTerm[a_] := mkComb[inlConst[], a];
inrTerm[b_] := mkComb[inrConst[], b];

(* ============================================================ *)
(* Witness theorem ⊢ (predicate) (mkInr b₀) — DISJ2 mirror      *)
(* ============================================================ *)

isSumWitnessInrThm =
  Module[{b0, mInr, witnessTm, refl,
          bV, rightEq, rightLam, rightExTm, existsB,
          aV, mInl, leftEq, leftLam, leftExTm,
          disj2Th,
          predLambda, predApplied, betaTh},
    b0 = mkVar["b0", βTy];
    mInr = mkInrConst[];
    witnessTm = mkComb[mInr, b0];           (* mkInr b₀ *)
    refl = REFL[witnessTm];

    bV = mkVar["b", βTy];
    rightEq  = mkEq[witnessTm, mkComb[mInr, bV]];
    rightLam = mkAbs[bV, rightEq];
    rightExTm = mkComb[existsC[βTy], rightLam];
    existsB = HOL`Bool`EXISTS[rightExTm, b0, refl];
    (* existsB : ⊢ ∃b. mkInr b₀ = mkInr b *)

    aV = mkVar["a", αTy];
    mInl = mkInlConst[];
    leftEq  = mkEq[witnessTm, mkComb[mInl, aV]];
    leftLam = mkAbs[aV, leftEq];
    leftExTm = mkComb[existsC[αTy], leftLam];

    disj2Th = HOL`Bool`DISJ2[existsB, leftExTm];
    (* disj2Th : ⊢ (∃a. mkInr b₀ = mkInl a) ∨ (∃b. mkInr b₀ = mkInr b) *)

    predLambda = isSumPredicateTerm[];
    predApplied = mkComb[predLambda, witnessTm];
    betaTh = BETACONV[predApplied];
    EQMP[SYM[betaTh], disj2Th]
  ];

(* ============================================================ *)
(* repInlThm / repInrThm — bridges                              *)
(* ============================================================ *)

repInlThm =
  Module[{aV, mInl, mkInlA, inlA,
          stepA, stepARhs, stepABeta, unfoldStep,
          repAppliedTh, instIsSum, instRepAbs, repAbsMkInl,
          a0v},
    aV = mkVar["a", αTy];
    mInl = mkInlConst[];
    mkInlA = mkComb[mInl, aV];
    inlA = inlTerm[aV];

    stepA = HOL`Equal`APTHM[inlDefThm, aV];
    stepARhs = concl[stepA][[2]];
    stepABeta = BETACONV[stepARhs];
    unfoldStep = TRANS[stepA, stepABeta];
    (* unfoldStep : ⊢ INL a = ABS_sum (mkInl a) *)

    repAppliedTh = HOL`Equal`APTERM[repSumConst[], unfoldStep];

    instRepAbs = INST[
      {mkVar["r", repSumTy] -> mkInlA},
      repAbsSumThm];
    a0v = mkVar["a0", αTy];
    instIsSum = INST[{a0v -> aV}, isSumWitnessThm];

    repAbsMkInl = EQMP[instRepAbs, instIsSum];
    TRANS[repAppliedTh, repAbsMkInl]
  ];

repInrThm =
  Module[{bV, mInr, mkInrB, inrB,
          stepB, stepBRhs, stepBBeta, unfoldStep,
          repAppliedTh, instIsSum, instRepAbs, repAbsMkInr,
          b0v},
    bV = mkVar["b", βTy];
    mInr = mkInrConst[];
    mkInrB = mkComb[mInr, bV];
    inrB = inrTerm[bV];

    stepB = HOL`Equal`APTHM[inrDefThm, bV];
    stepBRhs = concl[stepB][[2]];
    stepBBeta = BETACONV[stepBRhs];
    unfoldStep = TRANS[stepB, stepBBeta];

    repAppliedTh = HOL`Equal`APTERM[repSumConst[], unfoldStep];

    instRepAbs = INST[
      {mkVar["r", repSumTy] -> mkInrB},
      repAbsSumThm];
    b0v = mkVar["b0", βTy];
    instIsSum = INST[{b0v -> bV}, isSumWitnessInrThm];

    repAbsMkInr = EQMP[instRepAbs, instIsSum];
    TRANS[repAppliedTh, repAbsMkInr]
  ];

(* ============================================================ *)
(* mkInlInjThm / mkInrInjThm — extensional injectivity          *)
(*                                                              *)
(* For mkInl: apply both sides at (a, bDummy, T). The lambda    *)
(*   body (a = a') ∧ p' specialises to (a = a) ∧ T = T on the   *)
(*   LHS and (aP = a) ∧ T = (aP = a) on the RHS, leaving        *)
(*   T = (aP = a). Basic `(T = p) = p` flips, SYM finishes.     *)
(* For mkInr: same pattern at (aDummy, b, F), with ¬F = T via   *)
(*   basicSimpset.                                              *)
(* ============================================================ *)

mkInlInjThm =
  Module[{aV, aPV, bDummy, tConst, hypEq,
          step1, step2, step3, simplifiedEq,
          aEqaTh, conjPart, dischargedTh, symPart},
    aV = mkVar["a", αTy]; aPV = mkVar["aP", αTy];
    bDummy = mkVar["bDummy", βTy];
    tConst = mkConst["T", boolTy];

    hypEq = ASSUME[mkEq[
      mkComb[mkInlConst[], aV],
      mkComb[mkInlConst[], aPV]]];

    step1 = MKCOMB[hypEq, REFL[aV]];
    step2 = MKCOMB[step1, REFL[bDummy]];
    step3 = MKCOMB[step2, REFL[tConst]];
    (* step3 : ⊢ mkInl a a bDummy T = mkInl aP a bDummy T *)

    simplifiedEq = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{mkInlDefThm}], step3];
    (* simplifiedEq : ⊢ ((a = a) ∧ T) = ((aP = a) ∧ T) *)

    aEqaTh = HOL`Bool`EQTINTRO[REFL[aV]];   (* ⊢ (a = a) = T *)
    conjPart = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{aEqaTh}], simplifiedEq];
    (* conjPart : ⊢ aP = a   (after basic T∧T=T, p∧T=p, (T=p)=p collapses) *)

    symPart = HOL`Equal`SYM[conjPart];   (* ⊢ a = aP *)
    dischargedTh = HOL`Bool`DISCH[concl[hypEq], symPart];
    dischargedTh
  ];

mkInrInjThm =
  Module[{bV, bPV, aDummy, fConst, hypEq,
          step1, step2, step3, simplifiedEq,
          bEqbTh, conjPart, dischargedTh, symPart},
    bV = mkVar["b", βTy]; bPV = mkVar["bP", βTy];
    aDummy = mkVar["aDummy", αTy];
    fConst = mkConst["F", boolTy];

    hypEq = ASSUME[mkEq[
      mkComb[mkInrConst[], bV],
      mkComb[mkInrConst[], bPV]]];

    step1 = MKCOMB[hypEq, REFL[aDummy]];
    step2 = MKCOMB[step1, REFL[bV]];
    step3 = MKCOMB[step2, REFL[fConst]];
    (* step3 : ⊢ mkInr b aDummy b F = mkInr bP aDummy b F *)

    simplifiedEq = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{mkInrDefThm}], step3];
    (* simplifiedEq : ⊢ ((b = b) ∧ ¬F) = ((bP = b) ∧ ¬F) *)

    bEqbTh = HOL`Bool`EQTINTRO[REFL[bV]];
    conjPart = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{bEqbTh}], simplifiedEq];

    symPart = HOL`Equal`SYM[conjPart];
    dischargedTh = HOL`Bool`DISCH[concl[hypEq], symPart];
    dischargedTh
  ];

(* ============================================================ *)
(* inlInjThm / inrInjThm — top-level injectivity                *)
(*                                                              *)
(* APTERM REP_sum on the hypothesis, TRANS through the          *)
(* repInlThm / repInrThm bridges, MP with mkInl / mkInr         *)
(* injectivity. DISCH wraps the conclusion.                     *)
(* ============================================================ *)

inlInjThm =
  Module[{aV, aPV, hypEq, repEq,
          repAV, repAPV, mkInlEq, mkInlImp,
          finalImp},
    aV = mkVar["a", αTy]; aPV = mkVar["aP", αTy];
    hypEq = ASSUME[mkEq[inlTerm[aV], inlTerm[aPV]]];
    repEq = HOL`Equal`APTERM[repSumConst[], hypEq];

    repAV = repInlThm;
    repAPV = INST[{aV -> aPV}, repInlThm];
    mkInlEq = TRANS[
      TRANS[HOL`Equal`SYM[repAV], repEq],
      repAPV];
    (* mkInlEq : ⊢ mkInl a = mkInl aP *)

    mkInlImp = mkInlInjThm;
    finalImp = HOL`Bool`MP[mkInlImp, mkInlEq];
    HOL`Bool`DISCH[concl[hypEq], finalImp]
  ];

inrInjThm =
  Module[{bV, bPV, hypEq, repEq,
          repBV, repBPV, mkInrEq, mkInrImp,
          finalImp},
    bV = mkVar["b", βTy]; bPV = mkVar["bP", βTy];
    hypEq = ASSUME[mkEq[inrTerm[bV], inrTerm[bPV]]];
    repEq = HOL`Equal`APTERM[repSumConst[], hypEq];

    repBV = repInrThm;
    repBPV = INST[{bV -> bPV}, repInrThm];
    mkInrEq = TRANS[
      TRANS[HOL`Equal`SYM[repBV], repEq],
      repBPV];

    mkInrImp = mkInrInjThm;
    finalImp = HOL`Bool`MP[mkInrImp, mkInrEq];
    HOL`Bool`DISCH[concl[hypEq], finalImp]
  ];

(* ============================================================ *)
(* inlNotEqInrThm : ⊢ ¬ (INL a = INR b)                          *)
(*                                                              *)
(* APTERM REP_sum on the hypothetical equality; TRANS through  *)
(* repInlThm + SYM[repInrThm] gives mkInl a = mkInr b. Apply at*)
(* (a, b, T) and unfold via simpConv with the def thms +        *)
(* EQTINTRO[REFL[a]] + EQTINTRO[REFL[b]] reduces to T = F,     *)
(* whose EQMP with TRUTH gives F. NOTINTRO closes via DISCH +  *)
(* ⇒-to-¬.                                                     *)
(* ============================================================ *)

inlNotEqInrThm =
  Module[{aV, bV, tConst, hypEq, repEq, mkInlMkInrEq,
          step1, step2, step3, simplifiedEq,
          aEqaTh, bEqbTh, fThm, dischargedTh},
    aV = mkVar["a", αTy]; bV = mkVar["b", βTy];
    tConst = mkConst["T", boolTy];

    hypEq = ASSUME[mkEq[inlTerm[aV], inrTerm[bV]]];
    repEq = HOL`Equal`APTERM[repSumConst[], hypEq];
    (* repEq : ⊢ REP_sum (INL a) = REP_sum (INR b) *)

    (* Bridge to mkInl / mkInr equality. *)
    mkInlMkInrEq = TRANS[
      TRANS[HOL`Equal`SYM[repInlThm], repEq],
      repInrThm];
    (* mkInlMkInrEq : ⊢ mkInl a = mkInr b *)

    step1 = MKCOMB[mkInlMkInrEq, REFL[aV]];
    step2 = MKCOMB[step1, REFL[bV]];
    step3 = MKCOMB[step2, REFL[tConst]];
    (* step3 : ⊢ mkInl a a b T = mkInr b a b T *)

    (* simpConv unfolds both def thms, beta-reduces, applies basic to     *)
    (* collapse (a=a)∧T → (a=a) and (b=b)∧¬T → (b=b)∧F → F. Result: ⊢   *)
    (*   (mkInl a a b T = mkInr b a b T) = ((a = a) = F).                  *)
    simplifiedEq = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{mkInlDefThm, mkInrDefThm}], step3];

    (* Now simpConv with aEqaTh / bEqbTh + basic collapses (a=a) → T then *)
    (* (T = F) → F via basic `(T = p) = p`. The result CONVRULE-EQMPs to *)
    (* ⊢ F directly — no `T = F` intermediate survives.                    *)
    aEqaTh = HOL`Bool`EQTINTRO[REFL[aV]];
    bEqbTh = HOL`Bool`EQTINTRO[REFL[bV]];
    fThm = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{aEqaTh, bEqbTh}], simplifiedEq];
    (* fThm : ⊢ F  (under hyp INL a = INR b) *)

    dischargedTh = HOL`Bool`DISCH[concl[hypEq], fThm];
    HOL`Bool`NOTINTRO[dischargedTh]
    (* ⊢ ¬ (INL a = INR b) *)
  ];

End[];
EndPackage[];
