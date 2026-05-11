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
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`"
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

End[];
EndPackage[];
