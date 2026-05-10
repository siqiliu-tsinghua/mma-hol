(* ::Package:: *)

(* M7-1a stdlib/Pair — product type α × β (type-introduction stage).

   Encode pairs as α → β → bool functions of the form `λa b. a = x ∧ b = y`,
   following HOL Light pair.ml. The closed predicate `λp. ∃x y. p = mkPair x y`
   carves out exactly these characteristic functions; newBasicTypeDefinition
   then introduces the type `prod` with abs/rep bijection.

   This first cut builds the type itself + the underlying mkPair function;
   the constructor `,` and projections FST/SND come in a follow-up.

   Public API:
     - mkPairConst[]: the underlying mkPair constant.
     - mkPairDefThm:  ⊢ mkPair = (λx y. λa b. a = x ∧ b = y).
     - prodTy[a, b]:  build the type α × β.
     - absProdConst[]: the ABS_prod constant.
     - repProdConst[]: the REP_prod constant.
     - absRepProdThm: ⊢ ABS_prod (REP_prod a) = a.
     - repAbsProdThm: ⊢ (λp. ∃x y. p = mkPair x y) r = (REP_prod (ABS_prod r) = r).
*)

BeginPackage["HOL`Stdlib`Pair`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`"
}];

mkPairConst::usage =
  "mkPairConst[] — the polymorphic constant `mkPair : α → β → α → β → bool` " <>
  "underlying the product type encoding.";

mkPairDefThm::usage =
  "mkPairDefThm — ⊢ mkPair = (λx y. λa b. (a = x) ∧ (b = y)).";

prodTy::usage =
  "prodTy[a, b] — the product type tyApp[\"prod\", {a, b}].";

absProdConst::usage =
  "absProdConst[] — the ABS_prod constant introduced by newBasicTypeDefinition.";

repProdConst::usage =
  "repProdConst[] — the REP_prod constant introduced by newBasicTypeDefinition.";

absRepProdThm::usage =
  "absRepProdThm — ⊢ ABS_prod (REP_prod a) = a.";

repAbsProdThm::usage =
  "repAbsProdThm — ⊢ (λp. ∃x y. p = mkPair x y) r ⇔ REP_prod (ABS_prod r) = r.";

isPairPredicate::usage =
  "isPairPredicate[] — the closed predicate `λp. ∃x y. p = mkPair x y` " <>
  "used to carve out the product type. Returned as a term, not a constant.";

Begin["`Private`"];

(* ============================================================ *)
(* Bool / kernel constant shorthands                            *)
(* ============================================================ *)

andC[]      := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
existsC[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];

αTy = mkVarType["A"];
βTy = mkVarType["B"];
charTy = tyFun[αTy, tyFun[βTy, boolTy]];     (* α → β → bool *)
mkPairTy = tyFun[αTy, tyFun[βTy, charTy]];   (* α → β → α → β → bool *)

(* ============================================================ *)
(* mkPair = λx y. λa b. (a = x) ∧ (b = y)                       *)
(* ============================================================ *)

mkPairLambdaTerm[] :=
  Module[{x, y, a, b, body},
    x = mkVar["x", αTy]; y = mkVar["y", βTy];
    a = mkVar["a", αTy]; b = mkVar["b", βTy];
    body = mkAbs[a, mkAbs[b,
      mkComb[mkComb[andC[], mkEq[a, x]], mkEq[b, y]]]];
    mkAbs[x, mkAbs[y, body]]
  ];

mkPairDefThm = newDefinition[
  mkEq[mkVar["mkPair", mkPairTy], mkPairLambdaTerm[]]];

mkPairConst[] := mkConst["mkPair", mkPairTy];

(* ============================================================ *)
(* The closed predicate λp. ∃x y. p = mkPair x y               *)
(* ============================================================ *)

isPairPredicateTerm[] :=
  Module[{pVar, xVar, yVar, mkP, eqBody, innerLambda, innerEx,
          outerLambda, outerEx},
    pVar = mkVar["p", charTy];
    xVar = mkVar["x", αTy];
    yVar = mkVar["y", βTy];
    mkP = mkPairConst[];
    eqBody       = mkEq[pVar, mkComb[mkComb[mkP, xVar], yVar]];
    innerLambda  = mkAbs[yVar, eqBody];                (* λy. p = mkPair x y *)
    innerEx      = mkComb[existsC[βTy], innerLambda];  (* ∃y. p = mkPair x y *)
    outerLambda  = mkAbs[xVar, innerEx];               (* λx. ∃y. p = mkPair x y *)
    outerEx      = mkComb[existsC[αTy], outerLambda];  (* ∃x y. p = mkPair x y *)
    mkAbs[pVar, outerEx]                                (* λp. ∃x y. p = mkPair x y *)
  ];

isPairPredicate[] := isPairPredicateTerm[];

(* ============================================================ *)
(* Witness theorem  ⊢ (λp. ∃x y. p = mkPair x y) (mkPair x₀ y₀) *)
(*                                                              *)
(* Build via:                                                   *)
(*   1. refl     : ⊢ mkPair x₀ y₀ = mkPair x₀ y₀                *)
(*   2. existsB  : ⊢ ∃y. mkPair x₀ y₀ = mkPair x₀ y             *)
(*   3. existsAB : ⊢ ∃x y. mkPair x₀ y₀ = mkPair x y            *)
(*   4. betaTh   : ⊢ (predicate) (mkPair x₀ y₀) =               *)
(*                       (∃x y. mkPair x₀ y₀ = mkPair x y)      *)
(*   5. EQMP[SYM[betaTh], existsAB] gives the witness theorem.  *)
(* ============================================================ *)

isPairWitnessThm =
  Module[{x0, y0, mkP, witnessTm, refl,
          yVar, xVar,
          innerEqBody, innerLambda, innerExTm, existsB,
          outerInnerBody, outerInnerLambda, outerInnerEx,
          outerLambda, outerExTm, existsAB,
          predLambda, predApplied, betaTh},
    x0 = mkVar["x0", αTy]; y0 = mkVar["y0", βTy];
    mkP = mkPairConst[];
    witnessTm = mkComb[mkComb[mkP, x0], y0];
    refl = REFL[witnessTm];

    (* ∃y. mkPair x0 y0 = mkPair x0 y *)
    yVar = mkVar["y", βTy];
    innerEqBody = mkEq[witnessTm, mkComb[mkComb[mkP, x0], yVar]];
    innerLambda = mkAbs[yVar, innerEqBody];
    innerExTm = mkComb[existsC[βTy], innerLambda];
    existsB = HOL`Bool`EXISTS[innerExTm, y0, refl];

    (* ∃x. ∃y. mkPair x0 y0 = mkPair x y *)
    xVar = mkVar["x", αTy];
    outerInnerBody = mkEq[witnessTm, mkComb[mkComb[mkP, xVar], yVar]];
    outerInnerLambda = mkAbs[yVar, outerInnerBody];
    outerInnerEx = mkComb[existsC[βTy], outerInnerLambda];
    outerLambda = mkAbs[xVar, outerInnerEx];
    outerExTm = mkComb[existsC[αTy], outerLambda];
    existsAB = HOL`Bool`EXISTS[outerExTm, x0, existsB];

    (* Un-beta: predLambda applied to witness. *)
    predLambda = isPairPredicateTerm[];
    predApplied = mkComb[predLambda, witnessTm];
    betaTh = BETACONV[predApplied];
    EQMP[SYM[betaTh], existsAB]
  ];

(* ============================================================ *)
(* Introduce the prod type                                      *)
(* ============================================================ *)

{absRepProdThm, repAbsProdThm} =
  newBasicTypeDefinition["prod", "ABS_prod", "REP_prod", isPairWitnessThm];

prodTy[a_, b_] := mkType["prod", {a, b}];

absProdConst[] :=
  mkConst["ABS_prod",
    tyFun[charTy, prodTy[αTy, βTy]]];
repProdConst[] :=
  mkConst["REP_prod",
    tyFun[prodTy[αTy, βTy], charTy]];

End[];
EndPackage[];
