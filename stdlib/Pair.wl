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
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`"
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

pairConsConst::usage =
  "pairConsConst[] — the pair constructor constant `,` : α → β → α × β.";

pairConsDefThm::usage =
  "pairConsDefThm — ⊢ , = (λx y. ABS_prod (mkPair x y)).";

pairCons::usage =
  "pairCons[a, b] — build the pair term `(a, b)` = `mkComb[mkComb[,, a], b]`.";

destPair::usage =
  "destPair[t] — for a term of form `,` x y, return {x, y}; throw otherwise.";

mkPairInjThm::usage =
  "mkPairInjThm — ⊢ (mkPair x y = mkPair x' y') ⇒ (x = x' ∧ y = y'). " <>
  "Extensional injectivity of the underlying mkPair encoding, derived by " <>
  "applying both sides at (x, y) and reducing via mkPairDefThm + " <>
  "EQTINTRO[REFL[v]].";

pairInjThm::usage =
  "pairInjThm — ⊢ ((x, y) = (x', y')) ⇒ (x = x' ∧ y = y'). " <>
  "Injectivity of the `,` constructor. Chain: PAIR equality → apply " <>
  "REP_prod → mkPair equality (via repAbsProdThm + isPairWitness) → " <>
  "mkPair injectivity.";

repPairThm::usage =
  "repPairThm — ⊢ REP_prod (x, y) = mkPair x y. The bridge from the " <>
  "constructor down to the underlying characteristic function.";

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

(* ============================================================ *)
(* Pair constructor  `,` : α → β → α × β                        *)
(*                                                              *)
(*   , = λx y. ABS_prod (mkPair x y)                            *)
(* ============================================================ *)

pairConsTy = tyFun[αTy, tyFun[βTy, prodTy[αTy, βTy]]];

pairConsDefBody[] :=
  Module[{xV, yV},
    xV = mkVar["x", αTy]; yV = mkVar["y", βTy];
    mkAbs[xV, mkAbs[yV,
      mkComb[absProdConst[],
        mkComb[mkComb[mkPairConst[], xV], yV]]]]
  ];

pairConsDefThm = newDefinition[
  mkEq[mkVar[",", pairConsTy], pairConsDefBody[]]];

pairConsConst[] := mkConst[",", pairConsTy];

pairCons[a_, b_] := mkComb[mkComb[pairConsConst[], a], b];

destPair[comb[comb[const[",", _], a_], b_]] := {a, b};
destPair[other_] :=
  HOL`Error`holError["pair", "destPair: not a `,` application",
    <|"got" -> other|>];

(* ============================================================ *)
(* repPairThm : ⊢ REP_prod (x, y) = mkPair x y                  *)
(*                                                              *)
(* Chain:                                                       *)
(*   (a) PAIR x y = ABS_prod (mkPair x y)   — unfold + beta     *)
(*   (b) REP_prod (PAIR x y) =                                  *)
(*           REP_prod (ABS_prod (mkPair x y))   — APTERM        *)
(*   (c) isPair (mkPair x y) ⇔                                  *)
(*           REP_prod (ABS_prod (mkPair x y)) = mkPair x y      *)
(*       — INST r ↦ mkPair x y in repAbsProdThm                 *)
(*   (d) ⊢ REP_prod (ABS_prod (mkPair x y)) = mkPair x y        *)
(*       — EQMP[(c), isPairWitness INST'd]                      *)
(*   (e) TRANS[(b), (d)]                                        *)
(* ============================================================ *)

repPairThm =
  Module[{xV, yV, mkP, mkPairXY, pairXY,
          stepAx, stepAxRhs, stepAxBeta, stepA,
          stepAxy, stepAxyRhs, stepAxyBeta, unfoldStep,
          repAppliedTh, instIsPair, instRepAbs, repAbsMkPair,
          x0v, y0v},
    xV = mkVar["x", αTy]; yV = mkVar["y", βTy];
    mkP = mkPairConst[];
    mkPairXY = mkComb[mkComb[mkP, xV], yV];     (* mkPair x y *)
    pairXY   = pairCons[xV, yV];                 (* (x, y) *)

    (* (a) Unfold `,` via two APTHM + BETACONV steps to get               *)
    (*     ⊢ (x, y) = ABS_prod (mkPair x y).                              *)
    stepAx = HOL`Equal`APTHM[pairConsDefThm, xV];
    (* ⊢ , xV = (λx y. ABS_prod (mkPair x y)) xV *)
    stepAxRhs = concl[stepAx][[2]];
    stepAxBeta = BETACONV[stepAxRhs];
    (* ⊢ (λx y. ...) xV = (λy. ABS_prod (mkPair xV y)) *)
    stepA = TRANS[stepAx, stepAxBeta];

    stepAxy = HOL`Equal`APTHM[stepA, yV];
    stepAxyRhs = concl[stepAxy][[2]];
    stepAxyBeta = BETACONV[stepAxyRhs];
    unfoldStep = TRANS[stepAxy, stepAxyBeta];
    (* unfoldStep : ⊢ (x, y) = ABS_prod (mkPair x y) *)

    (* (b) Apply REP_prod to both sides via APTERM. *)
    repAppliedTh = HOL`Equal`APTERM[repProdConst[], unfoldStep];
    (* repAppliedTh : ⊢ REP_prod (x, y) = REP_prod (ABS_prod (mkPair x y)) *)

    (* (c) Instantiate repAbsProdThm: r ↦ mkPair x y. *)
    instRepAbs = INST[
      {mkVar["r", charTy] -> mkPairXY},
      repAbsProdThm];
    (* instRepAbs : ⊢ (predicate) (mkPair x y) =
                        (REP_prod (ABS_prod (mkPair x y)) = mkPair x y) *)

    (* (d) Instantiate isPairWitnessThm: x₀ ↦ x, y₀ ↦ y. *)
    x0v = mkVar["x0", αTy]; y0v = mkVar["y0", βTy];
    instIsPair = INST[{x0v -> xV, y0v -> yV}, isPairWitnessThm];

    repAbsMkPair = EQMP[instRepAbs, instIsPair];
    (* repAbsMkPair : ⊢ REP_prod (ABS_prod (mkPair x y)) = mkPair x y *)

    (* (e) TRANS *)
    TRANS[repAppliedTh, repAbsMkPair]
  ];

(* ============================================================ *)
(* mkPairInjThm : ⊢ (mkPair x y = mkPair x' y') ⇒                *)
(*                       (x = x' ∧ y = y')                       *)
(*                                                              *)
(* Apply both sides at (x, y) and simplify via mkPairDefThm     *)
(* + EQTINTRO[REFL[x/y]].                                        *)
(* ============================================================ *)

mkPairInjThm =
  Module[{xV, yV, xPV, yPV, hypEq, lhsAppX, lhsAppXY,
          xEqxTh, yEqyTh, simplifiedEq, conjPart, dischargedTh},
    xV = mkVar["x", αTy]; yV = mkVar["y", βTy];
    xPV = mkVar["xP", αTy]; yPV = mkVar["yP", βTy];

    hypEq = ASSUME[mkEq[
      mkComb[mkComb[mkPairConst[], xV], yV],
      mkComb[mkComb[mkPairConst[], xPV], yPV]]];
    (* (mkPair x y = mkPair xP yP) ⊢ mkPair x y = mkPair xP yP *)

    lhsAppX = MKCOMB[hypEq, REFL[xV]];
    (* ⊢ mkPair x y x = mkPair xP yP x  (under same hyp) *)
    lhsAppXY = MKCOMB[lhsAppX, REFL[yV]];
    (* ⊢ mkPair x y x y = mkPair xP yP x y *)

    (* Unfold mkPair on both sides + beta-reduce; result:                  *)
    (*   ⊢ (x = x ∧ y = y) = (x = xP ∧ y = yP)                              *)
    simplifiedEq = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{mkPairDefThm}], lhsAppXY];

    (* Now collapse LHS (x = x ∧ y = y) to T using EQTINTRO[REFL[v]],     *)
    (* then basic `(T = p) = p` flips the result to the bare conjunction.*)
    xEqxTh = HOL`Bool`EQTINTRO[REFL[xV]];   (* ⊢ (x = x) = T *)
    yEqyTh = HOL`Bool`EQTINTRO[REFL[yV]];   (* ⊢ (y = y) = T *)
    conjPart = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{xEqxTh, yEqyTh}],
      simplifiedEq];
    (* ⊢ x = xP ∧ y = yP, with hyp = (mkPair x y = mkPair xP yP) *)

    dischargedTh = HOL`Bool`DISCH[concl[hypEq], conjPart];
    (* ⊢ (mkPair x y = mkPair xP yP) ⇒ (x = xP ∧ y = yP) *)
    dischargedTh
  ];

(* ============================================================ *)
(* pairInjThm : ⊢ ((x, y) = (x', y')) ⇒ (x = x' ∧ y = y')         *)
(*                                                              *)
(* Apply REP_prod on the hypothesis, use repPairThm to bridge   *)
(* to mkPair equality, then MP with mkPairInjThm.               *)
(* ============================================================ *)

pairInjThm =
  Module[{xV, yV, xPV, yPV, hypEq, repEq, repXYTh, repXPYPTh,
          mkPairEq, mkPairInjInst, finalImp, x0, y0, xP0, yP0,
          mkPairImp, mkPairImpInst},
    xV = mkVar["x", αTy]; yV = mkVar["y", βTy];
    xPV = mkVar["xP", αTy]; yPV = mkVar["yP", βTy];

    hypEq = ASSUME[mkEq[pairCons[xV, yV], pairCons[xPV, yPV]]];
    (* ((x,y)=(xP,yP)) ⊢ (x,y) = (xP,yP) *)

    (* Apply REP_prod to both sides *)
    repEq = HOL`Equal`APTERM[repProdConst[], hypEq];
    (* ⊢ REP_prod (x,y) = REP_prod (xP,yP) *)

    (* repPairThm with x ↦ x, y ↦ y: ⊢ REP_prod (x, y) = mkPair x y.
       repPairThm was built with free x, y. INST to rebuild for our       *)
    (* current vars (they happen to match — same names — so trivial).     *)
    repXYTh = repPairThm;
    repXPYPTh = INST[{xV -> xPV, yV -> yPV}, repPairThm];

    (* TRANS the chain:                                                  *)
    (*   mkPair x y = REP_prod (x,y) = REP_prod (xP,yP) = mkPair xP yP   *)
    mkPairEq = TRANS[
      TRANS[HOL`Equal`SYM[repXYTh], repEq],
      repXPYPTh];
    (* mkPairEq : ⊢ mkPair x y = mkPair xP yP  (under same hyp) *)

    (* mkPairInjThm was built with free x, y, xP, yP. Same names → trivial *)
    (* INST. Discharge the antecedent via MP.                             *)
    mkPairImp = mkPairInjThm;
    finalImp = HOL`Bool`MP[mkPairImp, mkPairEq];
    (* finalImp : ⊢ x = xP ∧ y = yP (under (x,y)=(xP,yP) hyp) *)

    HOL`Bool`DISCH[concl[hypEq], finalImp]
    (* ⊢ ((x,y) = (xP,yP)) ⇒ (x = xP ∧ y = yP) *)
  ];

End[];
EndPackage[];
