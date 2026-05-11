(* ::Package:: *)

(* M7-1f stdlib/Option — option type α option (= NONE | SOME α).

   Encode α option as α → bool functions of one of two specific shapes:

     mkNone   = λa. F                          — never satisfied
     mkSome x = λa. a = x                      — satisfied only at x

   The closed predicate
     isOption P = (P = mkNone) ∨ (∃x. P = mkSome x)
   carves out exactly these characteristic functions; newBasicTypeDefinition
   introduces `option` with ABS_option / REP_option.

   NONE is a nullary constructor (just ABS_option mkNone, no λ).
   SOME = λx. ABS_option (mkSome x).

   Public API: types + def thms + REP-bridges + SOME injectivity +
   NONE ≠ SOME disjointness. mkNone injectivity is vacuous (no args).
*)

BeginPackage["HOL`Stdlib`Option`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`"
}];

mkNoneConst::usage = "mkNoneConst[] — underlying `mkNone : α → bool = λa. F`.";
mkSomeConst::usage = "mkSomeConst[] — underlying `mkSome : α → α → bool = λx a. a = x`.";

mkNoneDefThm::usage = "mkNoneDefThm — ⊢ mkNone = (λa. F).";
mkSomeDefThm::usage = "mkSomeDefThm — ⊢ mkSome = (λx a. a = x).";

optionTy::usage = "optionTy[a] — option type tyApp[\"option\", {a}].";

absOptionConst::usage = "absOptionConst[] — ABS_option : (α → bool) → α option.";
repOptionConst::usage = "repOptionConst[] — REP_option : α option → (α → bool).";

absRepOptionThm::usage = "absRepOptionThm — ⊢ ABS_option (REP_option a) = a.";
repAbsOptionThm::usage = "repAbsOptionThm — ⊢ (predicate) r = (REP_option (ABS_option r) = r).";

isOptionPredicate::usage =
  "isOptionPredicate[] — closed term λP. (P = mkNone) ∨ (∃x. P = mkSome x).";

isOptionWitnessThm::usage =
  "isOptionWitnessThm — ⊢ (predicate) mkNone, the DISJ1 witness.";

isOptionWitnessSomeThm::usage =
  "isOptionWitnessSomeThm — ⊢ (predicate) (mkSome x₀), the DISJ2 witness " <>
  "needed for the SOME-side REP_option bridge.";

noneConst::usage = "noneConst[] — NONE : α option.";
someConst::usage = "someConst[] — SOME : α → α option.";

noneDefThm::usage = "noneDefThm — ⊢ NONE = ABS_option mkNone.";
someDefThm::usage = "someDefThm — ⊢ SOME = (λx. ABS_option (mkSome x)).";

someTerm::usage = "someTerm[a] — build the term `SOME a`.";

repNoneThm::usage = "repNoneThm — ⊢ REP_option NONE = mkNone.";
repSomeThm::usage = "repSomeThm — ⊢ REP_option (SOME x) = mkSome x.";

mkSomeInjThm::usage =
  "mkSomeInjThm — ⊢ (mkSome x = mkSome xP) ⇒ (x = xP). " <>
  "Extensional injectivity, applied at x.";

someInjThm::usage =
  "someInjThm — ⊢ (SOME x = SOME xP) ⇒ (x = xP). " <>
  "Chain: APTERM REP_option + repSomeThm + mkSomeInjThm.";

noneNotEqSomeThm::usage =
  "noneNotEqSomeThm — ⊢ ¬ (NONE = SOME x). " <>
  "Disjointness: APTERM REP_option chain, apply at x; simpConv reduces " <>
  "to ⊢ F via mkNoneDefThm (mkNone x → F) + mkSomeDefThm (mkSome x x →" <>
  " x = x → T) + basic `(p = T) = p` collapsing F = T to F.";

Begin["`Private`"];

(* ============================================================ *)
(* Type vars, constants                                         *)
(* ============================================================ *)

αTy = mkVarType["A"];

repOptionTy = tyFun[αTy, boolTy];
mkNoneTy    = repOptionTy;
mkSomeTy    = tyFun[αTy, repOptionTy];

orC[]      := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
existsC[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];

(* ============================================================ *)
(* mkNone, mkSome                                               *)
(* ============================================================ *)

mkNoneLambdaTerm[] :=
  Module[{aV, fConst},
    aV = mkVar["a", αTy];
    fConst = mkConst["F", boolTy];
    mkAbs[aV, fConst]
  ];

mkSomeLambdaTerm[] :=
  Module[{xV, aV},
    xV = mkVar["x", αTy]; aV = mkVar["a", αTy];
    mkAbs[xV, mkAbs[aV, mkEq[aV, xV]]]
  ];

mkNoneDefThm = newDefinition[
  mkEq[mkVar["mkNone", mkNoneTy], mkNoneLambdaTerm[]]];

mkSomeDefThm = newDefinition[
  mkEq[mkVar["mkSome", mkSomeTy], mkSomeLambdaTerm[]]];

mkNoneConst[] := mkConst["mkNone", mkNoneTy];
mkSomeConst[] := mkConst["mkSome", mkSomeTy];

(* ============================================================ *)
(* isOption predicate                                           *)
(*   λP. (P = mkNone) ∨ (∃x. P = mkSome x)                      *)
(* ============================================================ *)

isOptionPredicateTerm[] :=
  Module[{pV, xV, mNone, mSome, leftEq,
          rightEq, rightLam, rightEx, disj},
    pV = mkVar["P", repOptionTy];
    xV = mkVar["x", αTy];
    mNone = mkNoneConst[]; mSome = mkSomeConst[];
    leftEq  = mkEq[pV, mNone];
    rightEq = mkEq[pV, mkComb[mSome, xV]];
    rightLam = mkAbs[xV, rightEq];
    rightEx  = mkComb[existsC[αTy], rightLam];
    disj = mkComb[mkComb[orC[], leftEq], rightEx];
    mkAbs[pV, disj]
  ];

isOptionPredicate[] := isOptionPredicateTerm[];

(* ============================================================ *)
(* Witness theorem ⊢ (predicate) mkNone via DISJ1               *)
(* ============================================================ *)

isOptionWitnessThm =
  Module[{mNone, witnessTm, refl,
          xV, mSome, rightEq, rightLam, rightExTm,
          disj1Th, predLambda, predApplied, betaTh},
    mNone = mkNoneConst[];
    witnessTm = mNone;
    refl = REFL[witnessTm];

    xV = mkVar["x", αTy];
    mSome = mkSomeConst[];
    rightEq = mkEq[witnessTm, mkComb[mSome, xV]];
    rightLam = mkAbs[xV, rightEq];
    rightExTm = mkComb[existsC[αTy], rightLam];

    disj1Th = HOL`Bool`DISJ1[refl, rightExTm];

    predLambda = isOptionPredicateTerm[];
    predApplied = mkComb[predLambda, witnessTm];
    betaTh = BETACONV[predApplied];
    EQMP[SYM[betaTh], disj1Th]
  ];

(* ============================================================ *)
(* Introduce the option type                                    *)
(* ============================================================ *)

{absRepOptionThm, repAbsOptionThm} =
  newBasicTypeDefinition["option", "ABS_option", "REP_option",
    isOptionWitnessThm];

optionTy[a_] := mkType["option", {a}];

absOptionConst[] :=
  mkConst["ABS_option", tyFun[repOptionTy, optionTy[αTy]]];
repOptionConst[] :=
  mkConst["REP_option", tyFun[optionTy[αTy], repOptionTy]];

(* ============================================================ *)
(* NONE, SOME constructors                                      *)
(* ============================================================ *)

noneTy = optionTy[αTy];

noneDefThm = newDefinition[
  mkEq[mkVar["NONE", noneTy],
    mkComb[absOptionConst[], mkNoneConst[]]]];

noneConst[] := mkConst["NONE", noneTy];

someTy = tyFun[αTy, optionTy[αTy]];

someDefBody[] :=
  Module[{xV},
    xV = mkVar["x", αTy];
    mkAbs[xV, mkComb[absOptionConst[], mkComb[mkSomeConst[], xV]]]
  ];

someDefThm = newDefinition[
  mkEq[mkVar["SOME", someTy], someDefBody[]]];

someConst[] := mkConst["SOME", someTy];

someTerm[a_] := mkComb[someConst[], a];

(* ============================================================ *)
(* DISJ2 witness for SOME side                                  *)
(* ============================================================ *)

isOptionWitnessSomeThm =
  Module[{x0, mSome, witnessTm, refl,
          xV, rightEq, rightLam, rightExTm, existsX,
          leftEq, disj2Th,
          predLambda, predApplied, betaTh},
    x0 = mkVar["x0", αTy];
    mSome = mkSomeConst[];
    witnessTm = mkComb[mSome, x0];
    refl = REFL[witnessTm];

    xV = mkVar["x", αTy];
    rightEq = mkEq[witnessTm, mkComb[mSome, xV]];
    rightLam = mkAbs[xV, rightEq];
    rightExTm = mkComb[existsC[αTy], rightLam];
    existsX = HOL`Bool`EXISTS[rightExTm, x0, refl];

    leftEq = mkEq[witnessTm, mkNoneConst[]];

    disj2Th = HOL`Bool`DISJ2[existsX, leftEq];

    predLambda = isOptionPredicateTerm[];
    predApplied = mkComb[predLambda, witnessTm];
    betaTh = BETACONV[predApplied];
    EQMP[SYM[betaTh], disj2Th]
  ];

(* ============================================================ *)
(* REP bridges                                                  *)
(* ============================================================ *)

repNoneThm =
  Module[{mNone, applied, instRepAbs, repAbsMkNone},
    mNone = mkNoneConst[];
    applied = HOL`Equal`APTERM[repOptionConst[], noneDefThm];
    (* applied : ⊢ REP_option NONE = REP_option (ABS_option mkNone) *)
    instRepAbs = INST[
      {mkVar["r", repOptionTy] -> mNone},
      repAbsOptionThm];
    repAbsMkNone = EQMP[instRepAbs, isOptionWitnessThm];
    TRANS[applied, repAbsMkNone]
  ];

repSomeThm =
  Module[{xV, mSome, mkSomeX,
          stepX, stepXRhs, stepXBeta, unfoldStep,
          repAppliedTh, instRepAbs, instIsOption, repAbsMkSome,
          x0v},
    xV = mkVar["x", αTy];
    mSome = mkSomeConst[];
    mkSomeX = mkComb[mSome, xV];

    stepX = HOL`Equal`APTHM[someDefThm, xV];
    stepXRhs = concl[stepX][[2]];
    stepXBeta = BETACONV[stepXRhs];
    unfoldStep = TRANS[stepX, stepXBeta];
    (* unfoldStep : ⊢ SOME x = ABS_option (mkSome x) *)

    repAppliedTh = HOL`Equal`APTERM[repOptionConst[], unfoldStep];

    instRepAbs = INST[
      {mkVar["r", repOptionTy] -> mkSomeX},
      repAbsOptionThm];
    x0v = mkVar["x0", αTy];
    instIsOption = INST[{x0v -> xV}, isOptionWitnessSomeThm];

    repAbsMkSome = EQMP[instRepAbs, instIsOption];
    TRANS[repAppliedTh, repAbsMkSome]
  ];

(* ============================================================ *)
(* mkSomeInjThm : ⊢ (mkSome x = mkSome xP) ⇒ (x = xP)            *)
(*                                                              *)
(* Apply at x; mkSome unfolds + betas to:                       *)
(*   (x = x) = (x = xP)                                          *)
(* xEqxTh + basic `(T = p) = p` closes to x = xP.               *)
(* ============================================================ *)

mkSomeInjThm =
  Module[{xV, xPV, hypEq, step1, simplifiedEq,
          xEqxTh, conjPart},
    xV = mkVar["x", αTy]; xPV = mkVar["xP", αTy];
    hypEq = ASSUME[mkEq[
      mkComb[mkSomeConst[], xV],
      mkComb[mkSomeConst[], xPV]]];
    step1 = MKCOMB[hypEq, REFL[xV]];

    simplifiedEq = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{mkSomeDefThm}], step1];

    xEqxTh = HOL`Bool`EQTINTRO[REFL[xV]];
    conjPart = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{xEqxTh}], simplifiedEq];
    HOL`Bool`DISCH[concl[hypEq], conjPart]
  ];

(* ============================================================ *)
(* someInjThm : ⊢ (SOME x = SOME xP) ⇒ (x = xP)                  *)
(* ============================================================ *)

someInjThm =
  Module[{xV, xPV, hypEq, repEq, repXV, repXPV, mkSomeEq, finalImp},
    xV = mkVar["x", αTy]; xPV = mkVar["xP", αTy];
    hypEq = ASSUME[mkEq[someTerm[xV], someTerm[xPV]]];
    repEq = HOL`Equal`APTERM[repOptionConst[], hypEq];

    repXV = repSomeThm;
    repXPV = INST[{xV -> xPV}, repSomeThm];
    mkSomeEq = TRANS[
      TRANS[HOL`Equal`SYM[repXV], repEq],
      repXPV];

    finalImp = HOL`Bool`MP[mkSomeInjThm, mkSomeEq];
    HOL`Bool`DISCH[concl[hypEq], finalImp]
  ];

(* ============================================================ *)
(* noneNotEqSomeThm : ⊢ ¬ (NONE = SOME x)                       *)
(*                                                              *)
(* APTERM REP_option, bridge to mkNone = mkSome x, apply at x;  *)
(* simpConv reduces LHS to F (via mkNoneDefThm) and RHS to      *)
(* (x = x) (via mkSomeDefThm). Outer eq F = (x = x) becomes     *)
(* F = T via xEqxTh, then basic `(p = T) = p` collapses to F.  *)
(* ============================================================ *)

noneNotEqSomeThm =
  Module[{xV, hypEq, repEq, mkNoneMkSomeEq,
          step1, simplifiedEq, xEqxTh, fThm, dischargedTh},
    xV = mkVar["x", αTy];
    hypEq = ASSUME[mkEq[noneConst[], someTerm[xV]]];
    repEq = HOL`Equal`APTERM[repOptionConst[], hypEq];

    mkNoneMkSomeEq = TRANS[
      TRANS[HOL`Equal`SYM[repNoneThm], repEq],
      repSomeThm];
    (* mkNoneMkSomeEq : ⊢ mkNone = mkSome x *)

    step1 = MKCOMB[mkNoneMkSomeEq, REFL[xV]];
    (* step1 : ⊢ mkNone x = mkSome x x *)

    simplifiedEq = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{mkNoneDefThm, mkSomeDefThm}], step1];
    (* simplifiedEq : ⊢ F = (x = x) *)

    xEqxTh = HOL`Bool`EQTINTRO[REFL[xV]];
    fThm = HOL`Drule`CONVRULE[
      HOL`Auto`Simp`simpConv[{xEqxTh}], simplifiedEq];
    (* fThm : ⊢ F *)

    dischargedTh = HOL`Bool`DISCH[concl[hypEq], fThm];
    HOL`Bool`NOTINTRO[dischargedTh]
  ];

End[];
EndPackage[];
