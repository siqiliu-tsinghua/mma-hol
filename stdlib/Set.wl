(* ::Package:: *)

(* M7-2-a stdlib/Set — set notation layer.

   Sets are α → bool predicates. All operations are derived definitions
   on this representation; semantically `x ∈ S` means `S x`. The wrapper
   `IN x S = S x` exists for syntactic convenience and to keep proofs
   readable.

   Constants defined here:
     IN          α → set → bool     IN x S = S x
     SUBSET      set → set → bool   S ⊆ T = ∀x. x ∈ S ⇒ x ∈ T
     UNION       set → set → set    UNION S T = λx. S x ∨ T x
     INTER       set → set → set    INTER S T = λx. S x ∧ T x
     DIFF        set → set → set    DIFF S T  = λx. S x ∧ ¬ T x
     EMPTY       set                EMPTY  = λx. F
     UNIV        set                UNIV   = λx. T

   Membership theorems (each derived by simpConv-unfolding the relevant
   def on both sides and TRANS-chaining):
     inUnionThm  ⊢ x ∈ A ∪ B  = (x ∈ A) ∨ (x ∈ B)
     inInterThm  ⊢ x ∈ A ∩ B  = (x ∈ A) ∧ (x ∈ B)
     inDiffThm   ⊢ x ∈ A ∖ B  = (x ∈ A) ∧ ¬ (x ∈ B)
     inEmptyThm  ⊢ x ∈ EMPTY  = F
     inUnivThm   ⊢ x ∈ UNIV   = T

   SUBSET-shaped theorems (reflexivity, transitivity) and the more
   advanced operations (POW, IMAGE, PREIMAGE, bounded quantifiers,
   function properties) defer to M7-2-b. Parser sugar `{x | P x}`
   defers to M7-2-parser.
*)

BeginPackage["HOL`Stdlib`Set`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`"
}];

inConst::usage = "inConst[] — IN : α → set → bool.";
subsetConst::usage = "subsetConst[] — SUBSET : set → set → bool.";
unionConst::usage = "unionConst[] — UNION : set → set → set.";
interConst::usage = "interConst[] — INTER : set → set → set.";
diffConst::usage = "diffConst[] — DIFF : set → set → set.";
emptyConst::usage = "emptyConst[] — EMPTY : set.";
univConst::usage = "univConst[] — UNIV : set.";

inDefThm::usage     = "inDefThm — ⊢ IN = (λx S. S x).";
subsetDefThm::usage = "subsetDefThm — ⊢ SUBSET = (λS T. ∀x. x ∈ S ⇒ x ∈ T).";
unionDefThm::usage  = "unionDefThm — ⊢ UNION = (λS T. λx. S x ∨ T x).";
interDefThm::usage  = "interDefThm — ⊢ INTER = (λS T. λx. S x ∧ T x).";
diffDefThm::usage   = "diffDefThm — ⊢ DIFF = (λS T. λx. S x ∧ ¬ T x).";
emptyDefThm::usage  = "emptyDefThm — ⊢ EMPTY = (λx. F).";
univDefThm::usage   = "univDefThm — ⊢ UNIV = (λx. T).";

inTerm::usage     = "inTerm[x, S] — build `x ∈ S` = `IN x S`.";
subsetTerm::usage = "subsetTerm[S, T] — build `S ⊆ T`.";
unionTerm::usage  = "unionTerm[S, T] — build `S ∪ T`.";
interTerm::usage  = "interTerm[S, T] — build `S ∩ T`.";
diffTerm::usage   = "diffTerm[S, T] — build `S ∖ T`.";

inUnionThm::usage = "inUnionThm — ⊢ x ∈ A ∪ B = (x ∈ A) ∨ (x ∈ B).";
inInterThm::usage = "inInterThm — ⊢ x ∈ A ∩ B = (x ∈ A) ∧ (x ∈ B).";
inDiffThm::usage  = "inDiffThm  — ⊢ x ∈ A ∖ B = (x ∈ A) ∧ ¬ (x ∈ B).";
inEmptyThm::usage = "inEmptyThm — ⊢ x ∈ EMPTY = F.";
inUnivThm::usage  = "inUnivThm  — ⊢ x ∈ UNIV  = T.";

subsetReflThm::usage = "subsetReflThm — ⊢ A ⊆ A.";
subsetTransThm::usage = "subsetTransThm — ⊢ A ⊆ B ⇒ B ⊆ C ⇒ A ⊆ C.";
unionSubsetLeftThm::usage  = "unionSubsetLeftThm  — ⊢ A ⊆ A ∪ B.";
unionSubsetRightThm::usage = "unionSubsetRightThm — ⊢ B ⊆ A ∪ B.";
interSubsetLeftThm::usage  = "interSubsetLeftThm  — ⊢ A ∩ B ⊆ A.";
interSubsetRightThm::usage = "interSubsetRightThm — ⊢ A ∩ B ⊆ B.";
emptySubsetThm::usage = "emptySubsetThm — ⊢ EMPTY ⊆ A.";
subsetUnivThm::usage  = "subsetUnivThm  — ⊢ A ⊆ UNIV.";

Begin["`Private`"];

(* ============================================================ *)
(* Type vars, helpers                                           *)
(* ============================================================ *)

αTy = mkVarType["A"];
setTy = tyFun[αTy, boolTy];

orC[]    := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
andC[]   := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
impC[]   := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notC[]   := mkConst["¬", tyFun[boolTy, boolTy]];
forallC[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];

(* ============================================================ *)
(* IN : α → set → bool,  IN x S = S x                            *)
(* ============================================================ *)

inTy = tyFun[αTy, tyFun[setTy, boolTy]];

inDefBody[] :=
  Module[{xV, sV},
    xV = mkVar["x", αTy]; sV = mkVar["S", setTy];
    mkAbs[xV, mkAbs[sV, mkComb[sV, xV]]]
  ];

inDefThm = newDefinition[mkEq[mkVar["IN", inTy], inDefBody[]]];
inConst[] := mkConst["IN", inTy];
inTerm[x_, s_] := mkComb[mkComb[inConst[], x], s];

(* ============================================================ *)
(* SUBSET : set → set → bool, SUBSET S T = ∀x. x ∈ S ⇒ x ∈ T     *)
(* ============================================================ *)

subsetTy = tyFun[setTy, tyFun[setTy, boolTy]];

subsetDefBody[] :=
  Module[{S, T, x, body},
    S = mkVar["S", setTy]; T = mkVar["T", setTy];
    x = mkVar["x", αTy];
    body = mkComb[mkComb[impC[], inTerm[x, S]], inTerm[x, T]];
    mkAbs[S, mkAbs[T,
      mkComb[forallC[αTy], mkAbs[x, body]]]]
  ];

subsetDefThm = newDefinition[mkEq[mkVar["SUBSET", subsetTy], subsetDefBody[]]];
subsetConst[] := mkConst["SUBSET", subsetTy];
subsetTerm[s_, t_] := mkComb[mkComb[subsetConst[], s], t];

(* ============================================================ *)
(* UNION, INTER, DIFF                                           *)
(* ============================================================ *)

setOpTy = tyFun[setTy, tyFun[setTy, setTy]];

unionDefBody[] :=
  Module[{S, T, x},
    S = mkVar["S", setTy]; T = mkVar["T", setTy]; x = mkVar["x", αTy];
    mkAbs[S, mkAbs[T, mkAbs[x,
      mkComb[mkComb[orC[], mkComb[S, x]], mkComb[T, x]]]]]
  ];

interDefBody[] :=
  Module[{S, T, x},
    S = mkVar["S", setTy]; T = mkVar["T", setTy]; x = mkVar["x", αTy];
    mkAbs[S, mkAbs[T, mkAbs[x,
      mkComb[mkComb[andC[], mkComb[S, x]], mkComb[T, x]]]]]
  ];

diffDefBody[] :=
  Module[{S, T, x},
    S = mkVar["S", setTy]; T = mkVar["T", setTy]; x = mkVar["x", αTy];
    mkAbs[S, mkAbs[T, mkAbs[x,
      mkComb[mkComb[andC[], mkComb[S, x]],
             mkComb[notC[], mkComb[T, x]]]]]]
  ];

unionDefThm = newDefinition[mkEq[mkVar["UNION", setOpTy], unionDefBody[]]];
interDefThm = newDefinition[mkEq[mkVar["INTER", setOpTy], interDefBody[]]];
diffDefThm  = newDefinition[mkEq[mkVar["DIFF",  setOpTy], diffDefBody[]]];

unionConst[] := mkConst["UNION", setOpTy];
interConst[] := mkConst["INTER", setOpTy];
diffConst[]  := mkConst["DIFF",  setOpTy];

unionTerm[s_, t_] := mkComb[mkComb[unionConst[], s], t];
interTerm[s_, t_] := mkComb[mkComb[interConst[], s], t];
diffTerm[s_, t_]  := mkComb[mkComb[diffConst[],  s], t];

(* ============================================================ *)
(* EMPTY, UNIV — nullary set constants                          *)
(* ============================================================ *)

emptyDefThm = newDefinition[mkEq[mkVar["EMPTY", setTy],
  mkAbs[mkVar["x", αTy], mkConst["F", boolTy]]]];
univDefThm  = newDefinition[mkEq[mkVar["UNIV",  setTy],
  mkAbs[mkVar["x", αTy], mkConst["T", boolTy]]]];

emptyConst[] := mkConst["EMPTY", setTy];
univConst[]  := mkConst["UNIV",  setTy];

(* ============================================================ *)
(* Membership theorems                                          *)
(*                                                              *)
(* Pattern: simpConv-unfold the relevant def thms on BOTH the   *)
(* `x ∈ S∘T` LHS and the `(x ∈ S) ∘ (x ∈ T)` RHS to a common    *)
(* underlying form `S x ∘ T x`. TRANS the two equations.        *)
(* ============================================================ *)

inUnionThm =
  Module[{xV, AV, BV, lhsTerm, rhsTerm, lhsRedTh, rhsRedTh},
    xV = mkVar["x", αTy];
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy];
    lhsTerm = inTerm[xV, unionTerm[AV, BV]];
    rhsTerm = mkComb[mkComb[orC[], inTerm[xV, AV]], inTerm[xV, BV]];
    lhsRedTh = HOL`Auto`Simp`simpConv[{inDefThm, unionDefThm}][lhsTerm];
    rhsRedTh = HOL`Auto`Simp`simpConv[{inDefThm}][rhsTerm];
    TRANS[lhsRedTh, HOL`Equal`SYM[rhsRedTh]]
  ];

inInterThm =
  Module[{xV, AV, BV, lhsTerm, rhsTerm, lhsRedTh, rhsRedTh},
    xV = mkVar["x", αTy];
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy];
    lhsTerm = inTerm[xV, interTerm[AV, BV]];
    rhsTerm = mkComb[mkComb[andC[], inTerm[xV, AV]], inTerm[xV, BV]];
    lhsRedTh = HOL`Auto`Simp`simpConv[{inDefThm, interDefThm}][lhsTerm];
    rhsRedTh = HOL`Auto`Simp`simpConv[{inDefThm}][rhsTerm];
    TRANS[lhsRedTh, HOL`Equal`SYM[rhsRedTh]]
  ];

inDiffThm =
  Module[{xV, AV, BV, lhsTerm, rhsTerm, lhsRedTh, rhsRedTh},
    xV = mkVar["x", αTy];
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy];
    lhsTerm = inTerm[xV, diffTerm[AV, BV]];
    rhsTerm = mkComb[mkComb[andC[], inTerm[xV, AV]],
      mkComb[notC[], inTerm[xV, BV]]];
    lhsRedTh = HOL`Auto`Simp`simpConv[{inDefThm, diffDefThm}][lhsTerm];
    rhsRedTh = HOL`Auto`Simp`simpConv[{inDefThm}][rhsTerm];
    TRANS[lhsRedTh, HOL`Equal`SYM[rhsRedTh]]
  ];

inEmptyThm =
  Module[{xV, lhsTerm},
    xV = mkVar["x", αTy];
    lhsTerm = inTerm[xV, emptyConst[]];
    HOL`Auto`Simp`simpConv[{inDefThm, emptyDefThm}][lhsTerm]
  ];

inUnivThm =
  Module[{xV, lhsTerm},
    xV = mkVar["x", αTy];
    lhsTerm = inTerm[xV, univConst[]];
    HOL`Auto`Simp`simpConv[{inDefThm, univDefThm}][lhsTerm]
  ];

(* ============================================================ *)
(* unfoldSubsetTerm[S, T] : ⊢ SUBSET S T = (∀x. IN x S ⇒ IN x T) *)
(*                                                              *)
(* Manual APTHM + BETACONV, twice. We deliberately avoid the    *)
(* simpConv[{subsetDefThm}] shortcut because basicSimpset would *)
(* immediately collapse the resulting `IN x A ⇒ IN x A` body to *)
(* T via the `p ⇒ p = T` schema, leaving us with `∀x. T` — not  *)
(* the structural ∀-form we need to EQMP against a GEN'd theorem*)
(* in reflexivity/transitivity proofs.                           *)
(* ============================================================ *)

unfoldSubsetTerm[S_, T_] :=
  Module[{step1, step1Rhs, step1Beta, step1Chain,
          step2, step2Rhs, step2Beta},
    step1 = HOL`Equal`APTHM[subsetDefThm, S];
    step1Rhs = concl[step1][[2]];
    step1Beta = BETACONV[step1Rhs];
    step1Chain = TRANS[step1, step1Beta];
    step2 = HOL`Equal`APTHM[step1Chain, T];
    step2Rhs = concl[step2][[2]];
    step2Beta = BETACONV[step2Rhs];
    TRANS[step2, step2Beta]
  ];

packSubset[genTh_, S_, T_] :=
  Module[{defApp},
    defApp = unfoldSubsetTerm[S, T];
    EQMP[HOL`Equal`SYM[defApp], genTh]
  ];

(* ============================================================ *)
(* SUBSET reflexivity / transitivity                            *)
(* ============================================================ *)

subsetReflThm =
  Module[{AV, xV, asInA, impSelf, genTh},
    AV = mkVar["A", setTy];
    xV = mkVar["x", αTy];
    asInA = ASSUME[inTerm[xV, AV]];
    impSelf = HOL`Bool`DISCH[concl[asInA], asInA];
    genTh = HOL`Bool`GEN[xV, impSelf];
    packSubset[genTh, AV, AV]
  ];

subsetTransThm =
  Module[{AV, BV, CV, xV,
          subAB, subBC, abUnfolded, bcUnfolded, specAB, specBC,
          hypIA, inB, inC, impAC, genAC, ac, imp1, imp2},
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy]; CV = mkVar["C", setTy];
    xV = mkVar["x", αTy];
    subAB = ASSUME[subsetTerm[AV, BV]];
    subBC = ASSUME[subsetTerm[BV, CV]];

    abUnfolded = EQMP[unfoldSubsetTerm[AV, BV], subAB];
    bcUnfolded = EQMP[unfoldSubsetTerm[BV, CV], subBC];

    specAB = HOL`Bool`SPEC[xV, abUnfolded];
    specBC = HOL`Bool`SPEC[xV, bcUnfolded];

    hypIA = ASSUME[inTerm[xV, AV]];
    inB = HOL`Bool`MP[specAB, hypIA];
    inC = HOL`Bool`MP[specBC, inB];
    impAC = HOL`Bool`DISCH[concl[hypIA], inC];

    genAC = HOL`Bool`GEN[xV, impAC];
    ac = packSubset[genAC, AV, CV];

    imp1 = HOL`Bool`DISCH[concl[subBC], ac];
    imp2 = HOL`Bool`DISCH[concl[subAB], imp1];
    imp2
  ];

(* ============================================================ *)
(* UNION / INTER subset relations                               *)
(* ============================================================ *)

unionSubsetLeftThm =
  Module[{AV, BV, xV, hypIA, disjTh, finalIA, impForX, genTh},
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy];
    xV = mkVar["x", αTy];
    hypIA = ASSUME[inTerm[xV, AV]];
    disjTh = HOL`Bool`DISJ1[hypIA, inTerm[xV, BV]];
    finalIA = EQMP[HOL`Equal`SYM[inUnionThm], disjTh];
    impForX = HOL`Bool`DISCH[concl[hypIA], finalIA];
    genTh = HOL`Bool`GEN[xV, impForX];
    packSubset[genTh, AV, unionTerm[AV, BV]]
  ];

unionSubsetRightThm =
  Module[{AV, BV, xV, hypIB, disjTh, finalIB, impForX, genTh},
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy];
    xV = mkVar["x", αTy];
    hypIB = ASSUME[inTerm[xV, BV]];
    disjTh = HOL`Bool`DISJ2[hypIB, inTerm[xV, AV]];
    finalIB = EQMP[HOL`Equal`SYM[inUnionThm], disjTh];
    impForX = HOL`Bool`DISCH[concl[hypIB], finalIB];
    genTh = HOL`Bool`GEN[xV, impForX];
    packSubset[genTh, BV, unionTerm[AV, BV]]
  ];

interSubsetLeftThm =
  Module[{AV, BV, xV, hypIAB, conjTh, inA, impForX, genTh},
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy];
    xV = mkVar["x", αTy];
    hypIAB = ASSUME[inTerm[xV, interTerm[AV, BV]]];
    conjTh = EQMP[inInterThm, hypIAB];
    inA = HOL`Bool`CONJUNCT1[conjTh];
    impForX = HOL`Bool`DISCH[concl[hypIAB], inA];
    genTh = HOL`Bool`GEN[xV, impForX];
    packSubset[genTh, interTerm[AV, BV], AV]
  ];

interSubsetRightThm =
  Module[{AV, BV, xV, hypIAB, conjTh, inB, impForX, genTh},
    AV = mkVar["A", setTy]; BV = mkVar["B", setTy];
    xV = mkVar["x", αTy];
    hypIAB = ASSUME[inTerm[xV, interTerm[AV, BV]]];
    conjTh = EQMP[inInterThm, hypIAB];
    inB = HOL`Bool`CONJUNCT2[conjTh];
    impForX = HOL`Bool`DISCH[concl[hypIAB], inB];
    genTh = HOL`Bool`GEN[xV, impForX];
    packSubset[genTh, interTerm[AV, BV], BV]
  ];

(* ============================================================ *)
(* EMPTY ⊆ A   and   A ⊆ UNIV                                   *)
(* ============================================================ *)

emptySubsetThm =
  Module[{AV, xV, hypIE, fTh, inA, impForX, genTh},
    AV = mkVar["A", setTy];
    xV = mkVar["x", αTy];
    hypIE = ASSUME[inTerm[xV, emptyConst[]]];
    fTh = EQMP[inEmptyThm, hypIE];               (* (x∈EMPTY) ⊢ F *)
    inA = HOL`Bool`CONTR[inTerm[xV, AV], fTh];   (* (x∈EMPTY) ⊢ x ∈ A *)
    impForX = HOL`Bool`DISCH[concl[hypIE], inA];
    genTh = HOL`Bool`GEN[xV, impForX];
    packSubset[genTh, emptyConst[], AV]
  ];

subsetUnivThm =
  Module[{AV, xV, inUniv, impForX, genTh},
    AV = mkVar["A", setTy];
    xV = mkVar["x", αTy];
    inUniv = EQMP[HOL`Equal`SYM[inUnivThm], HOL`Bool`TRUTH];
    (* inUniv : ⊢ x ∈ UNIV *)
    impForX = HOL`Bool`DISCH[inTerm[xV, AV], inUniv];
    genTh = HOL`Bool`GEN[xV, impForX];
    packSubset[genTh, AV, univConst[]]
  ];

End[];
EndPackage[];
