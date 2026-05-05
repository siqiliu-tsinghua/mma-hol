(* ::Package:: *)

(* M7-α-4-b PropTaut — propositional decision procedure.

   Given a propositional tautology t, builds ⊢ t by case-splitting on the
   free bool variables of t down to a closed formula, then evaluating the
   closed formula structurally via small derived rules.  Used by MESON to
   auto-prove the NNF / CNF / T-F normalization lemmas, and as MESON_TAC's
   propositional fallback.

   Trust boundary: every theorem comes from kernel rules (REFL/TRANS/MKCOMB
   /BETA/ASSUME/EQMP/DEDUCTANTISYM/INST/INSTTYPE) plus M4 derived rules.
   A bug here at worst means propTaut fails on a real tautology. *)

BeginPackage["HOL`Auto`PropTaut`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`"
}];

propTaut::usage =
  "propTaut[t] — propositional decision procedure.  t must be of type bool, " <>
  "built from the constants T, F, ¬, ∧, ∨, ⇒, = (where = is at type " <>
  "bool→bool→bool, i.e. ⇔), and free variables of type bool.  Returns ⊢ t " <>
  "when t is a tautology; throws holError tag 'propTaut' otherwise " <>
  "(non-tautology, quantified, or non-bool atom).";

nnfThm::usage =
  "nnfThm[⊢ P] → ⊢ NNF(P).  Applies the propositional NNF rewrite rules " <>
  "(¬¬, De Morgan, ⇒-elim, ⇔-elim, ¬⇒-elim, ¬⇔-elim) bottom-up to fixpoint.  " <>
  "Quantifiers are left untouched (handled at α-4-d).";

cnfThm::usage =
  "cnfThm[⊢ P] → ⊢ CNF(P).  Applies the ∨-over-∧ distribution rewrite " <>
  "rules bottom-up to fixpoint.  Input should be in NNF and quantifier-free.";

splitConjThm::usage =
  "splitConjThm[⊢ A ∧ B ∧ ⋯] → {⊢ A, ⊢ B, ⋯}.  Recursively splits a top-level " <>
  "conjunction via CONJUNCT1 / CONJUNCT2.  Returns {⊢ P} for any non-∧.";

clausifyPropThm::usage =
  "clausifyPropThm[⊢ P] → list of clause theorems.  Composes nnfThm → cnfThm → " <>
  "splitConjThm.  Each output theorem ⊢ Cᵢ is a disjunction of literals; the " <>
  "conjunction of all Cᵢ is propositionally equivalent to P.  Quantifier-free " <>
  "input only — first-order Skolemization happens elsewhere.";

clausifyContrapositives::usage =
  "clausifyContrapositives[Γ ⊢ M₁ ∨ ⋯ ∨ Mₖ] → {ruleThm₁, …, ruleThmₖ}.  For " <>
  "each pivot index p, returns Γ ⊢ ¬M_{j₁} ⇒ ⋯ ⇒ ¬M_{j_{k−1}} ⇒ Mₚ where j_i " <>
  "ranges over the non-pivot indices in original order.  Negative literals " <>
  "¬A are flipped (¬¬A → A) so antecedents are themselves literals.  k=1 " <>
  "returns the input theorem unchanged.  Used by MESON replay: each extension " <>
  "step picks one rule, INSTs σ, MPs in the closed sub-branch theorems for " <>
  "each ¬M_{j} antecedent, and produces ⊢ Mₚ.";

Begin["`Private`"];

ptBoolTy         := tyApp["bool", {}];
ptBoolBoolTy     := tyFun[ptBoolTy, ptBoolTy];
ptBoolBoolBoolTy := tyFun[ptBoolTy, tyFun[ptBoolTy, ptBoolTy]];

ptT[]         := mkConst["T", ptBoolTy];
ptF[]         := mkConst["F", ptBoolTy];
ptNot[p_]     := mkComb[mkConst["¬", ptBoolBoolTy], p];
ptAnd[p_, q_] := mkComb[mkComb[mkConst["∧", ptBoolBoolBoolTy], p], q];
ptOr[p_, q_]  := mkComb[mkComb[mkConst["∨", ptBoolBoolBoolTy], p], q];
ptImp[p_, q_] := mkComb[mkComb[mkConst["⇒", ptBoolBoolBoolTy], p], q];

isPtT[t_]   := t === ptT[];
isPtF[t_]   := t === ptF[];
isPtNot[comb[const["¬", _], _]] := True;
isPtNot[_]  := False;
isPtAnd[comb[comb[const["∧", _], _], _]] := True;
isPtAnd[_]  := False;
isPtOr[comb[comb[const["∨", _], _], _]]  := True;
isPtOr[_]   := False;
isPtImp[comb[comb[const["⇒", _], _], _]] := True;
isPtImp[_]  := False;
isPtIff[comb[comb[const["=", ty_], _], _]] := ty === ptBoolBoolBoolTy;
isPtIff[_]  := False;

destPtNot[comb[_, p_]]            := p;
destPtBin[comb[comb[_, p_], q_]]  := {p, q};

(* ============================================================ *)
(* Small derived rules used to close closed propositional terms. *)

notFThm[] :=
  HOL`Bool`NOTINTRO[HOL`Bool`DISCH[ptF[], ASSUME[ptF[]]]];

(* From Γ ⊢ p, derive Γ ⊢ ¬¬p. *)
notNotIntro[thP_] :=
  Module[{p, notP},
    p = concl[thP];
    notP = ptNot[p];
    HOL`Bool`NOTINTRO[
      HOL`Bool`DISCH[notP,
        HOL`Bool`MP[HOL`Bool`NOTELIM[ASSUME[notP]], thP]]]];

(* From Γ ⊢ ¬p, derive Γ ⊢ p = F. *)
eqfIntro[thNotP_] :=
  Module[{p, pToF, fToP},
    p    = concl[thNotP][[2]];
    pToF = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], ASSUME[p]];
    fToP = HOL`Bool`CONTR[p, ASSUME[ptF[]]];
    DEDUCTANTISYM[fToP, pToF]];

(* From Γ ⊢ ¬p and q:bool, derive Γ ⊢ ¬(p ∧ q). *)
notAndLeft[thNotP_, qTm_] :=
  Module[{p, pAndQ},
    p     = concl[thNotP][[2]];
    pAndQ = ptAnd[p, qTm];
    HOL`Bool`NOTINTRO[
      HOL`Bool`DISCH[pAndQ,
        HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP],
                    HOL`Bool`CONJUNCT1[ASSUME[pAndQ]]]]]];

(* From p:bool and Γ ⊢ ¬q, derive Γ ⊢ ¬(p ∧ q). *)
notAndRight[pTm_, thNotQ_] :=
  Module[{q, pAndQ},
    q     = concl[thNotQ][[2]];
    pAndQ = ptAnd[pTm, q];
    HOL`Bool`NOTINTRO[
      HOL`Bool`DISCH[pAndQ,
        HOL`Bool`MP[HOL`Bool`NOTELIM[thNotQ],
                    HOL`Bool`CONJUNCT2[ASSUME[pAndQ]]]]]];

(* From Γ₁ ⊢ ¬p and Γ₂ ⊢ ¬q, derive Γ₁∪Γ₂ ⊢ ¬(p ∨ q). *)
notOrBoth[thNotP_, thNotQ_] :=
  Module[{p, q, pOrQ, caseP, caseQ, fThm},
    p     = concl[thNotP][[2]];
    q     = concl[thNotQ][[2]];
    pOrQ  = ptOr[p, q];
    caseP = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], ASSUME[p]];
    caseQ = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotQ], ASSUME[q]];
    fThm  = HOL`Bool`DISJCASES[ASSUME[pOrQ], caseP, caseQ];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[pOrQ, fThm]]];

(* From Γ ⊢ ¬p and q:bool, derive Γ ⊢ p ⇒ q. *)
impFalse[thNotP_, qTm_] :=
  Module[{p, fThm},
    p    = concl[thNotP][[2]];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], ASSUME[p]];
    HOL`Bool`DISCH[p, HOL`Bool`CONTR[qTm, fThm]]];

(* From p:bool and Γ ⊢ q, derive Γ ⊢ p ⇒ q. *)
impTrue[pTm_, thQ_] := HOL`Bool`DISCH[pTm, thQ];

(* From Γ₁ ⊢ p and Γ₂ ⊢ ¬q, derive Γ₁∪Γ₂ ⊢ ¬(p ⇒ q). *)
notImp[thP_, thNotQ_] :=
  Module[{p, q, pImpQ, qThm, fThm},
    p     = concl[thP];
    q     = concl[thNotQ][[2]];
    pImpQ = ptImp[p, q];
    qThm  = HOL`Bool`MP[ASSUME[pImpQ], thP];
    fThm  = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotQ], qThm];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[pImpQ, fThm]]];

(* From Γ₁ ⊢ p and Γ₂ ⊢ q, derive Γ₁∪Γ₂ ⊢ p = q (at type bool). *)
iffTT[thP_, thQ_] :=
  TRANS[HOL`Bool`EQTINTRO[thP], SYM[HOL`Bool`EQTINTRO[thQ]]];

(* From Γ₁ ⊢ ¬p and Γ₂ ⊢ ¬q, derive Γ₁∪Γ₂ ⊢ p = q. *)
iffFF[thNotP_, thNotQ_] :=
  TRANS[eqfIntro[thNotP], SYM[eqfIntro[thNotQ]]];

(* From Γ₁ ⊢ p and Γ₂ ⊢ ¬q, derive Γ₁∪Γ₂ ⊢ ¬(p = q). *)
notIffTF[thP_, thNotQ_] :=
  Module[{p, q, pEqQ, qThm, fThm},
    p    = concl[thP];
    q    = concl[thNotQ][[2]];
    pEqQ = mkEq[p, q];
    qThm = EQMP[ASSUME[pEqQ], thP];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotQ], qThm];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[pEqQ, fThm]]];

(* From Γ₁ ⊢ ¬p and Γ₂ ⊢ q, derive Γ₁∪Γ₂ ⊢ ¬(p = q). *)
notIffFT[thNotP_, thQ_] :=
  Module[{p, q, pEqQ, pThm, fThm},
    p    = concl[thNotP][[2]];
    q    = concl[thQ];
    pEqQ = mkEq[p, q];
    pThm = EQMP[SYM[ASSUME[pEqQ]], thQ];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], pThm];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[pEqQ, fThm]]];

(* ============================================================ *)
(* Closed-formula evaluator.  Returns {sign, thm}.               *)
(*   sign = "T": thm = ⊢ t.                                      *)
(*   sign = "F": thm = ⊢ ¬t.                                     *)

propEvalClosed[t_] :=
  Which[
    isPtT[t],   {"T", HOL`Bool`TRUTH},
    isPtF[t],   {"F", notFThm[]},
    isPtNot[t],
      Module[{sub},
        sub = propEvalClosed[destPtNot[t]];
        If[sub[[1]] === "T",
          {"F", notNotIntro[sub[[2]]]},
          {"T", sub[[2]]}]],
    isPtAnd[t],
      Module[{pq, sp, sq},
        pq = destPtBin[t];
        sp = propEvalClosed[pq[[1]]];
        If[sp[[1]] === "F",
          {"F", notAndLeft[sp[[2]], pq[[2]]]},
          sq = propEvalClosed[pq[[2]]];
          If[sq[[1]] === "T",
            {"T", HOL`Bool`CONJ[sp[[2]], sq[[2]]]},
            {"F", notAndRight[pq[[1]], sq[[2]]]}]]],
    isPtOr[t],
      Module[{pq, sp, sq},
        pq = destPtBin[t];
        sp = propEvalClosed[pq[[1]]];
        If[sp[[1]] === "T",
          {"T", HOL`Bool`DISJ1[sp[[2]], pq[[2]]]},
          sq = propEvalClosed[pq[[2]]];
          If[sq[[1]] === "T",
            {"T", HOL`Bool`DISJ2[sq[[2]], pq[[1]]]},
            {"F", notOrBoth[sp[[2]], sq[[2]]]}]]],
    isPtImp[t],
      Module[{pq, sp, sq},
        pq = destPtBin[t];
        sp = propEvalClosed[pq[[1]]];
        If[sp[[1]] === "F",
          {"T", impFalse[sp[[2]], pq[[2]]]},
          sq = propEvalClosed[pq[[2]]];
          If[sq[[1]] === "T",
            {"T", impTrue[pq[[1]], sq[[2]]]},
            {"F", notImp[sp[[2]], sq[[2]]]}]]],
    isPtIff[t],
      Module[{pq, sp, sq},
        pq = destPtBin[t];
        sp = propEvalClosed[pq[[1]]];
        sq = propEvalClosed[pq[[2]]];
        Which[
          sp[[1]] === "T" && sq[[1]] === "T",
            {"T", iffTT[sp[[2]], sq[[2]]]},
          sp[[1]] === "F" && sq[[1]] === "F",
            {"T", iffFF[sp[[2]], sq[[2]]]},
          sp[[1]] === "T" && sq[[1]] === "F",
            {"F", notIffTF[sp[[2]], sq[[2]]]},
          True,
            {"F", notIffFT[sp[[2]], sq[[2]]]}]],
    True,
      HOL`Error`holError["propTaut",
        "propEvalClosed: unrecognized closed prop term",
        <|"t" -> t|>]];

(* ============================================================ *)
(* Free bool-typed variables of t. *)

propFreeBoolVars[t_] :=
  DeleteDuplicates[
    Cases[t, var[_String, ty_] /; ty === ptBoolTy, {0, Infinity}]];

(* For FOL inputs, propositional atoms may be compound bool-typed terms  *)
(* (e.g. P(x), Q(f y)) rather than bool vars.  collectCompoundBoolAtoms  *)
(* finds those at any depth.  An "atomic" bool term is one whose head is *)
(* not a propositional connective and which is not itself a bool var.    *)
propBoolAtomQ[t_] :=
  typeOf[t] === ptBoolTy &&
  ! MatchQ[t, var[_String, _]] &&
  ! (isPtT[t] || isPtF[t] || isPtNot[t] || isPtAnd[t] ||
     isPtOr[t] || isPtImp[t] || isPtIff[t]);

collectCompoundBoolAtoms[t_] :=
  DeleteDuplicates[Cases[t, _?propBoolAtomQ, {0, Infinity}]];

allVarNames[t_] :=
  DeleteDuplicates[Cases[t, var[n_String, _] :> n, {0, Infinity}]];

freshBoolVarNames[atoms_List, forbidden_List] :=
  Module[{used = forbidden, names = {}, i, base, cand},
    Do[
      base = "_pa"; cand = base <> ToString[i]; i = 1;
      While[MemberQ[used, cand], i++; cand = base <> ToString[i]];
      AppendTo[used, cand];
      AppendTo[names, cand],
      {Length[atoms]}
    ];
    names
  ];

(* ============================================================ *)
(* Combine ⊢ t[T/p] and ⊢ t[F/p] into ⊢ t via excluded middle.  *)

caseSplit[pVar_, t_, thmT_, thmF_] :=
  Module[{lambdaT, betaP, betaT, betaF, eqAtP, eqUnderP, tProofUnderP,
          notP, eqfNotP, eqAtFP, eqUnderNotP, tProofUnderNotP, em},
    lambdaT = mkAbs[pVar, t];
    betaP = BETACONV[mkComb[lambdaT, pVar]];
    betaT = BETACONV[mkComb[lambdaT, ptT[]]];
    betaF = BETACONV[mkComb[lambdaT, ptF[]]];
    eqAtP = MKCOMB[REFL[lambdaT], HOL`Bool`EQTINTRO[ASSUME[pVar]]];
    eqUnderP = TRANS[TRANS[SYM[betaP], eqAtP], betaT];
    tProofUnderP = EQMP[SYM[eqUnderP], thmT];
    notP    = ptNot[pVar];
    eqfNotP = eqfIntro[ASSUME[notP]];
    eqAtFP  = MKCOMB[REFL[lambdaT], eqfNotP];
    eqUnderNotP = TRANS[TRANS[SYM[betaP], eqAtFP], betaF];
    tProofUnderNotP = EQMP[SYM[eqUnderNotP], thmF];
    em = HOL`Bool`EXCLUDEDMIDDLE[pVar];
    HOL`Bool`DISJCASES[em, tProofUnderP, tProofUnderNotP]];

(* ============================================================ *)
(* Top-level driver. *)

HOL`Auto`PropTaut`propTaut[t_] := propTautImpl[t];

(* propTautImpl: detect compound bool atoms (FOL atoms like P(x)), abstract *)
(* them with fresh bool vars, run the bool-vars-only driver, INST back.     *)
propTautImpl[t_] :=
  Module[{atoms, freshNames, freshVars, abstractRules, instBack,
          abstractedT, abstractedThm},
    If[typeOf[t] =!= ptBoolTy,
      HOL`Error`holError["propTaut", "propTaut: term must be of type bool",
        <|"t" -> t, "type" -> typeOf[t]|>]];
    atoms = collectCompoundBoolAtoms[t];
    If[atoms === {},
      Return[propTautBoolVars[t]]];
    freshNames    = freshBoolVarNames[atoms, allVarNames[t]];
    freshVars     = Map[mkVar[#, ptBoolTy] &, freshNames];
    abstractRules = MapThread[Rule, {atoms, freshVars}];
    instBack      = MapThread[Rule, {freshVars, atoms}];
    abstractedT   = t /. abstractRules;
    abstractedThm = propTautBoolVars[abstractedT];
    INST[instBack, abstractedThm]
  ];

(* propTautBoolVars: original logic — assumes every bool atom in t is a *)
(* bool variable.  Recursive case-split + closed-formula evaluation.    *)
propTautBoolVars[t_] :=
  Module[{vars},
    vars = propFreeBoolVars[t];
    If[vars === {},
      Module[{ev},
        ev = propEvalClosed[t];
        If[ev[[1]] === "T", ev[[2]],
          HOL`Error`holError["propTaut", "propTaut: not a tautology",
            <|"t" -> t|>]]],
      Module[{p, tT, tF, thmT, thmF},
        p    = First[vars];
        tT   = t /. p -> ptT[];
        tF   = t /. p -> ptF[];
        thmT = propTautBoolVars[tT];
        thmF = propTautBoolVars[tF];
        caseSplit[p, t, thmT, thmF]]]
  ];

(* ============================================================ *)
(* Schema lemmas for clausify rewriting.  Built lazily on first  *)
(* nnfThm / cnfThm call.  Each is proved by propTaut at module   *)
(* boot — none of them is large enough to dominate load time.    *)

$pBool := var["p", ptBoolTy];
$qBool := var["q", ptBoolTy];
$rBool := var["r", ptBoolTy];

$nnfSchemata = Null;
$cnfSchemata = Null;

ensureSchemata[] :=
  If[$nnfSchemata === Null,
    $nnfSchemata = {
      (* ¬¬p = p *)
      propTautImpl[mkEq[ptNot[ptNot[$pBool]], $pBool]],
      (* ¬(p ∧ q) = ¬p ∨ ¬q *)
      propTautImpl[mkEq[
        ptNot[ptAnd[$pBool, $qBool]],
        ptOr[ptNot[$pBool], ptNot[$qBool]]]],
      (* ¬(p ∨ q) = ¬p ∧ ¬q *)
      propTautImpl[mkEq[
        ptNot[ptOr[$pBool, $qBool]],
        ptAnd[ptNot[$pBool], ptNot[$qBool]]]],
      (* (p ⇒ q) = ¬p ∨ q *)
      propTautImpl[mkEq[
        ptImp[$pBool, $qBool],
        ptOr[ptNot[$pBool], $qBool]]],
      (* ¬(p ⇒ q) = p ∧ ¬q *)
      propTautImpl[mkEq[
        ptNot[ptImp[$pBool, $qBool]],
        ptAnd[$pBool, ptNot[$qBool]]]],
      (* (p = q) = (¬p ∨ q) ∧ (¬q ∨ p)  — = at type bool *)
      propTautImpl[mkEq[
        mkEq[$pBool, $qBool],
        ptAnd[
          ptOr[ptNot[$pBool], $qBool],
          ptOr[ptNot[$qBool], $pBool]]]],
      (* ¬(p = q) = (p ∨ q) ∧ (¬p ∨ ¬q) *)
      propTautImpl[mkEq[
        ptNot[mkEq[$pBool, $qBool]],
        ptAnd[
          ptOr[$pBool, $qBool],
          ptOr[ptNot[$pBool], ptNot[$qBool]]]]]
    };
    $cnfSchemata = {
      (* (p ∧ q) ∨ r = (p ∨ r) ∧ (q ∨ r) *)
      propTautImpl[mkEq[
        ptOr[ptAnd[$pBool, $qBool], $rBool],
        ptAnd[ptOr[$pBool, $rBool], ptOr[$qBool, $rBool]]]],
      (* p ∨ (q ∧ r) = (p ∨ q) ∧ (p ∨ r) *)
      propTautImpl[mkEq[
        ptOr[$pBool, ptAnd[$qBool, $rBool]],
        ptAnd[ptOr[$pBool, $qBool], ptOr[$pBool, $rBool]]]]
    }
  ];

(* ============================================================ *)
(* Conversion helpers.                                           *)

combineConvs[{c_}] := c;
combineConvs[{c_, rest__}] := HOL`Drule`ORELSEC[c, combineConvs[{rest}]];

(* ============================================================ *)
(* nnfThm — ⊢ P → ⊢ NNF(P).                                      *)

HOL`Auto`PropTaut`nnfThm[th_] :=
  (
    ensureSchemata[];
    HOL`Drule`fixpointConvRule[
      HOL`Drule`DEPTHCONV[
        combineConvs[Map[HOL`Drule`REWRCONV, $nnfSchemata]]],
      th]
  );

(* ============================================================ *)
(* cnfThm — ⊢ P → ⊢ CNF(P).  Assumes input is in NNF.            *)

HOL`Auto`PropTaut`cnfThm[th_] :=
  (
    ensureSchemata[];
    HOL`Drule`fixpointConvRule[
      HOL`Drule`DEPTHCONV[
        combineConvs[Map[HOL`Drule`REWRCONV, $cnfSchemata]]],
      th]
  );

(* ============================================================ *)
(* splitConjThm — recursively split top-level ∧.                 *)

HOL`Auto`PropTaut`splitConjThm[th_] :=
  Module[{c},
    c = concl[th];
    If[isPtAnd[c],
      Join[
        HOL`Auto`PropTaut`splitConjThm[HOL`Bool`CONJUNCT1[th]],
        HOL`Auto`PropTaut`splitConjThm[HOL`Bool`CONJUNCT2[th]]],
      {th}]];

(* ============================================================ *)
(* clausifyPropThm — composed pipeline.                          *)

HOL`Auto`PropTaut`clausifyPropThm[th_] :=
  HOL`Auto`PropTaut`splitConjThm[
    HOL`Auto`PropTaut`cnfThm[
      HOL`Auto`PropTaut`nnfThm[th]]];

(* ============================================================ *)
(* clausifyContrapositives — k contrapositive rules per clause. *)

collectDisjuncts[t_] :=
  If[isPtOr[t],
    Module[{pq = destPtBin[t]},
      Join[collectDisjuncts[pq[[1]]], collectDisjuncts[pq[[2]]]]],
    {t}];

negateLiteral[t_] := If[isPtNot[t], destPtNot[t], ptNot[t]];

foldImps[{}, goal_]              := goal;
foldImps[{a_}, goal_]            := ptImp[a, goal];
foldImps[{a_, rest__}, goal_]    := ptImp[a, foldImps[{rest}, goal]];

contrapositiveAt[clauseThm_, lits_, p_Integer] :=
  If[Length[lits] === 1,
    clauseThm,
    Module[{pivot, nonPivots, antecedents, schema, schemaThm},
      pivot       = lits[[p]];
      nonPivots   = Delete[lits, p];
      antecedents = Map[negateLiteral, nonPivots];
      schema      = ptImp[concl[clauseThm], foldImps[antecedents, pivot]];
      schemaThm   = propTautImpl[schema];
      HOL`Bool`MP[schemaThm, clauseThm]
    ]];

HOL`Auto`PropTaut`clausifyContrapositives[clauseThm_] :=
  Module[{lits},
    lits = collectDisjuncts[concl[clauseThm]];
    Table[contrapositiveAt[clauseThm, lits, p], {p, 1, Length[lits]}]
  ];

End[];
EndPackage[];
