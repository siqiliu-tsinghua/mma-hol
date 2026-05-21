(* ::Package:: *)

(* M7-4-e stdlib/Finite — finite sets, inductively.

   FINITE is the smallest predicate on sets containing EMPTY and closed
   under INSERT (HOL Light style rule-induction definition):

     FINITE = λs. ∀P. (P EMPTY ∧ (∀x t. P t ⇒ P (x INSERT t))) ⇒ P s

   e.2 (this file, foundation): FINITE + the closure rules (EMPTY,
   INSERT, SING) and the strong induction principle
     ⊢ ∀P. P EMPTY ∧ (∀x s. FINITE s ∧ P s ⇒ P (x INSERT s))
            ⇒ ∀s. FINITE s ⇒ P s.
   e.3 adds the algebraic closure lemmas (SUBSET / UNION / IMAGE /
   DELETE). CARD / ∑ are a later step. *)

BeginPackage["HOL`Stdlib`Finite`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`", "HOL`Auto`PropTaut`", "HOL`Stdlib`Set`"
}];

finiteConst::usage = "finiteConst[] — FINITE : (α → bool) → bool. Smallest predicate with FINITE EMPTY and FINITE s ⇒ FINITE (x INSERT s).";
finiteDefThm::usage = "finiteDefThm — ⊢ FINITE = (λs. ∀P. (P EMPTY ∧ (∀x t. P t ⇒ P (x INSERT t))) ⇒ P s).";
finiteAppTerm::usage = "finiteAppTerm[s] — build `FINITE s`.";

finiteEmptyThm::usage  = "finiteEmptyThm — ⊢ FINITE EMPTY.";
finiteInsertThm::usage = "finiteInsertThm — ⊢ ∀x s. FINITE s ⇒ FINITE (x INSERT s).";
finiteSingThm::usage   = "finiteSingThm — ⊢ ∀x. FINITE (SING x).";
finiteInductThm::usage = "finiteInductThm — ⊢ ∀P. P EMPTY ∧ (∀x s. FINITE s ∧ P s ⇒ P (x INSERT s)) ⇒ ∀s. FINITE s ⇒ P s.";
finiteUnionThm::usage  = "finiteUnionThm — ⊢ ∀s t. FINITE s ⇒ FINITE t ⇒ FINITE (s ∪ t).";

Begin["`Private`"];

αTy   = mkVarType["A"];
setTy = tyFun[αTy, boolTy];
predTy = tyFun[setTy, boolTy];
finiteTy = tyFun[setTy, boolTy];

andC[]       := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
impC[]       := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
forallC[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
andTm[a_, b_] := mkComb[mkComb[andC[], a], b];
impTm[a_, b_] := mkComb[mkComb[impC[], a], b];

emptyTm[]         := HOL`Stdlib`Set`emptyConst[];
insertTm[x_, s_]  := HOL`Stdlib`Set`insertTerm[x, s];

xV = mkVar["x", αTy];
tV = mkVar["t", setTy];
sV = mkVar["s", setTy];

(* closedAt[fp] = fp EMPTY ∧ (∀x t. fp t ⇒ fp (x INSERT t)).         *)
(* Used both as the def body and (with fp a λ-set) at the induction  *)
(* minimality step; fp never has free x/t so the binders don't       *)
(* capture.                                                          *)
closedAt[fp_] :=
  andTm[mkComb[fp, emptyTm[]],
    mkComb[forallC[αTy], mkAbs[xV, mkComb[forallC[setTy], mkAbs[tV,
      impTm[mkComb[fp, tV], mkComb[fp, insertTm[xV, tV]]]]]]]];

(* ============================================================ *)
(* FINITE definition                                            *)
(* ============================================================ *)

Module[{fpV, finiteBody},
  fpV = mkVar["P", predTy];
  finiteBody = mkAbs[sV, mkComb[forallC[predTy], mkAbs[fpV,
    impTm[closedAt[fpV], mkComb[fpV, sV]]]]];
  finiteDefThm = newDefinition[mkEq[mkVar["FINITE", finiteTy], finiteBody]];
];

finiteConst[] := mkConst["FINITE", finiteTy];
finiteAppTerm[s_] := mkComb[finiteConst[], s];

(* ⊢ FINITE s = ∀P. closedAt[P] ⇒ P s *)
unfoldFinite[sTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[finiteDefThm, sTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ============================================================ *)
(* finiteEmptyThm : ⊢ FINITE EMPTY                              *)
(* ============================================================ *)

finiteEmptyThm =
  Module[{fpV, unf, closed, fpEmpty, disch, gen},
    fpV = mkVar["P", predTy];
    unf = unfoldFinite[emptyTm[]];
    closed = ASSUME[closedAt[fpV]];
    fpEmpty = HOL`Bool`CONJUNCT1[closed];
    disch = HOL`Bool`DISCH[closedAt[fpV], fpEmpty];
    gen = HOL`Bool`GEN[fpV, disch];
    EQMP[HOL`Equal`SYM[unf], gen]
  ];

(* ============================================================ *)
(* finiteInsertThm : ⊢ ∀x s. FINITE s ⇒ FINITE (x INSERT s)     *)
(* ============================================================ *)

finiteInsertThm =
  Module[{fpV, finSHyp, finSUnf, unfIns, closedTm, closed, fpS,
          stepConj, stepAt, fpIns, dischClosed, genFp, finIns, dischFin},
    fpV = mkVar["P", predTy];
    finSHyp = ASSUME[finiteAppTerm[sV]];
    finSUnf = EQMP[unfoldFinite[sV], finSHyp];
    (* (FINITE s) ⊢ ∀P. closedAt[P] ⇒ P s *)
    unfIns = unfoldFinite[insertTm[xV, sV]];
    closedTm = closedAt[fpV];
    closed = ASSUME[closedTm];
    fpS = HOL`Bool`MP[HOL`Bool`SPEC[fpV, finSUnf], closed];
    (* (FINITE s, closedAt P) ⊢ P s *)
    stepConj = HOL`Bool`CONJUNCT2[closed];
    stepAt = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[xV, stepConj]];
    (* (closedAt P) ⊢ P s ⇒ P (x INSERT s) *)
    fpIns = HOL`Bool`MP[stepAt, fpS];
    (* (FINITE s, closedAt P) ⊢ P (x INSERT s) *)
    dischClosed = HOL`Bool`DISCH[closedTm, fpIns];
    genFp = HOL`Bool`GEN[fpV, dischClosed];
    finIns = EQMP[HOL`Equal`SYM[unfIns], genFp];
    (* (FINITE s) ⊢ FINITE (x INSERT s) *)
    dischFin = HOL`Bool`DISCH[finiteAppTerm[sV], finIns];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[sV, dischFin]]
  ];

(* ============================================================ *)
(* finiteSingThm : ⊢ ∀x. FINITE (SING x)                        *)
(* ============================================================ *)

finiteSingThm =
  Module[{insAt, finInsEmpty, singUnfold, rewrite},
    insAt = HOL`Bool`SPEC[emptyTm[], HOL`Bool`SPEC[xV, finiteInsertThm]];
    (* ⊢ FINITE EMPTY ⇒ FINITE (x INSERT EMPTY) *)
    finInsEmpty = HOL`Bool`MP[insAt, finiteEmptyThm];
    (* ⊢ FINITE (x INSERT EMPTY) *)
    singUnfold = HOL`Equal`APTHM[HOL`Stdlib`Set`singDefThm, xV];
    singUnfold = TRANS[singUnfold, BETACONV[concl[singUnfold][[2]]]];
    (* ⊢ SING x = x INSERT EMPTY *)
    rewrite = HOL`Equal`APTERM[finiteConst[], singUnfold];
    (* ⊢ FINITE (SING x) = FINITE (x INSERT EMPTY) *)
    HOL`Bool`GEN[xV, EQMP[HOL`Equal`SYM[rewrite], finInsEmpty]]
  ];

(* ============================================================ *)
(* finiteInductThm — strong induction (FINITE s in the step).   *)
(*   Induct with Q = λs. FINITE s ∧ P s; closed[Q] follows from  *)
(*   the weak hypotheses + finiteEmpty/finiteInsert; minimality  *)
(*   (instantiate ∀P at Q) gives FINITE s ⇒ Q s ⇒ P s.           *)
(* ============================================================ *)

finiteInductThm =
  Module[{pV, hypTm, hHyp, pEmptyH, stepH, qLam,
          conj1, conj2, closedQ, finSHyp, finSUnf, specQ, qS,
          betaQs, qsUnf, pS, dischFin, genS, dischH},
    pV = mkVar["P", predTy];
    hypTm = andTm[mkComb[pV, emptyTm[]],
      mkComb[forallC[αTy], mkAbs[xV, mkComb[forallC[setTy], mkAbs[sV,
        impTm[andTm[finiteAppTerm[sV], mkComb[pV, sV]],
              mkComb[pV, insertTm[xV, sV]]]]]]]];
    hHyp = ASSUME[hypTm];
    pEmptyH = HOL`Bool`CONJUNCT1[hHyp];
    stepH = HOL`Bool`CONJUNCT2[hHyp];
    qLam = mkAbs[sV, andTm[finiteAppTerm[sV], mkComb[pV, sV]]];

    (* conj1 : (H) ⊢ Q EMPTY *)
    conj1 = Module[{betaQE, rhs},
      betaQE = BETACONV[mkComb[qLam, emptyTm[]]];
      rhs = HOL`Bool`CONJ[finiteEmptyThm, pEmptyH];
      EQMP[HOL`Equal`SYM[betaQE], rhs]
    ];

    (* conj2 : (H) ⊢ ∀x t. Q t ⇒ Q (x INSERT t) *)
    conj2 = Module[{qtHyp, betaQt, qtUnf, finT, finInsApp, stepAt,
                    pInsApp, qInsRhs, betaQins, qIns, dischQt},
      qtHyp = ASSUME[mkComb[qLam, tV]];
      betaQt = BETACONV[mkComb[qLam, tV]];
      qtUnf = EQMP[betaQt, qtHyp];
      (* (Q t) ⊢ FINITE t ∧ P t *)
      finT = HOL`Bool`CONJUNCT1[qtUnf];
      finInsApp = HOL`Bool`MP[
        HOL`Bool`SPEC[tV, HOL`Bool`SPEC[xV, finiteInsertThm]], finT];
      (* (Q t) ⊢ FINITE (x INSERT t) *)
      stepAt = HOL`Bool`SPEC[tV, HOL`Bool`SPEC[xV, stepH]];
      (* (H) ⊢ FINITE t ∧ P t ⇒ P (x INSERT t) *)
      pInsApp = HOL`Bool`MP[stepAt, qtUnf];
      (* (H, Q t) ⊢ P (x INSERT t) *)
      qInsRhs = HOL`Bool`CONJ[finInsApp, pInsApp];
      betaQins = BETACONV[mkComb[qLam, insertTm[xV, tV]]];
      qIns = EQMP[HOL`Equal`SYM[betaQins], qInsRhs];
      (* (H, Q t) ⊢ Q (x INSERT t) *)
      dischQt = HOL`Bool`DISCH[mkComb[qLam, tV], qIns];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[tV, dischQt]]
    ];

    closedQ = HOL`Bool`CONJ[conj1, conj2];
    (* (H) ⊢ closedAt[Q] *)

    finSHyp = ASSUME[finiteAppTerm[sV]];
    finSUnf = EQMP[unfoldFinite[sV], finSHyp];
    specQ = HOL`Bool`SPEC[qLam, finSUnf];
    (* (FINITE s) ⊢ closedAt[Q] ⇒ Q s *)
    qS = HOL`Bool`MP[specQ, closedQ];
    (* (FINITE s, H) ⊢ Q s *)
    betaQs = BETACONV[mkComb[qLam, sV]];
    qsUnf = EQMP[betaQs, qS];
    pS = HOL`Bool`CONJUNCT2[qsUnf];
    (* (FINITE s, H) ⊢ P s *)
    dischFin = HOL`Bool`DISCH[finiteAppTerm[sV], pS];
    genS = HOL`Bool`GEN[sV, dischFin];
    dischH = HOL`Bool`DISCH[hypTm, genS];
    HOL`Bool`GEN[pV, dischH]
  ];

(* ============================================================ *)
(* Local set-equality helper for the propositional identities.  *)
(* Mirrors auto/Set`setProve but with a caller-chosen rule set   *)
(* (so INSERT unfolds). Sound only for equalities whose per-     *)
(* element membership is a propositional tautology.              *)
(* ============================================================ *)

unionTm[a_, b_] := HOL`Stdlib`Set`unionTerm[a, b];

funcExtLocal[yV_, fTm_, gTm_, bodyTh_] :=
  Module[{absEq, etaF, etaG},
    absEq = ABS[yV, bodyTh];
    etaF = HOL`Bool`ISPEC[fTm, HOL`Bootstrap`etaAx];
    etaG = HOL`Bool`ISPEC[gTm, HOL`Bootstrap`etaAx];
    TRANS[TRANS[HOL`Equal`SYM[etaF], absEq], etaG]
  ];

setUnfoldRules[] := {HOL`Stdlib`Set`unionDefThm,
  HOL`Stdlib`Set`insertDefThm, HOL`Stdlib`Set`emptyDefThm};

freshLocal[base_String, forbidden_List] :=
  Module[{i = 0, cand = base},
    While[MemberQ[forbidden, cand], i++; cand = base <> ToString[i]];
    cand
  ];

propSetEq[lhsSet_, rhsSet_, rules_] :=
  Module[{domTy, yName, yV, appEq, simpEq, propTh, bodyTh},
    domTy = typeOf[lhsSet][[2, 1]];
    yName = freshLocal["y", First /@ freesIn[mkEq[lhsSet, rhsSet]]];
    yV = mkVar[yName, domTy];
    appEq = mkEq[mkComb[lhsSet, yV], mkComb[rhsSet, yV]];
    simpEq = HOL`Auto`Simp`simpConv[rules][appEq];
    propTh = HOL`Auto`PropTaut`propTaut[concl[simpEq][[2]]];
    bodyTh = EQMP[HOL`Equal`SYM[simpEq], propTh];
    funcExtLocal[yV, lhsSet, rhsSet, bodyTh]
  ];

(* ============================================================ *)
(* finiteUnionThm : ⊢ ∀s t. FINITE s ⇒ FINITE t ⇒ FINITE (s ∪ t) *)
(* Induct on s with P s = FINITE t ⇒ FINITE (s ∪ t).             *)
(* ============================================================ *)

finiteUnionThm =
  Module[{pBody, pLam, specInduct, specBeta, rules, emptyUnionEq,
          conj1, stepClean, ante, mainConcl, base},
    pBody[sArg_] := impTm[finiteAppTerm[tV], finiteAppTerm[unionTm[sArg, tV]]];
    pLam = mkAbs[sV, pBody[sV]];
    specInduct = HOL`Bool`ISPEC[pLam, finiteInductThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInduct];
    (* ⊢ (conj1 ∧ step) ⇒ ∀s. FINITE s ⇒ (FINITE t ⇒ FINITE (s ∪ t)) *)
    rules = setUnfoldRules[];

    (* conj1 : FINITE t ⇒ FINITE (EMPTY ∪ t) *)
    conj1 = Module[{eqE, ft, finEU},
      eqE = propSetEq[unionTm[emptyTm[], tV], tV, rules];
      (* ⊢ EMPTY ∪ t = t *)
      ft = ASSUME[finiteAppTerm[tV]];
      finEU = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[finiteConst[], eqE]], ft];
      (* ⊢ FINITE (EMPTY ∪ t) *)
      HOL`Bool`DISCH[finiteAppTerm[tV], finEU]
    ];

    (* step : ∀x s. (FINITE s ∧ P s) ⇒ (FINITE t ⇒ FINITE ((x INSERT s) ∪ t)) *)
    stepClean = Module[{conjTm, conjHyp, ps, ft, finSU, eqIns, finIns,
                        finXIns, dischFt, dischConj},
      conjTm = andTm[finiteAppTerm[sV], pBody[sV]];
      conjHyp = ASSUME[conjTm];
      ps = HOL`Bool`CONJUNCT2[conjHyp];
      ft = ASSUME[finiteAppTerm[tV]];
      finSU = HOL`Bool`MP[ps, ft];
      (* (conjHyp, FINITE t) ⊢ FINITE (s ∪ t) *)
      eqIns = propSetEq[unionTm[insertTm[xV, sV], tV],
        insertTm[xV, unionTm[sV, tV]], rules];
      (* ⊢ (x INSERT s) ∪ t = x INSERT (s ∪ t) *)
      finIns = HOL`Bool`MP[
        HOL`Bool`SPEC[unionTm[sV, tV], HOL`Bool`SPEC[xV, finiteInsertThm]],
        finSU];
      (* ⊢ FINITE (x INSERT (s ∪ t)) *)
      finXIns = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[finiteConst[], eqIns]],
        finIns];
      (* ⊢ FINITE ((x INSERT s) ∪ t) *)
      dischFt = HOL`Bool`DISCH[finiteAppTerm[tV], finXIns];
      dischConj = HOL`Bool`DISCH[conjTm, dischFt];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[sV, dischConj]]
    ];

    ante = HOL`Bool`CONJ[conj1, stepClean];
    mainConcl = HOL`Bool`MP[specBeta, ante];
    (* ⊢ ∀s. FINITE s ⇒ (FINITE t ⇒ FINITE (s ∪ t)) *)
    base = HOL`Bool`SPEC[sV, mainConcl];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[tV, base]]
  ];

End[];
EndPackage[];
