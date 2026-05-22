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
finiteSubsetThm::usage = "finiteSubsetThm — ⊢ ∀s. FINITE s ⇒ ∀t. t ⊆ s ⇒ FINITE t.";
finiteDeleteThm::usage = "finiteDeleteThm — ⊢ ∀s x. FINITE s ⇒ FINITE (DELETE s x).";
finiteImageThm::usage  = "finiteImageThm — ⊢ ∀f s. FINITE s ⇒ FINITE (IMAGE f s).";

Begin["`Private`"];

αTy   = mkVarType["A"];
βTy   = mkVarType["B"];
setTy = tyFun[αTy, boolTy];
setBTy = tyFun[βTy, boolTy];
fnTy  = tyFun[αTy, βTy];
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
fV = mkVar["f", fnTy];
yImV = mkVar["yIm", βTy];
zCh = mkVar["zCh", αTy];

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

(* ============================================================ *)
(* SUBSET machinery for finiteSubsetThm                         *)
(* ============================================================ *)

orC[]  := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notC[] := mkConst["¬", tyFun[boolTy, boolTy]];
notTm[p_] := mkComb[notC[], p];

inTm[y_, S_]      := HOL`Stdlib`Set`inTerm[y, S];
deleteTm[S_, x_]  := HOL`Stdlib`Set`deleteTerm[S, x];
subsetTm[S_, T_]  := HOL`Stdlib`Set`subsetTerm[S, T];

(* ⊢ IN y S = S y *)
inAppEq[y_, S_] :=
  HOL`Auto`Simp`simpConv[{HOL`Stdlib`Set`inDefThm}][inTm[y, S]];

(* INST-based membership equations, built deterministically (no simp     *)
(* absorption): the Set.wl theorems carry free vars y/x/S.               *)
inInsertAt[y_, x_, S_] := INST[{mkVar["y", αTy] -> y, mkVar["x", αTy] -> x,
  mkVar["S", setTy] -> S}, HOL`Stdlib`Set`inInsertThm];
inDeleteAt[y_, S_, x_] := INST[{mkVar["y", αTy] -> y, mkVar["S", setTy] -> S,
  mkVar["x", αTy] -> x}, HOL`Stdlib`Set`inDeleteThm];

(* β-instances (image type) for the IMAGE closure lemma. *)
emptyBTm[]   := mkConst["EMPTY", setBTy];
imageTm[f_, S_] := HOL`Stdlib`Set`imageTerm[f, S];
existsATm[bodyLam_] := mkComb[mkConst["∃", tyFun[tyFun[αTy, boolTy], boolTy]],
  bodyLam];

inEmptyAtA[y_] := INST[{mkVar["x", αTy] -> y}, HOL`Stdlib`Set`inEmptyThm];
inEmptyAtB[y_] := INST[{mkVar["x", βTy] -> y},
  INSTTYPE[{αTy -> βTy}, HOL`Stdlib`Set`inEmptyThm]];
inInsertBAt[y_, x_, S_] := INST[
  {mkVar["y", βTy] -> y, mkVar["x", βTy] -> x, mkVar["S", setBTy] -> S},
  INSTTYPE[{αTy -> βTy}, HOL`Stdlib`Set`inInsertThm]];
(* ⊢ IN y (IMAGE f S) = ∃x. IN x S ∧ y = f x *)
inImageAt[y_, f_, S_] := INST[{mkVar["y", βTy] -> y, mkVar["f", fnTy] -> f,
  mkVar["S", setTy] -> S}, HOL`Stdlib`Set`inImageThm];

(* ⊢ SUBSET S T = (∀x. IN x S ⇒ IN x T) *)
unfoldSubset[S_, T_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Set`subsetDefThm, S];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, T];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* from Γ ⊢ SUBSET S T, derive Γ ⊢ IN y S ⇒ IN y T *)
subsetElim[S_, T_, subsetTh_, y_] :=
  HOL`Bool`SPEC[y, EQMP[unfoldSubset[S, T], subsetTh]];

(* from Γ ⊢ ∀x. IN x S ⇒ IN x T, derive Γ ⊢ SUBSET S T *)
packSubset[S_, T_, genTh_] :=
  EQMP[HOL`Equal`SYM[unfoldSubset[S, T]], genTh];

(* from Γ ⊢ IN y S = IN y T (specific y), derive Γ ⊢ S = T *)
setExtFromInEq[S_, T_, yV_, bodyInEqTh_] :=
  Module[{bodyApp},
    bodyApp = TRANS[TRANS[HOL`Equal`SYM[inAppEq[yV, S]], bodyInEqTh],
      inAppEq[yV, T]];
    funcExtLocal[yV, S, T, bodyApp]
  ];

(* from Γ ⊢ t = U and Δ ⊢ FINITE U, derive Γ∪Δ ⊢ FINITE t *)
finRewrite[eqTh_, finU_] :=
  EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[finiteConst[], eqTh]], finU];

(* deleteSubset: from Γ ⊢ SUBSET t (x INSERT s), derive            *)
(*               Γ ⊢ SUBSET (DELETE t x) s.                         *)
deleteSubset[xElem_, tSet_, sSet_, tSubTh_] :=
  Module[{yV, dmTm, dmHyp, dmRed, yInT, yNeqX, yInXIns, redIns,
          caseEq, caseS, yInS, dischDm, gen},
    yV = mkVar["yDel", αTy];
    dmTm = inTm[yV, deleteTm[tSet, xElem]];
    dmHyp = ASSUME[dmTm];
    dmRed = EQMP[inDeleteAt[yV, tSet, xElem], dmHyp];
    (* (IN y (DELETE t x)) ⊢ IN y t ∧ ¬(y = x) *)
    yInT = HOL`Bool`CONJUNCT1[dmRed];
    yNeqX = HOL`Bool`CONJUNCT2[dmRed];
    yInXIns = HOL`Bool`MP[
      subsetElim[tSet, insertTm[xElem, sSet], tSubTh, yV], yInT];
    (* (…) ⊢ IN y (x INSERT s) *)
    redIns = EQMP[inInsertAt[yV, xElem, sSet], yInXIns];
    (* (…) ⊢ (y = x) ∨ IN y s *)
    caseEq = HOL`Bool`CONTR[inTm[yV, sSet],
      HOL`Bool`MP[HOL`Bool`NOTELIM[yNeqX], ASSUME[mkEq[yV, xElem]]]];
    (* (¬(y=x), y=x) ⊢ IN y s *)
    caseS = ASSUME[inTm[yV, sSet]];
    yInS = HOL`Bool`DISJCASES[redIns, caseEq, caseS];
    (* (…) ⊢ IN y s *)
    dischDm = HOL`Bool`DISCH[dmTm, yInS];
    gen = HOL`Bool`GEN[yV, dischDm];
    packSubset[deleteTm[tSet, xElem], sSet, gen]
  ];

(* condDeleteEqLeft: from Γ ⊢ IN x t, derive                       *)
(*                   Γ ⊢ t = x INSERT (DELETE t x).                 *)
condDeleteEqLeft[xElem_, tSet_, xInTHyp_] :=
  Module[{yV, rhsSet, memRHS, yEqX, yInTfromEq, caseEqBranch,
          caseConjBranch, th1, redFromIn, em, emEq, emNeq, th2, deduct},
    yV = mkVar["yIns", αTy];
    rhsSet = insertTm[xElem, deleteTm[tSet, xElem]];
    memRHS = TRANS[inInsertAt[yV, xElem, deleteTm[tSet, xElem]],
      HOL`Equal`APTERM[mkComb[orC[], mkEq[yV, xElem]],
        inDeleteAt[yV, tSet, xElem]]];
    (* ⊢ IN y rhsSet = (y = x) ∨ (IN y t ∧ ¬(y = x)) *)
    (* th1 : (IN y rhsSet) ⊢ IN y t  (uses IN x t for the y=x branch) *)
    th1 = Module[{mAssume, mRed, branchEq, branchConj},
      mAssume = ASSUME[inTm[yV, rhsSet]];
      mRed = EQMP[memRHS, mAssume];
      branchEq = HOL`Drule`SUBS[{HOL`Equal`SYM[ASSUME[mkEq[yV, xElem]]]},
        xInTHyp];
      (* (IN x t, y = x) ⊢ IN y t *)
      branchConj = HOL`Bool`CONJUNCT1[ASSUME[
        andTm[inTm[yV, tSet], notTm[mkEq[yV, xElem]]]]];
      HOL`Bool`DISJCASES[mRed, branchEq, branchConj]
    ];
    (* th2 : (IN y t) ⊢ IN y rhsSet *)
    th2 = Module[{yInT, emThm, br1, br2, redTh},
      yInT = ASSUME[inTm[yV, tSet]];
      emThm = HOL`Bool`EXCLUDEDMIDDLE[mkEq[yV, xElem]];
      br1 = HOL`Bool`DISJ1[ASSUME[mkEq[yV, xElem]],
        andTm[inTm[yV, tSet], notTm[mkEq[yV, xElem]]]];
      br2 = HOL`Bool`DISJ2[
        HOL`Bool`CONJ[yInT, ASSUME[notTm[mkEq[yV, xElem]]]],
        mkEq[yV, xElem]];
      redTh = HOL`Bool`DISJCASES[emThm, br1, br2];
      (* (IN y t) ⊢ (y = x) ∨ (IN y t ∧ ¬(y = x)) *)
      EQMP[HOL`Equal`SYM[memRHS], redTh]
    ];
    deduct = DEDUCTANTISYM[th1, th2];
    (* Γ ⊢ IN y t = IN y rhsSet *)
    setExtFromInEq[tSet, rhsSet, yV, deduct]
  ];

(* condDeleteEqRight: from Γ ⊢ ¬(IN x t), derive Γ ⊢ t = DELETE t x. *)
condDeleteEqRight[xElem_, tSet_, notXInTHyp_] :=
  Module[{yV, delSet, memDel, th1, th2, deduct},
    yV = mkVar["yIns", αTy];
    delSet = deleteTm[tSet, xElem];
    memDel = inDeleteAt[yV, tSet, xElem];
    (* ⊢ IN y (DELETE t x) = IN y t ∧ ¬(y = x) *)
    (* th1 : (IN y (DELETE t x)) ⊢ IN y t *)
    th1 = HOL`Bool`CONJUNCT1[EQMP[memDel, ASSUME[inTm[yV, delSet]]]];
    (* th2 : (IN y t) ⊢ IN y (DELETE t x), using ¬(IN x t) for y≠x *)
    th2 = Module[{yInT, yNeqX, conj},
      yInT = ASSUME[inTm[yV, tSet]];
      yNeqX = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[yV, xElem],
        HOL`Bool`MP[HOL`Bool`NOTELIM[notXInTHyp],
          HOL`Drule`SUBS[{ASSUME[mkEq[yV, xElem]]}, yInT]]]];
      (* (IN y t, ¬(IN x t)) ⊢ ¬(y = x) *)
      conj = HOL`Bool`CONJ[yInT, yNeqX];
      EQMP[HOL`Equal`SYM[memDel], conj]
    ];
    deduct = DEDUCTANTISYM[th1, th2];
    setExtFromInEq[tSet, delSet, yV, deduct]
  ];

(* ============================================================ *)
(* finiteSubsetThm : ⊢ ∀s. FINITE s ⇒ ∀t. t ⊆ s ⇒ FINITE t      *)
(* Induct on s with P s = ∀t. t ⊆ s ⇒ FINITE t.                 *)
(* ============================================================ *)

subsetPBody[sArg_] := mkComb[forallC[setTy], mkAbs[tV,
  impTm[subsetTm[tV, sArg], finiteAppTerm[tV]]]];

subsetBaseConj =
  Module[{tSub, subUnf, yV, impAtY, inEmptyAtY, th1, th2, deduct,
          tEqEmpty, finT},
    tSub = ASSUME[subsetTm[tV, emptyTm[]]];
    subUnf = EQMP[unfoldSubset[tV, emptyTm[]], tSub];
    (* (t ⊆ EMPTY) ⊢ ∀x. IN x t ⇒ IN x EMPTY *)
    yV = mkVar["yEmp", αTy];
    impAtY = HOL`Bool`SPEC[yV, subUnf];
    inEmptyAtY = INSTTYPE[{}, HOL`Bool`SPEC[yV,
      HOL`Bool`GEN[mkVar["x", αTy], HOL`Stdlib`Set`inEmptyThm]]];
    (* ⊢ IN y EMPTY = F  (re-aimed at yV) *)
    th1 = HOL`Bool`CONTR[inTm[yV, tV],
      EQMP[inEmptyAtY, ASSUME[inTm[yV, emptyTm[]]]]];
    (* (IN y EMPTY) ⊢ IN y t *)
    th2 = HOL`Bool`MP[impAtY, ASSUME[inTm[yV, tV]]];
    (* (t ⊆ EMPTY, IN y t) ⊢ IN y EMPTY *)
    deduct = DEDUCTANTISYM[th1, th2];
    (* (t ⊆ EMPTY) ⊢ IN y t = IN y EMPTY *)
    tEqEmpty = setExtFromInEq[tV, emptyTm[], yV, deduct];
    (* (t ⊆ EMPTY) ⊢ t = EMPTY *)
    finT = finRewrite[tEqEmpty, finiteEmptyThm];
    HOL`Bool`GEN[tV, HOL`Bool`DISCH[subsetTm[tV, emptyTm[]], finT]]
  ];

subsetStepConj =
  Module[{conjTm, conjHyp, ih, tSub, delSub, finDel, finInsDel, em,
          caseIn, caseNotIn, finT, dischTSub, genT, dischConj},
    conjTm = andTm[finiteAppTerm[sV], subsetPBody[sV]];
    conjHyp = ASSUME[conjTm];
    ih = HOL`Bool`CONJUNCT2[conjHyp];
    (* (conjHyp) ⊢ ∀t. t ⊆ s ⇒ FINITE t *)
    tSub = ASSUME[subsetTm[tV, insertTm[xV, sV]]];
    delSub = deleteSubset[xV, tV, sV, tSub];
    (* (tSub) ⊢ SUBSET (DELETE t x) s *)
    finDel = HOL`Bool`MP[HOL`Bool`SPEC[deleteTm[tV, xV], ih], delSub];
    (* (conjHyp, tSub) ⊢ FINITE (DELETE t x) *)
    finInsDel = HOL`Bool`MP[
      HOL`Bool`SPEC[deleteTm[tV, xV], HOL`Bool`SPEC[xV, finiteInsertThm]],
      finDel];
    (* (…) ⊢ FINITE (x INSERT (DELETE t x)) *)
    em = HOL`Bool`EXCLUDEDMIDDLE[inTm[xV, tV]];
    caseIn = finRewrite[condDeleteEqLeft[xV, tV, ASSUME[inTm[xV, tV]]],
      finInsDel];
    (* (IN x t, …) ⊢ FINITE t *)
    caseNotIn = finRewrite[
      condDeleteEqRight[xV, tV, ASSUME[notTm[inTm[xV, tV]]]], finDel];
    (* (¬(IN x t), …) ⊢ FINITE t *)
    finT = HOL`Bool`DISJCASES[em, caseIn, caseNotIn];
    (* (conjHyp, tSub) ⊢ FINITE t *)
    dischTSub = HOL`Bool`DISCH[subsetTm[tV, insertTm[xV, sV]], finT];
    genT = HOL`Bool`GEN[tV, dischTSub];
    dischConj = HOL`Bool`DISCH[conjTm, genT];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[sV, dischConj]]
  ];

finiteSubsetThm =
  Module[{pLam, specInduct, specBeta, ante},
    pLam = mkAbs[sV, subsetPBody[sV]];
    specInduct = HOL`Bool`ISPEC[pLam, finiteInductThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInduct];
    ante = HOL`Bool`CONJ[subsetBaseConj, subsetStepConj];
    HOL`Bool`MP[specBeta, ante]
  ];

(* ============================================================ *)
(* finiteDeleteThm : ⊢ ∀s x. FINITE s ⇒ FINITE (DELETE s x)     *)
(* DELETE s x ⊆ s, then finiteSubsetThm.                        *)
(* ============================================================ *)

finiteDeleteThm =
  Module[{finSHyp, delSubS, subsetAt, finDel},
    finSHyp = ASSUME[finiteAppTerm[sV]];
    delSubS = Module[{yV, dmTm, dmRed, yInS, gen},
      yV = mkVar["yDS", αTy];
      dmTm = inTm[yV, deleteTm[sV, xV]];
      dmRed = EQMP[inDeleteAt[yV, sV, xV], ASSUME[dmTm]];
      yInS = HOL`Bool`CONJUNCT1[dmRed];
      gen = HOL`Bool`GEN[yV, HOL`Bool`DISCH[dmTm, yInS]];
      packSubset[deleteTm[sV, xV], sV, gen]
    ];
    (* ⊢ SUBSET (DELETE s x) s *)
    subsetAt = HOL`Bool`MP[HOL`Bool`SPEC[sV, finiteSubsetThm], finSHyp];
    (* (FINITE s) ⊢ ∀t. t ⊆ s ⇒ FINITE t *)
    finDel = HOL`Bool`MP[HOL`Bool`SPEC[deleteTm[sV, xV], subsetAt], delSubS];
    (* (FINITE s) ⊢ FINITE (DELETE s x) *)
    HOL`Bool`GEN[sV, HOL`Bool`GEN[xV,
      HOL`Bool`DISCH[finiteAppTerm[sV], finDel]]]
  ];

(* ============================================================ *)
(* IMAGE closure : finiteImageThm                               *)
(*   ⊢ ∀f s. FINITE s ⇒ FINITE (IMAGE f s).                     *)
(* Two-type-var (α-set → β-set). Needs the ∃-carrying image     *)
(* identities, hand-rolled with CHOOSE/EXISTS/SUBS (MESON has   *)
(* no congruence so can't do z = x ⇒ f z = f x).                *)
(* ============================================================ *)

finiteAppTermB[s_] := mkComb[mkConst["FINITE", tyFun[setBTy, boolTy]], s];
insertBTm[x_, S_] := mkComb[mkComb[
  mkConst["INSERT", tyFun[βTy, tyFun[setBTy, setBTy]]], x], S];
finRewriteB[eqTh_, finU_] := EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[
  mkConst["FINITE", tyFun[setBTy, boolTy]], eqTh]], finU];

(* imageEmptyEq : ⊢ IMAGE f EMPTY = EMPTY *)
imageEmptyEq =
  Module[{lhsSet, inImgE, th1, th2, bodyAtZ, deduct},
    lhsSet = imageTm[fV, emptyTm[]];
    inImgE = inImageAt[yImV, fV, emptyTm[]];
    (* ⊢ IN y (IMAGE f EMPTY) = ∃x. IN x EMPTY ∧ y = f x *)
    th1 = HOL`Bool`CONTR[inTm[yImV, lhsSet],
      EQMP[inEmptyAtB[yImV], ASSUME[inTm[yImV, emptyBTm[]]]]];
    (* (IN y β-EMPTY) ⊢ IN y (IMAGE f EMPTY) *)
    th2 = Module[{exHyp, xInEmpty, yInBEmpty},
      exHyp = EQMP[inImgE, ASSUME[inTm[yImV, lhsSet]]];
      bodyAtZ = ASSUME[andTm[inTm[zCh, emptyTm[]], mkEq[yImV, mkComb[fV, zCh]]]];
      xInEmpty = HOL`Bool`CONJUNCT1[bodyAtZ];
      yInBEmpty = HOL`Bool`CONTR[inTm[yImV, emptyBTm[]],
        EQMP[inEmptyAtA[zCh], xInEmpty]];
      HOL`Bool`CHOOSE[zCh, exHyp, yInBEmpty]
    ];
    deduct = DEDUCTANTISYM[th1, th2];
    setExtFromInEq[lhsSet, emptyBTm[], yImV, deduct]
  ];

(* imageInsertEq : ⊢ IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s) *)
imageInsertEq =
  Module[{insAlpha, lhsSet, fxTm, imgS, rhsSet, lhsMem, existsLHS,
          rhsMem, imgSMem, existsImgS, th1, th2, deduct},
    insAlpha = insertTm[xV, sV];
    lhsSet = imageTm[fV, insAlpha];
    fxTm = mkComb[fV, xV];
    imgS = imageTm[fV, sV];
    rhsSet = insertBTm[fxTm, imgS];
    lhsMem = inImageAt[yImV, fV, insAlpha];
    (* ⊢ IN y lhsSet = ∃z. IN z (x INSERT s) ∧ y = f z *)
    existsLHS = concl[lhsMem][[2]];
    rhsMem = inInsertBAt[yImV, fxTm, imgS];
    (* ⊢ IN y rhsSet = (y = f x) ∨ IN y (IMAGE f s) *)
    imgSMem = inImageAt[yImV, fV, sV];
    existsImgS = concl[imgSMem][[2]];

    (* th1 : (IN y rhsSet) ⊢ IN y lhsSet *)
    th1 = Module[{rhsDisj, branch1, branch2},
      rhsDisj = EQMP[rhsMem, ASSUME[inTm[yImV, rhsSet]]];
      branch1 = Module[{yEqFx, inXIns, bodyWit, exLHS},
        yEqFx = ASSUME[mkEq[yImV, fxTm]];
        inXIns = EQMP[HOL`Equal`SYM[inInsertAt[xV, xV, sV]],
          HOL`Bool`DISJ1[REFL[xV], inTm[xV, sV]]];
        bodyWit = HOL`Bool`CONJ[inXIns, yEqFx];
        exLHS = HOL`Bool`EXISTS[existsLHS, xV, bodyWit];
        EQMP[HOL`Equal`SYM[lhsMem], exLHS]
      ];
      (* (y = f x) ⊢ IN y lhsSet *)
      branch2 = Module[{exImgS, bodyImg, wInS, yEqFw, wInIns, bodyWit2, exLHS2},
        exImgS = EQMP[imgSMem, ASSUME[inTm[yImV, imgS]]];
        bodyImg = ASSUME[andTm[inTm[zCh, sV], mkEq[yImV, mkComb[fV, zCh]]]];
        wInS = HOL`Bool`CONJUNCT1[bodyImg];
        yEqFw = HOL`Bool`CONJUNCT2[bodyImg];
        wInIns = EQMP[HOL`Equal`SYM[inInsertAt[zCh, xV, sV]],
          HOL`Bool`DISJ2[wInS, mkEq[zCh, xV]]];
        bodyWit2 = HOL`Bool`CONJ[wInIns, yEqFw];
        exLHS2 = HOL`Bool`EXISTS[existsLHS, zCh, bodyWit2];
        HOL`Bool`CHOOSE[zCh, exImgS, EQMP[HOL`Equal`SYM[lhsMem], exLHS2]]
      ];
      (* (IN y (IMAGE f s)) ⊢ IN y lhsSet *)
      HOL`Bool`DISJCASES[rhsDisj, branch1, branch2]
    ];

    (* th2 : (IN y lhsSet) ⊢ IN y rhsSet *)
    th2 = Module[{exLHSp, bodyP, wInIns, yEqFw, wDisj, branchA, branchB,
                  innerCases},
      exLHSp = EQMP[lhsMem, ASSUME[inTm[yImV, lhsSet]]];
      bodyP = ASSUME[andTm[inTm[zCh, insAlpha], mkEq[yImV, mkComb[fV, zCh]]]];
      wInIns = HOL`Bool`CONJUNCT1[bodyP];
      yEqFw = HOL`Bool`CONJUNCT2[bodyP];
      wDisj = EQMP[inInsertAt[zCh, xV, sV], wInIns];
      (* (body) ⊢ (z = x) ∨ IN z s *)
      branchA = Module[{zEqX, yEqFxThm, disj1},
        zEqX = ASSUME[mkEq[zCh, xV]];
        yEqFxThm = HOL`Drule`SUBS[{zEqX}, yEqFw];
        (* (body, z = x) ⊢ y = f x *)
        disj1 = HOL`Bool`DISJ1[yEqFxThm, inTm[yImV, imgS]];
        EQMP[HOL`Equal`SYM[rhsMem], disj1]
      ];
      branchB = Module[{wInSHyp, bodyImgWit, exImgSWit, yInImgS, disj2},
        wInSHyp = ASSUME[inTm[zCh, sV]];
        bodyImgWit = HOL`Bool`CONJ[wInSHyp, yEqFw];
        exImgSWit = HOL`Bool`EXISTS[existsImgS, zCh, bodyImgWit];
        yInImgS = EQMP[HOL`Equal`SYM[imgSMem], exImgSWit];
        disj2 = HOL`Bool`DISJ2[yInImgS, mkEq[yImV, fxTm]];
        EQMP[HOL`Equal`SYM[rhsMem], disj2]
      ];
      innerCases = HOL`Bool`DISJCASES[wDisj, branchA, branchB];
      HOL`Bool`CHOOSE[zCh, exLHSp, innerCases]
    ];

    deduct = DEDUCTANTISYM[th1, th2];
    setExtFromInEq[lhsSet, rhsSet, yImV, deduct]
  ];

finiteImageThm =
  Module[{pBodyImg, pLam, specInduct, specBeta, finiteEmptyB, finiteInsertB,
          conj1, conj2, ante, mainConcl},
    pBodyImg[sArg_] := finiteAppTermB[imageTm[fV, sArg]];
    pLam = mkAbs[sV, pBodyImg[sV]];
    specInduct = HOL`Bool`ISPEC[pLam, finiteInductThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInduct];
    finiteEmptyB = INSTTYPE[{αTy -> βTy}, finiteEmptyThm];
    finiteInsertB = INSTTYPE[{αTy -> βTy}, finiteInsertThm];

    conj1 = finRewriteB[imageEmptyEq, finiteEmptyB];
    (* ⊢ FINITE (IMAGE f EMPTY) *)

    conj2 = Module[{conjTm, conjHyp, finImgS, finImgIns, fxTm, imgS,
                    pIns, dischConj},
      conjTm = andTm[finiteAppTerm[sV], pBodyImg[sV]];
      conjHyp = ASSUME[conjTm];
      finImgS = HOL`Bool`CONJUNCT2[conjHyp];
      fxTm = mkComb[fV, xV]; imgS = imageTm[fV, sV];
      finImgIns = HOL`Bool`MP[
        HOL`Bool`SPEC[imgS, HOL`Bool`SPEC[fxTm, finiteInsertB]], finImgS];
      (* (conjHyp) ⊢ FINITE ((f x) INSERT IMAGE f s) *)
      pIns = finRewriteB[imageInsertEq, finImgIns];
      (* (conjHyp) ⊢ FINITE (IMAGE f (x INSERT s)) *)
      dischConj = HOL`Bool`DISCH[conjTm, pIns];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[sV, dischConj]]
    ];

    ante = HOL`Bool`CONJ[conj1, conj2];
    mainConcl = HOL`Bool`MP[specBeta, ante];
    (* ⊢ ∀s. FINITE s ⇒ FINITE (IMAGE f s) *)
    HOL`Bool`GEN[fV, mainConcl]
  ];

End[];
EndPackage[];
