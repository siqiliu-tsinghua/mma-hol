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

finrecConst::usage = "finrecConst[] — FINREC : (α→β→β) → β → num → (α→bool) → β → bool. Count-indexed fold graph (HOL Light FINREC): FINREC f b n s a holds when a is a fold of f over the n-element set s starting from b (any removal order). Scaffolding for the order-independent set fold behind CARD / ∑.";
finrecDefThm::usage = "finrecDefThm — ⊢ FINREC = (λf b. ITER (λs a. s = EMPTY ∧ a = b) (λr s a. ∃x c. x ∈ s ∧ r (DELETE s x) c ∧ a = f x c)).";
finrecZeroThm::usage = "finrecZeroThm — ⊢ FINREC f b 0 = (λs a. s = EMPTY ∧ a = b).";
finrecSucThm::usage  = "finrecSucThm — ⊢ FINREC f b (SUC n) = (λs a. ∃x c. x ∈ s ∧ FINREC f b n (DELETE s x) c ∧ a = f x c).";
finrecZeroAppThm::usage = "finrecZeroAppThm — ⊢ FINREC f b 0 s a = (s = EMPTY ∧ a = b).";
finrecSucAppThm::usage  = "finrecSucAppThm — ⊢ FINREC f b (SUC n) s a = (∃x c. x ∈ s ∧ FINREC f b n (DELETE s x) c ∧ a = f x c).";

deleteCommThm::usage = "deleteCommThm — ⊢ ∀s x y. (s DELETE x) DELETE y = (s DELETE y) DELETE x.";
sDelEmptyImpEqThm::usage = "sDelEmptyImpEqThm — ⊢ ∀s x y. (s DELETE x = EMPTY) ∧ (y ∈ s) ⇒ y = x.";
finrecExchangeBaseThm::usage = "finrecExchangeBaseThm — ⊢ ∀s a x. x ∈ s ∧ FINREC f b (SUC 0) s a ⇒ ∃c. FINREC f b 0 (s DELETE x) c ∧ a = f x c. (Base case n=1 of the FINREC exchange induction.)";
finrecExchangeThm::usage = "finrecExchangeThm — ⊢ (∀x y a. f x (f y a) = f y (f x a)) ⇒ ∀n s a x. x ∈ s ∧ FINREC f b (SUC n) s a ⇒ ∃c. FINREC f b n (s DELETE x) c ∧ a = f x c. The FINREC exchange / inversion lemma under full commutativity of the step function.";
finrecUniqueThm::usage = "finrecUniqueThm — ⊢ (∀x y a. f x (f y a) = f y (f x a)) ⇒ ∀n s a1 a2. FINREC f b n s a1 ∧ FINREC f b n s a2 ⇒ a1 = a2. FINREC is functional (in the result slot) under full commutativity.";
inMemAbsorbThm::usage = "inMemAbsorbThm — ⊢ ∀x s. x ∈ s ⇒ (x INSERT s) = s.";
notInMemDelInsertThm::usage = "notInMemDelInsertThm — ⊢ ∀x s. ¬(x ∈ s) ⇒ (x INSERT s) DELETE x = s.";
finrecExistsThm::usage = "finrecExistsThm — ⊢ ∀s. FINITE s ⇒ ∃n a. FINREC f b n s a. (No commutativity needed — pure constructive existence.)";

Begin["`Private`"];

αTy   = mkVarType["A"];
βTy   = mkVarType["B"];
setTy = tyFun[αTy, boolTy];
setBTy = tyFun[βTy, boolTy];
fnTy  = tyFun[αTy, βTy];
predTy = tyFun[setTy, boolTy];
finiteTy = tyFun[setTy, boolTy];

numTy = mkType["num", {}];

andC[]       := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
impC[]       := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
forallC[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
existsC[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];
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

(* ============================================================ *)
(* FINREC — count-indexed fold graph (HOL Light FINREC), the    *)
(* scaffolding for the order-independent set fold (ITSET) that  *)
(* CARD / ∑ rest on. Recursion on the count via Num`ITER:        *)
(*   FINREC f b 0       s a = (s = ∅ ∧ a = b)                    *)
(*   FINREC f b (SUC n) s a = ∃x c. x∈s ∧ FINREC f b n (s\x) c   *)
(*                                  ∧ a = f x c                  *)
(* ============================================================ *)

foldFnTy = tyFun[αTy, tyFun[βTy, βTy]];
recTy    = tyFun[setTy, tyFun[βTy, boolTy]];
finrecTy = tyFun[foldFnTy, tyFun[βTy, tyFun[numTy, recTy]]];

zeroTm[] := HOL`Stdlib`Num`zeroConst[];
sucTm[n_] := mkComb[HOL`Stdlib`Num`sucConst[], n];
iterRecConst[] := mkConst["ITER",
  tyFun[recTy, tyFun[tyFun[recTy, recTy], tyFun[numTy, recTy]]]];

finrec0Body[b_] :=
  Module[{sR, aR},
    sR = mkVar["sR", setTy]; aR = mkVar["aR", βTy];
    mkAbs[sR, mkAbs[aR, andTm[mkEq[sR, emptyTm[]], mkEq[aR, b]]]]
  ];

finrecStepBody[f_] :=
  Module[{recR, sR, aR, xR, cR, recApp, fxc, body, exC, exX},
    recR = mkVar["recR", recTy]; sR = mkVar["sR", setTy];
    aR = mkVar["aR", βTy]; xR = mkVar["xR", αTy]; cR = mkVar["cR", βTy];
    recApp = mkComb[mkComb[recR, deleteTm[sR, xR]], cR];
    fxc = mkComb[mkComb[f, xR], cR];
    body = andTm[inTm[xR, sR], andTm[recApp, mkEq[aR, fxc]]];
    exC = mkComb[existsC[βTy], mkAbs[cR, body]];
    exX = mkComb[existsC[αTy], mkAbs[xR, exC]];
    mkAbs[recR, mkAbs[sR, mkAbs[aR, exX]]]
  ];

Module[{fF, bF, body},
  fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy];
  body = mkAbs[fF, mkAbs[bF,
    mkComb[mkComb[iterRecConst[], finrec0Body[bF]], finrecStepBody[fF]]]];
  finrecDefThm = newDefinition[mkEq[mkVar["FINREC", finrecTy], body]];
];

finrecConst[] := mkConst["FINREC", finrecTy];
finrecApp[f_, b_, n_] := mkComb[mkComb[mkComb[finrecConst[], f], b], n];

(* ⊢ FINREC f b = ITER (finrec0Body b) (finrecStepBody f) *)
unfoldFinrec[f_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[finrecDefThm, f];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* Num`iterZeroEqThm / iterSucEqThm carry free e:A, f:A→A; aim them at  *)
(* the predicate target type recTy with the FINREC kernel/step.         *)
iterZeroAtRec[f_, b_] :=
  INST[{mkVar["e", recTy] -> finrec0Body[b],
        mkVar["f", tyFun[recTy, recTy]] -> finrecStepBody[f]},
    INSTTYPE[{tyVar["A"] -> recTy}, HOL`Stdlib`Num`iterZeroEqThm]];
iterSucAtRec[f_, b_] :=
  INST[{mkVar["e", recTy] -> finrec0Body[b],
        mkVar["f", tyFun[recTy, recTy]] -> finrecStepBody[f]},
    INSTTYPE[{tyVar["A"] -> recTy}, HOL`Stdlib`Num`iterSucEqThm]];

finrecZeroThm =
  Module[{fF, bF, ufb, apZero},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy];
    ufb = unfoldFinrec[fF, bF];
    apZero = HOL`Equal`APTHM[ufb, zeroTm[]];
    (* ⊢ FINREC f b 0 = ITER e0 step 0 *)
    TRANS[apZero, iterZeroAtRec[fF, bF]]
  ];

finrecSucThm =
  Module[{fF, bF, nF, ufb, apSuc, sucAt, iterN, stepN},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy]; nF = mkVar["n", numTy];
    ufb = unfoldFinrec[fF, bF];
    apSuc = HOL`Equal`APTHM[ufb, sucTm[nF]];
    (* ⊢ FINREC f b (SUC n) = ITER e0 step (SUC n) *)
    sucAt = HOL`Bool`SPEC[nF, iterSucAtRec[fF, bF]];
    (* ⊢ ITER e0 step (SUC n) = step (ITER e0 step n) *)
    iterN = HOL`Equal`SYM[HOL`Equal`APTHM[ufb, nF]];
    (* ⊢ ITER e0 step n = FINREC f b n *)
    stepN = HOL`Equal`APTERM[finrecStepBody[fF], iterN];
    (* ⊢ step (ITER e0 step n) = step (FINREC f b n) *)
    TRANS[TRANS[apSuc, sucAt], stepN]
  ];

(* Applied (β-reduced) forms used downstream. *)
finrecZeroAppThm =
  Module[{fF, bF, sR, aR, ap1},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy];
    sR = mkVar["sR", setTy]; aR = mkVar["aR", βTy];
    ap1 = HOL`Equal`APTHM[finrecZeroThm, sR];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap1 = HOL`Equal`APTHM[ap1, aR];
    TRANS[ap1, BETACONV[concl[ap1][[2]]]]
  ];

finrecSucAppThm =
  Module[{fF, bF, nF, sR, aR, ap2},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy]; nF = mkVar["n", numTy];
    sR = mkVar["sR", setTy]; aR = mkVar["aR", βTy];
    ap2 = HOL`Equal`APTHM[HOL`Equal`APTHM[finrecSucThm, sR], aR];
    (* ⊢ FINREC f b (SUC n) s a = (step (FINREC f b n)) s a *)
    HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], ap2]
  ];

(* ============================================================ *)
(* M7-4-f.2.a — helpers + base case (n=1) of the FINREC exchange. *)
(* The full exchange theorem (induction step) is M7-4-f.2.b.    *)
(* ============================================================ *)

(* deleteCommThm : ⊢ ∀s x y. (s\x)\y = (s\y)\x — propositional       *)
(* set identity, dispatched by propSetEq with deleteDefThm in scope. *)
deleteCommThm =
  Module[{sV2, xV2, yV2, eq},
    sV2 = mkVar["s", setTy]; xV2 = mkVar["x", αTy]; yV2 = mkVar["y", αTy];
    eq = propSetEq[deleteTm[deleteTm[sV2, xV2], yV2],
      deleteTm[deleteTm[sV2, yV2], xV2],
      {HOL`Stdlib`Set`deleteDefThm}];
    HOL`Bool`GEN[sV2, HOL`Bool`GEN[xV2, HOL`Bool`GEN[yV2, eq]]]
  ];

(* sDelEmptyImpEqThm : ⊢ ∀s x y. (s\x = ∅) ∧ (y∈s) ⇒ y = x.            *)
(* From y∈s ∧ ¬(y=x): inDeleteAt gives y∈s\x. SUBS with s\x=∅ rewrites *)
(* to y∈∅, which is F (inEmptyAt). CONTR. EM[y=x] closes y=x branch.   *)
sDelEmptyImpEqThm =
  Module[{sV2, xV2, yV2, conjTm, hyp, hSDel, hYInS, em, branchEq,
          branchNeq, body, disch},
    sV2 = mkVar["s", setTy]; xV2 = mkVar["x", αTy]; yV2 = mkVar["y", αTy];
    conjTm = andTm[mkEq[deleteTm[sV2, xV2], emptyTm[]], inTm[yV2, sV2]];
    hyp = ASSUME[conjTm];
    hSDel = HOL`Bool`CONJUNCT1[hyp];
    hYInS = HOL`Bool`CONJUNCT2[hyp];
    em = HOL`Bool`EXCLUDEDMIDDLE[mkEq[yV2, xV2]];
    branchEq = ASSUME[mkEq[yV2, xV2]];
    branchNeq = Module[{neq, yInDel, yInEmpty, fProof},
      neq = ASSUME[notTm[mkEq[yV2, xV2]]];
      yInDel = EQMP[HOL`Equal`SYM[inDeleteAt[yV2, sV2, xV2]],
        HOL`Bool`CONJ[hYInS, neq]];
      (* (y∈s, ¬(y=x)) ⊢ y ∈ s\x *)
      yInEmpty = HOL`Drule`SUBS[{hSDel}, yInDel];
      (* (y∈s, ¬(y=x), s\x=∅) ⊢ y ∈ EMPTY *)
      fProof = EQMP[inEmptyAtA[yV2], yInEmpty];
      (* (…) ⊢ F *)
      HOL`Bool`CONTR[mkEq[yV2, xV2], fProof]
      (* (¬(y=x), y∈s, s\x=∅) ⊢ y = x *)
    ];
    body = HOL`Bool`DISJCASES[em, branchEq, branchNeq];
    disch = HOL`Bool`DISCH[conjTm, body];
    HOL`Bool`GEN[sV2, HOL`Bool`GEN[xV2, HOL`Bool`GEN[yV2, disch]]]
  ];

(* finrecExchangeBaseThm : ⊢ ∀s a x. x∈s ∧ FINREC f b (SUC 0) s a    *)
(*                          ⇒ ∃c. FINREC f b 0 (s\x) c ∧ a = f x c.  *)
(* Unfold FINREC at SUC 0 to ∃x' c'. (...). CHOOSE x', c'. Inside,    *)
(* FINREC f b 0 (s\x') c' gives s\x' = ∅ ∧ c' = b. From x∈s + s\x'=∅, *)
(* sDelEmptyImpEqThm forces x = x'. Witness c = b; transport          *)
(* x'→x via SUBS and conclude.                                         *)
finrecExchangeBaseThm =
  Module[{fF, bF, sV2, aV2, xV2, xP, cP, conjTm, conjHyp, xInS, finRec1,
          finRec1Unf, innerExTm, bodyAtXP, bodyTm, bodyHyp, xPInS,
          finrec0AtSxP, aEqFxPcP, finrec0Unf, sMinusXPEqEmpty, cPEqB,
          xEqXP, sucXEqXP, sMinusXEqEmpty, aEqFxB, witnessC, fxBeqA,
          finrec0AtSx, existsBody, existsC2, chosenC, chosenXC, dischConj},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy];
    sV2 = mkVar["sEx", setTy]; aV2 = mkVar["aEx", βTy]; xV2 = mkVar["xEx", αTy];
    xP = mkVar["xP", αTy]; cP = mkVar["cP", βTy];

    conjTm = andTm[inTm[xV2, sV2],
      mkComb[mkComb[finrecApp[fF, bF, sucTm[zeroTm[]]], sV2], aV2]];
    conjHyp = ASSUME[conjTm];
    xInS = HOL`Bool`CONJUNCT1[conjHyp];
    finRec1 = HOL`Bool`CONJUNCT2[conjHyp];

    (* Unfold FINREC f b (SUC 0) s a — INST finrecSucAppThm at n=0,s=sV2,a=aV2 *)
    finRec1Unf = EQMP[INST[{mkVar["n", numTy] -> zeroTm[],
      mkVar["sR", setTy] -> sV2, mkVar["aR", βTy] -> aV2}, finrecSucAppThm],
      finRec1];
    (* (conjHyp) ⊢ ∃x' c'. x'∈s ∧ FINREC f b 0 (s\x') c' ∧ a = f x' c' *)

    (* Inner ∃: ∃c'. body[xP, c'] *)
    innerExTm = mkComb[existsC[βTy], mkAbs[cP,
      andTm[inTm[xP, sV2],
        andTm[mkComb[mkComb[finrecApp[fF, bF, zeroTm[]], deleteTm[sV2, xP]], cP],
          mkEq[aV2, mkComb[mkComb[fF, xP], cP]]]]]];
    bodyAtXP = ASSUME[innerExTm];
    bodyTm = andTm[inTm[xP, sV2],
      andTm[mkComb[mkComb[finrecApp[fF, bF, zeroTm[]], deleteTm[sV2, xP]], cP],
        mkEq[aV2, mkComb[mkComb[fF, xP], cP]]]];
    bodyHyp = ASSUME[bodyTm];

    xPInS = HOL`Bool`CONJUNCT1[bodyHyp];
    finrec0AtSxP = HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[bodyHyp]];
    aEqFxPcP = HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[bodyHyp]];

    (* From FINREC f b 0 (s\xP) cP : INST finrecZeroAppThm *)
    finrec0Unf = EQMP[INST[{mkVar["sR", setTy] -> deleteTm[sV2, xP],
      mkVar["aR", βTy] -> cP}, finrecZeroAppThm], finrec0AtSxP];
    (* (body) ⊢ (s\xP = ∅) ∧ (cP = b) *)
    sMinusXPEqEmpty = HOL`Bool`CONJUNCT1[finrec0Unf];
    cPEqB = HOL`Bool`CONJUNCT2[finrec0Unf];

    (* x = xP via sDelEmptyImpEqThm with hyps (s\xP = ∅) ∧ (x ∈ s) *)
    xEqXP = HOL`Bool`MP[
      HOL`Bool`SPEC[xV2, HOL`Bool`SPEC[xP, HOL`Bool`SPEC[sV2, sDelEmptyImpEqThm]]],
      HOL`Bool`CONJ[sMinusXPEqEmpty, xInS]];
    (* (body, conjHyp) ⊢ x = xP *)

    (* s\x = ∅: rewrite s\xP = ∅ using SYM[xEqXP] (xP → x) *)
    sMinusXEqEmpty = HOL`Drule`SUBS[{HOL`Equal`SYM[xEqXP]}, sMinusXPEqEmpty];
    (* (body, conjHyp) ⊢ s\x = ∅ *)

    (* a = f x b: from aEqFxPcP (a = f xP cP), substitute cP→b then xP→x. *)
    aEqFxB = HOL`Drule`SUBS[{HOL`Equal`SYM[xEqXP], cPEqB}, aEqFxPcP];
    (* (body, conjHyp) ⊢ a = f x b *)

    (* Build FINREC f b 0 (s\x) b *)
    finrec0AtSx = EQMP[HOL`Equal`SYM[INST[
      {mkVar["sR", setTy] -> deleteTm[sV2, xV2],
       mkVar["aR", βTy] -> bF}, finrecZeroAppThm]],
      HOL`Bool`CONJ[sMinusXEqEmpty, REFL[bF]]];
    (* (body, conjHyp) ⊢ FINREC f b 0 (s\x) b *)

    (* Combine: FINREC f b 0 (s\x) b ∧ a = f x b *)
    witnessC = HOL`Bool`CONJ[finrec0AtSx, aEqFxB];

    (* ∃c. FINREC f b 0 (s\x) c ∧ a = f x c, witness c = b *)
    existsBody = mkComb[existsC[βTy], mkAbs[cP,
      andTm[mkComb[mkComb[finrecApp[fF, bF, zeroTm[]], deleteTm[sV2, xV2]], cP],
        mkEq[aV2, mkComb[mkComb[fF, xV2], cP]]]]];
    existsC2 = HOL`Bool`EXISTS[existsBody, bF, witnessC];
    (* (body, conjHyp) ⊢ ∃c. … *)

    (* CHOOSE cP from the inner ∃, then CHOOSE xP from the outer ∃. *)
    chosenC = HOL`Bool`CHOOSE[cP, bodyAtXP, existsC2];
    (* (innerExTm[xP], conjHyp) ⊢ ∃c. … *)
    chosenXC = HOL`Bool`CHOOSE[xP, finRec1Unf, chosenC];
    (* (conjHyp) ⊢ ∃c. … *)

    dischConj = HOL`Bool`DISCH[conjTm, chosenXC];
    HOL`Bool`GEN[sV2, HOL`Bool`GEN[aV2, HOL`Bool`GEN[xV2, dischConj]]]
  ];

(* ============================================================ *)
(* M7-4-f.2.b — exchange lemma full induction step              *)
(*   (comm) ⊢ ∀n s a x. x∈s ∧ FINREC f b (SUC n) s a            *)
(*               ⇒ ∃c. FINREC f b n (s\x) c ∧ a = f x c.        *)
(* numInductionThm on n; base = finrecExchangeBaseThm.          *)
(* Step: unfold FINREC at SUC(SUC n) to ∃y c'. …; CHOOSE y, c'. *)
(* EM[x=y]. x=y branch: SUBS y→x; witness c=c'. x≠y branch: IH  *)
(* at (s\y, c', x) gives ∃c''. FINREC f b n ((s\y)\x) c'' ∧     *)
(* c'=f x c''. deleteCommThm + SUBS rewrites (s\y)\x → (s\x)\y. *)
(* y∈s\x via inDeleteAt. Build FINREC f b (SUC n) (s\x) (f y c'')*)
(* via finrecSucAppThm EXISTS at (y, c''). Comm SPEC y x c'':    *)
(* f y (f x c'') = f x (f y c''); chain with a=f y c'=f y(f x c'')*)
(* to get a = f x (f y c''). Witness c = f y c''.                *)
(* ============================================================ *)

commTm[fArg_] :=
  Module[{x, y, a},
    x = mkVar["xC", αTy]; y = mkVar["yC", αTy]; a = mkVar["aC", βTy];
    mkComb[forallC[αTy], mkAbs[x, mkComb[forallC[αTy], mkAbs[y,
      mkComb[forallC[βTy], mkAbs[a,
        mkEq[mkComb[mkComb[fArg, x], mkComb[mkComb[fArg, y], a]],
             mkComb[mkComb[fArg, y], mkComb[mkComb[fArg, x], a]]]]]]]]]];

finrecExchangeThm =
  Module[{fF, bF, nFv, sB, aB, xB, cB, commHypTm, commHyp, pIndBody, pIndLam,
          specInd, specBeta, step, ante, mainConcl},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy];
    nFv = mkVar["n", numTy];
    sB = mkVar["sEx", setTy]; aB = mkVar["aEx", βTy];
    xB = mkVar["xEx", αTy]; cB = mkVar["cP", βTy];

    commHypTm = commTm[fF];
    commHyp = ASSUME[commHypTm];

    (* pIndBody[nArg] := ∀sEx aEx xEx. (xEx∈sEx ∧ FINREC f b (SUC nArg) sEx aEx)
                            ⇒ ∃cP. FINREC f b nArg (sEx\xEx) cP ∧ aEx = f xEx cP *)
    pIndBody[nArg_] := mkComb[forallC[setTy], mkAbs[sB,
      mkComb[forallC[βTy], mkAbs[aB,
        mkComb[forallC[αTy], mkAbs[xB,
          impTm[andTm[inTm[xB, sB],
              mkComb[mkComb[finrecApp[fF, bF, sucTm[nArg]], sB], aB]],
            mkComb[existsC[βTy], mkAbs[cB,
              andTm[mkComb[mkComb[finrecApp[fF, bF, nArg], deleteTm[sB, xB]], cB],
                mkEq[aB, mkComb[mkComb[fF, xB], cB]]]]]]]]]]]];

    pIndLam = mkAbs[nFv, pIndBody[nFv]];
    specInd = HOL`Bool`ISPEC[pIndLam, HOL`Stdlib`Num`numInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];
    (* ⊢ pIndBody[0] ∧ (∀n. pIndBody[n] ⇒ pIndBody[SUC n]) ⇒ ∀n. pIndBody[n] *)

    step =
      Module[{nL, ihHyp, conjT, conjHyp, xInS, finRecSS, finRecSSUnf,
              yE, cPin, finRecSSUnfRHS, outerExLamForXR, innerExAtYE,
              innerExHyp, innerExBodyLam, bodyAtYECPin, bodyHyp,
              yInS, finRecSnAtSDelY, aEqFyCp, em, goalExistsTm,
              caseEq, caseNeq, resultUnion, chosenCP, chosenY,
              dischConj, gens, dischIH},
        nL = mkVar["n", numTy];
        ihHyp = ASSUME[pIndBody[nL]];
        conjT = andTm[inTm[xB, sB],
          mkComb[mkComb[finrecApp[fF, bF, sucTm[sucTm[nL]]], sB], aB]];
        conjHyp = ASSUME[conjT];
        xInS = HOL`Bool`CONJUNCT1[conjHyp];
        finRecSS = HOL`Bool`CONJUNCT2[conjHyp];

        finRecSSUnf = EQMP[INST[
          {mkVar["n", numTy] -> sucTm[nL],
           mkVar["sR", setTy] -> sB, mkVar["aR", βTy] -> aB},
          finrecSucAppThm], finRecSS];
        (* (conjHyp) ⊢ ∃xR cR. xR∈s ∧ FINREC f b (SUC nL) (s\xR) cR ∧ aB = f xR cR *)

        yE = mkVar["yE", αTy]; cPin = mkVar["cPin", βTy];
        finRecSSUnfRHS = concl[finRecSSUnf];
        outerExLamForXR = finRecSSUnfRHS[[2]];
        innerExAtYE = concl[BETACONV[mkComb[outerExLamForXR, yE]]][[2]];
        (* ∃cR. body[yE, cR] *)
        innerExHyp = ASSUME[innerExAtYE];
        innerExBodyLam = innerExAtYE[[2]];
        bodyAtYECPin = concl[BETACONV[mkComb[innerExBodyLam, cPin]]][[2]];
        bodyHyp = ASSUME[bodyAtYECPin];
        (* body: yE∈s ∧ FINREC f b (SUC nL) (s\yE) cPin ∧ aB = f yE cPin *)
        yInS = HOL`Bool`CONJUNCT1[bodyHyp];
        finRecSnAtSDelY = HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[bodyHyp]];
        aEqFyCp = HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[bodyHyp]];

        em = HOL`Bool`EXCLUDEDMIDDLE[mkEq[xB, yE]];

        goalExistsTm = mkComb[existsC[βTy], mkAbs[cB,
          andTm[mkComb[mkComb[finrecApp[fF, bF, sucTm[nL]], deleteTm[sB, xB]], cB],
            mkEq[aB, mkComb[mkComb[fF, xB], cB]]]]];

        caseEq = Module[{xEqY, sym, finRecAtSDelX, aEqFxCp, witC},
          xEqY = ASSUME[mkEq[xB, yE]];
          sym = HOL`Equal`SYM[xEqY];
          finRecAtSDelX = HOL`Drule`SUBS[{sym}, finRecSnAtSDelY];
          aEqFxCp = HOL`Drule`SUBS[{sym}, aEqFyCp];
          witC = HOL`Bool`CONJ[finRecAtSDelX, aEqFxCp];
          HOL`Bool`EXISTS[goalExistsTm, cPin, witC]
        ];

        caseNeq = Module[{xNeqY, yEqXAss, symYX, yNeqX, xInSDelY,
                          ihAt, ihMP, cPP, ihBodyT, ihBodyHyp,
                          finRecNAtSDelYDelX, cpEqFxCpp, delCommAt, delCommSym,
                          finRecNAtSDelXDelY, yInSDelX, fycPP, sucNAppInst,
                          sucNAppInstRHS, outerLamX, innerExAtYE2,
                          innerLamCR, bodyAtYECPP, witnessThree,
                          innerExisted, outerExisted, finRecSucNAtSDelXfyCpp,
                          aEqFyFxCpp, commAt, aEqFxFyCpp, witC2, exT2,
                          chosenCPP},
          xNeqY = ASSUME[notTm[mkEq[xB, yE]]];
          yEqXAss = ASSUME[mkEq[yE, xB]];
          symYX = HOL`Equal`SYM[yEqXAss];
          yNeqX = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[yE, xB],
            HOL`Bool`MP[HOL`Bool`NOTELIM[xNeqY], symYX]]];

          xInSDelY = EQMP[HOL`Equal`SYM[inDeleteAt[xB, sB, yE]],
            HOL`Bool`CONJ[xInS, xNeqY]];

          ihAt = HOL`Bool`SPEC[xB,
            HOL`Bool`SPEC[cPin, HOL`Bool`SPEC[deleteTm[sB, yE], ihHyp]]];
          ihMP = HOL`Bool`MP[ihAt,
            HOL`Bool`CONJ[xInSDelY, finRecSnAtSDelY]];

          cPP = mkVar["cPP", βTy];
          ihBodyT = andTm[
            mkComb[mkComb[finrecApp[fF, bF, nL],
              deleteTm[deleteTm[sB, yE], xB]], cPP],
            mkEq[cPin, mkComb[mkComb[fF, xB], cPP]]];
          ihBodyHyp = ASSUME[ihBodyT];
          finRecNAtSDelYDelX = HOL`Bool`CONJUNCT1[ihBodyHyp];
          cpEqFxCpp = HOL`Bool`CONJUNCT2[ihBodyHyp];

          delCommAt = HOL`Bool`SPEC[yE, HOL`Bool`SPEC[xB,
            HOL`Bool`SPEC[sB, deleteCommThm]]];
          (* ⊢ (sB\xB)\yE = (sB\yE)\xB *)
          delCommSym = HOL`Equal`SYM[delCommAt];
          (* ⊢ (sB\yE)\xB = (sB\xB)\yE *)
          finRecNAtSDelXDelY = HOL`Drule`SUBS[{delCommSym},
            finRecNAtSDelYDelX];
          (* (…) ⊢ FINREC f b nL ((sB\xB)\yE) cPP *)

          yInSDelX = EQMP[HOL`Equal`SYM[inDeleteAt[yE, sB, xB]],
            HOL`Bool`CONJ[yInS, yNeqX]];

          fycPP = mkComb[mkComb[fF, yE], cPP];
          sucNAppInst = INST[
            {mkVar["n", numTy] -> nL,
             mkVar["sR", setTy] -> deleteTm[sB, xB],
             mkVar["aR", βTy] -> fycPP},
            finrecSucAppThm];
          (* ⊢ FINREC f b (SUC nL) (sB\xB) (f yE cPP) = ∃xR cR. … *)
          sucNAppInstRHS = concl[sucNAppInst][[2]];
          outerLamX = sucNAppInstRHS[[2]];
          innerExAtYE2 = concl[BETACONV[mkComb[outerLamX, yE]]][[2]];
          innerLamCR = innerExAtYE2[[2]];
          bodyAtYECPP = concl[BETACONV[mkComb[innerLamCR, cPP]]][[2]];

          witnessThree = HOL`Bool`CONJ[yInSDelX,
            HOL`Bool`CONJ[finRecNAtSDelXDelY, REFL[fycPP]]];
          innerExisted = HOL`Bool`EXISTS[innerExAtYE2, cPP, witnessThree];
          outerExisted = HOL`Bool`EXISTS[sucNAppInstRHS, yE, innerExisted];
          finRecSucNAtSDelXfyCpp = EQMP[HOL`Equal`SYM[sucNAppInst], outerExisted];
          (* (…) ⊢ FINREC f b (SUC nL) (sB\xB) (f yE cPP) *)

          aEqFyFxCpp = HOL`Drule`SUBS[{cpEqFxCpp}, aEqFyCp];
          (* (body, ihBody) ⊢ aB = f yE (f xB cPP) *)
          commAt = HOL`Bool`SPEC[cPP, HOL`Bool`SPEC[xB,
            HOL`Bool`SPEC[yE, commHyp]]];
          (* (commHyp) ⊢ f yE (f xB cPP) = f xB (f yE cPP) *)
          aEqFxFyCpp = TRANS[aEqFyFxCpp, commAt];
          (* (commHyp, body, ihBody) ⊢ aB = f xB (f yE cPP) *)

          witC2 = HOL`Bool`CONJ[finRecSucNAtSDelXfyCpp, aEqFxFyCpp];
          exT2 = HOL`Bool`EXISTS[goalExistsTm, fycPP, witC2];
          (* (commHyp, body, ihBody, conjHyp) ⊢ ∃cP. … *)
          chosenCPP = HOL`Bool`CHOOSE[cPP, ihMP, exT2];
          chosenCPP
        ];

        resultUnion = HOL`Bool`DISJCASES[em, caseEq, caseNeq];
        chosenCP = HOL`Bool`CHOOSE[cPin, innerExHyp, resultUnion];
        chosenY = HOL`Bool`CHOOSE[yE, finRecSSUnf, chosenCP];

        dischConj = HOL`Bool`DISCH[conjT, chosenY];
        gens = HOL`Bool`GEN[sB, HOL`Bool`GEN[aB,
          HOL`Bool`GEN[xB, dischConj]]];
        dischIH = HOL`Bool`DISCH[pIndBody[nL], gens];
        HOL`Bool`GEN[nL, dischIH]
      ];

    ante = HOL`Bool`CONJ[finrecExchangeBaseThm, step];
    mainConcl = HOL`Bool`MP[specBeta, ante];
    (* (commHyp) ⊢ ∀n. pIndBody[n] *)
    HOL`Bool`DISCH[commHypTm, mainConcl]
    (* ⊢ commHypTm ⇒ ∀n. pIndBody[n] *)
  ];

(* ============================================================ *)
(* M7-4-f.3.a — FINREC uniqueness                                *)
(*   (comm) ⊢ ∀n s a1 a2. FINREC f b n s a1 ∧ FINREC f b n s a2  *)
(*               ⇒ a1 = a2.                                      *)
(* numInductionThm on n. Base n=0: both sides force a1=b=a2.    *)
(* Step n=SUC m: unfold FINREC at SUC m for a1 → ∃x1 c1. CHOOSE. *)
(* Apply finrecExchangeThm to FINREC f b (SUC m) s a2 at x1     *)
(* (using x1∈s from the first decomp) → ∃cAux. FINREC f b m     *)
(* (s\x1) cAux ∧ a2 = f x1 cAux. CHOOSE cAux. IH on (s\x1, c1,   *)
(* cAux) gives c1 = cAux; chain a1 = f x1 c1 = f x1 cAux = a2.   *)
(* No x1=x2 case-split — exchange handles both uniformly.        *)
(* ============================================================ *)

finrecUniqueThm =
  Module[{fF, bF, nFv, sU, a1U, a2U, c1U, cAuxU, x1U, commHypTm, commHyp,
          exchangeAt, pUniqBody, pUniqLam, specInd, specBeta, base, step,
          ante, mainConcl},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy];
    nFv = mkVar["n", numTy];
    sU = mkVar["sU", setTy]; a1U = mkVar["a1U", βTy]; a2U = mkVar["a2U", βTy];
    c1U = mkVar["c1U", βTy]; cAuxU = mkVar["cAuxU", βTy];
    x1U = mkVar["x1U", αTy];

    commHypTm = commTm[fF];
    commHyp = ASSUME[commHypTm];
    exchangeAt = HOL`Bool`MP[finrecExchangeThm, commHyp];
    (* (commHyp) ⊢ ∀n s a x. x∈s ∧ FINREC f b (SUC n) s a ⇒ ∃c. … *)

    pUniqBody[nArg_] := mkComb[forallC[setTy], mkAbs[sU,
      mkComb[forallC[βTy], mkAbs[a1U,
        mkComb[forallC[βTy], mkAbs[a2U,
          impTm[andTm[
              mkComb[mkComb[finrecApp[fF, bF, nArg], sU], a1U],
              mkComb[mkComb[finrecApp[fF, bF, nArg], sU], a2U]],
            mkEq[a1U, a2U]]]]]]]];

    pUniqLam = mkAbs[nFv, pUniqBody[nFv]];
    specInd = HOL`Bool`ISPEC[pUniqLam, HOL`Stdlib`Num`numInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];

    base =
      Module[{conjT, conjHyp, fr1, fr2, fr1Unf, fr2Unf, a1EqB, a2EqB,
              a1EqA2, dischConj},
        conjT = andTm[
          mkComb[mkComb[finrecApp[fF, bF, zeroTm[]], sU], a1U],
          mkComb[mkComb[finrecApp[fF, bF, zeroTm[]], sU], a2U]];
        conjHyp = ASSUME[conjT];
        fr1 = HOL`Bool`CONJUNCT1[conjHyp];
        fr2 = HOL`Bool`CONJUNCT2[conjHyp];
        fr1Unf = EQMP[INST[
          {mkVar["sR", setTy] -> sU, mkVar["aR", βTy] -> a1U},
          finrecZeroAppThm], fr1];
        fr2Unf = EQMP[INST[
          {mkVar["sR", setTy] -> sU, mkVar["aR", βTy] -> a2U},
          finrecZeroAppThm], fr2];
        a1EqB = HOL`Bool`CONJUNCT2[fr1Unf];
        a2EqB = HOL`Bool`CONJUNCT2[fr2Unf];
        a1EqA2 = TRANS[a1EqB, HOL`Equal`SYM[a2EqB]];
        dischConj = HOL`Bool`DISCH[conjT, a1EqA2];
        HOL`Bool`GEN[sU, HOL`Bool`GEN[a1U, HOL`Bool`GEN[a2U, dischConj]]]
      ];

    step =
      Module[{nL, ihHyp, conjT, conjHyp, fr1, fr2, fr1Unf, fr1UnfConcl,
              outerLamX1, innerExAtX1, innerExHyp, innerLamC1, bodyAtX1C1,
              bodyHyp, x1InS, frmAtSDelX1c1, a1EqFx1c1, exchAt, exchMP,
              cAuxBodyT, cAuxBodyHyp, frmAtSDelX1cAux, a2EqFx1cAux,
              ihAt, c1EqcAux, fxc1Eq, a1EqFxcAux, a1EqA2,
              chosenCAux, chosenC1, chosenX1, dischConj, gens, dischIH},
        nL = mkVar["n", numTy];
        ihHyp = ASSUME[pUniqBody[nL]];

        conjT = andTm[
          mkComb[mkComb[finrecApp[fF, bF, sucTm[nL]], sU], a1U],
          mkComb[mkComb[finrecApp[fF, bF, sucTm[nL]], sU], a2U]];
        conjHyp = ASSUME[conjT];
        fr1 = HOL`Bool`CONJUNCT1[conjHyp];
        fr2 = HOL`Bool`CONJUNCT2[conjHyp];

        fr1Unf = EQMP[INST[
          {mkVar["sR", setTy] -> sU, mkVar["aR", βTy] -> a1U},
          finrecSucAppThm], fr1];
        (* (conjHyp) ⊢ ∃xR cR. xR∈sU ∧ FINREC f b nL (sU\xR) cR ∧ a1U = f xR cR *)
        fr1UnfConcl = concl[fr1Unf];
        outerLamX1 = fr1UnfConcl[[2]];
        innerExAtX1 = concl[BETACONV[mkComb[outerLamX1, x1U]]][[2]];
        innerExHyp = ASSUME[innerExAtX1];
        innerLamC1 = innerExAtX1[[2]];
        bodyAtX1C1 = concl[BETACONV[mkComb[innerLamC1, c1U]]][[2]];
        bodyHyp = ASSUME[bodyAtX1C1];

        x1InS = HOL`Bool`CONJUNCT1[bodyHyp];
        frmAtSDelX1c1 = HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[bodyHyp]];
        a1EqFx1c1 = HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[bodyHyp]];

        exchAt = HOL`Bool`SPEC[x1U, HOL`Bool`SPEC[a2U,
          HOL`Bool`SPEC[sU, HOL`Bool`SPEC[nL, exchangeAt]]]];
        exchMP = HOL`Bool`MP[exchAt, HOL`Bool`CONJ[x1InS, fr2]];
        (* (commHyp, conjHyp, body) ⊢ ∃c. FINREC f b nL (sU\x1U) c ∧ a2U = f x1U c *)

        cAuxBodyT = andTm[
          mkComb[mkComb[finrecApp[fF, bF, nL], deleteTm[sU, x1U]], cAuxU],
          mkEq[a2U, mkComb[mkComb[fF, x1U], cAuxU]]];
        cAuxBodyHyp = ASSUME[cAuxBodyT];
        frmAtSDelX1cAux = HOL`Bool`CONJUNCT1[cAuxBodyHyp];
        a2EqFx1cAux = HOL`Bool`CONJUNCT2[cAuxBodyHyp];

        ihAt = HOL`Bool`SPEC[cAuxU, HOL`Bool`SPEC[c1U,
          HOL`Bool`SPEC[deleteTm[sU, x1U], ihHyp]]];
        c1EqcAux = HOL`Bool`MP[ihAt,
          HOL`Bool`CONJ[frmAtSDelX1c1, frmAtSDelX1cAux]];

        fxc1Eq = HOL`Equal`APTERM[mkComb[fF, x1U], c1EqcAux];
        a1EqFxcAux = TRANS[a1EqFx1c1, fxc1Eq];
        a1EqA2 = TRANS[a1EqFxcAux, HOL`Equal`SYM[a2EqFx1cAux]];

        chosenCAux = HOL`Bool`CHOOSE[cAuxU, exchMP, a1EqA2];
        chosenC1 = HOL`Bool`CHOOSE[c1U, innerExHyp, chosenCAux];
        chosenX1 = HOL`Bool`CHOOSE[x1U, fr1Unf, chosenC1];

        dischConj = HOL`Bool`DISCH[conjT, chosenX1];
        gens = HOL`Bool`GEN[sU, HOL`Bool`GEN[a1U,
          HOL`Bool`GEN[a2U, dischConj]]];
        dischIH = HOL`Bool`DISCH[pUniqBody[nL], gens];
        HOL`Bool`GEN[nL, dischIH]
      ];

    ante = HOL`Bool`CONJ[base, step];
    mainConcl = HOL`Bool`MP[specBeta, ante];
    HOL`Bool`DISCH[commHypTm, mainConcl]
  ];

(* ============================================================ *)
(* M7-4-f.3.b — FINREC existence + supporting set identities    *)
(*                                                              *)
(*   inMemAbsorbThm: x∈s ⇒ x INSERT s = s                       *)
(*   notInMemDelInsertThm: ¬(x∈s) ⇒ (x INSERT s) DELETE x = s   *)
(*   finrecExistsThm: FINITE s ⇒ ∃n a. FINREC f b n s a         *)
(*                                                              *)
(* finiteInduct on s for existence. INSERT step case-splits on  *)
(* x∈s: absorbed → witness same n, a; new → SUC n, f x a via    *)
(* the SUC clause + DEL-INSERT identity.                        *)
(* ============================================================ *)

inMemAbsorbThm =
  Module[{xV2, sV2, yV2, xInS, thLHS, thRHS, deduct, setEq, disch},
    xV2 = mkVar["x", αTy]; sV2 = mkVar["s", setTy]; yV2 = mkVar["yI", αTy];
    xInS = ASSUME[inTm[xV2, sV2]];
    thLHS = Module[{yInSh, disj},
      yInSh = ASSUME[inTm[yV2, sV2]];
      disj = HOL`Bool`DISJ2[yInSh, mkEq[yV2, xV2]];
      EQMP[HOL`Equal`SYM[inInsertAt[yV2, xV2, sV2]], disj]
    ];
    thRHS = Module[{yInIns, disjUnf, caseEq, caseIn},
      yInIns = ASSUME[inTm[yV2, insertTm[xV2, sV2]]];
      disjUnf = EQMP[inInsertAt[yV2, xV2, sV2], yInIns];
      caseEq = HOL`Drule`SUBS[{HOL`Equal`SYM[ASSUME[mkEq[yV2, xV2]]]}, xInS];
      caseIn = ASSUME[inTm[yV2, sV2]];
      HOL`Bool`DISJCASES[disjUnf, caseEq, caseIn]
    ];
    deduct = DEDUCTANTISYM[thLHS, thRHS];
    setEq = setExtFromInEq[insertTm[xV2, sV2], sV2, yV2, deduct];
    disch = HOL`Bool`DISCH[inTm[xV2, sV2], setEq];
    HOL`Bool`GEN[xV2, HOL`Bool`GEN[sV2, disch]]
  ];

notInMemDelInsertThm =
  Module[{xV2, sV2, yV2, notXInS, thLHS, thRHS, deduct, setEq, disch},
    xV2 = mkVar["x", αTy]; sV2 = mkVar["s", setTy]; yV2 = mkVar["yD", αTy];
    notXInS = ASSUME[notTm[inTm[xV2, sV2]]];
    thLHS = Module[{yInSh, yNeqX, yInIns, conj},
      yInSh = ASSUME[inTm[yV2, sV2]];
      yNeqX = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[yV2, xV2],
        HOL`Bool`MP[HOL`Bool`NOTELIM[notXInS],
          HOL`Drule`SUBS[{ASSUME[mkEq[yV2, xV2]]}, yInSh]]]];
      yInIns = EQMP[HOL`Equal`SYM[inInsertAt[yV2, xV2, sV2]],
        HOL`Bool`DISJ2[yInSh, mkEq[yV2, xV2]]];
      conj = HOL`Bool`CONJ[yInIns, yNeqX];
      EQMP[HOL`Equal`SYM[inDeleteAt[yV2, insertTm[xV2, sV2], xV2]], conj]
    ];
    thRHS = Module[{yInDelIns, delUnf, yInIns, yNeqX, insUnf, caseEq, caseIn},
      yInDelIns = ASSUME[inTm[yV2, deleteTm[insertTm[xV2, sV2], xV2]]];
      delUnf = EQMP[inDeleteAt[yV2, insertTm[xV2, sV2], xV2], yInDelIns];
      yInIns = HOL`Bool`CONJUNCT1[delUnf];
      yNeqX = HOL`Bool`CONJUNCT2[delUnf];
      insUnf = EQMP[inInsertAt[yV2, xV2, sV2], yInIns];
      caseEq = HOL`Bool`CONTR[inTm[yV2, sV2],
        HOL`Bool`MP[HOL`Bool`NOTELIM[yNeqX], ASSUME[mkEq[yV2, xV2]]]];
      caseIn = ASSUME[inTm[yV2, sV2]];
      HOL`Bool`DISJCASES[insUnf, caseEq, caseIn]
    ];
    deduct = DEDUCTANTISYM[thLHS, thRHS];
    setEq = setExtFromInEq[deleteTm[insertTm[xV2, sV2], xV2], sV2, yV2, deduct];
    disch = HOL`Bool`DISCH[notTm[inTm[xV2, sV2]], setEq];
    HOL`Bool`GEN[xV2, HOL`Bool`GEN[sV2, disch]]
  ];

finrecExistsThm =
  Module[{fF, bF, nU, aU, nC, aC, pExistsBody, pExistsLam, specInd, specBeta,
          base, step, ante, mainConcl},
    fF = mkVar["f", foldFnTy]; bF = mkVar["b", βTy];
    nU = mkVar["nE", numTy]; aU = mkVar["aE", βTy];
    nC = mkVar["nC", numTy]; aC = mkVar["aC", βTy];

    pExistsBody[sArg_] := mkComb[existsC[numTy], mkAbs[nU,
      mkComb[existsC[βTy], mkAbs[aU,
        mkComb[mkComb[finrecApp[fF, bF, nU], sArg], aU]]]]];

    pExistsLam = mkAbs[sV, pExistsBody[sV]];
    specInd = HOL`Bool`ISPEC[pExistsLam, finiteInductThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];

    base =
      Module[{frEmpB, exInnerTm, exInner},
        frEmpB = EQMP[HOL`Equal`SYM[INST[
          {mkVar["sR", setTy] -> emptyTm[], mkVar["aR", βTy] -> bF},
          finrecZeroAppThm]],
          HOL`Bool`CONJ[REFL[emptyTm[]], REFL[bF]]];
        exInnerTm = mkComb[existsC[βTy], mkAbs[aU,
          mkComb[mkComb[finrecApp[fF, bF, zeroTm[]], emptyTm[]], aU]]];
        exInner = HOL`Bool`EXISTS[exInnerTm, bF, frEmpB];
        HOL`Bool`EXISTS[pExistsBody[emptyTm[]], zeroTm[], exInner]
      ];

    step =
      Module[{conjT, conjHyp, ih, ihConcl, outerLamN, innerExAtNC,
              exInnerHyp, innerLamA, bodyAtNCAC, exBodyHyp, em, goalExistsTm,
              caseIn, caseNotIn, resultUnion, chosenA, chosenN,
              dischConj, gens},
        conjT = andTm[finiteAppTerm[sV], pExistsBody[sV]];
        conjHyp = ASSUME[conjT];
        ih = HOL`Bool`CONJUNCT2[conjHyp];
        ihConcl = concl[ih];
        outerLamN = ihConcl[[2]];
        innerExAtNC = concl[BETACONV[mkComb[outerLamN, nC]]][[2]];
        exInnerHyp = ASSUME[innerExAtNC];
        innerLamA = innerExAtNC[[2]];
        bodyAtNCAC = concl[BETACONV[mkComb[innerLamA, aC]]][[2]];
        exBodyHyp = ASSUME[bodyAtNCAC];
        (* exBodyHyp : FINREC f b nC sV aC *)

        em = HOL`Bool`EXCLUDEDMIDDLE[inTm[xV, sV]];
        goalExistsTm = pExistsBody[insertTm[xV, sV]];

        caseIn =
          Module[{xInS, xInsEqS, sEqXIns, frAtXIns, exInnerNewTm, exInnerNew},
            xInS = ASSUME[inTm[xV, sV]];
            xInsEqS = HOL`Bool`MP[
              HOL`Bool`SPEC[sV, HOL`Bool`SPEC[xV, inMemAbsorbThm]], xInS];
            sEqXIns = HOL`Equal`SYM[xInsEqS];
            frAtXIns = HOL`Drule`SUBS[{sEqXIns}, exBodyHyp];
            exInnerNewTm = mkComb[existsC[βTy], mkAbs[aU,
              mkComb[mkComb[finrecApp[fF, bF, nC], insertTm[xV, sV]], aU]]];
            exInnerNew = HOL`Bool`EXISTS[exInnerNewTm, aC, frAtXIns];
            HOL`Bool`EXISTS[goalExistsTm, nC, exInnerNew]
          ];

        caseNotIn =
          Module[{notXInS, delEq, frAtXInsDelX, xInIns, refl, fxa,
                  sucInst, sucInstRHS, outerLamY, innerExAtX, innerLamC,
                  bodyAtXAC, witnessC, innerExisted, outerExisted, frSuc,
                  exInnerNewTm, exInnerNew},
            notXInS = ASSUME[notTm[inTm[xV, sV]]];
            delEq = HOL`Bool`MP[
              HOL`Bool`SPEC[sV, HOL`Bool`SPEC[xV, notInMemDelInsertThm]],
              notXInS];
            frAtXInsDelX = HOL`Drule`SUBS[{HOL`Equal`SYM[delEq]}, exBodyHyp];
            xInIns = EQMP[HOL`Equal`SYM[inInsertAt[xV, xV, sV]],
              HOL`Bool`DISJ1[REFL[xV], inTm[xV, sV]]];
            fxa = mkComb[mkComb[fF, xV], aC];
            refl = REFL[fxa];

            sucInst = INST[
              {mkVar["n", numTy] -> nC,
               mkVar["sR", setTy] -> insertTm[xV, sV],
               mkVar["aR", βTy] -> fxa},
              finrecSucAppThm];
            sucInstRHS = concl[sucInst][[2]];
            outerLamY = sucInstRHS[[2]];
            innerExAtX = concl[BETACONV[mkComb[outerLamY, xV]]][[2]];
            innerLamC = innerExAtX[[2]];
            bodyAtXAC = concl[BETACONV[mkComb[innerLamC, aC]]][[2]];

            witnessC = HOL`Bool`CONJ[xInIns,
              HOL`Bool`CONJ[frAtXInsDelX, refl]];
            innerExisted = HOL`Bool`EXISTS[innerExAtX, aC, witnessC];
            outerExisted = HOL`Bool`EXISTS[sucInstRHS, xV, innerExisted];
            frSuc = EQMP[HOL`Equal`SYM[sucInst], outerExisted];

            exInnerNewTm = mkComb[existsC[βTy], mkAbs[aU,
              mkComb[mkComb[finrecApp[fF, bF, sucTm[nC]], insertTm[xV, sV]], aU]]];
            exInnerNew = HOL`Bool`EXISTS[exInnerNewTm, fxa, frSuc];
            HOL`Bool`EXISTS[goalExistsTm, sucTm[nC], exInnerNew]
          ];

        resultUnion = HOL`Bool`DISJCASES[em, caseIn, caseNotIn];
        chosenA = HOL`Bool`CHOOSE[aC, exInnerHyp, resultUnion];
        chosenN = HOL`Bool`CHOOSE[nC, ih, chosenA];
        dischConj = HOL`Bool`DISCH[conjT, chosenN];
        gens = HOL`Bool`GEN[xV, HOL`Bool`GEN[sV, dischConj]];
        gens
      ];

    ante = HOL`Bool`CONJ[base, step];
    mainConcl = HOL`Bool`MP[specBeta, ante];
    mainConcl
  ];

End[];
EndPackage[];
