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
  "HOL`Stdlib`Set`"
}];

finiteConst::usage = "finiteConst[] — FINITE : (α → bool) → bool. Smallest predicate with FINITE EMPTY and FINITE s ⇒ FINITE (x INSERT s).";
finiteDefThm::usage = "finiteDefThm — ⊢ FINITE = (λs. ∀P. (P EMPTY ∧ (∀x t. P t ⇒ P (x INSERT t))) ⇒ P s).";
finiteAppTerm::usage = "finiteAppTerm[s] — build `FINITE s`.";

finiteEmptyThm::usage  = "finiteEmptyThm — ⊢ FINITE EMPTY.";
finiteInsertThm::usage = "finiteInsertThm — ⊢ ∀x s. FINITE s ⇒ FINITE (x INSERT s).";
finiteSingThm::usage   = "finiteSingThm — ⊢ ∀x. FINITE (SING x).";
finiteInductThm::usage = "finiteInductThm — ⊢ ∀P. P EMPTY ∧ (∀x s. FINITE s ∧ P s ⇒ P (x INSERT s)) ⇒ ∀s. FINITE s ⇒ P s.";

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

End[];
EndPackage[];
