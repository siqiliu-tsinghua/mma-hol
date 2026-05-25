(* ::Package:: *)

(* FTA prerequisites (deferred from M7-3): a small set of number-theory
   helpers that are the immediate building blocks for the unique
   factorization theorem. The capstone itself — primeOrCompositeThm
   dichotomy → primeDivExistsThm (every n > 1 has a prime divisor) →
   factorization existence over lists → uniqueness modulo permutation
   — is staged in follow-on commits. *)

BeginPackage["HOL`Stdlib`FTA`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Stdlib`Num`", "HOL`Stdlib`List`"
}];

dividesPosThm::usage = "dividesPosThm — ⊢ ∀d n. ¬ (n = 0) ⇒ divides d n ⇒ ¬ (d = 0). If n is non-zero and d divides n, then d is non-zero.";
dividesTransThm::usage = "dividesTransThm — ⊢ ∀a b c. divides a b ⇒ divides b c ⇒ divides a c. Transitivity of divisibility.";
notOneNorZeroLtThm::usage = "notOneNorZeroLtThm — ⊢ ∀d. ¬ (d = 0) ⇒ ¬ (d = SUC 0) ⇒ SUC 0 < d. A num that is neither 0 nor 1 must be > 1.";
primeOrCompositeThm::usage = "primeOrCompositeThm — ⊢ ∀n. SUC 0 < n ⇒ prime n ∨ (∃d. SUC 0 < d ∧ d < n ∧ divides d n). Dichotomy: every n > 1 is prime or has a proper divisor.";
primeDivExistsThm::usage = "primeDivExistsThm — ⊢ ∀n. SUC 0 < n ⇒ ∃p. prime p ∧ divides p n. Every n > 1 has a prime divisor (FTA stage-1 capstone).";

posAddLtThm::usage = "posAddLtThm — ⊢ ∀c d. ¬ (d = 0) ⇒ c < c + d. Adding a positive amount strictly increases. (FTA stage-2 helper.)";
ltMultIfOneLtThm::usage = "ltMultIfOneLtThm — ⊢ ∀p c. SUC 0 < p ⇒ ¬ (c = 0) ⇒ c < p * c. Multiplying a positive amount by p > 1 strictly increases. (FTA stage-2 helper.)";
primeFactorsExistsThm::usage = "primeFactorsExistsThm — ⊢ ∀n. ¬ (n = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n. Every positive integer admits a prime factorization (FTA stage-2 capstone).";

notLeqSucSelfThm::usage = "notLeqSucSelfThm — ⊢ ∀n. ¬ (SUC n ≤ n). (Stage 3.a helper.)";
primeNotDivOneThm::usage = "primeNotDivOneThm — ⊢ ∀p. prime p ⇒ ¬ (divides p (SUC 0)). A prime cannot divide 1. (Stage 3.a helper.)";
primeDivFoldrTimesThm::usage = "primeDivFoldrTimesThm — ⊢ ∀p l. prime p ⇒ divides p (FOLDR * (SUC 0) l) ⇒ ∃y. MEM y l ∧ divides p y. Euclid's lemma on lists: a prime dividing a product of primes divides one of them. (FTA stage 3.a.)";

Begin["`Private`"];

numTy = mkType["num", {}];

zeroN[] := mkConst["0", numTy];
oneN[]  := mkComb[HOL`Stdlib`Num`sucConst[], zeroN[]];
timesN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`timesConst[], m], n];
ltN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], m], n];
dividesN[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], a], b];
notTm[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
orTm[a_, b_] := mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
existsNum[v_, body_] := mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
  mkAbs[v, body]];
andTm[a_, b_] := mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
impTm[a_, b_] := mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
primeN[p_] := mkComb[HOL`Stdlib`Num`primeConst[], p];

(* ⊢ divides a b = ∃c. b = a * c *)
unfoldDivides[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`dividesDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ a ≤ b = ∃k. a + k = b *)
unfoldLeq[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ a < b = SUC a ≤ b *)
unfoldLt[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

plusN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], m], n];
sucN[n_]      := mkComb[HOL`Stdlib`Num`sucConst[], n];
leqN[m_, n_]  := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], m], n];

(* Term builders at concrete num types for stage-2. *)
numListTy[] := HOL`Stdlib`List`listTy[numTy];
nilNumTm[]  := mkConst["NIL", numListTy[]];
consNumConst[] := mkConst["CONS",
  tyFun[numTy, tyFun[numListTy[], numListTy[]]]];
consNumApp[x_, l_] := mkComb[mkComb[consNumConst[], x], l];
allPredNumTy[] :=
  tyFun[tyFun[numTy, boolTy], tyFun[numListTy[], boolTy]];
allNumConst[] := mkConst["ALL", allPredNumTy[]];
allTm[pred_, list_] := mkComb[mkComb[allNumConst[], pred], list];
foldrNumNumConst[] :=
  mkConst["FOLDR", tyFun[
    tyFun[numTy, tyFun[numTy, numTy]],
    tyFun[numTy, tyFun[numListTy[], numTy]]]];
foldrTm[fn_, base_, list_] :=
  mkComb[mkComb[mkComb[foldrNumNumConst[], fn], base], list];
existsListTm[v_, body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[numListTy[], boolTy], boolTy]],
    mkAbs[v, body]];

(* ============================================================ *)
(* posAddLtThm  (stage-2 helper)                                 *)
(* From ¬(d=0): d = SUC d' (numCasesThm). Then                   *)
(*   c + d = c + SUC d' = SUC (c + d') = SUC c + d'.             *)
(* So ∃k. SUC c + k = c + d, i.e. SUC c ≤ c + d, i.e. c < c + d.  *)
(* ============================================================ *)

posAddLtThm =
  Module[{cV, dV, dpV, kV, dNotZHyp, casesAtD, zeroCase, sucCase,
          body, dischNotZ, gen},
    cV  = mkVar["cP", numTy];
    dV  = mkVar["dP", numTy];
    dpV = mkVar["dPpr", numTy];
    kV  = mkVar["kP", numTy];

    dNotZHyp = ASSUME[notTm[mkEq[dV, zeroN[]]]];
    casesAtD = HOL`Bool`SPEC[dV, HOL`Stdlib`Num`numCasesThm];
    (* ⊢ d = 0 ∨ ∃d'. d = SUC d' *)

    zeroCase = Module[{dEq0, fThm},
      dEq0 = ASSUME[mkEq[dV, zeroN[]]];
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[dNotZHyp], dEq0];
      HOL`Bool`CONTR[ltN[cV, plusN[cV, dV]], fThm]
    ];

    sucCase = Module[{exDpTm, exDpHyp, dEqSucDpHyp, cAddSucDp,
                      sucCAddDp, eqViaSuc, eqRewriteD, existsBody,
                      existsK, leqFolded, ltFolded, chosen},
      exDpTm = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[dpV, mkEq[dV, sucN[dpV]]]];
      exDpHyp = ASSUME[exDpTm];
      dEqSucDpHyp = ASSUME[mkEq[dV, sucN[dpV]]];

      cAddSucDp = HOL`Bool`SPEC[dpV, HOL`Bool`SPEC[cV,
        HOL`Stdlib`Num`plusSucEqThm]];
      (* ⊢ c + SUC d' = SUC (c + d') *)
      sucCAddDp = HOL`Bool`SPEC[dpV, HOL`Bool`SPEC[cV,
        HOL`Stdlib`Num`addLeftSucThm]];
      (* ⊢ SUC c + d' = SUC (c + d') *)
      eqViaSuc = TRANS[sucCAddDp, HOL`Equal`SYM[cAddSucDp]];
      (* ⊢ SUC c + d' = c + SUC d' *)
      eqRewriteD = HOL`Drule`SUBS[{HOL`Equal`SYM[dEqSucDpHyp]}, eqViaSuc];
      (* (d = SUC d') ⊢ SUC c + d' = c + d *)

      existsBody = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[kV, mkEq[plusN[sucN[cV], kV], plusN[cV, dV]]]];
      existsK = HOL`Bool`EXISTS[existsBody, dpV, eqRewriteD];
      (* (d = SUC d') ⊢ ∃k. SUC c + k = c + d *)
      leqFolded = EQMP[
        HOL`Equal`SYM[unfoldLeq[sucN[cV], plusN[cV, dV]]], existsK];
      (* (d = SUC d') ⊢ SUC c ≤ c + d *)
      ltFolded = EQMP[
        HOL`Equal`SYM[unfoldLt[cV, plusN[cV, dV]]], leqFolded];
      (* (d = SUC d') ⊢ c < c + d *)
      chosen = HOL`Bool`CHOOSE[dpV, exDpHyp, ltFolded];
      (* (∃d'. d = SUC d') ⊢ c < c + d *)
      chosen
    ];

    body = HOL`Bool`DISJCASES[casesAtD, zeroCase, sucCase];
    dischNotZ = HOL`Bool`DISCH[notTm[mkEq[dV, zeroN[]]], body];
    gen = HOL`Bool`GEN[cV, HOL`Bool`GEN[dV, dischNotZ]];
    gen
  ];

(* ============================================================ *)
(* ltMultIfOneLtThm  (stage-2 helper)                            *)
(* From SUC 0 < p: ∃k. SUC (SUC 0) + k = p. Simplify:            *)
(*   SUC (SUC 0) + k = SUC (SUC k), so p = SUC (SUC k).          *)
(*   Then p * c = SUC (SUC k) * c = c + (SUC k * c)              *)
(*              = c + (c + k * c).                                *)
(* Since c ≠ 0, c + k*c ≠ 0 (addEqZeroLeftThm); posAddLtThm       *)
(* gives c < c + (c + k*c) = p * c.                              *)
(* ============================================================ *)

ltMultIfOneLtThm =
  Module[{pV, cV, kV, oneLtPHyp, cNotZHyp, oneLtPUnf, leqExUnf,
          pEqAddHyp, innerEq, midEq, outerEq, pEqSSk,
          pTimesAt, outerTimesEq, innerTimesEq, pTimesDecomp,
          pTimesEq2, addNotZero, cLtDecomp, cLtPC, chosen,
          dischNotZ, dischOneLt, gen},
    pV = mkVar["pL", numTy]; cV = mkVar["cL", numTy];
    kV = mkVar["kL", numTy];

    oneLtPHyp = ASSUME[ltN[oneN[], pV]];
    cNotZHyp = ASSUME[notTm[mkEq[cV, zeroN[]]]];

    oneLtPUnf = EQMP[unfoldLt[oneN[], pV], oneLtPHyp];
    (* ⊢ SUC (SUC 0) ≤ p *)
    leqExUnf = EQMP[unfoldLeq[sucN[oneN[]], pV], oneLtPUnf];
    (* ⊢ ∃k. SUC (SUC 0) + k = p *)

    pEqAddHyp = ASSUME[mkEq[plusN[sucN[oneN[]], kV], pV]];
    (* (SUC (SUC 0) + k = p) ⊢ … *)

    innerEq = HOL`Bool`SPEC[kV, HOL`Stdlib`Num`addLeftZeroThm];
    (* ⊢ 0 + k = k *)
    midEq = TRANS[
      HOL`Bool`SPEC[kV, HOL`Bool`SPEC[zeroN[],
        HOL`Stdlib`Num`addLeftSucThm]],
      HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], innerEq]];
    (* ⊢ SUC 0 + k = SUC k *)
    outerEq = TRANS[
      HOL`Bool`SPEC[kV, HOL`Bool`SPEC[oneN[],
        HOL`Stdlib`Num`addLeftSucThm]],
      HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], midEq]];
    (* ⊢ SUC (SUC 0) + k = SUC (SUC k) *)

    pEqSSk = TRANS[HOL`Equal`SYM[pEqAddHyp], outerEq];
    (* (SUC (SUC 0) + k = p) ⊢ p = SUC (SUC k) *)

    pTimesAt = HOL`Equal`APTHM[
      HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], pEqSSk], cV];
    (* (…) ⊢ p * c = SUC (SUC k) * c *)

    outerTimesEq = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[sucN[kV],
      HOL`Stdlib`Num`timesLeftSucThm]];
    (* ⊢ SUC (SUC k) * c = c + (SUC k * c) *)
    innerTimesEq = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[kV,
      HOL`Stdlib`Num`timesLeftSucThm]];
    (* ⊢ SUC k * c = c + k * c *)
    pTimesDecomp = TRANS[outerTimesEq,
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`plusConst[], cV],
        innerTimesEq]];
    (* ⊢ SUC (SUC k) * c = c + (c + k * c) *)
    pTimesEq2 = TRANS[pTimesAt, pTimesDecomp];
    (* (…) ⊢ p * c = c + (c + k * c) *)

    addNotZero = Module[{addZHyp, cEq0FromAdd, fThm},
      addZHyp = ASSUME[mkEq[plusN[cV, timesN[kV, cV]], zeroN[]]];
      cEq0FromAdd = HOL`Bool`MP[
        HOL`Bool`SPEC[timesN[kV, cV], HOL`Bool`SPEC[cV,
          HOL`Stdlib`Num`addEqZeroLeftThm]], addZHyp];
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[cNotZHyp], cEq0FromAdd];
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[
        mkEq[plusN[cV, timesN[kV, cV]], zeroN[]], fThm]]
    ];
    (* (¬(c = 0)) ⊢ ¬(c + k * c = 0) *)

    cLtDecomp = HOL`Bool`MP[HOL`Bool`SPEC[plusN[cV, timesN[kV, cV]],
      HOL`Bool`SPEC[cV, posAddLtThm]], addNotZero];
    (* (¬(c = 0)) ⊢ c < c + (c + k * c) *)
    cLtPC = HOL`Drule`SUBS[{HOL`Equal`SYM[pTimesEq2]}, cLtDecomp];
    (* (¬(c = 0), SUC (SUC 0) + k = p) ⊢ c < p * c *)

    chosen = HOL`Bool`CHOOSE[kV, leqExUnf, cLtPC];
    (* (¬(c = 0), SUC 0 < p) ⊢ c < p * c *)
    dischNotZ = HOL`Bool`DISCH[notTm[mkEq[cV, zeroN[]]], chosen];
    dischOneLt = HOL`Bool`DISCH[ltN[oneN[], pV], dischNotZ];
    gen = HOL`Bool`GEN[pV, HOL`Bool`GEN[cV, dischOneLt]];
    gen
  ];

(* ============================================================ *)
(* dividesPosThm                                                 *)
(* Assume d|n and d = 0 (for contradiction). Unfold divides:    *)
(* ∃c. n = d*c. CHOOSE c. Substitute d = 0 → n = 0*c. Use        *)
(* timesCommThm + timesZeroEqThm: 0*c = c*0 = 0. So n = 0,       *)
(* contradicting ¬(n = 0).                                       *)
(* ============================================================ *)

dividesPosThm =
  Module[{dV, nV, notNzHyp, divHyp, dEq0Hyp, divUnf, cV,
          bodyEq, exHyp, nEqZC, zeroTimesC, nEqZero, fThm,
          chosenC, notDzero, dischDiv, dischNotN, gens},
    dV = mkVar["d", numTy]; nV = mkVar["n", numTy];
    notNzHyp = ASSUME[notTm[mkEq[nV, zeroN[]]]];
    divHyp = ASSUME[dividesN[dV, nV]];
    divUnf = EQMP[unfoldDivides[dV, nV], divHyp];

    dEq0Hyp = ASSUME[mkEq[dV, zeroN[]]];

    cV = mkVar["cD", numTy];
    bodyEq = mkEq[nV, timesN[dV, cV]];
    exHyp = ASSUME[bodyEq];
    nEqZC = HOL`Drule`SUBS[{dEq0Hyp}, exHyp];
    (* (bodyEq, dEq0Hyp) ⊢ n = 0*c *)
    zeroTimesC = TRANS[
      HOL`Bool`SPEC[cV, HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`timesCommThm]],
      HOL`Bool`SPEC[cV, HOL`Stdlib`Num`timesZeroEqThm]];
    (* ⊢ 0*c = 0  (via 0*c = c*0 = 0) *)
    nEqZero = TRANS[nEqZC, zeroTimesC];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notNzHyp], nEqZero];
    chosenC = HOL`Bool`CHOOSE[cV, divUnf, fThm];
    notDzero = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[dV, zeroN[]], chosenC]];
    dischDiv = HOL`Bool`DISCH[dividesN[dV, nV], notDzero];
    dischNotN = HOL`Bool`DISCH[notTm[mkEq[nV, zeroN[]]], dischDiv];
    gens = HOL`Bool`GEN[dV, HOL`Bool`GEN[nV, dischNotN]];
    gens
  ];

(* ============================================================ *)
(* dividesTransThm                                               *)
(* a|b: ∃j. b = a*j. b|c: ∃k. c = b*k. Substitute b = a*j:        *)
(* c = (a*j)*k. timesAssocThm: (a*j)*k = a*(j*k). EXISTS at      *)
(* (j*k) inside divides def of a|c.                              *)
(* ============================================================ *)

dividesTransThm =
  Module[{aV, bV, cV, divAB, divBC, divABunf, divBCunf, jV, kV,
          bEqAJhyp, cEqBKhyp, cEqAJKunassoc, assoc, cEqAJK,
          exTmA, divACInner, divACThm, chosenK, chosenJ,
          dischBC, dischAB, gens},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    divAB = ASSUME[dividesN[aV, bV]];
    divBC = ASSUME[dividesN[bV, cV]];
    divABunf = EQMP[unfoldDivides[aV, bV], divAB];
    divBCunf = EQMP[unfoldDivides[bV, cV], divBC];

    jV = mkVar["jD", numTy]; kV = mkVar["kD", numTy];
    bEqAJhyp = ASSUME[mkEq[bV, timesN[aV, jV]]];
    cEqBKhyp = ASSUME[mkEq[cV, timesN[bV, kV]]];

    cEqAJKunassoc = HOL`Drule`SUBS[{bEqAJhyp}, cEqBKhyp];
    (* (bEq, cEq) ⊢ c = (a*j) * k *)
    assoc = HOL`Bool`SPEC[kV, HOL`Bool`SPEC[jV, HOL`Bool`SPEC[aV,
      HOL`Stdlib`Num`timesAssocThm]]];
    cEqAJK = TRANS[cEqAJKunassoc, assoc];
    (* (bEq, cEq) ⊢ c = a * (j*k) *)

    exTmA = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mkVar["cD", numTy],
        mkEq[cV, timesN[aV, mkVar["cD", numTy]]]]];
    divACInner = HOL`Bool`EXISTS[exTmA, timesN[jV, kV], cEqAJK];
    divACThm = EQMP[HOL`Equal`SYM[unfoldDivides[aV, cV]], divACInner];
    (* (bEq, cEq) ⊢ divides a c *)
    chosenK = HOL`Bool`CHOOSE[kV, divBCunf, divACThm];
    chosenJ = HOL`Bool`CHOOSE[jV, divABunf, chosenK];
    dischBC = HOL`Bool`DISCH[dividesN[bV, cV], chosenJ];
    dischAB = HOL`Bool`DISCH[dividesN[aV, bV], dischBC];
    gens = HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, dischAB]]];
    gens
  ];

(* ============================================================ *)
(* notOneNorZeroLtThm                                            *)
(* ¬(d = 0) ⇒ 0 < d (= SUC 0 ≤ d via ltDefThm = 1 ≤ d).          *)
(* leqCaseEqLtThm: 1 ≤ d ⇒ 1 = d ∨ 1 < d. ¬(d = 1) = ¬(1 = d)    *)
(* by SYM rules out first; second is the goal.                   *)
(* ============================================================ *)

notOneNorZeroLtThm =
  Module[{dV, notDz, notD1, posD, oneLeqD, ap1, e1, ap2, e2, ltUnf,
          caseEq, oneEqDhyp, dEqOne, fThm, contrCase, idCase, body,
          dischNotD1, dischNotDz, gen},
    dV = mkVar["d", numTy];
    notDz = ASSUME[notTm[mkEq[dV, zeroN[]]]];
    notD1 = ASSUME[notTm[mkEq[dV, oneN[]]]];
    posD = HOL`Bool`MP[HOL`Bool`SPEC[dV, HOL`Stdlib`Num`ltZeroNotZeroThm],
      notDz];
    (* ⊢ 0 < d *)
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, zeroN[]];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, dV];
    ltUnf = TRANS[ap2, BETACONV[concl[ap2][[2]]]];
    (* ⊢ 0 < d = SUC 0 ≤ d  (i.e. = 1 ≤ d) *)
    oneLeqD = EQMP[ltUnf, posD];
    (* ⊢ 1 ≤ d *)
    caseEq = HOL`Bool`MP[HOL`Bool`SPEC[dV, HOL`Bool`SPEC[oneN[],
      HOL`Stdlib`Num`leqCaseEqLtThm]], oneLeqD];
    (* ⊢ 1 = d ∨ 1 < d *)
    oneEqDhyp = ASSUME[mkEq[oneN[], dV]];
    dEqOne = HOL`Equal`SYM[oneEqDhyp];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notD1], dEqOne];
    contrCase = HOL`Bool`CONTR[ltN[oneN[], dV], fThm];
    idCase = ASSUME[ltN[oneN[], dV]];
    body = HOL`Bool`DISJCASES[caseEq, contrCase, idCase];
    (* (notDz, notD1) ⊢ 1 < d *)
    dischNotD1 = HOL`Bool`DISCH[notTm[mkEq[dV, oneN[]]], body];
    dischNotDz = HOL`Bool`DISCH[notTm[mkEq[dV, zeroN[]]], dischNotD1];
    gen = HOL`Bool`GEN[dV, dischNotDz];
    gen
  ];

(* ============================================================ *)
(* primeOrCompositeThm                                           *)
(* EM[∃d. 1<d ∧ d<n ∧ d|n]. Yes-branch: DISJ2 directly.          *)
(* No-branch: prove prime n via primeDefThm — for any d|n,       *)
(* EM[d=1]; d≠1 case uses dividesPosThm + notOneNorZeroLtThm to  *)
(* get 1<d, dividesLeqThm to get d≤n, leqCaseEqLtThm to split    *)
(* d=n vs d<n; d<n gives a witness contradicting the no-branch.  *)
(* ============================================================ *)

primeOrCompositeThm =
  Module[{nV, oneLtNHyp, nNotZero, dV, exBody, exTm, em, conclTm,
          yesCase, noCase, primeUnf, allDivClause, primeFmt, primeAtN,
          conclBody, dischOneLtN, gen},
    nV = mkVar["n", numTy];
    oneLtNHyp = ASSUME[ltN[oneN[], nV]];

    nNotZero = Module[{nEq0Hyp, oneLtZero, fThm},
      nEq0Hyp = ASSUME[mkEq[nV, zeroN[]]];
      oneLtZero = HOL`Drule`SUBS[{nEq0Hyp}, oneLtNHyp];
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[oneN[],
        HOL`Stdlib`Num`notLtZeroThm]], oneLtZero];
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[nV, zeroN[]], fThm]]
    ];
    (* (1 < n) ⊢ ¬(n = 0) *)

    dV = mkVar["dV", numTy];
    exBody = andTm[ltN[oneN[], dV], andTm[ltN[dV, nV], dividesN[dV, nV]]];
    exTm = existsNum[dV, exBody];
    em = HOL`Bool`EXCLUDEDMIDDLE[exTm];

    conclTm = orTm[primeN[nV], exTm];

    yesCase = HOL`Bool`DISJ2[ASSUME[exTm], primeN[nV]];

    noCase = Module[{notExHyp, ap, allDivBody, dV2, divDNHyp, em2, caseEq,
                     caseNeq, body, disch, gen2, allDivThm, primeAtNLocal,
                     primeFmtLocal, primeUnfLocal},
      notExHyp = ASSUME[notTm[exTm]];

      primeUnfLocal = Module[{apP},
        apP = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, nV];
        TRANS[apP, BETACONV[concl[apP][[2]]]]
      ];
      (* ⊢ prime n = (SUC 0 < n) ∧ (∀d. divides d n ⇒ d = SUC 0 ∨ d = n) *)

      dV2 = mkVar["dD", numTy];
      divDNHyp = ASSUME[dividesN[dV2, nV]];
      em2 = HOL`Bool`EXCLUDEDMIDDLE[mkEq[dV2, oneN[]]];

      caseEq = HOL`Bool`DISJ1[ASSUME[mkEq[dV2, oneN[]]], mkEq[dV2, nV]];

      caseNeq = Module[{notDeq1, dNotZero, oneLtD, dLeqN, leqCase,
                        dEqNCase, dLtNCase, body2},
        notDeq1 = ASSUME[notTm[mkEq[dV2, oneN[]]]];
        dNotZero = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[nV, HOL`Bool`SPEC[dV2, dividesPosThm]],
          nNotZero], divDNHyp];
        oneLtD = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[dV2, notOneNorZeroLtThm], dNotZero], notDeq1];
        dLeqN = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[nV, HOL`Bool`SPEC[dV2, HOL`Stdlib`Num`dividesLeqThm]],
          nNotZero], divDNHyp];
        leqCase = HOL`Bool`MP[HOL`Bool`SPEC[nV, HOL`Bool`SPEC[dV2,
          HOL`Stdlib`Num`leqCaseEqLtThm]], dLeqN];
        (* ⊢ d = n ∨ d < n *)
        dEqNCase = HOL`Bool`DISJ2[ASSUME[mkEq[dV2, nV]], mkEq[dV2, oneN[]]];
        dLtNCase = Module[{dLtN, conjPart, exAtD, fThm3},
          dLtN = ASSUME[ltN[dV2, nV]];
          conjPart = HOL`Bool`CONJ[oneLtD, HOL`Bool`CONJ[dLtN, divDNHyp]];
          exAtD = HOL`Bool`EXISTS[exTm, dV2, conjPart];
          fThm3 = HOL`Bool`MP[HOL`Bool`NOTELIM[notExHyp], exAtD];
          HOL`Bool`CONTR[orTm[mkEq[dV2, oneN[]], mkEq[dV2, nV]], fThm3]
        ];
        body2 = HOL`Bool`DISJCASES[leqCase, dEqNCase, dLtNCase];
        body2
      ];

      body = HOL`Bool`DISJCASES[em2, caseEq, caseNeq];
      disch = HOL`Bool`DISCH[dividesN[dV2, nV], body];
      gen2 = HOL`Bool`GEN[dV2, disch];
      allDivThm = gen2;

      primeFmtLocal = HOL`Bool`CONJ[oneLtNHyp, allDivThm];
      primeAtNLocal = EQMP[HOL`Equal`SYM[primeUnfLocal], primeFmtLocal];
      HOL`Bool`DISJ1[primeAtNLocal, exTm]
    ];

    conclBody = HOL`Bool`DISJCASES[em, yesCase, noCase];
    dischOneLtN = HOL`Bool`DISCH[ltN[oneN[], nV], conclBody];
    gen = HOL`Bool`GEN[nV, dischOneLtN];
    gen
  ];

(* ============================================================ *)
(* primeDivExistsThm                                             *)
(* Strong induction on n: pLam n = 1<n ⇒ ∃p. prime p ∧ p|n.      *)
(* Apply primeOrCompositeThm. Prime case: p = n (dividesReflThm).*)
(* Composite case: CHOOSE d with 1<d ∧ d<n ∧ d|n; IH gives p|d;  *)
(* dividesTransThm gives p|n.                                    *)
(* ============================================================ *)

primeDivExistsThm =
  Module[{nV, kV, pV, ihBodyAtN, pLam, specInd, specBeta, stepAnte,
          stepLam, mainConcl},
    nV = mkVar["n", numTy]; kV = mkVar["kS", numTy]; pV = mkVar["pP", numTy];

    pLam = mkAbs[nV, impTm[ltN[oneN[], nV],
      existsNum[pV, andTm[primeN[pV], dividesN[pV, nV]]]]];

    specInd = HOL`Bool`ISPEC[pLam, HOL`Stdlib`Num`strongInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];
    (* ⊢ (∀n. (∀k. k<n ⇒ (1<k ⇒ ∃p. prime p ∧ p|k))
              ⇒ (1<n ⇒ ∃p. prime p ∧ p|n))
       ⇒ ∀n. 1<n ⇒ ∃p. prime p ∧ p|n *)

    stepAnte = Module[{nLocal, ihHyp, oneLtN, primeOrCompAt, mp, pocConcl,
                       primeCase, compositeCase, dV3, exTmLoc, exHyp,
                       conjBody, conjHyp, oneLtD, dLtN, dDivN, ihAtD, mpFromIH,
                       expConcl, pVLoc, exP, exPHyp, primePbody, primePbodyHyp,
                       primeP, pDivD, pDivN, conjOut, exAtP, chosenP, chosenDV,
                       finalEx, dischOneLtN, dischIH, gens},
      nLocal = mkVar["n", numTy];

      ihHyp = ASSUME[Module[{innerBody},
        innerBody = impTm[ltN[oneN[], kV],
          existsNum[pV, andTm[primeN[pV], dividesN[pV, kV]]]];
        mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[kV, impTm[ltN[kV, nLocal], innerBody]]]]];
      (* ihHyp: ∀k. k<n ⇒ (1<k ⇒ ∃p. prime p ∧ p|k) *)

      oneLtN = ASSUME[ltN[oneN[], nLocal]];

      primeOrCompAt = HOL`Bool`MP[
        HOL`Bool`SPEC[nLocal, primeOrCompositeThm], oneLtN];
      (* ⊢ prime n ∨ ∃d. 1<d ∧ d<n ∧ d|n *)

      primeCase = Module[{primeNHyp, divNN, conjP, exNoutTm, exOut},
        primeNHyp = ASSUME[primeN[nLocal]];
        divNN = HOL`Bool`SPEC[nLocal, HOL`Stdlib`Num`dividesReflThm];
        conjP = HOL`Bool`CONJ[primeNHyp, divNN];
        exNoutTm = existsNum[pV, andTm[primeN[pV], dividesN[pV, nLocal]]];
        HOL`Bool`EXISTS[exNoutTm, nLocal, conjP]
      ];

      compositeCase = Module[{dV3Loc, exTmLoc2, exHyp2, conjT, conjHyp2,
                              oneLtD2, restCJ, dLtN2, dDivN2, ihAtDLoc,
                              implFromIH, exPbody, exP2, exPbodyHyp2,
                              primeP2, pDivD2, pDivN2, conjOut2, exTmOut, exAtPout,
                              chosenPLoc, chosenDVLoc},
        dV3Loc = mkVar["dV", numTy];
        exTmLoc2 = existsNum[dV3Loc, andTm[ltN[oneN[], dV3Loc],
          andTm[ltN[dV3Loc, nLocal], dividesN[dV3Loc, nLocal]]]];
        exHyp2 = ASSUME[exTmLoc2];
        conjT = andTm[ltN[oneN[], dV3Loc],
          andTm[ltN[dV3Loc, nLocal], dividesN[dV3Loc, nLocal]]];
        conjHyp2 = ASSUME[conjT];
        oneLtD2 = HOL`Bool`CONJUNCT1[conjHyp2];
        restCJ = HOL`Bool`CONJUNCT2[conjHyp2];
        dLtN2 = HOL`Bool`CONJUNCT1[restCJ];
        dDivN2 = HOL`Bool`CONJUNCT2[restCJ];

        ihAtDLoc = HOL`Bool`SPEC[dV3Loc, ihHyp];
        (* ⊢ dV<n ⇒ (1<dV ⇒ ∃p. prime p ∧ p|dV) *)
        implFromIH = HOL`Bool`MP[HOL`Bool`MP[ihAtDLoc, dLtN2], oneLtD2];
        (* (…) ⊢ ∃p. prime p ∧ p|dV *)

        exPbody = andTm[primeN[pV], dividesN[pV, dV3Loc]];
        exP2 = existsNum[pV, exPbody];
        exPbodyHyp2 = ASSUME[exPbody];
        primeP2 = HOL`Bool`CONJUNCT1[exPbodyHyp2];
        pDivD2 = HOL`Bool`CONJUNCT2[exPbodyHyp2];
        pDivN2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[nLocal,
          HOL`Bool`SPEC[dV3Loc, HOL`Bool`SPEC[pV, dividesTransThm]]],
          pDivD2], dDivN2];
        (* (…) ⊢ divides p n *)
        conjOut2 = HOL`Bool`CONJ[primeP2, pDivN2];
        exTmOut = existsNum[pV, andTm[primeN[pV], dividesN[pV, nLocal]]];
        exAtPout = HOL`Bool`EXISTS[exTmOut, pV, conjOut2];
        chosenPLoc = HOL`Bool`CHOOSE[pV, implFromIH, exAtPout];
        chosenDVLoc = HOL`Bool`CHOOSE[dV3Loc, exHyp2, chosenPLoc];
        chosenDVLoc
      ];

      finalEx = HOL`Bool`DISJCASES[primeOrCompAt, primeCase, compositeCase];

      dischOneLtN = HOL`Bool`DISCH[ltN[oneN[], nLocal], finalEx];
      dischIH = HOL`Bool`DISCH[concl[ihHyp], dischOneLtN];
      gens = HOL`Bool`GEN[nLocal, dischIH];
      gens
    ];

    mainConcl = HOL`Bool`MP[specBeta, stepAnte];
    mainConcl
  ];

(* ============================================================ *)
(* primeFactorsExistsThm  (FTA stage 2)                          *)
(*                                                              *)
(* Strong induction on n with predicate                         *)
(*   P n = ¬(n = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n.   *)
(*                                                              *)
(* Step: assume IH for all k < n, and ¬(n = 0).                  *)
(*   ltZeroNotZeroThm: 0 < n.                                    *)
(*   ltDef + leqCaseEqLtThm: SUC 0 = n ∨ SUC 0 < n.              *)
(*                                                              *)
(*   Case SUC 0 = n: l = NIL.                                    *)
(*     allNilThm gives ALL prime NIL.                            *)
(*     foldrNilThm + the case hypothesis give FOLDR … NIL = n.   *)
(*                                                              *)
(*   Case SUC 0 < n: primeDivExistsThm yields prime p with p|n.  *)
(*     Unfolding p|n: ∃c. n = p*c.                                *)
(*     c ≠ 0 (else n = 0 contradicts ¬(n = 0)).                  *)
(*     prime p ⇒ SUC 0 < p; ltMultIfOneLtThm ⇒ c < p*c = n.       *)
(*     IH at c: ∃l'. ALL prime l' ∧ FOLDR * (SUC 0) l' = c.       *)
(*     Take l = CONS p l'.                                       *)
(*       allConsThm: ALL prime (CONS p l') = prime p ∧ ALL p l';  *)
(*       foldrConsThm: FOLDR * (SUC 0) (CONS p l')                *)
(*                    = p * (FOLDR * (SUC 0) l') = p * c = n.     *)
(* ============================================================ *)

primeFactorsExistsThm =
  Module[{αTy, βTy, nV, lV, pLam, exTmAtN, specInd, specBeta, stepAnte,
          mainConcl},
    αTy = mkVarType["A"]; βTy = mkVarType["B"];
    nV = mkVar["nF", numTy];
    lV = mkVar["lF", numListTy[]];

    (* P = λn. ¬(n = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n *)
    pLam = mkAbs[nV, impTm[notTm[mkEq[nV, zeroN[]]],
      existsListTm[lV, andTm[
        allTm[HOL`Stdlib`Num`primeConst[], lV],
        mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], nV]]]]];

    specInd = HOL`Bool`ISPEC[pLam, HOL`Stdlib`Num`strongInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];

    stepAnte = Module[{nLocal, kV, ihHypT, ihHyp, nNotZHyp, posN,
                       sucOneLeqN, caseEq, oneEqNCase, oneLtNCase,
                       finalCase, dischNotZ, dischIH, gen,
                       exConclTm},
      nLocal = mkVar["nF", numTy];
      kV     = mkVar["kF", numTy];

      exConclTm = existsListTm[lV, andTm[
        allTm[HOL`Stdlib`Num`primeConst[], lV],
        mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], nLocal]]];

      ihHypT = mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[kV, impTm[ltN[kV, nLocal],
          impTm[notTm[mkEq[kV, zeroN[]]],
            existsListTm[lV, andTm[
              allTm[HOL`Stdlib`Num`primeConst[], lV],
              mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], kV]]]]]]];
      ihHyp = ASSUME[ihHypT];

      nNotZHyp = ASSUME[notTm[mkEq[nLocal, zeroN[]]]];

      posN = HOL`Bool`MP[
        HOL`Bool`SPEC[nLocal, HOL`Stdlib`Num`ltZeroNotZeroThm],
        nNotZHyp];
      (* ⊢ 0 < n *)
      sucOneLeqN = EQMP[unfoldLt[zeroN[], nLocal], posN];
      (* ⊢ SUC 0 ≤ n *)
      caseEq = HOL`Bool`MP[
        HOL`Bool`SPEC[nLocal, HOL`Bool`SPEC[oneN[],
          HOL`Stdlib`Num`leqCaseEqLtThm]], sucOneLeqN];
      (* ⊢ SUC 0 = n ∨ SUC 0 < n *)

      (* --- Branch 1: SUC 0 = n. Use NIL. --- *)
      oneEqNCase = Module[{oneEqNHyp, allNilAtPrime, allNilTrue,
                           foldrNilAtNum, foldrNilEqN, conjBody, exAtNil},
        oneEqNHyp = ASSUME[mkEq[oneN[], nLocal]];

        allNilAtPrime = HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
          INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`allNilThm]];
        (* ⊢ ALL prime NIL = T *)
        allNilTrue = HOL`Bool`EQTELIM[allNilAtPrime];
        (* ⊢ ALL prime NIL *)

        foldrNilAtNum = HOL`Bool`SPEC[oneN[],
          HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
            INSTTYPE[{αTy -> numTy, βTy -> numTy},
              HOL`Stdlib`List`foldrNilThm]]];
        (* ⊢ FOLDR * (SUC 0) NIL = SUC 0 *)
        foldrNilEqN = TRANS[foldrNilAtNum, oneEqNHyp];
        (* (SUC 0 = n) ⊢ FOLDR * (SUC 0) NIL = n *)

        conjBody = HOL`Bool`CONJ[allNilTrue, foldrNilEqN];
        exAtNil = HOL`Bool`EXISTS[exConclTm, nilNumTm[], conjBody];
        exAtNil
      ];

      (* --- Branch 2: SUC 0 < n. Recurse via primeDivExistsThm. --- *)
      oneLtNCase = Module[{oneLtNHyp, primeDivAtN, pV, cV, primeAndDivBody,
                           primeAndDivHyp, primePThm, pDivN, pDivNUnf,
                           nEqPCBody, nEqPCHyp, cNotZ, primeUnfP, primePApplied,
                           oneLtPThm, cLtPC, cLtN, ihAtC, mpFromIH,
                           lBody, lHyp, allPrimeL, foldrLEqC, consPLTm,
                           allConsAtPL, conjAllPart, allPrimeCons,
                           foldrConsAtPL, replaceFoldr, replaceN, foldrConsEqN,
                           conjCons, exAtConsPL, chosenL, chosenC, chosenP},
        oneLtNHyp = ASSUME[ltN[oneN[], nLocal]];
        primeDivAtN = HOL`Bool`MP[
          HOL`Bool`SPEC[nLocal, primeDivExistsThm], oneLtNHyp];
        (* ⊢ ∃p. prime p ∧ p|n *)

        pV = mkVar["pF", numTy];
        cV = mkVar["cF", numTy];
        primeAndDivBody = andTm[primeN[pV], dividesN[pV, nLocal]];
        primeAndDivHyp = ASSUME[primeAndDivBody];
        primePThm = HOL`Bool`CONJUNCT1[primeAndDivHyp];
        pDivN = HOL`Bool`CONJUNCT2[primeAndDivHyp];

        pDivNUnf = EQMP[unfoldDivides[pV, nLocal], pDivN];
        (* (…) ⊢ ∃c. n = p * c *)
        nEqPCBody = mkEq[nLocal, timesN[pV, cV]];
        nEqPCHyp = ASSUME[nEqPCBody];

        cNotZ = Module[{cEq0Hyp, pTimes0, nEqPTimes0, nEq0, fThm},
          cEq0Hyp = ASSUME[mkEq[cV, zeroN[]]];
          pTimes0 = HOL`Bool`SPEC[pV, HOL`Stdlib`Num`timesZeroEqThm];
          nEqPTimes0 = TRANS[nEqPCHyp,
            HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], pV],
              cEq0Hyp]];
          nEq0 = TRANS[nEqPTimes0, pTimes0];
          fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[nNotZHyp], nEq0];
          HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[cV, zeroN[]], fThm]]
        ];
        (* (¬(n=0), n = p*c) ⊢ ¬(c = 0) *)

        primeUnfP = Module[{apP},
          apP = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, pV];
          TRANS[apP, BETACONV[concl[apP][[2]]]]
        ];
        (* ⊢ prime p = SUC 0 < p ∧ (∀d. divides d p ⇒ d = SUC 0 ∨ d = p) *)
        primePApplied = EQMP[primeUnfP, primePThm];
        oneLtPThm = HOL`Bool`CONJUNCT1[primePApplied];
        (* (…) ⊢ SUC 0 < p *)

        cLtPC = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[cV, HOL`Bool`SPEC[pV, ltMultIfOneLtThm]],
          oneLtPThm], cNotZ];
        (* (…) ⊢ c < p * c *)
        cLtN = HOL`Drule`SUBS[{HOL`Equal`SYM[nEqPCHyp]}, cLtPC];
        (* (…) ⊢ c < n *)

        ihAtC = HOL`Bool`SPEC[cV, ihHyp];
        (* ⊢ c < n ⇒ ¬(c = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = c *)
        mpFromIH = HOL`Bool`MP[HOL`Bool`MP[ihAtC, cLtN], cNotZ];
        (* (…) ⊢ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = c *)

        lBody = andTm[
          allTm[HOL`Stdlib`Num`primeConst[], lV],
          mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], cV]];
        lHyp = ASSUME[lBody];
        allPrimeL = HOL`Bool`CONJUNCT1[lHyp];
        foldrLEqC = HOL`Bool`CONJUNCT2[lHyp];

        consPLTm = consNumApp[pV, lV];

        allConsAtPL = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[pV,
          HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
            INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`allConsThm]]]];
        (* ⊢ ALL prime (CONS p l) = prime p ∧ ALL prime l *)
        conjAllPart = HOL`Bool`CONJ[primePThm, allPrimeL];
        allPrimeCons = EQMP[HOL`Equal`SYM[allConsAtPL], conjAllPart];
        (* (…) ⊢ ALL prime (CONS p l) *)

        foldrConsAtPL = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[pV,
          HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
            INSTTYPE[{αTy -> numTy, βTy -> numTy},
              HOL`Stdlib`List`foldrConsThm]]]]];
        (* ⊢ FOLDR * (SUC 0) (CONS p l) = p * (FOLDR * (SUC 0) l) *)
        replaceFoldr = HOL`Equal`APTERM[
          mkComb[HOL`Stdlib`Num`timesConst[], pV], foldrLEqC];
        (* (…) ⊢ p * (FOLDR * (SUC 0) l) = p * c *)
        replaceN = HOL`Equal`SYM[nEqPCHyp];
        (* (n = p*c) ⊢ p * c = n *)
        foldrConsEqN = TRANS[foldrConsAtPL, TRANS[replaceFoldr, replaceN]];
        (* (…) ⊢ FOLDR * (SUC 0) (CONS p l) = n *)

        conjCons = HOL`Bool`CONJ[allPrimeCons, foldrConsEqN];
        exAtConsPL = HOL`Bool`EXISTS[exConclTm, consPLTm, conjCons];
        (* (…) ⊢ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n *)

        chosenL = HOL`Bool`CHOOSE[lV, mpFromIH, exAtConsPL];
        chosenC = HOL`Bool`CHOOSE[cV, pDivNUnf, chosenL];
        chosenP = HOL`Bool`CHOOSE[pV, primeDivAtN, chosenC];
        chosenP
      ];

      finalCase = HOL`Bool`DISJCASES[caseEq, oneEqNCase, oneLtNCase];

      dischNotZ = HOL`Bool`DISCH[notTm[mkEq[nLocal, zeroN[]]], finalCase];
      dischIH = HOL`Bool`DISCH[ihHypT, dischNotZ];
      gen = HOL`Bool`GEN[nLocal, dischIH];
      gen
    ];

    mainConcl = HOL`Bool`MP[specBeta, stepAnte];
    mainConcl
  ];

(* ============================================================ *)
(* notLeqSucSelfThm  (stage-3.a helper)                          *)
(*   ⊢ ∀n. ¬ (SUC n ≤ n).                                        *)
(*                                                              *)
(* Assume SUC n ≤ n; combine with leqSucThm (n ≤ SUC n) via      *)
(* leqAntisymThm to get SUC n = n, contradicting sucNotEqSelfThm.*)
(* ============================================================ *)

notLeqSucSelfThm =
  Module[{nV, sucLeqHyp, nLeqSuc, antisym, sucEqN, notEq, fThm,
          notIntro, gen},
    nV = mkVar["nSL", numTy];
    sucLeqHyp = ASSUME[leqN[sucN[nV], nV]];
    nLeqSuc = HOL`Bool`SPEC[nV, HOL`Stdlib`Num`leqSucThm];
    (* ⊢ n ≤ SUC n *)
    antisym = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[nV, HOL`Bool`SPEC[sucN[nV],
        HOL`Stdlib`Num`leqAntisymThm]],
      sucLeqHyp], nLeqSuc];
    (* (SUC n ≤ n) ⊢ SUC n = n *)
    notEq = HOL`Bool`SPEC[nV, HOL`Stdlib`Num`sucNotEqSelfThm];
    (* ⊢ ¬(SUC n = n) *)
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notEq], antisym];
    (* (SUC n ≤ n) ⊢ F *)
    notIntro = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[leqN[sucN[nV], nV], fThm]];
    gen = HOL`Bool`GEN[nV, notIntro];
    gen
  ];

(* ============================================================ *)
(* primeNotDivOneThm  (stage-3.a helper)                         *)
(*   ⊢ ∀p. prime p ⇒ ¬ (divides p (SUC 0)).                      *)
(*                                                              *)
(* From prime p extract SUC 0 < p (primeDef CONJUNCT1).          *)
(* Unfold < to get SUC (SUC 0) ≤ p.                              *)
(* Assume divides p (SUC 0); dividesLeqThm with SUC 0 ≠ 0 gives  *)
(*   p ≤ SUC 0.                                                  *)
(* Combine SUC (SUC 0) ≤ p and p ≤ SUC 0 via leqTrans:            *)
(*   SUC (SUC 0) ≤ SUC 0, contradicting notLeqSucSelfThm.        *)
(* ============================================================ *)

primeNotDivOneThm =
  Module[{pV, primeHyp, primeUnf, primeUnfApplied, oneLtP, ltUnfP,
          dividesHyp, oneNotZero, pLeqOne, sucOneLeqOne, fThm,
          notIntro, dischPrime, gen, oneTm, sucOneTm},
    pV = mkVar["pND", numTy];
    oneTm = oneN[];
    sucOneTm = sucN[oneTm];

    primeHyp = ASSUME[primeN[pV]];
    primeUnf = Module[{apP},
      apP = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, pV];
      TRANS[apP, BETACONV[concl[apP][[2]]]]
    ];
    (* ⊢ prime p = SUC 0 < p ∧ (∀d. divides d p ⇒ d = SUC 0 ∨ d = p) *)
    primeUnfApplied = EQMP[primeUnf, primeHyp];
    oneLtP = HOL`Bool`CONJUNCT1[primeUnfApplied];
    (* (prime p) ⊢ SUC 0 < p *)
    ltUnfP = EQMP[unfoldLt[oneTm, pV], oneLtP];
    (* (prime p) ⊢ SUC (SUC 0) ≤ p *)

    dividesHyp = ASSUME[dividesN[pV, oneTm]];
    (* (divides p 1) ⊢ … *)

    oneNotZero = Module[{eqHyp, fT, suc0NeqZ},
      eqHyp = ASSUME[mkEq[oneTm, zeroN[]]];
      suc0NeqZ = HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`sucNotZeroThm];
      (* ⊢ ¬(SUC 0 = 0) *)
      fT = HOL`Bool`MP[HOL`Bool`NOTELIM[suc0NeqZ], eqHyp];
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[oneTm, zeroN[]], fT]]
    ];
    (* ⊢ ¬(SUC 0 = 0) *)

    pLeqOne = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[oneTm, HOL`Bool`SPEC[pV,
        HOL`Stdlib`Num`dividesLeqThm]],
      oneNotZero], dividesHyp];
    (* (divides p 1) ⊢ p ≤ SUC 0 *)

    sucOneLeqOne = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[oneTm, HOL`Bool`SPEC[pV,
        HOL`Bool`SPEC[sucOneTm, HOL`Stdlib`Num`leqTransThm]]],
      ltUnfP], pLeqOne];
    (* (prime p, divides p 1) ⊢ SUC (SUC 0) ≤ SUC 0 *)

    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[
      HOL`Bool`SPEC[oneTm, notLeqSucSelfThm]],
      sucOneLeqOne];
    (* (prime p, divides p 1) ⊢ F *)

    notIntro = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[
      dividesN[pV, oneTm], fThm]];
    (* (prime p) ⊢ ¬(divides p (SUC 0)) *)
    dischPrime = HOL`Bool`DISCH[primeN[pV], notIntro];
    gen = HOL`Bool`GEN[pV, dischPrime];
    gen
  ];

(* ============================================================ *)
(* primeDivFoldrTimesThm  (FTA stage 3.a)                        *)
(*   ⊢ ∀p l. prime p ⇒ divides p (FOLDR * (SUC 0) l)             *)
(*           ⇒ ∃y. MEM y l ∧ divides p y.                         *)
(*                                                              *)
(* For fixed prime p, list-induct on l.                          *)
(*   NIL: FOLDR * (SUC 0) NIL = SUC 0; divides p (SUC 0)         *)
(*         contradicts primeNotDivOneThm.                        *)
(*   CONS y l': FOLDR * (SUC 0) (CONS y l')                      *)
(*               = y * FOLDR * (SUC 0) l' (foldrConsThm).        *)
(*     euclidLemmaThm: p | y ∨ p | (FOLDR * (SUC 0) l').          *)
(*     - p|y branch: take MEM y (CONS y l') (head).               *)
(*     - p|FOLDR branch: IH gives ∃y'. MEM y' l' ∧ p|y';          *)
(*       MEM y' (CONS y l') via tail of memCons.                  *)
(* ============================================================ *)

primeDivFoldrTimesThm =
  Module[{αTy, βTy, pV, lV, yV, bndV, primeHyp, predLam, inductSpec,
          inductBeta, baseCase, indStep, conjForall, finalGen,
          dischPrime, gen, foldrAt, memAt, exConcl},
    αTy = mkVarType["A"]; βTy = mkVarType["B"];
    pV = mkVar["pE", numTy];
    lV = mkVar["lE", numListTy[]];
    yV = mkVar["yE", numTy];
    (* bndV is the fresh ∃-binder used in exConcl — distinct from the
       per-case witnesses yLocal / ypV so listTm can mention either freely. *)
    bndV = mkVar["yBnd", numTy];

    primeHyp = ASSUME[primeN[pV]];

    (* The MEM and FOLDR terms specialized to num. *)
    memAt[xTm_, listTm_] := mkComb[mkComb[
      mkConst["MEM", tyFun[numTy, tyFun[numListTy[], boolTy]]],
      xTm], listTm];

    foldrAt[listTm_] := foldrTm[
      HOL`Stdlib`Num`timesConst[], oneN[], listTm];

    (* exConcl[listTm] = ∃bndV. MEM bndV listTm ∧ divides p bndV *)
    exConcl[listTm_] := mkComb[
      mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[bndV, andTm[memAt[bndV, listTm], dividesN[pV, bndV]]]];

    (* P l ≡ divides p (FOLDR * (SUC 0) l) ⇒ ∃y. MEM y l ∧ divides p y *)
    predLam = mkAbs[lV,
      impTm[dividesN[pV, foldrAt[lV]], exConcl[lV]]];

    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];
    (* ⊢ (divides p (FOLDR * 1 NIL) ⇒ ∃y. MEM y NIL ∧ divides p y)
       ∧ (∀x l. (divides p (FOLDR * 1 l) ⇒ ∃y. MEM y l ∧ divides p y)
              ⇒ (divides p (FOLDR * 1 (CONS x l))
                   ⇒ ∃y. MEM y (CONS x l) ∧ divides p y))
       ⇒ ∀l. divides p (FOLDR * 1 l) ⇒ ∃y. MEM y l ∧ divides p y *)

    (* NIL case: divides p 1 contradicts primeNotDivOneThm. *)
    baseCase = Module[{foldrNilAtNum, divPFoldrHyp, divP1, notDivP1,
                       fThm, dischDiv},
      foldrNilAtNum = HOL`Bool`SPEC[oneN[],
        HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
          INSTTYPE[{αTy -> numTy, βTy -> numTy},
            HOL`Stdlib`List`foldrNilThm]]];
      (* ⊢ FOLDR * (SUC 0) NIL = SUC 0 *)
      divPFoldrHyp = ASSUME[dividesN[pV, foldrAt[nilNumTm[]]]];
      divP1 = HOL`Drule`SUBS[{foldrNilAtNum}, divPFoldrHyp];
      (* (divides p (FOLDR * 1 NIL)) ⊢ divides p (SUC 0) *)
      notDivP1 = HOL`Bool`MP[
        HOL`Bool`SPEC[pV, primeNotDivOneThm], primeHyp];
      (* (prime p) ⊢ ¬(divides p (SUC 0)) *)
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notDivP1], divP1];
      (* (prime p, divides p (FOLDR * 1 NIL)) ⊢ F *)
      dischDiv = HOL`Bool`DISCH[dividesN[pV, foldrAt[nilNumTm[]]],
        HOL`Bool`CONTR[exConcl[nilNumTm[]], fThm]];
      dischDiv
    ];

    (* CONS case: ∀y l. (IH) ⇒ (divides p (FOLDR * 1 (CONS y l))
                                ⇒ ∃z. MEM z (CONS y l) ∧ divides p z). *)
    indStep = Module[{yLocal, lLocal, ihHypT, ihHyp, foldrConsAt, divHyp,
                      divPYTimesFold, euclidAt, splitDisj,
                      headBranch, tailBranch, exFromBranches,
                      dischDiv, stepInner, allLOuter},
      yLocal = yV;
      lLocal = lV;

      ihHypT = impTm[dividesN[pV, foldrAt[lLocal]], exConcl[lLocal]];
      ihHyp = ASSUME[ihHypT];

      foldrConsAt = HOL`Bool`SPEC[lLocal, HOL`Bool`SPEC[yLocal,
        HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
          INSTTYPE[{αTy -> numTy, βTy -> numTy},
            HOL`Stdlib`List`foldrConsThm]]]]];
      (* ⊢ FOLDR * (SUC 0) (CONS y l)
           = y * FOLDR * (SUC 0) l *)

      divHyp = ASSUME[dividesN[pV, foldrAt[consNumApp[yLocal, lLocal]]]];
      divPYTimesFold = HOL`Drule`SUBS[{foldrConsAt}, divHyp];
      (* (…) ⊢ divides p (y * FOLDR * (SUC 0) l) *)

      euclidAt = HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[foldrAt[lLocal],
          HOL`Bool`SPEC[yLocal, HOL`Bool`SPEC[pV,
            HOL`Stdlib`Num`euclidLemmaThm]]],
        primeHyp], divPYTimesFold];
      (* (prime p, …) ⊢ divides p y ∨ divides p (FOLDR * 1 l) *)

      headBranch = Module[{divPYHyp, memConsAtY, eqYY, headDisj,
                           memYConsRaw, memYCons, conjY, exAtY},
        divPYHyp = ASSUME[dividesN[pV, yLocal]];

        memConsAtY = HOL`Bool`SPEC[lLocal, HOL`Bool`SPEC[yLocal,
          HOL`Bool`SPEC[yLocal,
            INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`memConsThm]]]];
        (* ⊢ MEM y (CONS y l) = (y = y ∨ MEM y l) *)
        eqYY = REFL[yLocal];
        (* ⊢ y = y *)
        headDisj = HOL`Bool`DISJ1[eqYY,
          mkComb[mkComb[
            mkConst["MEM", tyFun[numTy, tyFun[numListTy[], boolTy]]],
            yLocal], lLocal]];
        (* ⊢ y = y ∨ MEM y l *)
        memYCons = EQMP[HOL`Equal`SYM[memConsAtY], headDisj];
        (* ⊢ MEM y (CONS y l) *)
        conjY = HOL`Bool`CONJ[memYCons, divPYHyp];
        exAtY = HOL`Bool`EXISTS[exConcl[consNumApp[yLocal, lLocal]],
          yLocal, conjY];
        exAtY
      ];

      tailBranch = Module[{divPFoldHyp, ihApplied, ypV, conjYpBody,
                           conjYpHyp, memYpL, divPYp, memConsAtYp, tailDisj,
                           memYpCons, conjYpFinal, exAtYp, chosenYp},
        divPFoldHyp = ASSUME[dividesN[pV, foldrAt[lLocal]]];
        ihApplied = HOL`Bool`MP[ihHyp, divPFoldHyp];
        (* (IH, divides p (FOLDR * 1 l)) ⊢ ∃y. MEM y l ∧ divides p y *)

        ypV = mkVar["ypE", numTy];
        conjYpBody = andTm[memAt[ypV, lLocal], dividesN[pV, ypV]];
        conjYpHyp = ASSUME[conjYpBody];
        memYpL = HOL`Bool`CONJUNCT1[conjYpHyp];
        divPYp = HOL`Bool`CONJUNCT2[conjYpHyp];

        memConsAtYp = HOL`Bool`SPEC[lLocal, HOL`Bool`SPEC[yLocal,
          HOL`Bool`SPEC[ypV,
            INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`memConsThm]]]];
        (* ⊢ MEM y' (CONS y l) = (y' = y ∨ MEM y' l) *)
        tailDisj = HOL`Bool`DISJ2[memYpL, mkEq[ypV, yLocal]];
        (* ⊢ y' = y ∨ MEM y' l *)
        memYpCons = EQMP[HOL`Equal`SYM[memConsAtYp], tailDisj];
        (* (MEM y' l) ⊢ MEM y' (CONS y l) *)
        conjYpFinal = HOL`Bool`CONJ[memYpCons, divPYp];
        exAtYp = HOL`Bool`EXISTS[exConcl[consNumApp[yLocal, lLocal]],
          ypV, conjYpFinal];
        chosenYp = HOL`Bool`CHOOSE[ypV, ihApplied, exAtYp];
        chosenYp
      ];

      exFromBranches = HOL`Bool`DISJCASES[euclidAt, headBranch, tailBranch];
      (* (prime p, IH, divides p (FOLDR * 1 (CONS y l))) ⊢ ∃z. MEM z (CONS y l) ∧ divides p z *)

      dischDiv = HOL`Bool`DISCH[
        dividesN[pV, foldrAt[consNumApp[yLocal, lLocal]]],
        exFromBranches];
      stepInner = HOL`Bool`DISCH[ihHypT, dischDiv];
      allLOuter = HOL`Bool`GEN[yLocal, HOL`Bool`GEN[lLocal, stepInner]];
      allLOuter
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalGen = HOL`Bool`MP[inductBeta, conjForall];
    (* (prime p) ⊢ ∀l. divides p (FOLDR * 1 l) ⇒ ∃y. MEM y l ∧ divides p y *)

    dischPrime = HOL`Bool`DISCH[primeN[pV], finalGen];
    gen = HOL`Bool`GEN[pV, dischPrime];
    gen
  ];

End[];
EndPackage[];
