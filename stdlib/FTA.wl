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
  "HOL`Stdlib`Num`"
}];

dividesPosThm::usage = "dividesPosThm — ⊢ ∀d n. ¬ (n = 0) ⇒ divides d n ⇒ ¬ (d = 0). If n is non-zero and d divides n, then d is non-zero.";
dividesTransThm::usage = "dividesTransThm — ⊢ ∀a b c. divides a b ⇒ divides b c ⇒ divides a c. Transitivity of divisibility.";
notOneNorZeroLtThm::usage = "notOneNorZeroLtThm — ⊢ ∀d. ¬ (d = 0) ⇒ ¬ (d = SUC 0) ⇒ SUC 0 < d. A num that is neither 0 nor 1 must be > 1.";

Begin["`Private`"];

numTy = mkType["num", {}];

zeroN[] := mkConst["0", numTy];
oneN[]  := mkComb[HOL`Stdlib`Num`sucConst[], zeroN[]];
timesN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`timesConst[], m], n];
ltN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], m], n];
dividesN[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], a], b];
notTm[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];

(* ⊢ divides a b = ∃c. b = a * c *)
unfoldDivides[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`dividesDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
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

End[];
EndPackage[];
