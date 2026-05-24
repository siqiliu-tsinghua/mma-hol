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
primeOrCompositeThm::usage = "primeOrCompositeThm — ⊢ ∀n. SUC 0 < n ⇒ prime n ∨ (∃d. SUC 0 < d ∧ d < n ∧ divides d n). Dichotomy: every n > 1 is prime or has a proper divisor.";
primeDivExistsThm::usage = "primeDivExistsThm — ⊢ ∀n. SUC 0 < n ⇒ ∃p. prime p ∧ divides p n. Every n > 1 has a prime divisor (FTA stage-1 capstone).";

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

End[];
EndPackage[];
