(* M7-8 / stdlib/Real/Seq.wl - real sequences and epsilon-N limits. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

tendstoDefThm::usage = "tendstoDefThm - |- tendsto = (lambda a L. forall e. 0 < e ==> exists N. forall n. N <= n ==> realAbs (a n + realNeg L) < e).";
tendstoConst::usage = "tendstoConst[] - tendsto : (num -> real) -> real -> bool.";
tendstoTm::usage = "tendstoTm[a, L] - builds tendsto a L.";
unfoldTendsto::usage = "unfoldTendsto[a, L] - proves the beta-reduced tendsto definition at a and L.";

convergentDefThm::usage = "convergentDefThm - |- convergent = (lambda a. exists L. tendsto a L).";
convergentConst::usage = "convergentConst[] - convergent : (num -> real) -> bool.";
convergentTm::usage = "convergentTm[a] - builds convergent a.";

tendstoConstThm::usage = "tendstoConstThm - |- forall c. tendsto (lambda n. c) c.";
realNeAbsPosThm::usage = "realNeAbsPosThm - |- forall x. ~(x = 0) ==> 0 < realAbs x.";
tendstoUniqueThm::usage = "tendstoUniqueThm - |- forall a L1 L2. tendsto a L1 ==> tendsto a L2 ==> L1 = L2.";
tendstoAddThm::usage = "tendstoAddThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. a n + b n) (A + B).";
tendstoNegThm::usage = "tendstoNegThm - |- forall a A. tendsto a A ==> tendsto (lambda n. realNeg (a n)) (realNeg A).";
tendstoSubThm::usage = "tendstoSubThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. a n + realNeg (b n)) (A + realNeg B).";
tendstoConvergentThm::usage = "tendstoConvergentThm - |- forall a L. tendsto a L ==> convergent a.";

Begin["`Private`"];

seqTy = tyFun[numTy, realTy];
tendstoTy = tyFun[seqTy, tyFun[realTy, boolTy]];
convergentTy = tyFun[seqTy, boolTy];

seqNatAdd[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], aT], bT];
seqNatLe[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], aT], bT];
seqRealAbs[xT_] := mkComb[realAbsConst[], xT];
seqRealInv[xT_] := mkComb[realInvConst[], xT];

seqTwoNat[] := sucT[sucT[zeroN[]]];
seqTwoReal[] := realOfRatTm[ratOfIntTm[intOfNumTm[seqTwoNat[]]]];
seqHalf[eT_] := realMulTm[eT, seqRealInv[seqTwoReal[]]];

seqSpecAll[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

seqForallList[vs_List, body_] :=
  Fold[Function[{acc, v}, forallTm[v, acc]], body, Reverse[vs]];

seqImpList[hs_List, body_] :=
  Fold[Function[{acc, h}, impTm[h, acc]], body, Reverse[hs]];

seqRealLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqLeft], eqRight];

seqRealLtCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], eqLeft], eqRight];

seqNatLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Num`leqConst[], eqLeft], eqRight];

seqRealAddCongLeft[eq_, cT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], eq], REFL[cT]];

seqRealAddCongRight[cT_, eq_] :=
  HOL`Equal`APTERM[mkComb[realAddConst[], cT], eq];

seqRealAbsCong[eq_] := HOL`Equal`APTERM[realAbsConst[], eq];

seqLimitAtom[aT_, lT_, eT_, nT_] :=
  realLtTm[seqRealAbs[realAddTm[mkComb[aT, nT], realNegTm[lT]]], eT];

seqLimitAll[aT_, lT_, eT_, n0T_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    forallTm[nV, impTm[seqNatLe[n0T, nV], seqLimitAtom[aT, lT, eT, nV]]]
  ];

seqTendstoBody[aT_, lT_] :=
  Module[{eV, nV},
    eV = mkVar["e", realTy];
    nV = mkVar["N", numTy];
    forallTm[eV, impTm[realLtTm[zeroRealTm[], eV],
      existsTm[nV, seqLimitAll[aT, lT, eV, nV]]]]
  ];

tendstoDefThm =
  Module[{aV, lV, body},
    aV = mkVar["a", seqTy];
    lV = mkVar["L", realTy];
    body = mkAbs[aV, mkAbs[lV, seqTendstoBody[aV, lV]]];
    newDefinition[mkEq[mkVar["tendsto", tendstoTy], body]]
  ];

tendstoConst[] := mkConst["tendsto", tendstoTy];
tendstoTm[aT_, lT_] := mkComb[mkComb[tendstoConst[], aT], lT];

unfoldTendsto[aT_, lT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[tendstoDefThm, aT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, lT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

convergentDefThm =
  Module[{aV, lV, body},
    aV = mkVar["a", seqTy];
    lV = mkVar["L", realTy];
    body = mkAbs[aV, existsTm[lV, tendstoTm[aV, lV]]];
    newDefinition[mkEq[mkVar["convergent", convergentTy], body]]
  ];

convergentConst[] := mkConst["convergent", convergentTy];
convergentTm[aT_] := mkComb[convergentConst[], aT];

seqUnfoldConvergent[aT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[convergentDefThm, aT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqArithHalfPosThm =
  Module[{eV},
    eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[eV, impTm[realLtTm[zeroRealTm[], eV],
        realLtTm[zeroRealTm[], seqHalf[eV]]]]]
  ];

seqArithZeroDiffThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV},
        impTm[mkEq[realAddTm[xV, realNegTm[yV]], zeroRealTm[]], mkEq[xV, yV]]]]
  ];

seqArithDiffChainThm =
  Module[{xV, yV, zV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV, zV},
        mkEq[realAddTm[realAddTm[xV, realNegTm[yV]], realAddTm[yV, realNegTm[zV]]],
          realAddTm[xV, realNegTm[zV]]]]]
  ];

seqArithAddDiffThm =
  Module[{xV, yV, uV, vV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    uV = mkVar["u", realTy]; vV = mkVar["v", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV, uV, vV},
        mkEq[realAddTm[realAddTm[xV, yV], realNegTm[realAddTm[uV, vV]]],
          realAddTm[realAddTm[xV, realNegTm[uV]], realAddTm[yV, realNegTm[vV]]]]]]
  ];

seqArithNegDiffThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV},
        mkEq[realAddTm[realNegTm[xV], realNegTm[realNegTm[yV]]],
          realNegTm[realAddTm[xV, realNegTm[yV]]]]]]
  ];

seqArithTriangleLtThm =
  Module[{uV, vV, wV, eV},
    uV = mkVar["u", realTy]; vV = mkVar["v", realTy];
    wV = mkVar["w", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{uV, vV, wV, eV},
        seqImpList[{realLeTm[uV, realAddTm[vV, wV]],
          realLtTm[vV, seqHalf[eV]], realLtTm[wV, seqHalf[eV]]},
          realLtTm[uV, eV]]]]
  ];

seqArithUniqueContrThm =
  Module[{vV, wV, eV},
    vV = mkVar["v", realTy]; wV = mkVar["w", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{vV, wV, eV},
        seqImpList[{realLeTm[eV, realAddTm[vV, wV]],
          realLtTm[vV, seqHalf[eV]], realLtTm[wV, seqHalf[eV]]},
          realLtTm[eV, eV]]]]
  ];

seqUnfoldLeq[aT_, bT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, aT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, bT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

seqLeqAddSelf[mT_, kT_] :=
  Module[{jV, exTm, exThm},
    jV = mkVar["kLAS", numTy];
    exTm = existsTm[jV, mkEq[seqNatAdd[mT, jV], seqNatAdd[mT, kT]]];
    exThm = HOL`Bool`EXISTS[exTm, kT, REFL[seqNatAdd[mT, kT]]];
    EQMP[HOL`Equal`SYM[seqUnfoldLeq[mT, seqNatAdd[mT, kT]]], exThm]
  ];

seqLeqToSumLeft[mT_, kT_] := seqLeqAddSelf[mT, kT];

seqLeqToSumRight[mT_, kT_] :=
  Module[{raw, comm},
    raw = seqLeqAddSelf[kT, mT];
    comm = HOL`Bool`SPEC[mT, HOL`Bool`SPEC[kT, HOL`Stdlib`Num`addCommThm]];
    EQMP[seqNatLeCong[REFL[kT], comm], raw]
  ];

seqLeqTrans[abTh_, bcTh_] :=
  Module[{aT, bT, cT},
    aT = concl[abTh][[1, 2]]; bT = concl[abTh][[2]]; cT = concl[bcTh][[2]];
    HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[HOL`Stdlib`Num`leqTransThm, {aT, bT, cT}], abTh], bcTh]
  ];

tendstoConstThm =
  Module[{cV, nV, eV, constSeq, hE, appEq, sumEq, sumZero, absEq, ltGoal,
          impN, allN, exN, body, folded},
    cV = mkVar["c", realTy]; nV = mkVar["n", numTy]; eV = mkVar["e", realTy];
    constSeq = mkAbs[nV, cV];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    appEq = HOL`Equal`BETACONV[mkComb[constSeq, nV]];
    sumEq = seqRealAddCongLeft[appEq, realNegTm[cV]];
    sumZero = TRANS[sumEq, HOL`Bool`SPEC[cV, realAddNegThm]];
    absEq = TRANS[seqRealAbsCong[sumZero], realAbsZeroThm];
    ltGoal = EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], hE];
    impN = HOL`Bool`DISCH[seqNatLe[zeroN[], nV], ltGoal];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[constSeq, cV, eV, mkVar["N", numTy]]],
      zeroN[], allN];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], exN]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[constSeq, cV]], body];
    HOL`Bool`GEN[cV, folded]
  ];

realNeAbsPosThm =
  Module[{xV, hNe, hPos, hNeg, absPos, hNotLt, ltNotLe, notNotLe, dd, xLe0,
          xEq0, ff, lt0x, posBranch, absNeg, notLeLt, xLt0, negPos,
          negBranch, body},
    xV = mkVar["x", realTy];
    hNe = ASSUME[notTm[mkEq[xV, zeroRealTm[]]]];
    hPos = ASSUME[realLeTm[zeroRealTm[], xV]];
    absPos = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
    hNotLt = ASSUME[notTm[realLtTm[zeroRealTm[], xV]]];
    ltNotLe = HOL`Bool`SPEC[xV, HOL`Bool`SPEC[zeroRealTm[], realLtNotLeThm]];
    notNotLe = EQMP[HOL`Equal`APTERM[notC[], ltNotLe], hNotLt];
    dd = HOL`Auto`PropTaut`propTaut[
      impTm[notTm[notTm[realLeTm[xV, zeroRealTm[]]]], realLeTm[xV, zeroRealTm[]]]];
    xLe0 = HOL`Bool`MP[dd, notNotLe];
    xEq0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[zeroRealTm[], HOL`Bool`SPEC[xV, realLeAntisymThm]], xLe0], hPos];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[hNe], xEq0];
    lt0x = HOL`Bool`CCONTR[realLtTm[zeroRealTm[], xV], ff];
    posBranch = EQMP[seqRealLtCong[REFL[zeroRealTm[]], HOL`Equal`SYM[absPos]], lt0x];

    hNeg = ASSUME[notTm[realLeTm[zeroRealTm[], xV]]];
    absNeg = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg];
    notLeLt = HOL`Bool`SPEC[xV, HOL`Bool`SPEC[zeroRealTm[], HOL`Auto`RealArith`realNotLeLtThm]];
    xLt0 = EQMP[notLeLt, hNeg];
    negPos = HOL`Bool`MP[HOL`Bool`SPEC[xV, realNegPosThm], xLt0];
    negBranch = EQMP[seqRealLtCong[REFL[zeroRealTm[]], HOL`Equal`SYM[absNeg]], negPos];

    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], xV]],
      posBranch, negBranch];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[notTm[mkEq[xV, zeroRealTm[]]], body]]
  ];

tendstoUniqueThm =
  Module[{aV, l1V, l2V, h1, h2, hNe, diff, e0, half, hDiff0, diffImpEq,
          eqL1L2, ffDiff, notDiff0, ePos, halfPos, u1, u2, ex1, ex2, nW1,
          nW2, all1Tm, all2Tm, hAll1, hAll2, nSum, le1, le2, d1, d2, an,
          vAbs, wAbs, xTerm, yTerm, tri, chainEq, triLeftEq, negNegL1,
          leftComm, leftNegNeg, negEq, xNegEq, absXEq, rhsEq, triLe, eLtE,
          notELtE, ff, chosen2, chosen1, eqTh},
    aV = mkVar["a", seqTy]; l1V = mkVar["L1", realTy]; l2V = mkVar["L2", realTy];
    h1 = ASSUME[tendstoTm[aV, l1V]]; h2 = ASSUME[tendstoTm[aV, l2V]];
    hNe = ASSUME[notTm[mkEq[l1V, l2V]]];
    diff = realAddTm[l1V, realNegTm[l2V]];
    e0 = seqRealAbs[diff]; half = seqHalf[e0];

    hDiff0 = ASSUME[mkEq[diff, zeroRealTm[]]];
    diffImpEq = seqSpecAll[seqArithZeroDiffThm, {l1V, l2V}];
    eqL1L2 = HOL`Bool`MP[diffImpEq, hDiff0];
    ffDiff = HOL`Bool`MP[HOL`Bool`NOTELIM[hNe], eqL1L2];
    notDiff0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[diff, zeroRealTm[]], ffDiff]];
    ePos = HOL`Bool`MP[HOL`Bool`SPEC[diff, realNeAbsPosThm], notDiff0];
    halfPos = HOL`Bool`MP[HOL`Bool`SPEC[e0, seqArithHalfPosThm], ePos];
    u1 = EQMP[unfoldTendsto[aV, l1V], h1];
    u2 = EQMP[unfoldTendsto[aV, l2V], h2];
    ex1 = HOL`Bool`MP[HOL`Bool`SPEC[half, u1], halfPos];
    ex2 = HOL`Bool`MP[HOL`Bool`SPEC[half, u2], halfPos];

    nW1 = mkVar["nW1", numTy]; nW2 = mkVar["nW2", numTy];
    all1Tm = seqLimitAll[aV, l1V, half, nW1];
    all2Tm = seqLimitAll[aV, l2V, half, nW2];
    hAll1 = ASSUME[all1Tm]; hAll2 = ASSUME[all2Tm];
    nSum = seqNatAdd[nW1, nW2];
    le1 = seqLeqToSumLeft[nW1, nW2];
    le2 = seqLeqToSumRight[nW1, nW2];
    d1 = HOL`Bool`MP[HOL`Bool`SPEC[nSum, hAll1], le1];
    d2 = HOL`Bool`MP[HOL`Bool`SPEC[nSum, hAll2], le2];
    an = mkComb[aV, nSum];
    vAbs = seqRealAbs[realAddTm[an, realNegTm[l1V]]];
    wAbs = seqRealAbs[realAddTm[an, realNegTm[l2V]]];
    xTerm = realAddTm[l1V, realNegTm[an]];
    yTerm = realAddTm[an, realNegTm[l2V]];
    tri = seqSpecAll[realAbsTriangleThm, {xTerm, yTerm}];
    chainEq = seqSpecAll[seqArithDiffChainThm, {l1V, an, l2V}];
    triLeftEq = seqRealAbsCong[chainEq];
    leftComm = HOL`Bool`SPEC[realNegTm[an], HOL`Bool`SPEC[l1V, realAddCommThm]];
    negNegL1 = HOL`Bool`SPEC[l1V, realNegNegThm];
    leftNegNeg = seqRealAddCongRight[realNegTm[an], negNegL1];
    negEq = seqSpecAll[seqArithNegDiffThm, {an, l1V}];
    xNegEq = TRANS[leftComm, TRANS[HOL`Equal`SYM[leftNegNeg], negEq]];
    absXEq = TRANS[seqRealAbsCong[xNegEq],
      HOL`Bool`SPEC[realAddTm[an, realNegTm[l1V]], realAbsNegThm]];
    rhsEq = seqRealAddCongLeft[absXEq, wAbs];
    triLe = EQMP[seqRealLeCong[triLeftEq, rhsEq], tri];
    eLtE = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithUniqueContrThm, {vAbs, wAbs, e0}], triLe], d1], d2];
    notELtE = HOL`Bool`SPEC[e0, HOL`Auto`RealArith`realLtIrreflThm];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notELtE], eLtE];
    chosen2 = HOL`Bool`CHOOSE[nW2, ex2, ff];
    chosen1 = HOL`Bool`CHOOSE[nW1, ex1, chosen2];
    eqTh = HOL`Bool`CCONTR[mkEq[l1V, l2V], chosen1];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[l1V, HOL`Bool`GEN[l2V,
      HOL`Bool`DISCH[tendstoTm[aV, l1V], HOL`Bool`DISCH[tendstoTm[aV, l2V], eqTh]]]]]
  ];

tendstoAddThm =
  Module[{aV, bV, avV, bvV, eV, nV, hA, hB, hE, half, halfPos, uA, uB, exA,
          exB, nW1, nW2, allATm, allBTm, hAllA, hAllB, nSum, hN, leA0, leB0,
          leA, leB, dA, dB, an, bn, seqAdd, limit, appEq, betaEq, arithEq,
          argEq, absEq, xTerm, yTerm, vAbs, wAbs, tri, triOld, ltGoal, impN,
          allN, exN, body, folded, chosenB, chosenA},
    aV = mkVar["a", seqTy]; bV = mkVar["b", seqTy];
    avV = mkVar["A", realTy]; bvV = mkVar["B", realTy];
    eV = mkVar["e", realTy]; nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]]; hB = ASSUME[tendstoTm[bV, bvV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    half = seqHalf[eV];
    halfPos = HOL`Bool`MP[HOL`Bool`SPEC[eV, seqArithHalfPosThm], hE];
    uA = EQMP[unfoldTendsto[aV, avV], hA];
    uB = EQMP[unfoldTendsto[bV, bvV], hB];
    exA = HOL`Bool`MP[HOL`Bool`SPEC[half, uA], halfPos];
    exB = HOL`Bool`MP[HOL`Bool`SPEC[half, uB], halfPos];
    nW1 = mkVar["nW1", numTy]; nW2 = mkVar["nW2", numTy];
    allATm = seqLimitAll[aV, avV, half, nW1];
    allBTm = seqLimitAll[bV, bvV, half, nW2];
    hAllA = ASSUME[allATm]; hAllB = ASSUME[allBTm];
    nSum = seqNatAdd[nW1, nW2];
    hN = ASSUME[seqNatLe[nSum, nV]];
    leA0 = seqLeqToSumLeft[nW1, nW2];
    leB0 = seqLeqToSumRight[nW1, nW2];
    leA = seqLeqTrans[leA0, hN];
    leB = seqLeqTrans[leB0, hN];
    dA = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllA], leA];
    dB = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllB], leB];
    an = mkComb[aV, nV]; bn = mkComb[bV, nV];
    seqAdd = mkAbs[nV, realAddTm[mkComb[aV, nV], mkComb[bV, nV]]];
    limit = realAddTm[avV, bvV];
    appEq = HOL`Equal`BETACONV[mkComb[seqAdd, nV]];
    betaEq = seqRealAddCongLeft[appEq, realNegTm[limit]];
    arithEq = seqSpecAll[seqArithAddDiffThm, {an, bn, avV, bvV}];
    argEq = TRANS[betaEq, arithEq];
    absEq = seqRealAbsCong[argEq];
    xTerm = realAddTm[an, realNegTm[avV]];
    yTerm = realAddTm[bn, realNegTm[bvV]];
    vAbs = seqRealAbs[xTerm]; wAbs = seqRealAbs[yTerm];
    tri = seqSpecAll[realAbsTriangleThm, {xTerm, yTerm}];
    triOld = EQMP[seqRealLeCong[HOL`Equal`SYM[absEq], REFL[realAddTm[vAbs, wAbs]]], tri];
    ltGoal = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithTriangleLtThm,
        {seqRealAbs[realAddTm[mkComb[seqAdd, nV], realNegTm[limit]]], vAbs, wAbs, eV}],
      triOld], dA], dB];
    impN = HOL`Bool`DISCH[seqNatLe[nSum, nV], ltGoal];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[seqAdd, limit, eV, mkVar["N", numTy]]],
      nSum, allN];
    chosenB = HOL`Bool`CHOOSE[nW2, exB, exN];
    chosenA = HOL`Bool`CHOOSE[nW1, exA, chosenB];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosenA]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[seqAdd, limit]], body];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[avV, HOL`Bool`GEN[bvV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], HOL`Bool`DISCH[tendstoTm[bV, bvV], folded]]]]]]
  ];

tendstoNegThm =
  Module[{aV, avV, eV, nV, hA, hE, uA, exA, nW, allTm, hAll, hN, dA, an,
          seqNeg, limit, appEq, betaEq, arithEq, argEq, absEq, ltGoal, impN,
          allN, exN, body, folded, chosen},
    aV = mkVar["a", seqTy]; avV = mkVar["A", realTy];
    eV = mkVar["e", realTy]; nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    uA = EQMP[unfoldTendsto[aV, avV], hA];
    exA = HOL`Bool`MP[HOL`Bool`SPEC[eV, uA], hE];
    nW = mkVar["nW", numTy];
    allTm = seqLimitAll[aV, avV, eV, nW];
    hAll = ASSUME[allTm];
    hN = ASSUME[seqNatLe[nW, nV]];
    dA = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAll], hN];
    an = mkComb[aV, nV];
    seqNeg = mkAbs[nV, realNegTm[mkComb[aV, nV]]];
    limit = realNegTm[avV];
    appEq = HOL`Equal`BETACONV[mkComb[seqNeg, nV]];
    betaEq = seqRealAddCongLeft[appEq, realNegTm[limit]];
    arithEq = seqSpecAll[seqArithNegDiffThm, {an, avV}];
    argEq = TRANS[betaEq, arithEq];
    absEq = TRANS[seqRealAbsCong[argEq],
      HOL`Bool`SPEC[realAddTm[an, realNegTm[avV]], realAbsNegThm]];
    ltGoal = EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], dA];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], ltGoal];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[seqNeg, limit, eV, mkVar["N", numTy]]],
      nW, allN];
    chosen = HOL`Bool`CHOOSE[nW, exA, exN];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosen]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[seqNeg, limit]], body];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[avV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], folded]]]
  ];

tendstoSubThm =
  Module[{aV, bV, avV, bvV, nV, hA, hB, negSeq, negTh, addInst, addRes, clean},
    aV = mkVar["a", seqTy]; bV = mkVar["b", seqTy];
    avV = mkVar["A", realTy]; bvV = mkVar["B", realTy];
    nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]]; hB = ASSUME[tendstoTm[bV, bvV]];
    negSeq = mkAbs[nV, realNegTm[mkComb[bV, nV]]];
    negTh = HOL`Bool`MP[seqSpecAll[tendstoNegThm, {bV, bvV}], hB];
    addInst = seqSpecAll[tendstoAddThm, {aV, negSeq, avV, realNegTm[bvV]}];
    addRes = HOL`Bool`MP[HOL`Bool`MP[addInst, hA], negTh];
    clean = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], addRes];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[avV, HOL`Bool`GEN[bvV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], HOL`Bool`DISCH[tendstoTm[bV, bvV], clean]]]]]]
  ];

tendstoConvergentThm =
  Module[{aV, lV, h, exThm, convThm},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy];
    h = ASSUME[tendstoTm[aV, lV]];
    exThm = HOL`Bool`EXISTS[existsTm[lV, tendstoTm[aV, lV]], lV, h];
    convThm = EQMP[HOL`Equal`SYM[seqUnfoldConvergent[aV]], exThm];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[tendstoTm[aV, lV], convThm]]]
  ];

End[];
EndPackage[];
