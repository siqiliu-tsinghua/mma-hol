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

eventuallyDefThm::usage = "eventuallyDefThm - |- eventually = (lambda P. exists N. forall n. N <= n ==> P n).";
eventuallyConst::usage = "eventuallyConst[] - eventually : (num -> bool) -> bool.";
eventuallyTm::usage = "eventuallyTm[P] - builds eventually P.";
unfoldEventually::usage = "unfoldEventually[P] - proves the beta-reduced eventually definition at P.";

eventuallyBoundedDefThm::usage = "eventuallyBoundedDefThm - |- eventuallyBounded = (lambda u. exists B. 0 < B /\\ eventually (lambda n. realAbs (u n) < B)).";
eventuallyBoundedConst::usage = "eventuallyBoundedConst[] - eventuallyBounded : (num -> real) -> bool.";
eventuallyBoundedTm::usage = "eventuallyBoundedTm[u] - builds eventuallyBounded u.";
unfoldEventuallyBounded::usage = "unfoldEventuallyBounded[u] - proves the beta-reduced eventuallyBounded definition at u.";

eventuallyAwayFromZeroDefThm::usage = "eventuallyAwayFromZeroDefThm - |- eventuallyAwayFromZero = (lambda u. exists c. 0 < c /\\ eventually (lambda n. c < realAbs (u n))).";
eventuallyAwayFromZeroConst::usage = "eventuallyAwayFromZeroConst[] - eventuallyAwayFromZero : (num -> real) -> bool.";
eventuallyAwayFromZeroTm::usage = "eventuallyAwayFromZeroTm[u] - builds eventuallyAwayFromZero u.";
unfoldEventuallyAwayFromZero::usage = "unfoldEventuallyAwayFromZero[u] - proves the beta-reduced eventuallyAwayFromZero definition at u.";

tendstoConstThm::usage = "tendstoConstThm - |- forall c. tendsto (lambda n. c) c.";
realNeAbsPosThm::usage = "realNeAbsPosThm - |- forall x. ~(x = 0) ==> 0 < realAbs x.";
tendstoUniqueThm::usage = "tendstoUniqueThm - |- forall a L1 L2. tendsto a L1 ==> tendsto a L2 ==> L1 = L2.";
tendstoAddThm::usage = "tendstoAddThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. a n + b n) (A + B).";
tendstoNegThm::usage = "tendstoNegThm - |- forall a A. tendsto a A ==> tendsto (lambda n. realNeg (a n)) (realNeg A).";
tendstoSubThm::usage = "tendstoSubThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. a n + realNeg (b n)) (A + realNeg B).";
tendstoConvergentThm::usage = "tendstoConvergentThm - |- forall a L. tendsto a L ==> convergent a.";
eventuallyOfForallThm::usage = "eventuallyOfForallThm - |- forall P. (forall n. P n) ==> eventually P.";
eventuallyMonoThm::usage = "eventuallyMonoThm - |- forall P Q. (forall n. P n ==> Q n) ==> eventually P ==> eventually Q.";
eventuallyAndThm::usage = "eventuallyAndThm - |- forall P Q. eventually P ==> eventually Q ==> eventually (lambda n. P n /\\ Q n).";
tendstoEventuallyThm::usage = "tendstoEventuallyThm - |- forall a L e. tendsto a L ==> 0 < e ==> eventually (lambda n. realAbs (a n + realNeg L) < e).";
seqTendstoEventuallyBoundedThm::usage = "seqTendstoEventuallyBoundedThm - |- forall a L. tendsto a L ==> eventuallyBounded a.";
seqTendstoEventuallyAwayFromZeroThm::usage = "seqTendstoEventuallyAwayFromZeroThm - |- forall a L. tendsto a L ==> ~(L = 0) ==> eventuallyAwayFromZero a.";

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

seqBetaClean[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

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

eventuallyPredTy = tyFun[numTy, boolTy];
eventuallyTy = tyFun[eventuallyPredTy, boolTy];
eventuallyBoundedTy = tyFun[seqTy, boolTy];
eventuallyAwayFromZeroTy = tyFun[seqTy, boolTy];

seqOneNat[] := sucT[zeroN[]];
seqOneReal[] := realOfRatTm[ratOfIntTm[intOfNumTm[seqOneNat[]]]];

seqEventuallyAll[pT_, n0T_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    forallTm[nV, impTm[seqNatLe[n0T, nV], mkComb[pT, nV]]]
  ];

seqEventuallyBody[pT_] :=
  Module[{n0V},
    n0V = mkVar["N", numTy];
    existsTm[n0V, seqEventuallyAll[pT, n0V]]
  ];

seqBoundPred[uT_, bT_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    mkAbs[nV, realLtTm[seqRealAbs[mkComb[uT, nV]], bT]]
  ];

seqAwayPred[uT_, cT_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    mkAbs[nV, realLtTm[cT, seqRealAbs[mkComb[uT, nV]]]]
  ];

seqEventuallyBoundedBody[uT_] :=
  Module[{bV},
    bV = mkVar["B", realTy];
    existsTm[bV, conjTm[realLtTm[zeroRealTm[], bV],
      eventuallyTm[seqBoundPred[uT, bV]]]]
  ];

seqEventuallyAwayFromZeroBody[uT_] :=
  Module[{cV},
    cV = mkVar["c", realTy];
    existsTm[cV, conjTm[realLtTm[zeroRealTm[], cV],
      eventuallyTm[seqAwayPred[uT, cV]]]]
  ];

eventuallyDefThm =
  Module[{pV, body},
    pV = mkVar["P", eventuallyPredTy];
    body = mkAbs[pV, seqEventuallyBody[pV]];
    newDefinition[mkEq[mkVar["eventually", eventuallyTy], body]]
  ];

eventuallyConst[] := mkConst["eventually", eventuallyTy];
eventuallyTm[pT_] := mkComb[eventuallyConst[], pT];

unfoldEventually[pT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[eventuallyDefThm, pT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

eventuallyBoundedDefThm =
  Module[{uV, body},
    uV = mkVar["u", seqTy];
    body = mkAbs[uV, seqEventuallyBoundedBody[uV]];
    newDefinition[mkEq[mkVar["eventuallyBounded", eventuallyBoundedTy], body]]
  ];

eventuallyBoundedConst[] := mkConst["eventuallyBounded", eventuallyBoundedTy];
eventuallyBoundedTm[uT_] := mkComb[eventuallyBoundedConst[], uT];

unfoldEventuallyBounded[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[eventuallyBoundedDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

eventuallyAwayFromZeroDefThm =
  Module[{uV, body},
    uV = mkVar["u", seqTy];
    body = mkAbs[uV, seqEventuallyAwayFromZeroBody[uV]];
    newDefinition[mkEq[mkVar["eventuallyAwayFromZero", eventuallyAwayFromZeroTy], body]]
  ];

eventuallyAwayFromZeroConst[] := mkConst["eventuallyAwayFromZero", eventuallyAwayFromZeroTy];
eventuallyAwayFromZeroTm[uT_] := mkComb[eventuallyAwayFromZeroConst[], uT];

unfoldEventuallyAwayFromZero[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[eventuallyAwayFromZeroDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqArithSubAddCancelThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV},
        mkEq[realAddTm[realAddTm[xV, realNegTm[yV]], yV], xV]]]
  ];

seqArithAddOnePosThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, impTm[realLeTm[zeroRealTm[], xV],
        realLtTm[zeroRealTm[], realAddTm[xV, seqOneReal[]]]]]]
  ];

seqArithBoundSumThm =
  Module[{pV, qV},
    pV = mkVar["p", realTy]; qV = mkVar["q", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{pV, qV},
        impTm[realLtTm[pV, seqOneReal[]],
          realLtTm[realAddTm[pV, qV], realAddTm[qV, seqOneReal[]]]]]]
  ];

seqArithHalfDoubleThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, mkEq[realAddTm[seqHalf[xV], seqHalf[xV]], xV]]]
  ];

seqArithAwayThm =
  Module[{xV, dV, uV, cV},
    xV = mkVar["x", realTy]; dV = mkVar["d", realTy];
    uV = mkVar["u", realTy]; cV = mkVar["c", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, dV, uV, cV},
        seqImpList[{mkEq[realAddTm[cV, cV], xV],
          realLeTm[xV, realAddTm[dV, uV]], realLtTm[dV, cV]},
          realLtTm[cV, uV]]]]
  ];

eventuallyOfForallThm =
  Module[{pV, nV, hAll, pN, impN, allN, exThm, folded},
    pV = mkVar["P", eventuallyPredTy]; nV = mkVar["n", numTy];
    hAll = ASSUME[forallTm[nV, mkComb[pV, nV]]];
    pN = HOL`Bool`SPEC[nV, hAll];
    impN = HOL`Bool`DISCH[seqNatLe[zeroN[], nV], pN];
    allN = HOL`Bool`GEN[nV, impN];
    exThm = HOL`Bool`EXISTS[seqEventuallyBody[pV], zeroN[], allN];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[pV]], exThm];
    HOL`Bool`GEN[pV, HOL`Bool`DISCH[forallTm[nV, mkComb[pV, nV]], folded]]
  ];

eventuallyMonoThm =
  Module[{pV, qV, nV, nW, hPQ, hEvP, exP, allPTm, hAllP, hLe, pN, qImp,
          qN, impN, allQ, exQ, folded, chosen},
    pV = mkVar["P", eventuallyPredTy]; qV = mkVar["Q", eventuallyPredTy];
    nV = mkVar["n", numTy]; nW = mkVar["nW", numTy];
    hPQ = ASSUME[forallTm[nV, impTm[mkComb[pV, nV], mkComb[qV, nV]]]];
    hEvP = ASSUME[eventuallyTm[pV]];
    exP = EQMP[unfoldEventually[pV], hEvP];
    allPTm = seqEventuallyAll[pV, nW];
    hAllP = ASSUME[allPTm];
    hLe = ASSUME[seqNatLe[nW, nV]];
    pN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllP], hLe];
    qImp = HOL`Bool`SPEC[nV, hPQ];
    qN = HOL`Bool`MP[qImp, pN];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], qN];
    allQ = HOL`Bool`GEN[nV, impN];
    exQ = HOL`Bool`EXISTS[seqEventuallyBody[qV], nW, allQ];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[qV]], exQ];
    chosen = HOL`Bool`CHOOSE[nW, exP, folded];
    HOL`Bool`GEN[pV, HOL`Bool`GEN[qV,
      HOL`Bool`DISCH[forallTm[nV, impTm[mkComb[pV, nV], mkComb[qV, nV]]],
        HOL`Bool`DISCH[eventuallyTm[pV], chosen]]]]
  ];

eventuallyAndThm =
  Module[{pV, qV, nV, nW1, nW2, pred, hEvP, hEvQ, exP, exQ, allPTm, allQTm,
          hAllP, hAllQ, nSum, hLe, leP0, leQ0, leP, leQ, pN, qN, conjN,
          betaN, redexN, impN, allN, exN, folded, chosenQ, chosenP},
    pV = mkVar["P", eventuallyPredTy]; qV = mkVar["Q", eventuallyPredTy];
    nV = mkVar["n", numTy]; nW1 = mkVar["nW1", numTy]; nW2 = mkVar["nW2", numTy];
    pred = mkAbs[nV, conjTm[mkComb[pV, nV], mkComb[qV, nV]]];
    hEvP = ASSUME[eventuallyTm[pV]]; hEvQ = ASSUME[eventuallyTm[qV]];
    exP = EQMP[unfoldEventually[pV], hEvP];
    exQ = EQMP[unfoldEventually[qV], hEvQ];
    allPTm = seqEventuallyAll[pV, nW1];
    allQTm = seqEventuallyAll[qV, nW2];
    hAllP = ASSUME[allPTm]; hAllQ = ASSUME[allQTm];
    nSum = seqNatAdd[nW1, nW2];
    hLe = ASSUME[seqNatLe[nSum, nV]];
    leP0 = seqLeqToSumLeft[nW1, nW2];
    leQ0 = seqLeqToSumRight[nW1, nW2];
    leP = seqLeqTrans[leP0, hLe];
    leQ = seqLeqTrans[leQ0, hLe];
    pN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllP], leP];
    qN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllQ], leQ];
    conjN = HOL`Bool`CONJ[pN, qN];
    betaN = HOL`Equal`BETACONV[mkComb[pred, nV]];
    redexN = EQMP[HOL`Equal`SYM[betaN], conjN];
    impN = HOL`Bool`DISCH[seqNatLe[nSum, nV], redexN];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[seqEventuallyBody[pred], nSum, allN];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[pred]], exN];
    chosenQ = HOL`Bool`CHOOSE[nW2, exQ, folded];
    chosenP = HOL`Bool`CHOOSE[nW1, exP, chosenQ];
    HOL`Bool`GEN[pV, HOL`Bool`GEN[qV,
      HOL`Bool`DISCH[eventuallyTm[pV], HOL`Bool`DISCH[eventuallyTm[qV], chosenP]]]]
  ];

tendstoEventuallyThm =
  Module[{aV, lV, eV, nV, nW, pred, hT, hE, unfolded, exRed, allTm, hAll,
          hLe, closeN, betaN, redexN, impN, allN, exN, folded, chosen},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy]; eV = mkVar["e", realTy];
    nV = mkVar["n", numTy]; nW = mkVar["nW", numTy];
    pred = mkAbs[nV, seqLimitAtom[aV, lV, eV, nV]];
    hT = ASSUME[tendstoTm[aV, lV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    unfolded = EQMP[unfoldTendsto[aV, lV], hT];
    exRed = HOL`Bool`MP[HOL`Bool`SPEC[eV, unfolded], hE];
    allTm = seqLimitAll[aV, lV, eV, nW];
    hAll = ASSUME[allTm];
    hLe = ASSUME[seqNatLe[nW, nV]];
    closeN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAll], hLe];
    betaN = HOL`Equal`BETACONV[mkComb[pred, nV]];
    redexN = EQMP[HOL`Equal`SYM[betaN], closeN];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], redexN];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[seqEventuallyBody[pred], nW, allN];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[pred]], exN];
    chosen = HOL`Bool`CHOOSE[nW, exRed, folded];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV, HOL`Bool`GEN[eV,
      HOL`Bool`DISCH[tendstoTm[aV, lV],
        HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosen]]]]]
  ];

seqTendstoEventuallyBoundedThm =
  Module[{aV, lV, nV, hT, oneR, bT, closePred, boundPred, absLNonneg, bPos,
          closeEv, monoInst, hClose, an, diff, appAbs, subAdd, absEq, triRaw,
          triLe, rhsLt, ltGoal, pointImp, pointAll, evBound, conjB, exB, folded},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy]; nV = mkVar["n", numTy];
    hT = ASSUME[tendstoTm[aV, lV]];
    oneR = seqOneReal[];
    bT = realAddTm[seqRealAbs[lV], oneR];
    closePred = mkAbs[nV, seqLimitAtom[aV, lV, oneR, nV]];
    boundPred = seqBoundPred[aV, bT];
    absLNonneg = HOL`Bool`SPEC[lV, realAbsNonnegThm];
    bPos = HOL`Bool`MP[HOL`Bool`SPEC[seqRealAbs[lV], seqArithAddOnePosThm], absLNonneg];
    closeEv = HOL`Bool`MP[
      HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm, {aV, lV, oneR}], hT],
      HOL`Auto`RealArith`rnumPos[1]];
    monoInst = seqBetaClean[seqSpecAll[eventuallyMonoThm, {closePred, boundPred}]];
    hClose = ASSUME[seqLimitAtom[aV, lV, oneR, nV]];
    an = mkComb[aV, nV];
    diff = realAddTm[an, realNegTm[lV]];
    appAbs = seqRealAbs[mkComb[aV, nV]];
    subAdd = seqSpecAll[seqArithSubAddCancelThm, {an, lV}];
    absEq = seqRealAbsCong[subAdd];
    triRaw = seqSpecAll[realAbsTriangleThm, {diff, lV}];
    triLe = EQMP[seqRealLeCong[absEq,
      REFL[realAddTm[seqRealAbs[diff], seqRealAbs[lV]]]], triRaw];
    rhsLt = HOL`Bool`MP[
      seqSpecAll[seqArithBoundSumThm, {seqRealAbs[diff], seqRealAbs[lV]}], hClose];
    ltGoal = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeLtTransThm,
        {appAbs, realAddTm[seqRealAbs[diff], seqRealAbs[lV]], bT}], triLe], rhsLt];
    pointImp = HOL`Bool`DISCH[seqLimitAtom[aV, lV, oneR, nV], ltGoal];
    pointAll = HOL`Bool`GEN[nV, pointImp];
    evBound = HOL`Bool`MP[HOL`Bool`MP[monoInst, pointAll], closeEv];
    conjB = HOL`Bool`CONJ[bPos, evBound];
    exB = HOL`Bool`EXISTS[seqEventuallyBoundedBody[aV], bT, conjB];
    folded = EQMP[HOL`Equal`SYM[unfoldEventuallyBounded[aV]], exB];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[tendstoTm[aV, lV], folded]]]
  ];

seqTendstoEventuallyAwayFromZeroThm =
  Module[{aV, lV, nV, hT, hNe, absL, cT, closePred, awayPred, absLPos, cPos,
          closeEv, monoInst, hClose, an, diffAL, diffLA, leftComm,
          negNegL, leftNegNeg, negEq, diffNegEq, absDiffEq, closeLA, subAdd,
          absEq, triRaw, triLe, halfDouble, awayLt, pointImp, pointAll, evAway,
          conjC, exC, folded},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy]; nV = mkVar["n", numTy];
    hT = ASSUME[tendstoTm[aV, lV]];
    hNe = ASSUME[notTm[mkEq[lV, zeroRealTm[]]]];
    absL = seqRealAbs[lV];
    cT = seqHalf[absL];
    closePred = mkAbs[nV, seqLimitAtom[aV, lV, cT, nV]];
    awayPred = seqAwayPred[aV, cT];
    absLPos = HOL`Bool`MP[HOL`Bool`SPEC[lV, realNeAbsPosThm], hNe];
    cPos = HOL`Bool`MP[HOL`Bool`SPEC[absL, seqArithHalfPosThm], absLPos];
    closeEv = HOL`Bool`MP[
      HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm, {aV, lV, cT}], hT], cPos];
    monoInst = seqBetaClean[seqSpecAll[eventuallyMonoThm, {closePred, awayPred}]];
    hClose = ASSUME[seqLimitAtom[aV, lV, cT, nV]];
    an = mkComb[aV, nV];
    diffAL = realAddTm[an, realNegTm[lV]];
    diffLA = realAddTm[lV, realNegTm[an]];
    leftComm = HOL`Bool`SPEC[realNegTm[an], HOL`Bool`SPEC[lV, realAddCommThm]];
    negNegL = HOL`Bool`SPEC[lV, realNegNegThm];
    leftNegNeg = seqRealAddCongRight[realNegTm[an], negNegL];
    negEq = seqSpecAll[seqArithNegDiffThm, {an, lV}];
    diffNegEq = TRANS[leftComm, TRANS[HOL`Equal`SYM[leftNegNeg], negEq]];
    absDiffEq = TRANS[seqRealAbsCong[diffNegEq], HOL`Bool`SPEC[diffAL, realAbsNegThm]];
    closeLA = EQMP[HOL`Equal`SYM[seqRealLtCong[absDiffEq, REFL[cT]]], hClose];
    subAdd = seqSpecAll[seqArithSubAddCancelThm, {lV, an}];
    absEq = seqRealAbsCong[subAdd];
    triRaw = seqSpecAll[realAbsTriangleThm, {diffLA, an}];
    triLe = EQMP[seqRealLeCong[absEq,
      REFL[realAddTm[seqRealAbs[diffLA], seqRealAbs[an]]]], triRaw];
    halfDouble = HOL`Bool`SPEC[absL, seqArithHalfDoubleThm];
    awayLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithAwayThm, {absL, seqRealAbs[diffLA], seqRealAbs[an], cT}],
      halfDouble], triLe], closeLA];
    pointImp = HOL`Bool`DISCH[seqLimitAtom[aV, lV, cT, nV], awayLt];
    pointAll = HOL`Bool`GEN[nV, pointImp];
    evAway = HOL`Bool`MP[HOL`Bool`MP[monoInst, pointAll], closeEv];
    conjC = HOL`Bool`CONJ[cPos, evAway];
    exC = HOL`Bool`EXISTS[seqEventuallyAwayFromZeroBody[aV], cT, conjC];
    folded = EQMP[HOL`Equal`SYM[unfoldEventuallyAwayFromZero[aV]], exC];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[tendstoTm[aV, lV],
        HOL`Bool`DISCH[notTm[mkEq[lV, zeroRealTm[]]], folded]]]]
  ];

End[];
EndPackage[];
