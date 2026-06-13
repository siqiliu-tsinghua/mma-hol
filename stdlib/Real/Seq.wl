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
realAbsMulThm::usage = "realAbsMulThm - |- forall x y. realAbs (realMul x y) = realMul (realAbs x) (realAbs y).";
seqTendstoMulThm::usage = "seqTendstoMulThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. realMul (a n) (b n)) (realMul A B).";
seqTendstoScalarMulThm::usage = "seqTendstoScalarMulThm - |- forall a A c. tendsto a A ==> tendsto (lambda n. realMul c (a n)) (realMul c A).";

monoIncDefThm::usage = "monoIncDefThm - |- monoInc = (lambda u. forall n m. n <= m ==> realLe (u n) (u m)).";
monoIncConst::usage = "monoIncConst[] - monoInc : (num -> real) -> bool.";
monoIncTm::usage = "monoIncTm[u] - builds monoInc u.";
unfoldMonoInc::usage = "unfoldMonoInc[u] - proves the beta-reduced monoInc definition at u.";
monoDecDefThm::usage = "monoDecDefThm - |- monoDec = (lambda u. forall n m. n <= m ==> realLe (u m) (u n)).";
monoDecConst::usage = "monoDecConst[] - monoDec : (num -> real) -> bool.";
monoDecTm::usage = "monoDecTm[u] - builds monoDec u.";
unfoldMonoDec::usage = "unfoldMonoDec[u] - proves the beta-reduced monoDec definition at u.";
seqBddAboveDefThm::usage = "seqBddAboveDefThm - |- seqBddAbove = (lambda u. exists B. forall n. realLe (u n) B).";
seqBddAboveConst::usage = "seqBddAboveConst[] - seqBddAbove : (num -> real) -> bool.";
seqBddAboveTm::usage = "seqBddAboveTm[u] - builds seqBddAbove u.";
unfoldSeqBddAbove::usage = "unfoldSeqBddAbove[u] - proves the beta-reduced seqBddAbove definition at u.";
seqBddBelowDefThm::usage = "seqBddBelowDefThm - |- seqBddBelow = (lambda u. exists B. forall n. realLe B (u n)).";
seqBddBelowConst::usage = "seqBddBelowConst[] - seqBddBelow : (num -> real) -> bool.";
seqBddBelowTm::usage = "seqBddBelowTm[u] - builds seqBddBelow u.";
unfoldSeqBddBelow::usage = "unfoldSeqBddBelow[u] - proves the beta-reduced seqBddBelow definition at u.";
realAbsSubLtThm::usage = "realAbsSubLtThm - |- forall x a e. realLt (a + -e) x ==> realLt x (a + e) ==> realLt (realAbs (x + -a)) e.";
realSupLtMemThm::usage = "realSupLtMemThm - |- forall S t. (exists a. S a) ==> (exists u. forall a. S a ==> realLe a u) ==> realLt t (realSup S) ==> exists a. S a /\\ realLt t a.";
monoIncTendstoSupThm::usage = "monoIncTendstoSupThm - |- forall u. monoInc u ==> seqBddAbove u ==> tendsto u (realSup (lambda x. exists n. x = u n)).";
monoConvergesIncThm::usage = "monoConvergesIncThm - |- forall u. monoInc u ==> seqBddAbove u ==> exists L. tendsto u L.";
monoConvergesDecThm::usage = "monoConvergesDecThm - |- forall u. monoDec u ==> seqBddBelow u ==> exists L. tendsto u L.";

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

seqRealMulCongLeft[eq_, cT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realMulConst[], eq], REFL[cT]];

seqRealMulCongRight[cT_, eq_] :=
  HOL`Equal`APTERM[mkComb[realMulConst[], cT], eq];

seqMulOneLeft[xT_] :=
  TRANS[HOL`Bool`SPEC[xT, HOL`Bool`SPEC[seqOneReal[], realMulCommThm]],
    HOL`Bool`SPEC[xT, realMulOneThm]];

seqMulDistribRight[xT_, yT_, zT_] :=
  Module[{commL, dist, commX, commY, rhs1, rhs2},
    commL = HOL`Bool`SPEC[zT, HOL`Bool`SPEC[realAddTm[xT, yT], realMulCommThm]];
    dist = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT,
      HOL`Bool`SPEC[zT, realMulDistribThm]]];
    commX = HOL`Bool`SPEC[xT, HOL`Bool`SPEC[zT, realMulCommThm]];
    commY = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[zT, realMulCommThm]];
    rhs1 = seqRealAddCongLeft[commX, realMulTm[zT, yT]];
    rhs2 = seqRealAddCongRight[realMulTm[xT, zT], commY];
    TRANS[commL, TRANS[dist, TRANS[rhs1, rhs2]]]
  ];

seqScaleCancelRight[xT_, yT_, yNe0_] :=
  Module[{iy, assoc, comm, inv, middle, one},
    iy = seqRealInv[yT];
    assoc = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[iy,
      HOL`Bool`SPEC[xT, realMulAssocThm]]];
    comm = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[iy, realMulCommThm]];
    inv = HOL`Bool`MP[HOL`Bool`SPEC[yT, realMulInvThm], yNe0];
    middle = seqRealMulCongRight[xT, TRANS[comm, inv]];
    one = HOL`Bool`SPEC[xT, realMulOneThm];
    TRANS[assoc, TRANS[middle, one]]
  ];

seqScaleCancelLeft[xT_, yT_, yNe0_] :=
  Module[{iy, assoc, inv, middle, one},
    iy = seqRealInv[yT];
    assoc = HOL`Equal`SYM[HOL`Bool`SPEC[xT, HOL`Bool`SPEC[iy,
      HOL`Bool`SPEC[yT, realMulAssocThm]]]];
    inv = HOL`Bool`MP[HOL`Bool`SPEC[yT, realMulInvThm], yNe0];
    middle = seqRealMulCongLeft[inv, xT];
    one = seqMulOneLeft[xT];
    TRANS[assoc, TRANS[middle, one]]
  ];

seqArithPosNeZeroThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, impTm[realLtTm[zeroRealTm[], xV],
        notTm[mkEq[xV, zeroRealTm[]]]]]]
  ];

seqArithLtAddOneThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, realLtTm[xV, realAddTm[xV, seqOneReal[]]]]]
  ];

seqLtImpLeRule[ltTh_] :=
  Module[{aT, bT},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]];
    HOL`Bool`MP[seqSpecAll[realLtImpLeThm, {aT, bT}], ltTh]
  ];

seqLeLtTransRule[leTh_, ltTh_] :=
  Module[{aT, bT, cT},
    aT = concl[leTh][[1, 2]]; bT = concl[leTh][[2]]; cT = concl[ltTh][[2]];
    HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLeLtTransThm, {aT, bT, cT}],
      leTh], ltTh]
  ];

seqMulLeRightRule[leTh_, cNonneg_] :=
  Module[{aT, bT, cT, mono, leftComm, rightComm},
    aT = concl[leTh][[1, 2]]; bT = concl[leTh][[2]]; cT = concl[cNonneg][[2]];
    mono = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLeMulMonoThm, {aT, bT, cT}],
      cNonneg], leTh];
    leftComm = HOL`Bool`SPEC[aT, HOL`Bool`SPEC[cT, realMulCommThm]];
    rightComm = HOL`Bool`SPEC[bT, HOL`Bool`SPEC[cT, realMulCommThm]];
    EQMP[seqRealLeCong[leftComm, rightComm], mono]
  ];

seqMulLtRightRule[ltTh_, cPos_] :=
  Module[{aT, bT, cT, mono, leftComm, rightComm},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]]; cT = concl[cPos][[2]];
    mono = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLtMulMonoThm, {aT, bT, cT}],
      cPos], ltTh];
    leftComm = HOL`Bool`SPEC[aT, HOL`Bool`SPEC[cT, realMulCommThm]];
    rightComm = HOL`Bool`SPEC[bT, HOL`Bool`SPEC[cT, realMulCommThm]];
    EQMP[seqRealLtCong[leftComm, rightComm], mono]
  ];

realAbsNonposThm =
  Module[{xV, hNonpos, body},
    xV = mkVar["x", realTy];
    hNonpos = ASSUME[realLeTm[xV, zeroRealTm[]]];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], xV]],
      Module[{hPos, xEq0, absTo0, negTo0},
        hPos = ASSUME[realLeTm[zeroRealTm[], xV]];
        xEq0 = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[zeroRealTm[], HOL`Bool`SPEC[xV, realLeAntisymThm]],
          hNonpos], hPos];
        absTo0 = TRANS[seqRealAbsCong[xEq0], realAbsZeroThm];
        negTo0 = TRANS[HOL`Equal`APTERM[realNegConst[], xEq0], realNegZeroThm];
        TRANS[absTo0, HOL`Equal`SYM[negTo0]]
      ],
      Module[{hNeg},
        hNeg = ASSUME[notTm[realLeTm[zeroRealTm[], xV]]];
        HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLeTm[xV, zeroRealTm[]], body]]
  ];

realAbsMulThm =
  Module[{xV, yV, xy, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; xy = realMulTm[xV, yV];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], xV]],
      Module[{hXpos},
        hXpos = ASSUME[realLeTm[zeroRealTm[], xV]];
        HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], yV]],
          Module[{hYpos, hXYpos, absX, absY, absXY, rhs1, rhs2},
            hYpos = ASSUME[realLeTm[zeroRealTm[], yV]];
            hXYpos = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNonnegThm]], hXpos], hYpos];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hXpos];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsPosThm], hYpos];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsPosThm], hXYpos];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[xV, absY];
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, rhs2]]]
          ],
          Module[{hYneg, yLe0, negYNonneg, hProd, mulNeg, hNegProd, negNegLe0,
                  xyLe0, absX, absY, absXY, rhs1, rhs2, rhs3},
            hYneg = ASSUME[notTm[realLeTm[zeroRealTm[], yV]]];
            yLe0 = HOL`Bool`MP[HOL`Bool`SPEC[yV, notNonnegToLeZeroThm], hYneg];
            negYNonneg = HOL`Bool`MP[HOL`Bool`SPEC[yV, realNegNonnegThm], yLe0];
            hProd = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[realNegTm[yV], HOL`Bool`SPEC[xV, realMulNonnegThm]],
              hXpos], negYNonneg];
            mulNeg = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNegRightThm]];
            hNegProd = EQMP[seqRealLeCong[REFL[zeroRealTm[]], mulNeg], hProd];
            negNegLe0 = HOL`Bool`MP[HOL`Bool`SPEC[realNegTm[xy], realNegNonposThm],
              hNegProd];
            xyLe0 = EQMP[seqRealLeCong[HOL`Bool`SPEC[xy, realNegNegThm],
              REFL[zeroRealTm[]]], negNegLe0];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hXpos];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsNonposThm], yLe0];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsNonposThm], xyLe0];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[xV, absY];
            rhs3 = mulNeg;
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, TRANS[rhs2, rhs3]]]]
          ]]
      ],
      Module[{hXneg, xLe0, negXNonneg},
        hXneg = ASSUME[notTm[realLeTm[zeroRealTm[], xV]]];
        xLe0 = HOL`Bool`MP[HOL`Bool`SPEC[xV, notNonnegToLeZeroThm], hXneg];
        negXNonneg = HOL`Bool`MP[HOL`Bool`SPEC[xV, realNegNonnegThm], xLe0];
        HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], yV]],
          Module[{hYpos, hProd, mulNeg, hNegProd, negNegLe0, xyLe0, absX, absY,
                  absXY, rhs1, rhs2, rhs3},
            hYpos = ASSUME[realLeTm[zeroRealTm[], yV]];
            hProd = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[yV, HOL`Bool`SPEC[realNegTm[xV], realMulNonnegThm]],
              negXNonneg], hYpos];
            mulNeg = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNegLeftThm]];
            hNegProd = EQMP[seqRealLeCong[REFL[zeroRealTm[]], mulNeg], hProd];
            negNegLe0 = HOL`Bool`MP[HOL`Bool`SPEC[realNegTm[xy], realNegNonposThm],
              hNegProd];
            xyLe0 = EQMP[seqRealLeCong[HOL`Bool`SPEC[xy, realNegNegThm],
              REFL[zeroRealTm[]]], negNegLe0];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNonposThm], xLe0];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsPosThm], hYpos];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsNonposThm], xyLe0];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[realNegTm[xV], absY];
            rhs3 = mulNeg;
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, TRANS[rhs2, rhs3]]]]
          ],
          Module[{hYneg, yLe0, negYNonneg, hProd, negLeft, negRight, negNeg,
                  prodEq, hXYpos, absX, absY, absXY, rhs1, rhs2, rhs3},
            hYneg = ASSUME[notTm[realLeTm[zeroRealTm[], yV]]];
            yLe0 = HOL`Bool`MP[HOL`Bool`SPEC[yV, notNonnegToLeZeroThm], hYneg];
            negYNonneg = HOL`Bool`MP[HOL`Bool`SPEC[yV, realNegNonnegThm], yLe0];
            hProd = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[realNegTm[yV],
                HOL`Bool`SPEC[realNegTm[xV], realMulNonnegThm]],
              negXNonneg], negYNonneg];
            negLeft = HOL`Bool`SPEC[realNegTm[yV],
              HOL`Bool`SPEC[xV, realMulNegLeftThm]];
            negRight = HOL`Equal`APTERM[realNegConst[],
              HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNegRightThm]]];
            negNeg = HOL`Bool`SPEC[xy, realNegNegThm];
            prodEq = TRANS[negLeft, TRANS[negRight, negNeg]];
            hXYpos = EQMP[seqRealLeCong[REFL[zeroRealTm[]], prodEq], hProd];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNonposThm], xLe0];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsNonposThm], yLe0];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsPosThm], hXYpos];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[realNegTm[xV], absY];
            rhs3 = prodEq;
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, TRANS[rhs2, rhs3]]]]
          ]]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

mulSubMulThm =
  Module[{xV, yV, aV, bV, lhs, rhs1, rhs2, rhs, ay, eq1, eq2, rhsA, rhsB,
          rhsExpand, cancel},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    lhs = realAddTm[realMulTm[xV, yV], realNegTm[realMulTm[aV, bV]]];
    rhs1 = realMulTm[realAddTm[xV, realNegTm[aV]], yV];
    rhs2 = realMulTm[aV, realAddTm[yV, realNegTm[bV]]];
    rhs = realAddTm[rhs1, rhs2];
    ay = realMulTm[aV, yV];
    eq1 = TRANS[seqMulDistribRight[xV, realNegTm[aV], yV],
      seqRealAddCongRight[realMulTm[xV, yV],
        HOL`Bool`SPEC[yV, HOL`Bool`SPEC[aV, realMulNegLeftThm]]]];
    eq2 = TRANS[HOL`Bool`SPEC[realNegTm[bV], HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[aV, realMulDistribThm]]],
      seqRealAddCongRight[ay,
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, realMulNegRightThm]]]];
    rhsA = realAddTm[realMulTm[xV, yV], realNegTm[ay]];
    rhsB = realAddTm[ay, realNegTm[realMulTm[aV, bV]]];
    rhsExpand = TRANS[seqRealAddCongLeft[eq1, rhs2],
      seqRealAddCongRight[rhsA, eq2]];
    cancel = seqSpecAll[seqArithDiffChainThm,
      {realMulTm[xV, yV], ay, realMulTm[aV, bV]}];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Equal`SYM[TRANS[rhsExpand, cancel]]]]]]
  ];

seqRealInvPositiveThm =
  Module[{xV, ix, hPos, hNeX, invEq, invNonnegRaw, invRewrite, invNonneg,
          hInvEq0, prodEq0, oneEq0, ffInvEq0, invNe0, hInvLe0, eq0Inv, ffLe,
          notLe, ltEq, body},
    xV = mkVar["x", realTy]; ix = seqRealInv[xV];
    hPos = ASSUME[realLtTm[zeroRealTm[], xV]];
    hNeX = HOL`Bool`MP[HOL`Bool`SPEC[xV, seqArithPosNeZeroThm], hPos];
    invEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realInvPosThm], hPos];
    invNonnegRaw = HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosNonnegThm], hPos];
    invRewrite = seqRealLeCong[REFL[zeroRealTm[]], HOL`Equal`SYM[invEq]];
    invNonneg = EQMP[invRewrite, invNonnegRaw];
    hInvEq0 = ASSUME[mkEq[ix, zeroRealTm[]]];
    prodEq0 = TRANS[seqRealMulCongRight[xV, hInvEq0],
      HOL`Bool`SPEC[xV, realMulZeroThm]];
    oneEq0 = TRANS[HOL`Equal`SYM[
      HOL`Bool`MP[HOL`Bool`SPEC[xV, realMulInvThm], hNeX]], prodEq0];
    ffInvEq0 = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Auto`RealArith`rnumNe[1, 0]],
      oneEq0];
    invNe0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[ix, zeroRealTm[]], ffInvEq0]];
    hInvLe0 = ASSUME[realLeTm[ix, zeroRealTm[]]];
    eq0Inv = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[ix, HOL`Bool`SPEC[zeroRealTm[], realLeAntisymThm]],
      invNonneg], hInvLe0];
    ffLe = HOL`Bool`MP[HOL`Bool`NOTELIM[invNe0], HOL`Equal`SYM[eq0Inv]];
    notLe = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[ix, zeroRealTm[]], ffLe]];
    ltEq = HOL`Bool`SPEC[zeroRealTm[], HOL`Bool`SPEC[ix,
      HOL`Auto`RealArith`realNotLeLtThm]];
    body = EQMP[ltEq, notLe];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], xV], body]]
  ];

seqTendstoMulThm =
  Module[{uV, vV, aV, bV, eV, nV, hU, hV, hE, e2, e2Pos, boundedV,
          exBound, boundW, boundPred, boundConjTm, hBoundConj, hBoundPos,
          hEvBound, absA, aBound, aBoundPos, boundNe0, aBoundNe0, invBound,
          invABound, invBoundPos, invABoundPos, deltaU, deltaV, deltaUPos,
          deltaVPos, scaleU, scaleV, closeUPred, closeVPred, evU, evV,
          evPairRaw, evPair, pairPred, evAllRaw, evAll, allPred, prodSeq,
          prodLim, goalPred, hPoint, allBeta, hAllConj, hPair, hBound,
          hCloseU, hCloseV, un, vn, uDiff, vDiff, t1, t2, prodDiff, absT1,
          absT2, absUDiff, absVn, absVDiff, absMul1, hBoundLe, absUDiffNonneg,
          le1Base, le1, lt1Base, lt1, term1, absMul2, absALtBound,
          absALeBound, absVDiffNonneg, le2Base, le2, lt2Base, lt2, term2,
          decompEq, triRaw, triLe, diffLt, appEq, argEq, absEq, ltGoal,
          goalBeta, pointGoal, pointImp, pointAll, monoInst, evGoal, exGoal,
          body, folded, chosenBound},
    uV = mkVar["a", seqTy]; vV = mkVar["b", seqTy];
    aV = mkVar["A", realTy]; bV = mkVar["B", realTy];
    eV = mkVar["e", realTy]; nV = mkVar["n", numTy];
    hU = ASSUME[tendstoTm[uV, aV]]; hV = ASSUME[tendstoTm[vV, bV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    e2 = seqHalf[eV];
    e2Pos = HOL`Bool`MP[HOL`Bool`SPEC[eV, seqArithHalfPosThm], hE];
    boundedV = HOL`Bool`MP[seqSpecAll[seqTendstoEventuallyBoundedThm, {vV, bV}], hV];
    exBound = EQMP[unfoldEventuallyBounded[vV], boundedV];
    boundW = mkVar["boundW", realTy];
    boundPred = seqBoundPred[vV, boundW];
    boundConjTm = conjTm[realLtTm[zeroRealTm[], boundW], eventuallyTm[boundPred]];
    hBoundConj = ASSUME[boundConjTm];
    hBoundPos = HOL`Bool`CONJUNCT1[hBoundConj];
    hEvBound = HOL`Bool`CONJUNCT2[hBoundConj];
    absA = seqRealAbs[aV];
    aBound = realAddTm[absA, seqOneReal[]];
    aBoundPos = HOL`Bool`MP[HOL`Bool`SPEC[absA, seqArithAddOnePosThm],
      HOL`Bool`SPEC[aV, realAbsNonnegThm]];
    boundNe0 = HOL`Bool`MP[HOL`Bool`SPEC[boundW, seqArithPosNeZeroThm], hBoundPos];
    aBoundNe0 = HOL`Bool`MP[HOL`Bool`SPEC[aBound, seqArithPosNeZeroThm], aBoundPos];
    invBound = seqRealInv[boundW];
    invABound = seqRealInv[aBound];
    invBoundPos = HOL`Bool`MP[HOL`Bool`SPEC[boundW, seqRealInvPositiveThm], hBoundPos];
    invABoundPos = HOL`Bool`MP[HOL`Bool`SPEC[aBound, seqRealInvPositiveThm], aBoundPos];
    deltaU = realMulTm[e2, invBound];
    deltaV = realMulTm[invABound, e2];
    deltaUPos = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[invBound, HOL`Bool`SPEC[e2, realLtMulPosThm]],
      e2Pos], invBoundPos];
    deltaVPos = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[e2, HOL`Bool`SPEC[invABound, realLtMulPosThm]],
      invABoundPos], e2Pos];
    scaleU = seqScaleCancelRight[e2, boundW, boundNe0];
    scaleV = seqScaleCancelLeft[e2, aBound, aBoundNe0];
    closeUPred = mkAbs[nV, seqLimitAtom[uV, aV, deltaU, nV]];
    closeVPred = mkAbs[nV, seqLimitAtom[vV, bV, deltaV, nV]];
    evU = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm,
      {uV, aV, deltaU}], hU], deltaUPos];
    evV = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm,
      {vV, bV, deltaV}], hV], deltaVPos];
    evPairRaw = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[eventuallyAndThm,
      {closeUPred, closeVPred}], evU], evV];
    evPair = seqBetaClean[evPairRaw];
    pairPred = concl[evPair][[2]];
    evAllRaw = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[eventuallyAndThm,
      {pairPred, boundPred}], evPair], hEvBound];
    evAll = seqBetaClean[evAllRaw];
    allPred = concl[evAll][[2]];
    prodSeq = mkAbs[nV, realMulTm[mkComb[uV, nV], mkComb[vV, nV]]];
    prodLim = realMulTm[aV, bV];
    goalPred = mkAbs[nV, seqLimitAtom[prodSeq, prodLim, eV, nV]];

    hPoint = ASSUME[mkComb[allPred, nV]];
    allBeta = HOL`Equal`BETACONV[mkComb[allPred, nV]];
    hAllConj = EQMP[allBeta, hPoint];
    hPair = HOL`Bool`CONJUNCT1[hAllConj];
    hBound = HOL`Bool`CONJUNCT2[hAllConj];
    hCloseU = HOL`Bool`CONJUNCT1[hPair];
    hCloseV = HOL`Bool`CONJUNCT2[hPair];
    un = mkComb[uV, nV]; vn = mkComb[vV, nV];
    uDiff = realAddTm[un, realNegTm[aV]];
    vDiff = realAddTm[vn, realNegTm[bV]];
    t1 = realMulTm[uDiff, vn];
    t2 = realMulTm[aV, vDiff];
    prodDiff = realAddTm[realMulTm[un, vn], realNegTm[prodLim]];
    absT1 = seqRealAbs[t1]; absT2 = seqRealAbs[t2];
    absUDiff = seqRealAbs[uDiff]; absVn = seqRealAbs[vn]; absVDiff = seqRealAbs[vDiff];

    absMul1 = seqSpecAll[realAbsMulThm, {uDiff, vn}];
    hBoundLe = seqLtImpLeRule[hBound];
    absUDiffNonneg = HOL`Bool`SPEC[uDiff, realAbsNonnegThm];
    le1Base = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLeMulMonoThm,
      {absVn, boundW, absUDiff}], absUDiffNonneg], hBoundLe];
    le1 = EQMP[seqRealLeCong[HOL`Equal`SYM[absMul1],
      REFL[realMulTm[absUDiff, boundW]]], le1Base];
    lt1Base = seqMulLtRightRule[hCloseU, hBoundPos];
    lt1 = seqLeLtTransRule[le1, lt1Base];
    term1 = EQMP[seqRealLtCong[REFL[absT1], scaleU], lt1];

    absMul2 = seqSpecAll[realAbsMulThm, {aV, vDiff}];
    absALtBound = HOL`Bool`SPEC[absA, seqArithLtAddOneThm];
    absALeBound = seqLtImpLeRule[absALtBound];
    absVDiffNonneg = HOL`Bool`SPEC[vDiff, realAbsNonnegThm];
    le2Base = seqMulLeRightRule[absALeBound, absVDiffNonneg];
    le2 = EQMP[seqRealLeCong[HOL`Equal`SYM[absMul2],
      REFL[realMulTm[aBound, absVDiff]]], le2Base];
    lt2Base = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLtMulMonoThm,
      {absVDiff, deltaV, aBound}], aBoundPos], hCloseV];
    lt2 = seqLeLtTransRule[le2, lt2Base];
    term2 = EQMP[seqRealLtCong[REFL[absT2], scaleV], lt2];

    decompEq = seqSpecAll[mulSubMulThm, {un, vn, aV, bV}];
    triRaw = seqSpecAll[realAbsTriangleThm, {t1, t2}];
    triLe = EQMP[seqRealLeCong[HOL`Equal`SYM[seqRealAbsCong[decompEq]],
      REFL[realAddTm[absT1, absT2]]], triRaw];
    diffLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithTriangleLtThm, {seqRealAbs[prodDiff], absT1, absT2, eV}],
      triLe], term1], term2];
    appEq = HOL`Equal`BETACONV[mkComb[prodSeq, nV]];
    argEq = seqRealAddCongLeft[appEq, realNegTm[prodLim]];
    absEq = seqRealAbsCong[argEq];
    ltGoal = EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], diffLt];
    goalBeta = HOL`Equal`BETACONV[mkComb[goalPred, nV]];
    pointGoal = EQMP[HOL`Equal`SYM[goalBeta], ltGoal];
    pointImp = HOL`Bool`DISCH[mkComb[allPred, nV], pointGoal];
    pointAll = HOL`Bool`GEN[nV, pointImp];
    monoInst = seqSpecAll[eventuallyMonoThm, {allPred, goalPred}];
    evGoal = HOL`Bool`MP[HOL`Bool`MP[monoInst, pointAll], evAll];
    exGoal = seqBetaClean[EQMP[unfoldEventually[goalPred], evGoal]];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], exGoal]];
    folded = EQMP[HOL`Equal`SYM[seqBetaClean[unfoldTendsto[prodSeq, prodLim]]], body];
    chosenBound = HOL`Bool`CHOOSE[boundW, exBound, folded];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[vV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[tendstoTm[uV, aV], HOL`Bool`DISCH[tendstoTm[vV, bV],
        chosenBound]]]]]]
  ];

seqTendstoScalarMulThm =
  Module[{aV, avV, cV, nV, hA, constSeq, constTh, prodInst, prodTh, cleanProd,
          seqLeft, seqRight, betaL, betaR, bodyComm, pointEq, pointAll, seqEq,
          limitEq, tendstoEq, reshaped},
    aV = mkVar["a", seqTy]; avV = mkVar["A", realTy]; cV = mkVar["c", realTy];
    nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]];
    constSeq = mkAbs[nV, cV];
    constTh = HOL`Bool`SPEC[cV, tendstoConstThm];
    prodInst = seqSpecAll[seqTendstoMulThm, {aV, constSeq, avV, cV}];
    prodTh = HOL`Bool`MP[HOL`Bool`MP[prodInst, hA], constTh];
    cleanProd = seqBetaClean[prodTh];
    seqLeft = mkAbs[nV, realMulTm[mkComb[aV, nV], cV]];
    seqRight = mkAbs[nV, realMulTm[cV, mkComb[aV, nV]]];
    betaL = HOL`Equal`BETACONV[mkComb[seqLeft, nV]];
    betaR = HOL`Equal`BETACONV[mkComb[seqRight, nV]];
    bodyComm = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[mkComb[aV, nV], realMulCommThm]];
    pointEq = TRANS[betaL, TRANS[bodyComm, HOL`Equal`SYM[betaR]]];
    pointAll = HOL`Bool`GEN[nV, pointEq];
    seqEq = HOL`Stdlib`List`funcExtThm[seqLeft, seqRight, pointAll];
    limitEq = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[avV, realMulCommThm]];
    tendstoEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[tendstoConst[], seqEq], limitEq];
    reshaped = EQMP[tendstoEq, cleanProd];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[avV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], reshaped]]]]
  ];

monoPredTy = tyFun[seqTy, boolTy];
seqBddTy = tyFun[seqTy, boolTy];
seqSetTy = tyFun[realTy, boolTy];

seqRealSup[sT_] := mkComb[realSupConst[], sT];

seqRangeTm[uT_] :=
  Module[{xR, nR},
    xR = mkVar["xR", realTy]; nR = mkVar["nR", numTy];
    mkAbs[xR, existsTm[nR, mkEq[xR, mkComb[uT, nR]]]]
  ];

seqRangeMemThm[rangeT_, uT_, nT_] :=
  Module[{xT, beta, exThm},
    xT = mkComb[uT, nT];
    beta = HOL`Equal`BETACONV[mkComb[rangeT, xT]];
    exThm = HOL`Bool`EXISTS[concl[beta][[2]], nT, REFL[xT]];
    EQMP[HOL`Equal`SYM[beta], exThm]
  ];

seqRangeNonemptyThm[rangeT_, uT_] :=
  Module[{aR, mem0},
    aR = mkVar["aR", realTy];
    mem0 = seqRangeMemThm[rangeT, uT, zeroN[]];
    HOL`Bool`EXISTS[existsTm[aR, mkComb[rangeT, aR]], mkComb[uT, zeroN[]], mem0]
  ];

seqMonoIncBody[uT_] :=
  Module[{nV, mV},
    nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    forallTm[nV, forallTm[mV,
      impTm[seqNatLe[nV, mV], realLeTm[mkComb[uT, nV], mkComb[uT, mV]]]]]
  ];

seqMonoDecBody[uT_] :=
  Module[{nV, mV},
    nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    forallTm[nV, forallTm[mV,
      impTm[seqNatLe[nV, mV], realLeTm[mkComb[uT, mV], mkComb[uT, nV]]]]]
  ];

seqBddAboveBody[uT_] :=
  Module[{bV, nV},
    bV = mkVar["B", realTy]; nV = mkVar["n", numTy];
    existsTm[bV, forallTm[nV, realLeTm[mkComb[uT, nV], bV]]]
  ];

seqBddBelowBody[uT_] :=
  Module[{bV, nV},
    bV = mkVar["B", realTy]; nV = mkVar["n", numTy];
    existsTm[bV, forallTm[nV, realLeTm[bV, mkComb[uT, nV]]]]
  ];

monoIncDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["monoInc", monoPredTy],
      mkAbs[uV, seqMonoIncBody[uV]]]]
  ];

monoIncConst[] := mkConst["monoInc", monoPredTy];
monoIncTm[uT_] := mkComb[monoIncConst[], uT];

unfoldMonoInc[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[monoIncDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

monoDecDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["monoDec", monoPredTy],
      mkAbs[uV, seqMonoDecBody[uV]]]]
  ];

monoDecConst[] := mkConst["monoDec", monoPredTy];
monoDecTm[uT_] := mkComb[monoDecConst[], uT];

unfoldMonoDec[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[monoDecDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqBddAboveDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["seqBddAbove", seqBddTy],
      mkAbs[uV, seqBddAboveBody[uV]]]]
  ];

seqBddAboveConst[] := mkConst["seqBddAbove", seqBddTy];
seqBddAboveTm[uT_] := mkComb[seqBddAboveConst[], uT];

unfoldSeqBddAbove[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[seqBddAboveDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqBddBelowDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["seqBddBelow", seqBddTy],
      mkAbs[uV, seqBddBelowBody[uV]]]]
  ];

seqBddBelowConst[] := mkConst["seqBddBelow", seqBddTy];
seqBddBelowTm[uT_] := mkComb[seqBddBelowConst[], uT];

unfoldSeqBddBelow[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[seqBddBelowDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqArithAbsUpperThm =
  Module[{xV, aV, eV},
    xV = mkVar["x", realTy]; aV = mkVar["a", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, aV, eV},
        impTm[realLtTm[xV, realAddTm[aV, eV]],
          realLtTm[realAddTm[xV, realNegTm[aV]], eV]]]]
  ];

seqArithAbsLowerThm =
  Module[{xV, aV, eV},
    xV = mkVar["x", realTy]; aV = mkVar["a", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, aV, eV},
        impTm[realLtTm[realAddTm[aV, realNegTm[eV]], xV],
          realLtTm[realNegTm[realAddTm[xV, realNegTm[aV]]], eV]]]]
  ];

seqArithSubSelfLtThm =
  Module[{sV, eV},
    sV = mkVar["s", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{sV, eV},
        impTm[realLtTm[zeroRealTm[], eV],
          realLtTm[realAddTm[sV, realNegTm[eV]], sV]]]]
  ];

seqArithSelfLtAddThm =
  Module[{sV, eV},
    sV = mkVar["s", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{sV, eV},
        impTm[realLtTm[zeroRealTm[], eV],
          realLtTm[sV, realAddTm[sV, eV]]]]]
  ];

seqArithLtLeContrThm =
  Module[{tV, sV},
    tV = mkVar["t", realTy]; sV = mkVar["s", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{tV, sV},
        seqImpList[{realLtTm[tV, sV], realLeTm[sV, tV]}, realLtTm[tV, tV]]]]
  ];

realAbsSubLtThm =
  Module[{xV, aV, eV, diff, hLeft, hRight, body},
    xV = mkVar["x", realTy]; aV = mkVar["a", realTy]; eV = mkVar["e", realTy];
    diff = realAddTm[xV, realNegTm[aV]];
    hLeft = ASSUME[realLtTm[realAddTm[aV, realNegTm[eV]], xV]];
    hRight = ASSUME[realLtTm[xV, realAddTm[aV, eV]]];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], diff]],
      Module[{hNonneg, absEq, diffLt},
        hNonneg = ASSUME[realLeTm[zeroRealTm[], diff]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[diff, realAbsPosThm], hNonneg];
        diffLt = HOL`Bool`MP[seqSpecAll[seqArithAbsUpperThm, {xV, aV, eV}], hRight];
        EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], diffLt]
      ],
      Module[{hNotNonneg, notLeLt, diffLt0, diffLe0, absEq, negDiffLt},
        hNotNonneg = ASSUME[notTm[realLeTm[zeroRealTm[], diff]]];
        notLeLt = HOL`Bool`SPEC[diff,
          HOL`Bool`SPEC[zeroRealTm[], HOL`Auto`RealArith`realNotLeLtThm]];
        diffLt0 = EQMP[notLeLt, hNotNonneg];
        diffLe0 = seqLtImpLeRule[diffLt0];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[diff, realAbsNonposThm], diffLe0];
        negDiffLt = HOL`Bool`MP[seqSpecAll[seqArithAbsLowerThm, {xV, aV, eV}], hLeft];
        EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], negDiffLt]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[aV, HOL`Bool`GEN[eV,
      HOL`Bool`DISCH[realLtTm[realAddTm[aV, realNegTm[eV]], xV],
        HOL`Bool`DISCH[realLtTm[xV, realAddTm[aV, eV]], body]]]]]
  ];

realSupLtMemThm =
  Module[{sV, tV, aV, uB, hneTm, hbndTm, goalTm, hne, hbnd, hLt, hNotGoal,
          aB, hSa, hNotLe, notLeLt, ltTa, conjA, exA, ffA, leAt, ubAll,
          least, badLt, ff, body},
    sV = mkVar["S", seqSetTy]; tV = mkVar["t", realTy];
    aV = mkVar["a", realTy]; uB = mkVar["u", realTy]; aB = mkVar["aB", realTy];
    hneTm = existsTm[aV, mkComb[sV, aV]];
    hbndTm = existsTm[uB,
      forallTm[aV, impTm[mkComb[sV, aV], realLeTm[aV, uB]]]];
    goalTm = existsTm[aV, conjTm[mkComb[sV, aV], realLtTm[tV, aV]]];
    hne = ASSUME[hneTm]; hbnd = ASSUME[hbndTm];
    hLt = ASSUME[realLtTm[tV, seqRealSup[sV]]];
    hNotGoal = ASSUME[notTm[goalTm]];
    hSa = ASSUME[mkComb[sV, aB]];
    hNotLe = ASSUME[notTm[realLeTm[aB, tV]]];
    notLeLt = HOL`Bool`SPEC[tV,
      HOL`Bool`SPEC[aB, HOL`Auto`RealArith`realNotLeLtThm]];
    ltTa = EQMP[notLeLt, hNotLe];
    conjA = HOL`Bool`CONJ[hSa, ltTa];
    exA = HOL`Bool`EXISTS[goalTm, aB, conjA];
    ffA = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotGoal], exA];
    leAt = HOL`Bool`CCONTR[realLeTm[aB, tV], ffA];
    ubAll = HOL`Bool`GEN[aB, HOL`Bool`DISCH[mkComb[sV, aB], leAt]];
    least = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realSupLeastThm, {sV, tV}], hne], hbnd], ubAll];
    badLt = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithLtLeContrThm, {tV, seqRealSup[sV]}], hLt], least];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[
      HOL`Bool`SPEC[tV, HOL`Auto`RealArith`realLtIrreflThm]], badLt];
    body = HOL`Bool`CCONTR[goalTm, ff];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[tV,
      HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm,
        HOL`Bool`DISCH[realLtTm[tV, seqRealSup[sV]], body]]]]]
  ];

monoIncTendstoSupThm =
  Module[{uV, range, sup, hMono, hBdd, monoAll, bddEx, bW, hAllB,
          nBdd, nonempty, bounded, supUpper, eV, hE, below, belowLtSup, memEx,
          aW, hMemConj, hRangeA, hBelowA, betaRangeA, exRangeN, nW, hEqA,
          hBelowUN, nV, hLeNn, monoStep, leUN, hLeft, hUNleSup, supLtPlus,
          hRight, absClose, impN, allN, exN, chosenN, chosenA, epsBody,
          tendBody, folded, chosenB},
    uV = mkVar["u", seqTy];
    range = seqRangeTm[uV]; sup = seqRealSup[range];
    hMono = ASSUME[monoIncTm[uV]]; hBdd = ASSUME[seqBddAboveTm[uV]];
    monoAll = EQMP[unfoldMonoInc[uV], hMono];
    bddEx = EQMP[unfoldSeqBddAbove[uV], hBdd];
    bW = mkVar["bW", realTy]; nBdd = mkVar["n", numTy];
    hAllB = ASSUME[forallTm[nBdd, realLeTm[mkComb[uV, nBdd], bW]]];
    nonempty = seqRangeNonemptyThm[range, uV];
    bounded = Module[{aB, wB, hRange, exNRange, nB, hEq, boundN, leAB, impA, allA},
      aB = mkVar["aB", realTy]; nB = mkVar["nB", numTy];
      wB = mkVar["wB", realTy];
      hRange = ASSUME[mkComb[range, aB]];
      exNRange = EQMP[HOL`Equal`BETACONV[mkComb[range, aB]], hRange];
      hEq = ASSUME[mkEq[aB, mkComb[uV, nB]]];
      boundN = HOL`Bool`SPEC[nB, hAllB];
      leAB = EQMP[HOL`Equal`SYM[seqRealLeCong[hEq, REFL[bW]]], boundN];
      impA = HOL`Bool`DISCH[mkComb[range, aB], HOL`Bool`CHOOSE[nB, exNRange, leAB]];
      allA = HOL`Bool`GEN[aB, impA];
      HOL`Bool`EXISTS[existsTm[wB,
        forallTm[aB, impTm[mkComb[range, aB], realLeTm[aB, wB]]]],
        bW, allA]
    ];
    supUpper = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[range, realSupUpperThm],
      nonempty], bounded];
    eV = mkVar["e", realTy];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    below = realAddTm[sup, realNegTm[eV]];
    belowLtSup = HOL`Bool`MP[seqSpecAll[seqArithSubSelfLtThm, {sup, eV}], hE];
    memEx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realSupLtMemThm, {range, below}], nonempty], bounded], belowLtSup];
    aW = mkVar["aW", realTy]; nW = mkVar["nW", numTy]; nV = mkVar["n", numTy];
    hMemConj = ASSUME[conjTm[mkComb[range, aW], realLtTm[below, aW]]];
    hRangeA = HOL`Bool`CONJUNCT1[hMemConj];
    hBelowA = HOL`Bool`CONJUNCT2[hMemConj];
    betaRangeA = HOL`Equal`BETACONV[mkComb[range, aW]];
    exRangeN = EQMP[betaRangeA, hRangeA];
    hEqA = ASSUME[mkEq[aW, mkComb[uV, nW]]];
    hBelowUN = EQMP[seqRealLtCong[REFL[below], hEqA], hBelowA];
    hLeNn = ASSUME[seqNatLe[nW, nV]];
    monoStep = HOL`Bool`MP[seqSpecAll[monoAll, {nW, nV}], hLeNn];
    leUN = monoStep;
    hLeft = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLtLeTransThm, {below, mkComb[uV, nW], mkComb[uV, nV]}],
      hBelowUN], leUN];
    hUNleSup = HOL`Bool`MP[HOL`Bool`SPEC[mkComb[uV, nV], supUpper],
      seqRangeMemThm[range, uV, nV]];
    supLtPlus = HOL`Bool`MP[seqSpecAll[seqArithSelfLtAddThm, {sup, eV}], hE];
    hRight = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeLtTransThm, {mkComb[uV, nV], sup, realAddTm[sup, eV]}],
      hUNleSup], supLtPlus];
    absClose = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realAbsSubLtThm, {mkComb[uV, nV], sup, eV}], hLeft], hRight];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], absClose];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[uV, sup, eV, mkVar["N", numTy]]],
      nW, allN];
    chosenN = HOL`Bool`CHOOSE[nW, exRangeN, exN];
    chosenA = HOL`Bool`CHOOSE[aW, memEx, chosenN];
    epsBody = HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosenA];
    tendBody = HOL`Bool`GEN[eV, epsBody];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[uV, sup]], tendBody];
    chosenB = HOL`Bool`CHOOSE[bW, bddEx, folded];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[monoIncTm[uV],
      HOL`Bool`DISCH[seqBddAboveTm[uV], chosenB]]]
  ];

monoConvergesIncThm =
  Module[{uV, hMono, hBdd, range, sup, tend, exThm},
    uV = mkVar["u", seqTy]; range = seqRangeTm[uV]; sup = seqRealSup[range];
    hMono = ASSUME[monoIncTm[uV]]; hBdd = ASSUME[seqBddAboveTm[uV]];
    tend = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uV, monoIncTendstoSupThm],
      hMono], hBdd];
    exThm = HOL`Bool`EXISTS[existsTm[mkVar["L", realTy], tendstoTm[uV, mkVar["L", realTy]]],
      sup, tend];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[monoIncTm[uV],
      HOL`Bool`DISCH[seqBddAboveTm[uV], exThm]]]
  ];

monoConvergesDecThm =
  Module[{uV, nV, vSeq, hDec, hBelow, decAll, monoV, belowEx, bW, hAllBelow,
          nBelow, bddAboveV, incEx, lW, hTendV, negTend, seqLeft, betaL, negNeg,
          pointEq, pointAll, seqEq, tendEq, tendU, exFinal, chosenL, chosenB},
    uV = mkVar["u", seqTy]; nV = mkVar["n", numTy];
    vSeq = mkAbs[nV, realNegTm[mkComb[uV, nV]]];
    hDec = ASSUME[monoDecTm[uV]]; hBelow = ASSUME[seqBddBelowTm[uV]];
    decAll = EQMP[unfoldMonoDec[uV], hDec];
    monoV = Module[{nA, mA, hLe, decLe, negLe, impNM, allM, allN},
      nA = mkVar["nA", numTy]; mA = mkVar["mA", numTy];
      hLe = ASSUME[seqNatLe[nA, mA]];
      decLe = HOL`Bool`MP[seqSpecAll[decAll, {nA, mA}], hLe];
      negLe = HOL`Bool`MP[
        seqSpecAll[realLeNegThm, {mkComb[uV, mA], mkComb[uV, nA]}], decLe];
      impNM = HOL`Bool`DISCH[seqNatLe[nA, mA], negLe];
      allM = HOL`Bool`GEN[mA, impNM];
      allN = HOL`Bool`GEN[nA, allM];
      EQMP[HOL`Equal`SYM[seqBetaClean[unfoldMonoInc[vSeq]]], allN]
    ];
    belowEx = EQMP[unfoldSeqBddBelow[uV], hBelow];
    bW = mkVar["bW", realTy]; nBelow = mkVar["n", numTy];
    hAllBelow = ASSUME[forallTm[nBelow, realLeTm[bW, mkComb[uV, nBelow]]]];
    bddAboveV = Module[{nA, lower, negLe, allN, cleanUnfold, exB},
      nA = mkVar["nA", numTy];
      lower = HOL`Bool`SPEC[nA, hAllBelow];
      negLe = HOL`Bool`MP[
        seqSpecAll[realLeNegThm, {bW, mkComb[uV, nA]}], lower];
      allN = HOL`Bool`GEN[nA, negLe];
      cleanUnfold = seqBetaClean[unfoldSeqBddAbove[vSeq]];
      exB = HOL`Bool`EXISTS[concl[cleanUnfold][[2]], realNegTm[bW], allN];
      EQMP[HOL`Equal`SYM[cleanUnfold], exB]
    ];
    incEx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[vSeq, monoConvergesIncThm],
      monoV], bddAboveV];
    lW = mkVar["lW", realTy];
    hTendV = ASSUME[tendstoTm[vSeq, lW]];
    negTend = seqBetaClean[HOL`Bool`MP[seqSpecAll[tendstoNegThm, {vSeq, lW}], hTendV]];
    seqLeft = concl[negTend][[1, 2]];
    betaL = HOL`Equal`BETACONV[mkComb[seqLeft, nV]];
    negNeg = HOL`Bool`SPEC[mkComb[uV, nV], realNegNegThm];
    pointEq = TRANS[betaL, negNeg];
    pointAll = HOL`Bool`GEN[nV, pointEq];
    seqEq = HOL`Stdlib`List`funcExtThm[seqLeft, uV, pointAll];
    tendEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[tendstoConst[], seqEq],
      REFL[realNegTm[lW]]];
    tendU = EQMP[tendEq, negTend];
    exFinal = HOL`Bool`EXISTS[existsTm[mkVar["L", realTy], tendstoTm[uV, mkVar["L", realTy]]],
      realNegTm[lW], tendU];
    chosenL = HOL`Bool`CHOOSE[lW, incEx, exFinal];
    chosenB = HOL`Bool`CHOOSE[bW, belowEx, chosenL];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[monoDecTm[uV],
      HOL`Bool`DISCH[seqBddBelowTm[uV], chosenB]]]
  ];

End[];
EndPackage[];
