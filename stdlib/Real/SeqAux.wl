(* M8.2 / stdlib/Real/SeqAux.wl - dyadic sequence prerequisites. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`Arith`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

dyadicDefThm::usage = "dyadicDefThm - epsilon-selected num recursion for dyadic powers of two.";
dyadicConst::usage = "dyadicConst[] - dyadic : num -> real.";
dyadicTm::usage = "dyadicTm[n] - builds dyadic n.";
unfoldDyadic::usage = "unfoldDyadic[] - proves the deep-beta-reduced dyadic definition.";
dyadicRecSpecThm::usage = "dyadicRecSpecThm - |- dyadic 0 = 1 /\\ forall n. dyadic (SUC n) = realMul (dyadic n) 2.";
dyadicZeroThm::usage = "dyadicZeroThm - |- dyadic 0 = 1.";
dyadicSuccThm::usage = "dyadicSuccThm - |- forall n. dyadic (SUC n) = realMul (dyadic n) 2.";
dyadicSuccAddThm::usage = "dyadicSuccAddThm - |- forall n. dyadic (SUC n) = realAdd (dyadic n) (dyadic n).";
dyadicPosThm::usage = "dyadicPosThm - |- forall n. realLt 0 (dyadic n).";
dyadicNeZeroThm::usage = "dyadicNeZeroThm - |- forall n. ~(dyadic n = 0).";
oneLeDyadicThm::usage = "oneLeDyadicThm - |- forall n. realLe 1 (dyadic n).";
natLeDyadicThm::usage = "natLeDyadicThm - |- forall n. realLe (&R (&Q (&Z n))) (dyadic n).";
existsDyadicGtThm::usage = "existsDyadicGtThm - |- forall x. exists n. realLt x (dyadic n).";
dyadicArchThm::usage = "dyadicArchThm - |- forall L eps. realLe 0 L ==> realLt 0 eps ==> exists n. realLt (realMul L (realInv (dyadic n))) eps.";
intervalPointsCloseThm::usage = "intervalPointsCloseThm - |- forall a b x y eps. a <= x ==> x <= b ==> a <= y ==> y <= b ==> b - a < eps ==> abs (x - y) < eps.";
lengthLtOfCloseThm::usage = "lengthLtOfCloseThm - |- forall a b eps. a <= b ==> abs ((b - a) - 0) < eps ==> b - a < eps.";

Begin["`Private`"];

seqAuxDyadicTy = tyFun[numTy, realTy];

seqAuxTwoNat[] := sucT[sucT[zeroN[]]];
seqAuxOneReal[] := realOfRatTm[oneQ[]];
seqAuxTwoReal[] := realOfRatTm[ratOfIntTm[intOfNumTm[seqAuxTwoNat[]]]];
seqAuxNatReal[nT_] := realOfRatTm[ratOfIntTm[intOfNumTm[nT]]];
seqAuxRealInv[xT_] := mkComb[realInvConst[], xT];
seqAuxRealAbs[xT_] := mkComb[realAbsConst[], xT];
seqAuxSelectTm[ty_, predT_] := mkComb[mkConst["@", tyFun[tyFun[ty, boolTy], ty]], predT];

seqAuxSpecAll[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

seqAuxBetaClean[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

seqAuxForallList[vs_List, body_] :=
  Fold[Function[{acc, v}, forallTm[v, acc]], body, Reverse[vs]];

seqAuxImpList[hs_List, body_] :=
  Fold[Function[{acc, h}, impTm[h, acc]], body, Reverse[hs]];

seqAuxRealLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqLeft], eqRight];

seqAuxRealLtCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], eqLeft], eqRight];

seqAuxRealMulCongLeft[eq_, cT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realMulConst[], eq], REFL[cT]];

seqAuxRealMulCongRight[cT_, eq_] :=
  HOL`Equal`APTERM[mkComb[realMulConst[], cT], eq];

seqAuxLtImpLeRule[ltTh_] :=
  Module[{aT, bT},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]];
    HOL`Bool`MP[seqAuxSpecAll[realLtImpLeThm, {aT, bT}], ltTh]
  ];

seqAuxLeTransRule[leAB_, leBC_] :=
  Module[{aT, bT, cT},
    aT = concl[leAB][[1, 2]]; bT = concl[leAB][[2]]; cT = concl[leBC][[2]];
    HOL`Bool`MP[HOL`Bool`MP[seqAuxSpecAll[realLeTransThm, {aT, bT, cT}],
      leAB], leBC]
  ];

seqAuxLtLeTransRule[ltAB_, leBC_] :=
  Module[{aT, bT, cT},
    aT = concl[ltAB][[1, 2]]; bT = concl[ltAB][[2]]; cT = concl[leBC][[2]];
    HOL`Bool`MP[HOL`Bool`MP[seqAuxSpecAll[realLtLeTransThm, {aT, bT, cT}],
      ltAB], leBC]
  ];

seqAuxMulLtRightRule[ltTh_, cPos_] :=
  Module[{aT, bT, cT, mono, leftComm, rightComm},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]]; cT = concl[cPos][[2]];
    mono = HOL`Bool`MP[HOL`Bool`MP[seqAuxSpecAll[realLtMulMonoThm, {aT, bT, cT}],
      cPos], ltTh];
    leftComm = HOL`Bool`SPEC[aT, HOL`Bool`SPEC[cT, realMulCommThm]];
    rightComm = HOL`Bool`SPEC[bT, HOL`Bool`SPEC[cT, realMulCommThm]];
    EQMP[seqAuxRealLtCong[leftComm, rightComm], mono]
  ];

seqAuxDyadicStepFun[] :=
  Module[{xIt},
    xIt = mkVar["xIt", realTy];
    mkAbs[xIt, realMulTm[xIt, seqAuxTwoReal[]]]
  ];

seqAuxDyadicRecPred[] :=
  Module[{gIt, nW, fT},
    gIt = mkVar["gIt", seqAuxDyadicTy]; nW = mkVar["nW", numTy];
    fT = seqAuxDyadicStepFun[];
    mkAbs[gIt, conjTm[mkEq[mkComb[gIt, zeroN[]], seqAuxOneReal[]],
      forallTm[nW, mkEq[mkComb[gIt, sucT[nW]], mkComb[fT, mkComb[gIt, nW]]]]]]
  ];

dyadicDefThm =
  newDefinition[mkEq[mkVar["dyadic", seqAuxDyadicTy],
    seqAuxSelectTm[seqAuxDyadicTy, seqAuxDyadicRecPred[]]]];

dyadicConst[] := mkConst["dyadic", seqAuxDyadicTy];
dyadicTm[nT_] := mkComb[dyadicConst[], nT];

unfoldDyadic[] := seqAuxBetaClean[dyadicDefThm];

dyadicRecSpecThm =
  Module[{iter, exIter, sat, folded},
    iter = HOL`Kernel`INSTTYPE[{tyVar["A"] -> realTy}, HOL`Stdlib`Num`numIterationThm];
    exIter = seqAuxBetaClean[
      HOL`Bool`SPEC[seqAuxDyadicStepFun[], HOL`Bool`SPEC[seqAuxOneReal[], iter]]];
    sat = HOL`Stdlib`Num`selectOfExists[seqAuxDyadicRecPred[], exIter];
    folded = seqAuxBetaClean[HOL`Drule`SUBS[{HOL`Equal`SYM[unfoldDyadic[]]}, sat]];
    folded
  ];

dyadicZeroThm = HOL`Bool`CONJUNCT1[dyadicRecSpecThm];
dyadicSuccThm = HOL`Bool`CONJUNCT2[dyadicRecSpecThm];

seqAuxZeroLtOneThm =
  HOL`Auto`RealArith`realArithProve[realLtTm[zeroRealTm[], seqAuxOneReal[]]];

seqAuxZeroLtTwoThm =
  HOL`Auto`RealArith`realArithProve[realLtTm[zeroRealTm[], seqAuxTwoReal[]]];

seqAuxZeroLeOneThm =
  HOL`Auto`RealArith`realArithProve[realLeTm[zeroRealTm[], seqAuxOneReal[]]];

seqAuxMulTwoAddThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, mkEq[realMulTm[xV, seqAuxTwoReal[]], realAddTm[xV, xV]]]]
  ];

seqAuxLeSelfAddThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, impTm[realLeTm[zeroRealTm[], xV],
        realLeTm[xV, realAddTm[xV, xV]]]]]
  ];

seqAuxNatSucRealThm =
  Module[{kV, sucKnatEq, sucZeq, sucQeq, sucReq},
    kV = mkVar["k", numTy];
    sucKnatEq = HOL`Equal`SYM[TRANS[
      HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[kV, HOL`Stdlib`Num`plusSucEqThm]],
      HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[],
        HOL`Bool`SPEC[kV, HOL`Stdlib`Num`plusZeroEqThm]]]];
    sucZeq = TRANS[HOL`Equal`APTERM[intOfNumC[], sucKnatEq],
      HOL`Bool`SPEC[sucT[zeroN[]], HOL`Bool`SPEC[kV,
        HOL`Stdlib`Int`intOfNumAddThm]]];
    sucQeq = TRANS[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratOfIntConst[], sucZeq],
      HOL`Bool`SPEC[intOfNumTm[sucT[zeroN[]]], HOL`Bool`SPEC[intOfNumTm[kV],
        HOL`Stdlib`Rat`ratOfIntAddThm]]];
    sucReq = TRANS[HOL`Equal`APTERM[realOfRatConst[], sucQeq],
      HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[ratOfIntTm[intOfNumTm[kV]],
        realOfRatAddThm]]];
    HOL`Bool`GEN[kV, sucReq]
  ];

dyadicSuccAddThm =
  Module[{nV, succEq, mulTwoEq},
    nV = mkVar["n", numTy];
    succEq = HOL`Bool`SPEC[nV, dyadicSuccThm];
    mulTwoEq = HOL`Bool`SPEC[dyadicTm[nV], seqAuxMulTwoAddThm];
    HOL`Bool`GEN[nV, TRANS[succEq, mulTwoEq]]
  ];

dyadicPosThm =
  Module[{nInd, pLam, baseRaw, base, ihTm, ih, stepMul, stepEq, step,
          stepAll, indSpec},
    nInd = mkVar["nInd", numTy];
    pLam = mkAbs[nInd, realLtTm[zeroRealTm[], dyadicTm[nInd]]];
    baseRaw = seqAuxZeroLtOneThm;
    base = EQMP[seqAuxRealLtCong[REFL[zeroRealTm[]], HOL`Equal`SYM[dyadicZeroThm]],
      baseRaw];
    ihTm = realLtTm[zeroRealTm[], dyadicTm[nInd]]; ih = ASSUME[ihTm];
    stepMul = HOL`Bool`MP[HOL`Bool`MP[
      seqAuxSpecAll[realLtMulPosThm, {dyadicTm[nInd], seqAuxTwoReal[]}],
      ih], seqAuxZeroLtTwoThm];
    stepEq = HOL`Bool`SPEC[nInd, dyadicSuccThm];
    step = EQMP[seqAuxRealLtCong[REFL[zeroRealTm[]], HOL`Equal`SYM[stepEq]], stepMul];
    stepAll = HOL`Bool`GEN[nInd, HOL`Bool`DISCH[ihTm, step]];
    indSpec = seqAuxBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]]
  ];

dyadicNeZeroThm =
  Module[{nV, pos, ne},
    nV = mkVar["n", numTy];
    pos = HOL`Bool`SPEC[nV, dyadicPosThm];
    ne = HOL`Bool`MP[HOL`Bool`SPEC[dyadicTm[nV], seqArithPosNeZeroThm], pos];
    HOL`Bool`GEN[nV, ne]
  ];

oneLeDyadicThm =
  Module[{nInd, pLam, base, ihTm, ih, pos, nonneg, leSelfAdd, succAdd,
          leStep, step, stepAll, indSpec},
    nInd = mkVar["nInd", numTy];
    pLam = mkAbs[nInd, realLeTm[seqAuxOneReal[], dyadicTm[nInd]]];
    base = EQMP[seqAuxRealLeCong[REFL[seqAuxOneReal[]],
      HOL`Equal`SYM[dyadicZeroThm]], HOL`Bool`SPEC[seqAuxOneReal[], realLeReflThm]];
    ihTm = realLeTm[seqAuxOneReal[], dyadicTm[nInd]]; ih = ASSUME[ihTm];
    pos = HOL`Bool`SPEC[nInd, dyadicPosThm];
    nonneg = seqAuxLtImpLeRule[pos];
    leSelfAdd = HOL`Bool`MP[HOL`Bool`SPEC[dyadicTm[nInd], seqAuxLeSelfAddThm],
      nonneg];
    succAdd = HOL`Bool`SPEC[nInd, dyadicSuccAddThm];
    leStep = EQMP[seqAuxRealLeCong[REFL[dyadicTm[nInd]], HOL`Equal`SYM[succAdd]],
      leSelfAdd];
    step = seqAuxLeTransRule[ih, leStep];
    stepAll = HOL`Bool`GEN[nInd, HOL`Bool`DISCH[ihTm, step]];
    indSpec = seqAuxBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]]
  ];

natLeDyadicThm =
  Module[{nInd, pLam, base, ihTm, ih, natSuc, oneLe, addLe, succAdd,
          step, stepAll, indSpec},
    nInd = mkVar["nInd", numTy];
    pLam = mkAbs[nInd, realLeTm[seqAuxNatReal[nInd], dyadicTm[nInd]]];
    base = EQMP[seqAuxRealLeCong[REFL[seqAuxNatReal[zeroN[]]],
      HOL`Equal`SYM[dyadicZeroThm]], seqAuxZeroLeOneThm];
    ihTm = realLeTm[seqAuxNatReal[nInd], dyadicTm[nInd]]; ih = ASSUME[ihTm];
    natSuc = HOL`Bool`SPEC[nInd, seqAuxNatSucRealThm];
    oneLe = HOL`Bool`SPEC[nInd, oneLeDyadicThm];
    addLe = HOL`Bool`MP[HOL`Bool`MP[
      seqAuxSpecAll[HOL`Auto`RealArith`realLeAddMono2Thm,
        {seqAuxNatReal[nInd], dyadicTm[nInd], seqAuxOneReal[], dyadicTm[nInd]}],
      ih], oneLe];
    succAdd = HOL`Bool`SPEC[nInd, dyadicSuccAddThm];
    step = EQMP[seqAuxRealLeCong[HOL`Equal`SYM[natSuc], HOL`Equal`SYM[succAdd]],
      addLe];
    stepAll = HOL`Bool`GEN[nInd, HOL`Bool`DISCH[ihTm, step]];
    indSpec = seqAuxBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]]
  ];

existsDyadicGtThm =
  Module[{xV, nW, arch, hArchTm, hArch, natLe, ltDy, ex},
    xV = mkVar["x", realTy]; nW = mkVar["nW", numTy];
    arch = HOL`Bool`SPEC[xV, realArchThm];
    hArchTm = realLtTm[xV, seqAuxNatReal[nW]]; hArch = ASSUME[hArchTm];
    natLe = HOL`Bool`SPEC[nW, natLeDyadicThm];
    ltDy = seqAuxLtLeTransRule[hArch, natLe];
    ex = HOL`Bool`EXISTS[existsTm[nW, realLtTm[xV, dyadicTm[nW]]], nW, ltDy];
    HOL`Bool`GEN[xV, HOL`Bool`CHOOSE[nW, arch, ex]]
  ];

seqAuxCancelRightInvEqOne[xT_, yT_, yNe0_] :=
  Module[{comm, invLaw},
    comm = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[seqAuxRealInv[yT], realMulCommThm]];
    invLaw = HOL`Bool`MP[HOL`Bool`SPEC[yT, realMulInvThm], yNe0];
    TRANS[comm, invLaw]
  ];

seqAuxRightCancelInv[leftT_, yT_, yNe0_] :=
  Module[{assoc, cancel, one},
    assoc = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[seqAuxRealInv[yT],
      HOL`Bool`SPEC[leftT, realMulAssocThm]]];
    cancel = seqAuxCancelRightInvEqOne[leftT, yT, yNe0];
    one = HOL`Bool`SPEC[leftT, realMulOneThm];
    TRANS[assoc, TRANS[seqAuxRealMulCongRight[leftT, cancel], one]]
  ];

dyadicArchThm =
  Module[{lV, epsV, nW, hLTm, hEpsTm, hL, hEps, xT, exDy, hDyTm, hDy,
          epsNe0, epsPosInv, mulLt, leftCancel, hLLtDEps, dT, dPos, dNe0,
          invD, invDPos, finalLtRaw, rhsCommL, rhsAssoc, rhsInv, rhsCongR,
          rhsOne, rhsEq, finalLt, exN, body},
    lV = mkVar["L", realTy]; epsV = mkVar["eps", realTy]; nW = mkVar["nW", numTy];
    hLTm = realLeTm[zeroRealTm[], lV]; hEpsTm = realLtTm[zeroRealTm[], epsV];
    hL = ASSUME[hLTm]; hEps = ASSUME[hEpsTm];
    xT = realMulTm[lV, seqAuxRealInv[epsV]];
    exDy = HOL`Bool`SPEC[xT, existsDyadicGtThm];
    hDyTm = realLtTm[xT, dyadicTm[nW]]; hDy = ASSUME[hDyTm];
    epsNe0 = HOL`Bool`MP[HOL`Bool`SPEC[epsV, seqArithPosNeZeroThm], hEps];
    epsPosInv = HOL`Bool`MP[HOL`Bool`SPEC[epsV, seqRealInvPositiveThm], hEps];
    mulLt = seqAuxMulLtRightRule[hDy, hEps];
    leftCancel = seqAuxRightCancelInv[lV, epsV, epsNe0];
    hLLtDEps = EQMP[seqAuxRealLtCong[leftCancel, REFL[realMulTm[dyadicTm[nW], epsV]]],
      mulLt];
    dT = dyadicTm[nW]; dPos = HOL`Bool`SPEC[nW, dyadicPosThm];
    dNe0 = HOL`Bool`SPEC[nW, dyadicNeZeroThm];
    invD = seqAuxRealInv[dT];
    invDPos = HOL`Bool`MP[HOL`Bool`SPEC[dT, seqRealInvPositiveThm], dPos];
    finalLtRaw = seqAuxMulLtRightRule[hLLtDEps, invDPos];
    (* finalLtRaw : L·invD < ((dyadic n)·eps)·invD; rewrite the RHS to eps:
       ((dyadic n)·eps)·invD = (eps·(dyadic n))·invD = eps·((dyadic n)·invD)
        = eps·1 = eps. *)
    rhsCommL = seqAuxRealMulCongLeft[
      HOL`Bool`SPEC[epsV, HOL`Bool`SPEC[dT, realMulCommThm]], invD];
    rhsAssoc = HOL`Bool`SPEC[invD, HOL`Bool`SPEC[dT,
      HOL`Bool`SPEC[epsV, realMulAssocThm]]];
    rhsInv = HOL`Bool`MP[HOL`Bool`SPEC[dT, realMulInvThm], dNe0];
    rhsCongR = seqAuxRealMulCongRight[epsV, rhsInv];
    rhsOne = HOL`Bool`SPEC[epsV, realMulOneThm];
    rhsEq = TRANS[rhsCommL, TRANS[rhsAssoc, TRANS[rhsCongR, rhsOne]]];
    finalLt = EQMP[seqAuxRealLtCong[REFL[realMulTm[lV, invD]], rhsEq],
      finalLtRaw];
    exN = HOL`Bool`EXISTS[existsTm[nW,
      realLtTm[realMulTm[lV, seqAuxRealInv[dyadicTm[nW]]], epsV]], nW, finalLt];
    body = HOL`Bool`CHOOSE[nW, exDy, exN];
    HOL`Bool`GEN[lV, HOL`Bool`GEN[epsV,
      HOL`Bool`DISCH[hLTm, HOL`Bool`DISCH[hEpsTm, body]]]]
  ];

seqAuxIntervalLowerThm =
  Module[{aV, bV, xV, yV, epsV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; xV = mkVar["x", realTy];
    yV = mkVar["y", realTy]; epsV = mkVar["eps", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqAuxForallList[{aV, bV, xV, yV, epsV},
        seqAuxImpList[{realLeTm[aV, xV], realLeTm[xV, bV],
          realLeTm[aV, yV], realLeTm[yV, bV],
          realLtTm[realAddTm[bV, realNegTm[aV]], epsV]},
          realLtTm[realAddTm[yV, realNegTm[epsV]], xV]]]]
  ];

seqAuxIntervalUpperThm =
  Module[{aV, bV, xV, yV, epsV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; xV = mkVar["x", realTy];
    yV = mkVar["y", realTy]; epsV = mkVar["eps", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqAuxForallList[{aV, bV, xV, yV, epsV},
        seqAuxImpList[{realLeTm[aV, xV], realLeTm[xV, bV],
          realLeTm[aV, yV], realLeTm[yV, bV],
          realLtTm[realAddTm[bV, realNegTm[aV]], epsV]},
          realLtTm[xV, realAddTm[yV, epsV]]]]]
  ];

intervalPointsCloseThm =
  Module[{aV, bV, xV, yV, epsV, hAxTm, hXbTm, hAyTm, hYbTm, hLenTm,
          hAx, hXb, hAy, hYb, hLen, lower, upper, close},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; xV = mkVar["x", realTy];
    yV = mkVar["y", realTy]; epsV = mkVar["eps", realTy];
    hAxTm = realLeTm[aV, xV]; hXbTm = realLeTm[xV, bV];
    hAyTm = realLeTm[aV, yV]; hYbTm = realLeTm[yV, bV];
    hLenTm = realLtTm[realAddTm[bV, realNegTm[aV]], epsV];
    hAx = ASSUME[hAxTm]; hXb = ASSUME[hXbTm]; hAy = ASSUME[hAyTm];
    hYb = ASSUME[hYbTm]; hLen = ASSUME[hLenTm];
    lower = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`MP[seqAuxSpecAll[seqAuxIntervalLowerThm,
        {aV, bV, xV, yV, epsV}], hAx], hXb], hAy], hYb], hLen];
    upper = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`MP[seqAuxSpecAll[seqAuxIntervalUpperThm,
        {aV, bV, xV, yV, epsV}], hAx], hXb], hAy], hYb], hLen];
    close = HOL`Bool`MP[HOL`Bool`MP[
      seqAuxSpecAll[realAbsSubLtThm, {xV, yV, epsV}], lower], upper];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`GEN[epsV, HOL`Bool`DISCH[hAxTm, HOL`Bool`DISCH[hXbTm,
        HOL`Bool`DISCH[hAyTm, HOL`Bool`DISCH[hYbTm,
          HOL`Bool`DISCH[hLenTm, close]]]]]]]]]]
  ];

seqAuxLengthNonnegThm =
  Module[{aV, bV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqAuxForallList[{aV, bV},
        impTm[realLeTm[aV, bV],
          realLeTm[zeroRealTm[], realAddTm[bV, realNegTm[aV]]]]]]
  ];

seqAuxDropZeroThm =
  Module[{zV},
    zV = mkVar["z", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[zV, mkEq[realAddTm[zV, realNegTm[zeroRealTm[]]], zV]]]
  ];

lengthLtOfCloseThm =
  Module[{aV, bV, epsV, len, hLeTm, hCloseTm, hLe, hClose, lenNonneg,
          dropZero, absDrop, absPos, absEq, body},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; epsV = mkVar["eps", realTy];
    len = realAddTm[bV, realNegTm[aV]];
    hLeTm = realLeTm[aV, bV];
    hCloseTm = realLtTm[seqAuxRealAbs[realAddTm[len, realNegTm[zeroRealTm[]]]], epsV];
    hLe = ASSUME[hLeTm]; hClose = ASSUME[hCloseTm];
    lenNonneg = HOL`Bool`MP[seqAuxSpecAll[seqAuxLengthNonnegThm, {aV, bV}], hLe];
    dropZero = HOL`Bool`SPEC[len, seqAuxDropZeroThm];
    absDrop = HOL`Equal`APTERM[realAbsConst[], dropZero];
    absPos = HOL`Bool`MP[HOL`Bool`SPEC[len, realAbsPosThm], lenNonneg];
    absEq = TRANS[absDrop, absPos];
    body = EQMP[seqAuxRealLtCong[absEq, REFL[epsV]], hClose];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[epsV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hCloseTm, body]]]]]
  ];

End[];
EndPackage[];
