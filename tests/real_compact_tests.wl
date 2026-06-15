(* ::Package:: *)

(* Tests for M8.2 stdlib/Real/Compact.wl - sequential compactness. *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Drule`"];
Needs["HOL`Stdlib`Pair`"];
Needs["HOL`Stdlib`Num`"];
Needs["HOL`Stdlib`Int`"];
Needs["HOL`Stdlib`Rat`"];
Needs["HOL`Stdlib`Real`"];
Needs["HOL`Auto`Arith`"];
Needs["HOL`Auto`RealArith`"];

numTyRCT = mkType["num", {}];
realTyRCT = mkType["real", {}];
seqTyRCT = tyFun[numTyRCT, realTyRCT];
numFunTyRCT = tyFun[numTyRCT, numTyRCT];
realListTyRCT = HOL`Stdlib`List`listTy[realTyRCT];
setTyRCT = tyFun[realTyRCT, boolTy];
iotaTyRCT = mkVarType["iota"];
iotaListTyRCT = HOL`Stdlib`List`listTy[iotaTyRCT];
intervalTyRCT = tyFun[realTyRCT, tyFun[realTyRCT, setTyRCT]];
isOpenTyRCT = tyFun[setTyRCT, boolTy];
coverTyRCT = tyFun[iotaTyRCT, setTyRCT];
coversTyRCT = tyFun[coverTyRCT, tyFun[setTyRCT, boolTy]];
listSubcoverTyRCT = tyFun[coverTyRCT,
  tyFun[setTyRCT, tyFun[iotaListTyRCT, boolTy]]];
midpointTyRCT = tyFun[realTyRCT, tyFun[realTyRCT, realTyRCT]];
noFiniteSubcoverTyRCT = tyFun[coverTyRCT,
  tyFun[realTyRCT, tyFun[realTyRCT, boolTy]]];
pairTyRCT = HOL`Stdlib`Pair`prodTy[realTyRCT, realTyRCT];
badIntervalTyRCT = noFiniteSubcoverTyRCT;
stepIntervalTyRCT = tyFun[coverTyRCT, tyFun[pairTyRCT, pairTyRCT]];
bisectIntervalTyRCT = tyFun[coverTyRCT,
  tyFun[realTyRCT, tyFun[realTyRCT, tyFun[numTyRCT, pairTyRCT]]]];
lowerTyRCT = tyFun[coverTyRCT,
  tyFun[realTyRCT, tyFun[realTyRCT, tyFun[numTyRCT, realTyRCT]]]];

zeroNumRCT[] := HOL`Stdlib`Num`zeroConst[];
sucNumRCT[n_] := mkComb[HOL`Stdlib`Num`sucConst[], n];
oneNumRCT[] := sucNumRCT[zeroNumRCT[]];
twoNumRCT[] := sucNumRCT[oneNumRCT[]];
intOfNumRCT[n_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], n];
ratOfIntRCT[z_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], z];
realOfRatRCT[q_] := mkComb[HOL`Stdlib`Real`realOfRatConst[], q];
natRealRCT[n_] := realOfRatRCT[ratOfIntRCT[intOfNumRCT[n]]];
zeroRealRCT[] := mkComb[HOL`Stdlib`Real`realOfRatConst[],
  mkComb[HOL`Stdlib`Rat`ratOfIntConst[],
    mkComb[HOL`Stdlib`Int`intOfNumConst[], zeroNumRCT[]]]];
oneRealRCT[] := natRealRCT[oneNumRCT[]];
twoRealRCT[] := natRealRCT[twoNumRCT[]];
realAddRCT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], x], y];
realNegRCT[x_] := mkComb[HOL`Stdlib`Real`realNegConst[], x];
realMulRCT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realMulConst[], x], y];
realInvRCT[x_] := mkComb[HOL`Stdlib`Real`realInvConst[], x];
realAbsRCT[x_] := mkComb[HOL`Stdlib`Real`realAbsConst[], x];
rLeRCT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], a], b];
rLtRCT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], a], b];
andRCT[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
orRCT[p_, q_] := mkComb[
  mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impRCT[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
notRCT[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
forallRCT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
existsRCT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
memRCT[x_, xs_] := mkComb[
  mkComb[mkConst["MEM", tyFun[realTyRCT, tyFun[realListTyRCT, boolTy]]], x], xs];
nilRealRCT[] := mkConst["NIL", realListTyRCT];
consRealRCT[] := mkConst["CONS", tyFun[realTyRCT,
  tyFun[realListTyRCT, realListTyRCT]]];
memIotaRCT[i_, js_] := mkComb[
  mkComb[mkConst["MEM", tyFun[iotaTyRCT, tyFun[iotaListTyRCT, boolTy]]], i], js];
nilIotaRCT[] := mkConst["NIL", iotaListTyRCT];
consIotaRCT[x_, xs_] := mkComb[
  mkComb[mkConst["CONS", tyFun[iotaTyRCT, tyFun[iotaListTyRCT, iotaListTyRCT]]], x],
  xs];
appendIotaRCT[xs_, ys_] := mkComb[
  mkComb[mkConst["APPEND", tyFun[iotaListTyRCT, tyFun[iotaListTyRCT, iotaListTyRCT]]],
    xs], ys];
pairRCT[a_, b_] := mkComb[
  mkComb[mkConst[",", tyFun[realTyRCT, tyFun[realTyRCT, pairTyRCT]]], a], b];
fstRCT[p_] := mkComb[mkConst["FST", tyFun[pairTyRCT, realTyRCT]], p];
sndRCT[p_] := mkComb[mkConst["SND", tyFun[pairTyRCT, realTyRCT]], p];
condRCT[ty_, c_, a_, b_] := mkComb[
  mkComb[mkComb[HOL`Bool`condConst[ty], c], a], b];

specAllRCT[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

listInstIotaRCT[th_] := HOL`Kernel`INSTTYPE[{mkVarType["A"] -> iotaTyRCT}, th];

memConsIotaEqRCT[x_, y_, xs_] :=
  specAllRCT[listInstIotaRCT[HOL`Stdlib`List`memConsThm], {x, y, xs}];

betaCleanRCT[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

assertConclRCT[name_, th_, expected_] := (
  HOLTest`assertTrue[isThm[th], name <> " is thm"];
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

constSeqRCT[cT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRCT];
    mkAbs[nV, cT]
  ];

seqBoundedAllRCT[uT_, loT_, hiT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRCT];
    forallRCT[nV, andRCT[
      rLeRCT[loT, mkComb[uT, nV]],
      rLeRCT[mkComb[uT, nV], hiT]]]
  ];

seqBoundedBodyRCT[uT_] :=
  Module[{loV, hiV},
    loV = mkVar["lo", realTyRCT]; hiV = mkVar["hi", realTyRCT];
    existsRCT[loV, existsRCT[hiV, seqBoundedAllRCT[uT, loV, hiV]]]
  ];

hasConvergentSubseqBodyRCT[uT_, lT_] :=
  Module[{phiV, subSeq},
    phiV = mkVar["phi", numFunTyRCT];
    subSeq = HOL`Stdlib`Real`subsequenceTm[uT, phiV];
    existsRCT[phiV, andRCT[HOL`Stdlib`Real`subseqIndexTm[phiV],
      HOL`Stdlib`Real`tendstoTm[subSeq, lT]]]
  ];

bwGoalRCT[uT_] :=
  Module[{lV},
    lV = mkVar["l", realTyRCT];
    existsRCT[lV, HOL`Stdlib`Real`hasConvergentSubseqTm[uT, lV]]
  ];

monoSubseqBodyRCT[uT_, phiT_] :=
  Module[{subSeq},
    subSeq = HOL`Stdlib`Real`subsequenceTm[uT, phiT];
    andRCT[HOL`Stdlib`Real`subseqIndexTm[phiT],
      orRCT[HOL`Stdlib`Real`monoIncTm[subSeq], HOL`Stdlib`Real`monoDecTm[subSeq]]]
  ];

listInfiniteBodyRCT[sT_] :=
  Module[{xsV, xV},
    xsV = mkVar["xs", realListTyRCT]; xV = mkVar["x", realTyRCT];
    forallRCT[xsV, existsRCT[xV, andRCT[mkComb[sT, xV], notRCT[memRCT[xV, xsV]]]]]
  ];

setBoundedBodyRCT[sT_] :=
  Module[{loV, hiV, xV},
    loV = mkVar["lo", realTyRCT]; hiV = mkVar["hi", realTyRCT];
    xV = mkVar["x", realTyRCT];
    existsRCT[loV, existsRCT[hiV, forallRCT[xV,
      impRCT[mkComb[sT, xV], andRCT[rLeRCT[loV, xV], rLeRCT[xV, hiV]]]]]]
  ];

distBodyRCT[yT_, xT_] :=
  realAbsRCT[realAddRCT[yT, realNegRCT[xT]]];

accumulationBodyRCT[sT_, xT_] :=
  Module[{epsV, yV},
    epsV = mkVar["eps", realTyRCT]; yV = mkVar["y", realTyRCT];
    forallRCT[epsV, impRCT[rLtRCT[zeroRealRCT[], epsV],
      existsRCT[yV, andRCT[mkComb[sT, yV],
        andRCT[notRCT[mkEq[yV, xT]],
          rLtRCT[HOL`Stdlib`Real`distTm[yV, xT], epsV]]]]]]
  ];

freshListRecBodyRCT[sT_] :=
  Module[{nV, fl, fs},
    nV = mkVar["n", numTyRCT];
    fl = HOL`Stdlib`Real`freshListTm[sT]; fs = HOL`Stdlib`Real`freshSeqTm[sT];
    andRCT[mkEq[mkComb[fl, zeroNumRCT[]], nilRealRCT[]],
      forallRCT[nV, mkEq[mkComb[fl, sucNumRCT[nV]],
        mkComb[mkComb[consRealRCT[], mkComb[fs, nV]], mkComb[fl, nV]]]]]
  ];

freshSeqMemBodyRCT[sT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRCT];
    forallRCT[nV, mkComb[sT, mkComb[HOL`Stdlib`Real`freshSeqTm[sT], nV]]]
  ];

freshSeqNeBodyRCT[sT_] :=
  Module[{mV, nV, fs},
    mV = mkVar["m", numTyRCT]; nV = mkVar["n", numTyRCT];
    fs = HOL`Stdlib`Real`freshSeqTm[sT];
    forallRCT[mV, forallRCT[nV, impRCT[
      mkComb[mkComb[HOL`Stdlib`Num`ltConst[], mV], nV],
      notRCT[mkEq[mkComb[fs, nV], mkComb[fs, mV]]]]]]
  ];

freshLimitShapeRCT[sT_, phiT_, lT_] :=
  Module[{fs, subSeq},
    fs = HOL`Stdlib`Real`freshSeqTm[sT];
    subSeq = HOL`Stdlib`Real`subsequenceTm[fs, phiT];
    impRCT[HOL`Stdlib`Real`listInfiniteTm[sT],
      impRCT[HOL`Stdlib`Real`subseqIndexTm[phiT],
        impRCT[HOL`Stdlib`Real`tendstoTm[subSeq, lT],
          HOL`Stdlib`Real`accumulationPointTm[sT, lT]]]]
  ];

accumulationGoalRCT[sT_] :=
  Module[{xV},
    xV = mkVar["x", realTyRCT];
    existsRCT[xV, HOL`Stdlib`Real`accumulationPointTm[sT, xV]]
  ];

openIntervalBodyRCT[leftT_, rightT_, xT_] :=
  andRCT[rLtRCT[leftT, xT], rLtRCT[xT, rightT]];

closedIntervalBodyRCT[leftT_, rightT_, xT_] :=
  andRCT[rLeRCT[leftT, xT], rLeRCT[xT, rightT]];

closedIntervalSetRCT[leftT_, rightT_] :=
  mkComb[mkComb[HOL`Stdlib`Real`closedIntervalConst[], leftT], rightT];

midpointBodyRCT[aT_, bT_] :=
  realMulRCT[realAddRCT[aT, bT], realInvRCT[twoRealRCT[]]];

halfLengthRCT[aT_, bT_] :=
  realMulRCT[realAddRCT[bT, realNegRCT[aT]], realInvRCT[twoRealRCT[]]];

isOpenBodyRCT[uT_] :=
  Module[{xV, leftV, rightV, yV},
    xV = mkVar["x", realTyRCT]; leftV = mkVar["left", realTyRCT];
    rightV = mkVar["right", realTyRCT]; yV = mkVar["y", realTyRCT];
    forallRCT[xV, impRCT[mkComb[uT, xV],
      existsRCT[leftV, existsRCT[rightV,
        andRCT[rLtRCT[leftV, xV],
          andRCT[rLtRCT[xV, rightV],
            forallRCT[yV, impRCT[
              HOL`Stdlib`Real`openIntervalTm[leftV, rightV, yV],
              mkComb[uT, yV]]]]]]]]]
  ];

coversBodyRCT[uT_, sT_] :=
  Module[{xV, iV},
    xV = mkVar["x", realTyRCT]; iV = mkVar["i", iotaTyRCT];
    forallRCT[xV, impRCT[mkComb[sT, xV],
      existsRCT[iV, mkComb[mkComb[uT, iV], xV]]]]
  ];

listSubcoverBodyRCT[uT_, sT_, jsT_] :=
  Module[{xV, iV},
    xV = mkVar["x", realTyRCT]; iV = mkVar["i", iotaTyRCT];
    forallRCT[xV, impRCT[mkComb[sT, xV],
      existsRCT[iV, andRCT[memIotaRCT[iV, jsT],
        mkComb[mkComb[uT, iV], xV]]]]]
  ];

finiteSubcoverBodyRCT[uT_, sT_] :=
  Module[{jsV},
    jsV = mkVar["js", iotaListTyRCT];
    existsRCT[jsV, HOL`Stdlib`Real`listSubcoverTm[uT, sT, jsV]]
  ];

noFiniteSubcoverBodyRCT[uT_, aT_, bT_] :=
  notRCT[HOL`Stdlib`Real`finiteSubcoverTm[uT, closedIntervalSetRCT[aT, bT]]];

badIntervalBodyRCT[uT_, aT_, bT_] :=
  andRCT[rLeRCT[aT, bT], HOL`Stdlib`Real`noFiniteSubcoverTm[uT, aT, bT]];

stepIntervalBodyRCT[uT_, pT_] :=
  Module[{loT, hiT, midT, condT},
    loT = fstRCT[pT]; hiT = sndRCT[pT]; midT = HOL`Stdlib`Real`midpointTm[loT, hiT];
    condT = HOL`Stdlib`Real`finiteSubcoverTm[uT, closedIntervalSetRCT[loT, midT]];
    condRCT[pairTyRCT, condT, pairRCT[midT, hiT], pairRCT[loT, midT]]
  ];

bisectAtRCT[uT_, leftT_, rightT_, nT_] :=
  mkComb[HOL`Stdlib`Real`bisectIntervalTm[uT, leftT, rightT], nT];
lowerAtRCT[uT_, leftT_, rightT_, nT_] :=
  mkComb[HOL`Stdlib`Real`lowerTm[uT, leftT, rightT], nT];
upperAtRCT[uT_, leftT_, rightT_, nT_] :=
  mkComb[HOL`Stdlib`Real`upperTm[uT, leftT, rightT], nT];
stepCondRCT[uT_, leftT_, rightT_, nT_] :=
  HOL`Stdlib`Real`finiteSubcoverTm[uT,
    closedIntervalSetRCT[lowerAtRCT[uT, leftT, rightT, nT],
      HOL`Stdlib`Real`midpointTm[lowerAtRCT[uT, leftT, rightT, nT],
        upperAtRCT[uT, leftT, rightT, nT]]]];

constSeqBoundedRCT[cT_] :=
  Module[{nV, seq, clean, outerEx, betaLo, innerEx, leCC, allN, exHi, exLo},
    nV = mkVar["n", numTyRCT]; seq = constSeqRCT[cT];
    clean = betaCleanRCT[HOL`Stdlib`Real`unfoldSeqBounded[seq]];
    outerEx = concl[clean][[2]];
    betaLo = HOL`Equal`BETACONV[mkComb[outerEx[[2]], cT]];
    innerEx = concl[betaLo][[2]];
    leCC = HOL`Bool`SPEC[cT, HOL`Stdlib`Real`realLeReflThm];
    allN = HOL`Bool`GEN[nV, HOL`Bool`CONJ[leCC, leCC]];
    exHi = HOL`Bool`EXISTS[innerEx, cT, allN];
    exLo = HOL`Bool`EXISTS[outerEx, cT, exHi];
    EQMP[HOL`Equal`SYM[clean], exLo]
  ];

HOLTest`runTests["stdlib/Real/Compact: definitions and builders",
  Module[{uV, lV, th, expected},
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqBoundedDefThm], {},
      "seqBoundedDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqBoundedDefThm],
      "seqBoundedDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`hasConvergentSubseqDefThm], {},
      "hasConvergentSubseqDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`hasConvergentSubseqDefThm],
      "hasConvergentSubseqDef is thm"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`seqBoundedConst[]],
      tyFun[seqTyRCT, boolTy], "seqBoundedConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`hasConvergentSubseqConst[]],
      tyFun[seqTyRCT, tyFun[realTyRCT, boolTy]], "hasConvergentSubseqConst type"];

    uV = mkVar["uCompactRCT", seqTyRCT]; lV = mkVar["lCompactRCT", realTyRCT];
    th = HOL`Stdlib`Real`unfoldSeqBounded[uV];
    expected = mkEq[HOL`Stdlib`Real`seqBoundedTm[uV], seqBoundedBodyRCT[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldSeqBounded body"];

    th = HOL`Stdlib`Real`unfoldHasConvergentSubseq[uV, lV];
    expected = mkEq[HOL`Stdlib`Real`hasConvergentSubseqTm[uV, lV],
      hasConvergentSubseqBodyRCT[uV, lV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "unfoldHasConvergentSubseq body"]]];

HOLTest`runTests["stdlib/Real/Compact: theorem objects",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`Private`seqBoundedSubseqAboveThm],
    "seqBoundedSubseqAboveThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`Private`seqBoundedSubseqAboveThm], {},
    "seqBoundedSubseqAboveThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`Private`seqBoundedSubseqBelowThm],
    "seqBoundedSubseqBelowThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`Private`seqBoundedSubseqBelowThm], {},
    "seqBoundedSubseqBelowThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`bwSequentialThm],
    "bwSequentialThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`bwSequentialThm], {},
    "bwSequentialThm no hyps"]];

HOLTest`runTests["stdlib/Real/Compact: theorem shapes",
  Module[{uV, phiV, subSeq, th, expected},
    uV = mkVar["uShapeRCT", seqTyRCT];
    phiV = mkVar["phiShapeRCT", numFunTyRCT];
    subSeq = HOL`Stdlib`Real`subsequenceTm[uV, phiV];

    th = specAllRCT[HOL`Stdlib`Real`Private`seqBoundedSubseqAboveThm, {uV, phiV}];
    expected = impRCT[HOL`Stdlib`Real`seqBoundedTm[uV],
      HOL`Stdlib`Real`seqBddAboveTm[subSeq]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "seqBoundedSubseqAbove instantiated shape"];

    th = specAllRCT[HOL`Stdlib`Real`Private`seqBoundedSubseqBelowThm, {uV, phiV}];
    expected = impRCT[HOL`Stdlib`Real`seqBoundedTm[uV],
      HOL`Stdlib`Real`seqBddBelowTm[subSeq]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "seqBoundedSubseqBelow instantiated shape"];

    th = HOL`Bool`SPEC[uV, HOL`Stdlib`Real`bwSequentialThm];
    expected = impRCT[HOL`Stdlib`Real`seqBoundedTm[uV], bwGoalRCT[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "bwSequential instantiated shape"]]];

HOLTest`runTests["stdlib/Real/Compact: constant sequence boundedness",
  Module[{cV, cSeq, bounded, inst, th, expected},
    cV = mkVar["cCompactRCT", realTyRCT];
    cSeq = constSeqRCT[cV];
    bounded = constSeqBoundedRCT[cV];
    expected = HOL`Stdlib`Real`seqBoundedTm[cSeq];
    assertConclRCT["constant seqBounded", bounded, expected];

    inst = HOL`Bool`SPEC[cSeq, HOL`Stdlib`Real`bwSequentialThm];
    th = HOL`Bool`MP[inst, bounded];
    expected = bwGoalRCT[cSeq];
    assertConclRCT["constant bwSequential", th, expected]]];

HOLTest`runTests["stdlib/Real/Compact: accumulation definitions",
  Module[{sV, xV, yV, th, expected},
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`listInfiniteConst[]],
      tyFun[setTyRCT, boolTy], "listInfiniteConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`setBoundedConst[]],
      tyFun[setTyRCT, boolTy], "setBoundedConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`distConst[]],
      tyFun[realTyRCT, tyFun[realTyRCT, realTyRCT]], "distConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`accumulationPointConst[]],
      tyFun[setTyRCT, tyFun[realTyRCT, boolTy]], "accumulationPointConst type"];

    sV = mkVar["SAccumDefRCT", setTyRCT];
    xV = mkVar["xAccumDefRCT", realTyRCT];
    yV = mkVar["yAccumDefRCT", realTyRCT];

    th = HOL`Stdlib`Real`unfoldListInfinite[sV];
    expected = mkEq[HOL`Stdlib`Real`listInfiniteTm[sV], listInfiniteBodyRCT[sV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldListInfinite body"];

    th = HOL`Stdlib`Real`unfoldSetBounded[sV];
    expected = mkEq[HOL`Stdlib`Real`setBoundedTm[sV], setBoundedBodyRCT[sV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldSetBounded body"];

    th = HOL`Stdlib`Real`unfoldDist[yV, xV];
    expected = mkEq[HOL`Stdlib`Real`distTm[yV, xV], distBodyRCT[yV, xV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldDist body"];

    th = HOL`Stdlib`Real`unfoldAccumulationPoint[sV, xV];
    expected = mkEq[HOL`Stdlib`Real`accumulationPointTm[sV, xV],
      accumulationBodyRCT[sV, xV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "unfoldAccumulationPoint body"]]];

HOLTest`runTests["stdlib/Real/Compact: fresh theorem objects",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`freshListRecSpecThm],
    "freshListRecSpecThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`freshListRecSpecThm], {},
    "freshListRecSpecThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`freshSeqMemThm],
    "freshSeqMemThm is thm"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`freshSeqNotMemThm],
    "freshSeqNotMemThm is thm"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`freshSeqMemFreshListOfLtThm],
    "freshSeqMemFreshListOfLtThm is thm"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`freshSeqNeOfLtThm],
    "freshSeqNeOfLtThm is thm"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`freshSeqBoundedThm],
    "freshSeqBoundedThm is thm"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`freshLimitIsAccumThm],
    "freshLimitIsAccumThm is thm"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`accumulationPrincipleThm],
    "accumulationPrincipleThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`accumulationPrincipleThm], {},
    "accumulationPrincipleThm no hyps"]];

HOLTest`runTests["stdlib/Real/Compact: fresh theorem shapes",
  Module[{sV, phiV, lV, th, expected},
    sV = mkVar["SAccumShapeRCT", setTyRCT];
    phiV = mkVar["phiAccumShapeRCT", numFunTyRCT];
    lV = mkVar["lAccumShapeRCT", realTyRCT];

    th = HOL`Bool`SPEC[sV, HOL`Stdlib`Real`freshListRecSpecThm];
    expected = freshListRecBodyRCT[sV];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "freshListRecSpec instantiated shape"];

    th = HOL`Bool`SPEC[sV, HOL`Stdlib`Real`freshSeqMemThm];
    expected = impRCT[HOL`Stdlib`Real`listInfiniteTm[sV], freshSeqMemBodyRCT[sV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "freshSeqMem instantiated shape"];

    th = HOL`Bool`SPEC[sV, HOL`Stdlib`Real`freshSeqNeOfLtThm];
    expected = impRCT[HOL`Stdlib`Real`listInfiniteTm[sV], freshSeqNeBodyRCT[sV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "freshSeqNe instantiated shape"];

    th = specAllRCT[HOL`Stdlib`Real`freshLimitIsAccumThm, {sV, phiV, lV}];
    expected = freshLimitShapeRCT[sV, phiV, lV];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "freshLimitIsAccum instantiated shape"];

    th = HOL`Bool`SPEC[sV, HOL`Stdlib`Real`accumulationPrincipleThm];
    expected = impRCT[HOL`Stdlib`Real`setBoundedTm[sV],
      impRCT[HOL`Stdlib`Real`listInfiniteTm[sV], accumulationGoalRCT[sV]]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "accumulationPrinciple instantiated shape"]]];

(* NOTE: no testExit[] here — the runners (run_all/run_fast/dev) call it once
   centrally; a per-file testExit[] would Exit[] the process and truncate
   run_all (it passes dev.wls only because that runs this file last). *)

HOLTest`runTests["stdlib/Real/Compact: cover vocabulary",
  Module[{leftV, rightV, xV, yV, uV, coverV, sV, jsV, th, expected,
          defs},
    defs = {
      {"openIntervalDef", HOL`Stdlib`Real`openIntervalDefThm},
      {"closedIntervalDef", HOL`Stdlib`Real`closedIntervalDefThm},
      {"isOpenDef", HOL`Stdlib`Real`isOpenDefThm},
      {"coversDef", HOL`Stdlib`Real`coversDefThm},
      {"listSubcoverDef", HOL`Stdlib`Real`listSubcoverDefThm},
      {"finiteSubcoverDef", HOL`Stdlib`Real`finiteSubcoverDefThm}};
    Scan[Function[{entry},
      HOLTest`assertTrue[isThm[entry[[2]]], entry[[1]] <> " is thm"];
      HOLTest`assertEq[hyp[entry[[2]]], {}, entry[[1]] <> " no hyps"]], defs];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`openIntervalConst[]],
      intervalTyRCT, "openIntervalConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`closedIntervalConst[]],
      intervalTyRCT, "closedIntervalConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`isOpenConst[]],
      isOpenTyRCT, "isOpenConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`coversConst[]],
      coversTyRCT, "coversConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`listSubcoverConst[]],
      listSubcoverTyRCT, "listSubcoverConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`finiteSubcoverConst[]],
      coversTyRCT, "finiteSubcoverConst type"];

    leftV = mkVar["leftCoverRCT", realTyRCT];
    rightV = mkVar["rightCoverRCT", realTyRCT];
    xV = mkVar["xCoverRCT", realTyRCT];
    yV = mkVar["yCoverRCT", realTyRCT];
    uV = mkVar["UCoverSetRCT", setTyRCT];
    coverV = mkVar["UCoverRCT", coverTyRCT];
    sV = mkVar["SCoverRCT", setTyRCT];
    jsV = mkVar["jsCoverRCT", iotaListTyRCT];

    th = HOL`Stdlib`Real`unfoldOpenInterval[leftV, rightV, xV];
    expected = mkEq[HOL`Stdlib`Real`openIntervalTm[leftV, rightV, xV],
      openIntervalBodyRCT[leftV, rightV, xV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldOpenInterval body"];

    th = HOL`Stdlib`Real`unfoldClosedInterval[leftV, rightV, xV];
    expected = mkEq[HOL`Stdlib`Real`closedIntervalTm[leftV, rightV, xV],
      closedIntervalBodyRCT[leftV, rightV, xV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldClosedInterval body"];

    expected = forallRCT[leftV, forallRCT[rightV, forallRCT[xV,
      mkEq[HOL`Stdlib`Real`openIntervalTm[leftV, rightV, xV],
        openIntervalBodyRCT[leftV, rightV, xV]]]]];
    HOLTest`assertTrue[aconv[concl[HOL`Stdlib`Real`openIntervalMemThm], expected],
      "openIntervalMemThm shape"];

    expected = forallRCT[leftV, forallRCT[rightV, forallRCT[xV,
      mkEq[HOL`Stdlib`Real`closedIntervalTm[leftV, rightV, xV],
        closedIntervalBodyRCT[leftV, rightV, xV]]]]];
    HOLTest`assertTrue[aconv[concl[HOL`Stdlib`Real`closedIntervalMemThm], expected],
      "closedIntervalMemThm shape"];

    th = HOL`Stdlib`Real`unfoldIsOpen[uV];
    expected = mkEq[HOL`Stdlib`Real`isOpenTm[uV], isOpenBodyRCT[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldIsOpen body"];

    th = HOL`Stdlib`Real`unfoldCovers[coverV, sV];
    expected = mkEq[HOL`Stdlib`Real`coversTm[coverV, sV],
      coversBodyRCT[coverV, sV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldCovers body"];

    th = HOL`Stdlib`Real`unfoldListSubcover[coverV, sV, jsV];
    expected = mkEq[HOL`Stdlib`Real`listSubcoverTm[coverV, sV, jsV],
      listSubcoverBodyRCT[coverV, sV, jsV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldListSubcover body"];

    th = HOL`Stdlib`Real`unfoldFiniteSubcover[coverV, sV];
    expected = mkEq[HOL`Stdlib`Real`finiteSubcoverTm[coverV, sV],
      finiteSubcoverBodyRCT[coverV, sV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldFiniteSubcover body"]]];

HOLTest`runTests["stdlib/Real/Compact: midpoint and noFiniteSubcover vocabulary",
  Module[{aV, bV, coverV, th, expected, defs},
    defs = {
      {"midpointDef", HOL`Stdlib`Real`midpointDefThm},
      {"noFiniteSubcoverDef", HOL`Stdlib`Real`noFiniteSubcoverDefThm}};
    Scan[Function[{entry},
      HOLTest`assertTrue[isThm[entry[[2]]], entry[[1]] <> " is thm"];
      HOLTest`assertEq[hyp[entry[[2]]], {}, entry[[1]] <> " no hyps"]], defs];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`midpointConst[]],
      midpointTyRCT, "midpointConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`noFiniteSubcoverConst[]],
      noFiniteSubcoverTyRCT, "noFiniteSubcoverConst type"];

    aV = mkVar["aMidDefRCT", realTyRCT];
    bV = mkVar["bMidDefRCT", realTyRCT];
    coverV = mkVar["UMidDefRCT", coverTyRCT];

    th = HOL`Stdlib`Real`unfoldMidpoint[aV, bV];
    expected = mkEq[HOL`Stdlib`Real`midpointTm[aV, bV], midpointBodyRCT[aV, bV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldMidpoint body"];

    th = HOL`Stdlib`Real`unfoldNoFiniteSubcover[coverV, aV, bV];
    expected = mkEq[HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, aV, bV],
      noFiniteSubcoverBodyRCT[coverV, aV, bV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "unfoldNoFiniteSubcover body"]]];

HOLTest`runTests["stdlib/Real/Compact: midpoint theorem shapes",
  Module[{aV, bV, mid, th, expected, z0, z1, z2, arith, folded},
    aV = mkVar["aMidShapeRCT", realTyRCT];
    bV = mkVar["bMidShapeRCT", realTyRCT];
    mid = HOL`Stdlib`Real`midpointTm[aV, bV];

    th = specAllRCT[HOL`Stdlib`Real`leftLeMidpointThm, {aV, bV}];
    expected = impRCT[rLeRCT[aV, bV], rLeRCT[aV, mid]];
    assertConclRCT["leftLeMidpoint shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`midpointLeRightThm, {aV, bV}];
    expected = impRCT[rLeRCT[aV, bV], rLeRCT[mid, bV]];
    assertConclRCT["midpointLeRight shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`leftLtMidpointThm, {aV, bV}];
    expected = impRCT[rLtRCT[aV, bV], rLtRCT[aV, mid]];
    assertConclRCT["leftLtMidpoint shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`midpointLtRightThm, {aV, bV}];
    expected = impRCT[rLtRCT[aV, bV], rLtRCT[mid, bV]];
    assertConclRCT["midpointLtRight shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`midpointSubLeftThm, {aV, bV}];
    expected = mkEq[realAddRCT[mid, realNegRCT[aV]], halfLengthRCT[aV, bV]];
    assertConclRCT["midpointSubLeft shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`rightSubMidpointThm, {aV, bV}];
    expected = mkEq[realAddRCT[bV, realNegRCT[mid]], halfLengthRCT[aV, bV]];
    assertConclRCT["rightSubMidpoint shape", th, expected];

    z0 = zeroRealRCT[]; z1 = oneRealRCT[]; z2 = twoRealRCT[];
    arith = HOL`Auto`RealArith`realArithProve[
      mkEq[midpointBodyRCT[z0, z2], z1]];
    folded = betaCleanRCT[HOL`Drule`SUBS[
      {HOL`Equal`SYM[HOL`Stdlib`Real`unfoldMidpoint[z0, z2]]}, arith]];
    expected = mkEq[HOL`Stdlib`Real`midpointTm[z0, z2], z1];
    assertConclRCT["midpoint zero two", folded, expected]]];

HOLTest`runTests["stdlib/Real/Compact: MEM APPEND theorem shapes",
  Module[{iV, jsV, ksV, th, expected, consOne, memCons, concrete},
    iV = mkVar["iMemAppendRCT", iotaTyRCT];
    jsV = mkVar["jsMemAppendRCT", iotaListTyRCT];
    ksV = mkVar["ksMemAppendRCT", iotaListTyRCT];

    th = specAllRCT[HOL`Stdlib`Real`memAppendLeftThm, {iV, jsV, ksV}];
    expected = impRCT[memIotaRCT[iV, jsV],
      memIotaRCT[iV, appendIotaRCT[jsV, ksV]]];
    assertConclRCT["memAppendLeft shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`memAppendRightThm, {iV, jsV, ksV}];
    expected = impRCT[memIotaRCT[iV, ksV],
      memIotaRCT[iV, appendIotaRCT[jsV, ksV]]];
    assertConclRCT["memAppendRight shape", th, expected];

    consOne = consIotaRCT[iV, nilIotaRCT[]];
    memCons = EQMP[HOL`Equal`SYM[memConsIotaEqRCT[iV, iV, nilIotaRCT[]]],
      HOL`Bool`DISJ1[REFL[iV], memIotaRCT[iV, nilIotaRCT[]]]];
    concrete = HOL`Bool`MP[
      specAllRCT[HOL`Stdlib`Real`memAppendLeftThm, {iV, consOne, ksV}], memCons];
    expected = memIotaRCT[iV, appendIotaRCT[consOne, ksV]];
    assertConclRCT["memAppendLeft concrete", concrete, expected]]];

HOLTest`runTests["stdlib/Real/Compact: subcover theorem shapes",
  Module[{coverV, aV, mV, bV, jsV, ksV, leftSet, rightSet, wholeSet,
          th, expected},
    coverV = mkVar["USubcoverRCT", coverTyRCT];
    aV = mkVar["aSubcoverRCT", realTyRCT];
    mV = mkVar["mSubcoverRCT", realTyRCT];
    bV = mkVar["bSubcoverRCT", realTyRCT];
    jsV = mkVar["jsSubcoverRCT", iotaListTyRCT];
    ksV = mkVar["ksSubcoverRCT", iotaListTyRCT];
    leftSet = closedIntervalSetRCT[aV, mV];
    rightSet = closedIntervalSetRCT[mV, bV];
    wholeSet = closedIntervalSetRCT[aV, bV];

    th = specAllRCT[HOL`Stdlib`Real`combineHalfSubcoverThm,
      {coverV, aV, mV, bV, jsV, ksV}];
    expected = impRCT[HOL`Stdlib`Real`listSubcoverTm[coverV, leftSet, jsV],
      impRCT[HOL`Stdlib`Real`listSubcoverTm[coverV, rightSet, ksV],
        HOL`Stdlib`Real`listSubcoverTm[coverV, wholeSet,
          appendIotaRCT[jsV, ksV]]]];
    assertConclRCT["combineHalfSubcover shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`finiteSubcoverOfHalvesThm,
      {coverV, aV, mV, bV}];
    expected = impRCT[HOL`Stdlib`Real`finiteSubcoverTm[coverV, leftSet],
      impRCT[HOL`Stdlib`Real`finiteSubcoverTm[coverV, rightSet],
        HOL`Stdlib`Real`finiteSubcoverTm[coverV, wholeSet]]];
    assertConclRCT["finiteSubcoverOfHalves shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`rightHalfBadThm, {coverV, aV, bV, mV}];
    expected = impRCT[HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, aV, bV],
      impRCT[HOL`Stdlib`Real`finiteSubcoverTm[coverV, leftSet],
        HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, mV, bV]]];
    assertConclRCT["rightHalfBad shape", th, expected]]];

HOLTest`runTests["stdlib/Real/Compact: bisection recursion shapes",
  Module[{coverV, leftV, rightV, nV, pV, bisN, loN, hiN, midN, condN,
          th, expected, defs},
    coverV = mkVar["UBisectRCT", coverTyRCT];
    leftV = mkVar["leftBisectRCT", realTyRCT];
    rightV = mkVar["rightBisectRCT", realTyRCT];
    nV = mkVar["nBisectRCT", numTyRCT];
    pV = mkVar["pBisectRCT", pairTyRCT];

    defs = {
      {"badIntervalDef", HOL`Stdlib`Real`badIntervalDefThm},
      {"stepIntervalDef", HOL`Stdlib`Real`stepIntervalDefThm},
      {"bisectIntervalDef", HOL`Stdlib`Real`bisectIntervalDefThm},
      {"lowerDef", HOL`Stdlib`Real`lowerDefThm},
      {"upperDef", HOL`Stdlib`Real`upperDefThm}};
    Scan[Function[{entry},
      HOLTest`assertTrue[isThm[entry[[2]]], entry[[1]] <> " is thm"];
      HOLTest`assertEq[hyp[entry[[2]]], {}, entry[[1]] <> " no hyps"]], defs];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`badIntervalConst[]],
      badIntervalTyRCT, "badIntervalConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`stepIntervalConst[]],
      stepIntervalTyRCT, "stepIntervalConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`bisectIntervalConst[]],
      bisectIntervalTyRCT, "bisectIntervalConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`lowerConst[]],
      lowerTyRCT, "lowerConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`upperConst[]],
      lowerTyRCT, "upperConst type"];

    th = HOL`Stdlib`Real`unfoldBadInterval[coverV, leftV, rightV];
    expected = mkEq[HOL`Stdlib`Real`badIntervalTm[coverV, leftV, rightV],
      badIntervalBodyRCT[coverV, leftV, rightV]];
    assertConclRCT["unfoldBadInterval body", th, expected];

    th = HOL`Stdlib`Real`unfoldStepInterval[coverV, pV];
    expected = mkEq[HOL`Stdlib`Real`stepIntervalTm[coverV, pV],
      stepIntervalBodyRCT[coverV, pV]];
    assertConclRCT["unfoldStepInterval body", th, expected];

    th = HOL`Stdlib`Real`unfoldLower[coverV, leftV, rightV, nV];
    expected = mkEq[lowerAtRCT[coverV, leftV, rightV, nV],
      fstRCT[bisectAtRCT[coverV, leftV, rightV, nV]]];
    assertConclRCT["unfoldLower body", th, expected];

    th = HOL`Stdlib`Real`unfoldUpper[coverV, leftV, rightV, nV];
    expected = mkEq[upperAtRCT[coverV, leftV, rightV, nV],
      sndRCT[bisectAtRCT[coverV, leftV, rightV, nV]]];
    assertConclRCT["unfoldUpper body", th, expected];

    bisN = bisectAtRCT[coverV, leftV, rightV, nV];
    th = specAllRCT[HOL`Stdlib`Real`bisectRecSpecThm, {coverV, leftV, rightV}];
    expected = andRCT[
      mkEq[bisectAtRCT[coverV, leftV, rightV, zeroNumRCT[]], pairRCT[leftV, rightV]],
      forallRCT[nV, mkEq[bisectAtRCT[coverV, leftV, rightV, sucNumRCT[nV]],
        HOL`Stdlib`Real`stepIntervalTm[coverV, bisN]]]];
    assertConclRCT["bisectRecSpec shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lowerZeroThm, {coverV, leftV, rightV}];
    expected = mkEq[lowerAtRCT[coverV, leftV, rightV, zeroNumRCT[]], leftV];
    assertConclRCT["lowerZero shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`upperZeroThm, {coverV, leftV, rightV}];
    expected = mkEq[upperAtRCT[coverV, leftV, rightV, zeroNumRCT[]], rightV];
    assertConclRCT["upperZero shape", th, expected];

    loN = lowerAtRCT[coverV, leftV, rightV, nV];
    hiN = upperAtRCT[coverV, leftV, rightV, nV];
    midN = HOL`Stdlib`Real`midpointTm[loN, hiN];
    condN = stepCondRCT[coverV, leftV, rightV, nV];

    th = specAllRCT[HOL`Stdlib`Real`lowerSuccRightThm, {coverV, leftV, rightV, nV}];
    expected = impRCT[condN,
      mkEq[lowerAtRCT[coverV, leftV, rightV, sucNumRCT[nV]], midN]];
    assertConclRCT["lowerSuccRight shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`upperSuccRightThm, {coverV, leftV, rightV, nV}];
    expected = impRCT[condN,
      mkEq[upperAtRCT[coverV, leftV, rightV, sucNumRCT[nV]], hiN]];
    assertConclRCT["upperSuccRight shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lowerSuccLeftThm, {coverV, leftV, rightV, nV}];
    expected = impRCT[notRCT[condN],
      mkEq[lowerAtRCT[coverV, leftV, rightV, sucNumRCT[nV]], loN]];
    assertConclRCT["lowerSuccLeft shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`upperSuccLeftThm, {coverV, leftV, rightV, nV}];
    expected = impRCT[notRCT[condN],
      mkEq[upperAtRCT[coverV, leftV, rightV, sucNumRCT[nV]], midN]];
    assertConclRCT["upperSuccLeft shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`badIntervalsThm, {coverV, leftV, rightV}];
    expected = impRCT[rLeRCT[leftV, rightV],
      impRCT[HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, leftV, rightV],
        forallRCT[nV, HOL`Stdlib`Real`badIntervalTm[coverV,
          lowerAtRCT[coverV, leftV, rightV, nV],
          upperAtRCT[coverV, leftV, rightV, nV]]]]];
    assertConclRCT["badIntervals shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`nestedIntervalsThm, {coverV, leftV, rightV}];
    expected = impRCT[rLeRCT[leftV, rightV],
      impRCT[HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, leftV, rightV],
        HOL`Stdlib`Real`nestedIntervalsTm[
          HOL`Stdlib`Real`lowerTm[coverV, leftV, rightV],
          HOL`Stdlib`Real`upperTm[coverV, leftV, rightV]]]];
    assertConclRCT["nestedIntervals shape", th, expected]]];

HOLTest`runTests["stdlib/Real/Compact: length theorem shapes",
  Module[{coverV, leftV, rightV, nV, bigNV, lenAt, lenSeq, dyN, subLR,
          natLe, th, expected},
    coverV = mkVar["ULengthRCT", coverTyRCT];
    leftV = mkVar["leftLengthRCT", realTyRCT];
    rightV = mkVar["rightLengthRCT", realTyRCT];
    nV = mkVar["nLengthRCT", numTyRCT];
    bigNV = mkVar["NLengthRCT", numTyRCT];
    lenSeq = HOL`Stdlib`Real`intervalLengthTm[coverV, leftV, rightV];
    lenAt[k_] := mkComb[lenSeq, k];
    dyN = HOL`Stdlib`Real`dyadicTm[nV];
    subLR = realAddRCT[rightV, realNegRCT[leftV]];
    natLe[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`intervalLengthConst[]],
      lowerTyRCT, "intervalLengthConst type"];

    th = HOL`Stdlib`Real`unfoldIntervalLength[coverV, leftV, rightV, nV];
    expected = mkEq[lenAt[nV], realAddRCT[
      upperAtRCT[coverV, leftV, rightV, nV],
      realNegRCT[lowerAtRCT[coverV, leftV, rightV, nV]]]];
    assertConclRCT["unfoldIntervalLength body", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lengthZeroThm, {coverV, leftV, rightV}];
    expected = mkEq[lenAt[zeroNumRCT[]], subLR];
    assertConclRCT["lengthZero shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lengthSuccThm, {coverV, leftV, rightV, nV}];
    expected = mkEq[lenAt[sucNumRCT[nV]],
      realMulRCT[lenAt[nV], realInvRCT[twoRealRCT[]]]];
    assertConclRCT["lengthSucc shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lengthInvariantThm, {coverV, leftV, rightV, nV}];
    expected = mkEq[realMulRCT[dyN, lenAt[nV]], subLR];
    assertConclRCT["lengthInvariant shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lengthFormulaThm, {coverV, leftV, rightV, nV}];
    expected = mkEq[lenAt[nV], realMulRCT[subLR, realInvRCT[dyN]]];
    assertConclRCT["lengthFormula shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lengthNonnegThm, {coverV, leftV, rightV}];
    expected = impRCT[rLeRCT[leftV, rightV],
      impRCT[HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, leftV, rightV],
        forallRCT[nV, rLeRCT[zeroRealRCT[], lenAt[nV]]]]];
    assertConclRCT["lengthNonneg shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lengthDecreaseThm, {coverV, leftV, rightV}];
    expected = impRCT[rLeRCT[leftV, rightV],
      impRCT[HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, leftV, rightV],
        forallRCT[bigNV, forallRCT[nV,
          impRCT[natLe[bigNV, nV], rLeRCT[lenAt[nV], lenAt[bigNV]]]]]]];
    assertConclRCT["lengthDecrease shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`lengthsToZeroThm, {coverV, leftV, rightV}];
    expected = impRCT[rLeRCT[leftV, rightV],
      impRCT[HOL`Stdlib`Real`noFiniteSubcoverTm[coverV, leftV, rightV],
        HOL`Stdlib`Real`intervalLengthsToZeroTm[
          HOL`Stdlib`Real`lowerTm[coverV, leftV, rightV],
          HOL`Stdlib`Real`upperTm[coverV, leftV, rightV]]]];
    assertConclRCT["lengthsToZero shape", th, expected]]];

HOLTest`runTests["stdlib/Real/Compact: Heine Borel capstone shapes",
  Module[{coverV, leftV, rightV, xV, aV, bV, yV, iV, iOpenV,
          hClosedX, hClosedY, hLenLeft, hLenRight, hInside, closedSet,
          hOpen, th, expected},
    coverV = mkVar["UHeineRCT", coverTyRCT];
    leftV = mkVar["leftHeineRCT", realTyRCT];
    rightV = mkVar["rightHeineRCT", realTyRCT];
    xV = mkVar["xHeineRCT", realTyRCT];
    aV = mkVar["aHeineRCT", realTyRCT];
    bV = mkVar["bHeineRCT", realTyRCT];
    yV = mkVar["yHeineRCT", realTyRCT];
    iV = mkVar["iHeineRCT", iotaTyRCT];
    iOpenV = mkVar["iOpenHeineRCT", iotaTyRCT];
    hClosedX = HOL`Stdlib`Real`closedIntervalTm[leftV, rightV, xV];
    hClosedY = HOL`Stdlib`Real`closedIntervalTm[leftV, rightV, yV];
    hLenLeft = rLtRCT[realAddRCT[rightV, realNegRCT[leftV]],
      realAddRCT[xV, realNegRCT[aV]]];
    hLenRight = rLtRCT[realAddRCT[rightV, realNegRCT[leftV]],
      realAddRCT[bV, realNegRCT[xV]]];
    closedSet = closedIntervalSetRCT[leftV, rightV];
    hInside = forallRCT[yV, impRCT[HOL`Stdlib`Real`openIntervalTm[aV, bV, yV],
      mkComb[mkComb[coverV, iV], yV]]];

    th = specAllRCT[HOL`Stdlib`Real`intervalSubsetOpenIntervalThm,
      {leftV, rightV, xV, aV, bV, yV}];
    expected = impRCT[hClosedX, impRCT[hClosedY, impRCT[hLenLeft,
      impRCT[hLenRight, HOL`Stdlib`Real`openIntervalTm[aV, bV, yV]]]]];
    assertConclRCT["intervalSubsetOpenInterval shape", th, expected];

    th = specAllRCT[HOL`Stdlib`Real`singletonSubcoverOfSmallIntervalThm,
      {coverV, leftV, rightV, xV, aV, bV, iV}];
    expected = impRCT[hClosedX, impRCT[hLenLeft, impRCT[hLenRight,
      impRCT[hInside, HOL`Stdlib`Real`finiteSubcoverTm[coverV, closedSet]]]]];
    assertConclRCT["singletonSubcoverOfSmallInterval shape", th, expected];

    hOpen = forallRCT[iOpenV, HOL`Stdlib`Real`isOpenTm[mkComb[coverV, iOpenV]]];
    th = specAllRCT[HOL`Stdlib`Real`compactnessPrincipleThm,
      {coverV, leftV, rightV}];
    expected = impRCT[rLeRCT[leftV, rightV], impRCT[hOpen,
      impRCT[HOL`Stdlib`Real`coversTm[coverV, closedSet],
        HOL`Stdlib`Real`finiteSubcoverTm[coverV, closedSet]]]];
    assertConclRCT["compactnessPrinciple shape", th, expected]]];
