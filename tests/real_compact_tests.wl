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

zeroNumRCT[] := HOL`Stdlib`Num`zeroConst[];
sucNumRCT[n_] := mkComb[HOL`Stdlib`Num`sucConst[], n];
zeroRealRCT[] := mkComb[HOL`Stdlib`Real`realOfRatConst[],
  mkComb[HOL`Stdlib`Rat`ratOfIntConst[],
    mkComb[HOL`Stdlib`Int`intOfNumConst[], zeroNumRCT[]]]];
realAddRCT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], x], y];
realNegRCT[x_] := mkComb[HOL`Stdlib`Real`realNegConst[], x];
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

specAllRCT[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

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
