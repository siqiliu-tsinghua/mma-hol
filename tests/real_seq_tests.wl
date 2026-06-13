(* ::Package:: *)

(* Tests for M7-8 stdlib/Real/Seq.wl - real sequence limits. *)

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

numTyRST = mkType["num", {}];
realTyRST = mkType["real", {}];
seqTyRST = tyFun[numTyRST, realTyRST];
eventuallyPredTyRST = tyFun[numTyRST, boolTy];

natRST[n_Integer] := Nest[mkComb[HOL`Stdlib`Num`sucConst[], #] &,
  HOL`Stdlib`Num`zeroConst[], n];
intOfNumRST[nT_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], nT];
ratOfIntRST[zT_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], zT];
realOfRatRST[qT_] := mkComb[HOL`Stdlib`Real`realOfRatConst[], qT];
rnumRST[n_Integer] := realOfRatRST[ratOfIntRST[intOfNumRST[natRST[n]]]];
zeroRealRST[] := rnumRST[0];

rAddRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], a], b];
rNegRST[a_] := mkComb[HOL`Stdlib`Real`realNegConst[], a];
rAbsRST[a_] := mkComb[HOL`Stdlib`Real`realAbsConst[], a];
rMulRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realMulConst[], a], b];
rLeRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], a], b];
rLtRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], a], b];
rSupRST[s_] := mkComb[HOL`Stdlib`Real`realSupConst[], s];
nLeRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
nLtRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], a], b];
andRST[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
orRST[p_, q_] := mkComb[
  mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impRST[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
notRST[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
forallRST[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
existsRST[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];

specAllRST[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

betaCleanRST[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

constSeqRST[cT_] := Module[{nV}, nV = mkVar["n", numTyRST]; mkAbs[nV, cT]];

limitAtomRST[aT_, lT_, eT_, nT_] :=
  rLtRST[rAbsRST[rAddRST[mkComb[aT, nT], rNegRST[lT]]], eT];

limitAllRST[aT_, lT_, eT_, n0T_] :=
  Module[{nV},
    nV = mkVar["n", numTyRST];
    forallRST[nV, impRST[nLeRST[n0T, nV], limitAtomRST[aT, lT, eT, nV]]]
  ];

tendstoBodyRST[aT_, lT_] :=
  Module[{eV, nV},
    eV = mkVar["e", realTyRST];
    nV = mkVar["N", numTyRST];
    forallRST[eV, impRST[rLtRST[zeroRealRST[], eV],
      existsRST[nV, limitAllRST[aT, lT, eV, nV]]]]
  ];

eventuallyAllRST[pT_, n0T_] :=
  Module[{nV},
    nV = mkVar["n", numTyRST];
    forallRST[nV, impRST[nLeRST[n0T, nV], mkComb[pT, nV]]]
  ];

eventuallyBodyRST[pT_] :=
  Module[{nV},
    nV = mkVar["N", numTyRST];
    existsRST[nV, eventuallyAllRST[pT, nV]]
  ];

boundedPredRST[uT_, bT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRST];
    mkAbs[nV, rLtRST[rAbsRST[mkComb[uT, nV]], bT]]
  ];

awayPredRST[uT_, cT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRST];
    mkAbs[nV, rLtRST[cT, rAbsRST[mkComb[uT, nV]]]]
  ];

eventuallyBoundedBodyRST[uT_] :=
  Module[{bV},
    bV = mkVar["B", realTyRST];
    existsRST[bV, andRST[rLtRST[zeroRealRST[], bV],
      HOL`Stdlib`Real`eventuallyTm[boundedPredRST[uT, bV]]]]
  ];

eventuallyAwayBodyRST[uT_] :=
  Module[{cV},
    cV = mkVar["c", realTyRST];
    existsRST[cV, andRST[rLtRST[zeroRealRST[], cV],
      HOL`Stdlib`Real`eventuallyTm[awayPredRST[uT, cV]]]]
  ];

rangeRST[uT_] :=
  Module[{xV, nV},
    xV = mkVar["xR", realTyRST]; nV = mkVar["nR", numTyRST];
    mkAbs[xV, existsRST[nV, mkEq[xV, mkComb[uT, nV]]]]
  ];

monoIncBodyRST[uT_] :=
  Module[{nV, mV},
    nV = mkVar["n", numTyRST]; mV = mkVar["m", numTyRST];
    forallRST[nV, forallRST[mV,
      impRST[nLeRST[nV, mV], rLeRST[mkComb[uT, nV], mkComb[uT, mV]]]]]
  ];

monoDecBodyRST[uT_] :=
  Module[{nV, mV},
    nV = mkVar["n", numTyRST]; mV = mkVar["m", numTyRST];
    forallRST[nV, forallRST[mV,
      impRST[nLeRST[nV, mV], rLeRST[mkComb[uT, mV], mkComb[uT, nV]]]]]
  ];

seqBddAboveBodyRST[uT_] :=
  Module[{bV, nV},
    bV = mkVar["B", realTyRST]; nV = mkVar["n", numTyRST];
    existsRST[bV, forallRST[nV, rLeRST[mkComb[uT, nV], bV]]]
  ];

seqBddBelowBodyRST[uT_] :=
  Module[{bV, nV},
    bV = mkVar["B", realTyRST]; nV = mkVar["n", numTyRST];
    existsRST[bV, forallRST[nV, rLeRST[bV, mkComb[uT, nV]]]]
  ];

subseqIndexBodyRST[phiT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRST];
    forallRST[nV, nLtRST[mkComb[phiT, nV],
      mkComb[phiT, mkComb[HOL`Stdlib`Num`sucConst[], nV]]]]
  ];

subsequenceBodyRST[uT_, phiT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRST];
    mkAbs[nV, mkComb[uT, mkComb[phiT, nV]]]
  ];

peakBodyRST[uT_, nT_] :=
  Module[{mV},
    mV = mkVar["m", numTyRST];
    forallRST[mV, impRST[nLeRST[nT, mV],
      rLeRST[mkComb[uT, mV], mkComb[uT, nT]]]]
  ];

monoSubseqGoalRST[uT_] :=
  Module[{phiV, subSeq},
    phiV = mkVar["phi", tyFun[numTyRST, numTyRST]];
    subSeq = HOL`Stdlib`Real`subsequenceTm[uT, phiV];
    existsRST[phiV, andRST[HOL`Stdlib`Real`subseqIndexTm[phiV],
      orRST[HOL`Stdlib`Real`monoIncTm[subSeq], HOL`Stdlib`Real`monoDecTm[subSeq]]]]
  ];

constPeakRST[cT_, nT_] :=
  Module[{mV, seq, clean, point, allM},
    mV = mkVar["m", numTyRST]; seq = constSeqRST[cT];
    clean = betaCleanRST[HOL`Stdlib`Real`unfoldPeak[seq, nT]];
    point = HOL`Bool`SPEC[cT, HOL`Stdlib`Real`realLeReflThm];
    allM = HOL`Bool`GEN[mV, HOL`Bool`DISCH[nLeRST[nT, mV], point]];
    EQMP[HOL`Equal`SYM[clean], allM]
  ];

constMonoIncRST[cT_] :=
  Module[{nV, mV, seq, clean, impN, allM, allN},
    nV = mkVar["n", numTyRST]; mV = mkVar["m", numTyRST];
    seq = constSeqRST[cT];
    clean = betaCleanRST[HOL`Stdlib`Real`unfoldMonoInc[seq]];
    impN = HOL`Bool`DISCH[nLeRST[nV, mV],
      HOL`Bool`SPEC[cT, HOL`Stdlib`Real`realLeReflThm]];
    allM = HOL`Bool`GEN[mV, impN];
    allN = HOL`Bool`GEN[nV, allM];
    EQMP[HOL`Equal`SYM[clean], allN]
  ];

constMonoDecRST[cT_] :=
  Module[{nV, mV, seq, clean, impN, allM, allN},
    nV = mkVar["n", numTyRST]; mV = mkVar["m", numTyRST];
    seq = constSeqRST[cT];
    clean = betaCleanRST[HOL`Stdlib`Real`unfoldMonoDec[seq]];
    impN = HOL`Bool`DISCH[nLeRST[nV, mV],
      HOL`Bool`SPEC[cT, HOL`Stdlib`Real`realLeReflThm]];
    allM = HOL`Bool`GEN[mV, impN];
    allN = HOL`Bool`GEN[nV, allM];
    EQMP[HOL`Equal`SYM[clean], allN]
  ];

constBddAboveRST[cT_] :=
  Module[{nV, seq, clean, allN, exB},
    nV = mkVar["n", numTyRST]; seq = constSeqRST[cT];
    clean = betaCleanRST[HOL`Stdlib`Real`unfoldSeqBddAbove[seq]];
    allN = HOL`Bool`GEN[nV, HOL`Bool`SPEC[cT, HOL`Stdlib`Real`realLeReflThm]];
    exB = HOL`Bool`EXISTS[concl[clean][[2]], cT, allN];
    EQMP[HOL`Equal`SYM[clean], exB]
  ];

constBddBelowRST[cT_] :=
  Module[{nV, seq, clean, allN, exB},
    nV = mkVar["n", numTyRST]; seq = constSeqRST[cT];
    clean = betaCleanRST[HOL`Stdlib`Real`unfoldSeqBddBelow[seq]];
    allN = HOL`Bool`GEN[nV, HOL`Bool`SPEC[cT, HOL`Stdlib`Real`realLeReflThm]];
    exB = HOL`Bool`EXISTS[concl[clean][[2]], cT, allN];
    EQMP[HOL`Equal`SYM[clean], exB]
  ];

assertConclRST[name_String, th_, expected_] := (
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

HOLTest`runTests["stdlib/Real/Seq: definitions and builders",
  Module[{aV, lV, th, expected, rhs},
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoDefThm], {}, "tendstoDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoDefThm], "tendstoDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`convergentDefThm], {}, "convergentDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`convergentDefThm], "convergentDef is thm"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`tendstoConst[]],
      tyFun[seqTyRST, tyFun[realTyRST, boolTy]], "tendstoConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`convergentConst[]],
      tyFun[seqTyRST, boolTy], "convergentConst type"];

    aV = mkVar["aSeqRST", seqTyRST]; lV = mkVar["LRST", realTyRST];
    th = HOL`Stdlib`Real`unfoldTendsto[aV, lV];
    expected = mkEq[HOL`Stdlib`Real`tendstoTm[aV, lV], tendstoBodyRST[aV, lV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldTendsto full body"];
    rhs = concl[th][[2]];
    HOLTest`assertEq[rhs[[1]], mkConst["∀", tyFun[tyFun[realTyRST, boolTy], boolTy]],
      "unfoldTendsto rhs starts forall"]]];

HOLTest`runTests["stdlib/Real/Seq: eventually definitions and builders",
  Module[{pV, uV, th, expected},
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`eventuallyDefThm], {}, "eventuallyDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`eventuallyDefThm], "eventuallyDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`eventuallyBoundedDefThm], {},
      "eventuallyBoundedDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`eventuallyBoundedDefThm],
      "eventuallyBoundedDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`eventuallyAwayFromZeroDefThm], {},
      "eventuallyAwayDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`eventuallyAwayFromZeroDefThm],
      "eventuallyAwayDef is thm"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`eventuallyConst[]],
      tyFun[eventuallyPredTyRST, boolTy], "eventuallyConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`eventuallyBoundedConst[]],
      tyFun[seqTyRST, boolTy], "eventuallyBoundedConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`eventuallyAwayFromZeroConst[]],
      tyFun[seqTyRST, boolTy], "eventuallyAwayConst type"];

    pV = mkVar["PRST", eventuallyPredTyRST];
    th = HOL`Stdlib`Real`unfoldEventually[pV];
    expected = mkEq[HOL`Stdlib`Real`eventuallyTm[pV], eventuallyBodyRST[pV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldEventually full body"];

    uV = mkVar["uRST", seqTyRST];
    th = HOL`Stdlib`Real`unfoldEventuallyBounded[uV];
    expected = mkEq[HOL`Stdlib`Real`eventuallyBoundedTm[uV],
      eventuallyBoundedBodyRST[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldEventuallyBounded body"];

    th = HOL`Stdlib`Real`unfoldEventuallyAwayFromZero[uV];
    expected = mkEq[HOL`Stdlib`Real`eventuallyAwayFromZeroTm[uV],
      eventuallyAwayBodyRST[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldEventuallyAway body"]]];

HOLTest`runTests["stdlib/Real/Seq: theorem objects",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoConstThm], "tendstoConstThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoConstThm], {}, "tendstoConstThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNeAbsPosThm], "realNeAbsPosThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNeAbsPosThm], {}, "realNeAbsPosThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoUniqueThm], "tendstoUniqueThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoUniqueThm], {}, "tendstoUniqueThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoAddThm], "tendstoAddThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoAddThm], {}, "tendstoAddThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoNegThm], "tendstoNegThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoNegThm], {}, "tendstoNegThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoSubThm], "tendstoSubThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoSubThm], {}, "tendstoSubThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoConvergentThm],
    "tendstoConvergentThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoConvergentThm], {},
    "tendstoConvergentThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`eventuallyOfForallThm],
    "eventuallyOfForallThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`eventuallyOfForallThm], {},
    "eventuallyOfForallThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`eventuallyMonoThm],
    "eventuallyMonoThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`eventuallyMonoThm], {},
    "eventuallyMonoThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`eventuallyAndThm],
    "eventuallyAndThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`eventuallyAndThm], {},
    "eventuallyAndThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`tendstoEventuallyThm],
    "tendstoEventuallyThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`tendstoEventuallyThm], {},
    "tendstoEventuallyThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqTendstoEventuallyBoundedThm],
    "seqTendstoEventuallyBoundedThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqTendstoEventuallyBoundedThm], {},
    "seqTendstoEventuallyBoundedThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqTendstoEventuallyAwayFromZeroThm],
    "seqTendstoEventuallyAwayFromZeroThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqTendstoEventuallyAwayFromZeroThm], {},
    "seqTendstoEventuallyAwayFromZeroThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsMulThm], "realAbsMulThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsMulThm], {}, "realAbsMulThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqTendstoMulThm],
    "seqTendstoMulThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqTendstoMulThm], {},
    "seqTendstoMulThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqTendstoScalarMulThm],
    "seqTendstoScalarMulThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqTendstoScalarMulThm], {},
    "seqTendstoScalarMulThm no hyps"]];

HOLTest`runTests["stdlib/Real/Seq: constant sequences",
  Module[{cV, th, expected},
    th = HOL`Bool`SPEC[zeroRealRST[], HOL`Stdlib`Real`tendstoConstThm];
    expected = HOL`Stdlib`Real`tendstoTm[constSeqRST[zeroRealRST[]], zeroRealRST[]];
    assertConclRST["constant zero", th, expected];

    cV = mkVar["cRST", realTyRST];
    th = HOL`Bool`SPEC[cV, HOL`Stdlib`Real`tendstoConstThm];
    expected = HOL`Stdlib`Real`tendstoTm[constSeqRST[cV], cV];
    assertConclRST["constant variable", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: absolute value positivity",
  Module[{th, expected},
    th = HOL`Bool`MP[
      HOL`Bool`SPEC[rnumRST[1], HOL`Stdlib`Real`realNeAbsPosThm],
      HOL`Auto`RealArith`rnumNe[1, 0]];
    expected = rLtRST[zeroRealRST[], rAbsRST[rnumRST[1]]];
    assertConclRST["realNeAbsPos one", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: uniqueness and calculus laws",
  Module[{cV, dV, cSeq, dSeq, cLim, dLim, th, inst, expected},
    cV = mkVar["cRST", realTyRST]; dV = mkVar["dRST", realTyRST];
    cSeq = constSeqRST[cV]; dSeq = constSeqRST[dV];
    cLim = HOL`Bool`SPEC[cV, HOL`Stdlib`Real`tendstoConstThm];
    dLim = HOL`Bool`SPEC[dV, HOL`Stdlib`Real`tendstoConstThm];

    inst = specAllRST[HOL`Stdlib`Real`tendstoUniqueThm, {cSeq, cV, cV}];
    th = HOL`Bool`MP[HOL`Bool`MP[inst, cLim], cLim];
    assertConclRST["unique constant", th, mkEq[cV, cV]];

    inst = specAllRST[HOL`Stdlib`Real`tendstoAddThm, {cSeq, dSeq, cV, dV}];
    th = betaCleanRST[HOL`Bool`MP[HOL`Bool`MP[inst, cLim], dLim]];
    expected = HOL`Stdlib`Real`tendstoTm[constSeqRST[rAddRST[cV, dV]], rAddRST[cV, dV]];
    assertConclRST["add constants", th, expected];

    inst = specAllRST[HOL`Stdlib`Real`tendstoNegThm, {cSeq, cV}];
    th = betaCleanRST[HOL`Bool`MP[inst, cLim]];
    expected = HOL`Stdlib`Real`tendstoTm[constSeqRST[rNegRST[cV]], rNegRST[cV]];
    assertConclRST["neg constant", th, expected];

    inst = specAllRST[HOL`Stdlib`Real`tendstoSubThm, {cSeq, dSeq, cV, dV}];
    th = betaCleanRST[HOL`Bool`MP[HOL`Bool`MP[inst, cLim], dLim]];
    expected = HOL`Stdlib`Real`tendstoTm[
      constSeqRST[rAddRST[cV, rNegRST[dV]]], rAddRST[cV, rNegRST[dV]]];
    assertConclRST["sub constants", th, expected];

    inst = specAllRST[HOL`Stdlib`Real`tendstoConvergentThm, {cSeq, cV}];
    th = HOL`Bool`MP[inst, cLim];
    expected = HOL`Stdlib`Real`convergentTm[cSeq];
    assertConclRST["constant convergent", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: eventually combinators",
  Module[{nV, pPred, qPred, pAll, qAll, pEv, qEv, pqAll, inst, th, expected,
          andPred},
    nV = mkVar["n", numTyRST];
    pPred = mkAbs[nV, rLtRST[zeroRealRST[], rnumRST[1]]];
    qPred = mkAbs[nV, rLtRST[zeroRealRST[], rnumRST[2]]];
    pAll = HOL`Bool`GEN[nV, HOL`Auto`RealArith`rnumPos[1]];
    qAll = HOL`Bool`GEN[nV, HOL`Auto`RealArith`rnumPos[2]];

    inst = betaCleanRST[HOL`Bool`SPEC[pPred, HOL`Stdlib`Real`eventuallyOfForallThm]];
    pEv = HOL`Bool`MP[inst, pAll];
    expected = HOL`Stdlib`Real`eventuallyTm[pPred];
    assertConclRST["eventuallyOfForall concrete", pEv, expected];

    pqAll = HOL`Bool`GEN[nV, HOL`Bool`DISCH[
      rLtRST[zeroRealRST[], rnumRST[1]], HOL`Auto`RealArith`rnumPos[2]]];
    inst = betaCleanRST[specAllRST[HOL`Stdlib`Real`eventuallyMonoThm,
      {pPred, qPred}]];
    qEv = HOL`Bool`MP[HOL`Bool`MP[inst, pqAll], pEv];
    expected = HOL`Stdlib`Real`eventuallyTm[qPred];
    assertConclRST["eventuallyMono concrete", qEv, expected];

    inst = betaCleanRST[HOL`Bool`SPEC[qPred, HOL`Stdlib`Real`eventuallyOfForallThm]];
    qEv = HOL`Bool`MP[inst, qAll];
    inst = betaCleanRST[specAllRST[HOL`Stdlib`Real`eventuallyAndThm, {pPred, qPred}]];
    th = HOL`Bool`MP[HOL`Bool`MP[inst, pEv], qEv];
    andPred = mkAbs[nV, andRST[rLtRST[zeroRealRST[], rnumRST[1]],
      rLtRST[zeroRealRST[], rnumRST[2]]]];
    expected = HOL`Stdlib`Real`eventuallyTm[andPred];
    assertConclRST["eventuallyAnd concrete", betaCleanRST[th], expected]]];

HOLTest`runTests["stdlib/Real/Seq: eventually consequences of tendsto",
  Module[{cV, oneR, cSeq, oneSeq, cLim, oneLim, inst, th, expected, nV},
    cV = mkVar["cRST", realTyRST];
    oneR = rnumRST[1];
    cSeq = constSeqRST[cV];
    oneSeq = constSeqRST[oneR];
    cLim = HOL`Bool`SPEC[cV, HOL`Stdlib`Real`tendstoConstThm];
    oneLim = HOL`Bool`SPEC[oneR, HOL`Stdlib`Real`tendstoConstThm];
    nV = mkVar["n", numTyRST];

    inst = specAllRST[HOL`Stdlib`Real`tendstoEventuallyThm, {cSeq, cV, oneR}];
    th = betaCleanRST[HOL`Bool`MP[
      HOL`Bool`MP[inst, cLim], HOL`Auto`RealArith`rnumPos[1]]];
    expected = HOL`Stdlib`Real`eventuallyTm[
      mkAbs[nV, rLtRST[rAbsRST[rAddRST[cV, rNegRST[cV]]], oneR]]];
    assertConclRST["tendstoEventually constant", th, expected];

    inst = specAllRST[HOL`Stdlib`Real`seqTendstoEventuallyBoundedThm, {cSeq, cV}];
    th = HOL`Bool`MP[inst, cLim];
    expected = HOL`Stdlib`Real`eventuallyBoundedTm[cSeq];
    assertConclRST["constant eventually bounded", th, expected];

    inst = specAllRST[HOL`Stdlib`Real`seqTendstoEventuallyAwayFromZeroThm,
      {oneSeq, oneR}];
    th = HOL`Bool`MP[HOL`Bool`MP[inst, oneLim], HOL`Auto`RealArith`rnumNe[1, 0]];
    expected = HOL`Stdlib`Real`eventuallyAwayFromZeroTm[oneSeq];
    assertConclRST["constant eventually away from zero", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: multiplication prerequisites",
  Module[{twoR, threeR, negTwoR, negThreeR, xV, yV, aV, bV, th, expected},
    twoR = rnumRST[2]; threeR = rnumRST[3];
    negTwoR = rNegRST[twoR]; negThreeR = rNegRST[threeR];

    th = specAllRST[HOL`Stdlib`Real`realAbsMulThm, {twoR, threeR}];
    expected = mkEq[rAbsRST[rMulRST[twoR, threeR]],
      rMulRST[rAbsRST[twoR], rAbsRST[threeR]]];
    assertConclRST["abs mul positive positive", th, expected];

    th = specAllRST[HOL`Stdlib`Real`realAbsMulThm, {negTwoR, threeR}];
    expected = mkEq[rAbsRST[rMulRST[negTwoR, threeR]],
      rMulRST[rAbsRST[negTwoR], rAbsRST[threeR]]];
    assertConclRST["abs mul negative positive", th, expected];

    th = specAllRST[HOL`Stdlib`Real`realAbsMulThm, {negTwoR, negThreeR}];
    expected = mkEq[rAbsRST[rMulRST[negTwoR, negThreeR]],
      rMulRST[rAbsRST[negTwoR], rAbsRST[negThreeR]]];
    assertConclRST["abs mul negative negative", th, expected];

    xV = mkVar["xRST", realTyRST]; yV = mkVar["yRST", realTyRST];
    aV = mkVar["aRST", realTyRST]; bV = mkVar["bRST", realTyRST];
    th = specAllRST[HOL`Stdlib`Real`Private`mulSubMulThm, {xV, yV, aV, bV}];
    expected = mkEq[rAddRST[rMulRST[xV, yV], rNegRST[rMulRST[aV, bV]]],
      rAddRST[rMulRST[rAddRST[xV, rNegRST[aV]], yV],
        rMulRST[aV, rAddRST[yV, rNegRST[bV]]]]];
    assertConclRST["mul sub mul shape", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: multiplication limit laws on constants",
  Module[{cV, dV, cSeq, dSeq, cLim, dLim, inst, th, expected},
    cV = mkVar["cRST", realTyRST]; dV = mkVar["dRST", realTyRST];
    cSeq = constSeqRST[cV]; dSeq = constSeqRST[dV];
    cLim = HOL`Bool`SPEC[cV, HOL`Stdlib`Real`tendstoConstThm];
    dLim = HOL`Bool`SPEC[dV, HOL`Stdlib`Real`tendstoConstThm];

    inst = specAllRST[HOL`Stdlib`Real`seqTendstoMulThm, {cSeq, dSeq, cV, dV}];
    th = betaCleanRST[HOL`Bool`MP[HOL`Bool`MP[inst, cLim], dLim]];
    expected = HOL`Stdlib`Real`tendstoTm[constSeqRST[rMulRST[cV, dV]], rMulRST[cV, dV]];
    assertConclRST["mul constants", th, expected];

    inst = specAllRST[HOL`Stdlib`Real`seqTendstoMulThm, {cSeq, cSeq, cV, cV}];
    th = betaCleanRST[HOL`Bool`MP[HOL`Bool`MP[inst, cLim], cLim]];
    expected = HOL`Stdlib`Real`tendstoTm[constSeqRST[rMulRST[cV, cV]], rMulRST[cV, cV]];
    assertConclRST["mul constant itself", th, expected];

    inst = specAllRST[HOL`Stdlib`Real`seqTendstoScalarMulThm, {dSeq, dV, cV}];
    th = betaCleanRST[HOL`Bool`MP[inst, dLim]];
    expected = HOL`Stdlib`Real`tendstoTm[constSeqRST[rMulRST[cV, dV]], rMulRST[cV, dV]];
    assertConclRST["scalar mul constants", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: monotone definitions and builders",
  Module[{uV, th, expected},
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`monoIncDefThm], {}, "monoIncDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`monoIncDefThm], "monoIncDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`monoDecDefThm], {}, "monoDecDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`monoDecDefThm], "monoDecDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqBddAboveDefThm], {},
      "seqBddAboveDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqBddAboveDefThm],
      "seqBddAboveDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqBddBelowDefThm], {},
      "seqBddBelowDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqBddBelowDefThm],
      "seqBddBelowDef is thm"];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`monoIncConst[]],
      tyFun[seqTyRST, boolTy], "monoIncConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`monoDecConst[]],
      tyFun[seqTyRST, boolTy], "monoDecConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`seqBddAboveConst[]],
      tyFun[seqTyRST, boolTy], "seqBddAboveConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`seqBddBelowConst[]],
      tyFun[seqTyRST, boolTy], "seqBddBelowConst type"];

    uV = mkVar["uMonoRST", seqTyRST];
    th = HOL`Stdlib`Real`unfoldMonoInc[uV];
    expected = mkEq[HOL`Stdlib`Real`monoIncTm[uV], monoIncBodyRST[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldMonoInc body"];

    th = HOL`Stdlib`Real`unfoldMonoDec[uV];
    expected = mkEq[HOL`Stdlib`Real`monoDecTm[uV], monoDecBodyRST[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldMonoDec body"];

    th = HOL`Stdlib`Real`unfoldSeqBddAbove[uV];
    expected = mkEq[HOL`Stdlib`Real`seqBddAboveTm[uV], seqBddAboveBodyRST[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldSeqBddAbove body"];

    th = HOL`Stdlib`Real`unfoldSeqBddBelow[uV];
    expected = mkEq[HOL`Stdlib`Real`seqBddBelowTm[uV], seqBddBelowBodyRST[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldSeqBddBelow body"]]];

HOLTest`runTests["stdlib/Real/Seq: monotone theorem objects",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsSubLtThm],
    "realAbsSubLtThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsSubLtThm], {},
    "realAbsSubLtThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realSupLtMemThm],
    "realSupLtMemThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realSupLtMemThm], {},
    "realSupLtMemThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`monoIncTendstoSupThm],
    "monoIncTendstoSupThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`monoIncTendstoSupThm], {},
    "monoIncTendstoSupThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`monoConvergesIncThm],
    "monoConvergesIncThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`monoConvergesIncThm], {},
    "monoConvergesIncThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`monoConvergesDecThm],
    "monoConvergesDecThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`monoConvergesDecThm], {},
    "monoConvergesDecThm no hyps"]];

HOLTest`runTests["stdlib/Real/Seq: abs bounds and sup member shape",
  Module[{oneR, sV, tV, aV, uB, hLeft, hRight, inst, th, expected},
    oneR = rnumRST[1];
    hLeft = HOL`Auto`RealArith`realArithProve[
      rLtRST[rAddRST[oneR, rNegRST[oneR]], oneR]];
    hRight = HOL`Auto`RealArith`realArithProve[
      rLtRST[oneR, rAddRST[oneR, oneR]]];
    inst = specAllRST[HOL`Stdlib`Real`realAbsSubLtThm, {oneR, oneR, oneR}];
    th = HOL`Bool`MP[HOL`Bool`MP[inst, hLeft], hRight];
    expected = rLtRST[rAbsRST[rAddRST[oneR, rNegRST[oneR]]], oneR];
    assertConclRST["realAbsSubLt concrete", th, expected];

    sV = mkVar["SRST", tyFun[realTyRST, boolTy]];
    tV = mkVar["tRST", realTyRST];
    aV = mkVar["a", realTyRST]; uB = mkVar["u", realTyRST];
    th = specAllRST[HOL`Stdlib`Real`realSupLtMemThm, {sV, tV}];
    expected = impRST[existsRST[aV, mkComb[sV, aV]],
      impRST[existsRST[uB, forallRST[aV, impRST[mkComb[sV, aV], rLeRST[aV, uB]]]],
        impRST[rLtRST[tV, rSupRST[sV]],
          existsRST[aV, andRST[mkComb[sV, aV], rLtRST[tV, aV]]]]]];
    assertConclRST["realSupLtMem instantiated shape", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: monotone convergence on constants",
  Module[{cV, cSeq, monoInc, monoDec, bddAbove, bddBelow, inst, th, expected, lV},
    cV = mkVar["cMonoRST", realTyRST];
    cSeq = constSeqRST[cV];
    lV = mkVar["L", realTyRST];
    monoInc = constMonoIncRST[cV];
    monoDec = constMonoDecRST[cV];
    bddAbove = constBddAboveRST[cV];
    bddBelow = constBddBelowRST[cV];

    expected = HOL`Stdlib`Real`monoIncTm[cSeq];
    assertConclRST["constant monoInc", monoInc, expected];
    expected = HOL`Stdlib`Real`monoDecTm[cSeq];
    assertConclRST["constant monoDec", monoDec, expected];
    expected = HOL`Stdlib`Real`seqBddAboveTm[cSeq];
    assertConclRST["constant bddAbove", bddAbove, expected];
    expected = HOL`Stdlib`Real`seqBddBelowTm[cSeq];
    assertConclRST["constant bddBelow", bddBelow, expected];

    inst = HOL`Bool`SPEC[cSeq, HOL`Stdlib`Real`monoConvergesIncThm];
    th = HOL`Bool`MP[HOL`Bool`MP[inst, monoInc], bddAbove];
    expected = existsRST[lV, HOL`Stdlib`Real`tendstoTm[cSeq, lV]];
    assertConclRST["constant monoConvergesInc", th, expected];

    inst = HOL`Bool`SPEC[cSeq, HOL`Stdlib`Real`monoConvergesDecThm];
    th = HOL`Bool`MP[HOL`Bool`MP[inst, monoDec], bddBelow];
    expected = existsRST[lV, HOL`Stdlib`Real`tendstoTm[cSeq, lV]];
    assertConclRST["constant monoConvergesDec", th, expected]]];

HOLTest`runTests["stdlib/Real/Seq: subsequence definitions and builders",
  Module[{uV, phiV, nV, th, expected},
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`subseqIndexDefThm], {},
      "subseqIndexDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`subseqIndexDefThm],
      "subseqIndexDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`subsequenceDefThm], {},
      "subsequenceDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`subsequenceDefThm],
      "subsequenceDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`peakDefThm], {}, "peakDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`peakDefThm], "peakDef is thm"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`subseqIndexConst[]],
      tyFun[tyFun[numTyRST, numTyRST], boolTy], "subseqIndexConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`subsequenceConst[]],
      tyFun[seqTyRST, tyFun[tyFun[numTyRST, numTyRST], seqTyRST]],
      "subsequenceConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`peakConst[]],
      tyFun[seqTyRST, tyFun[numTyRST, boolTy]], "peakConst type"];

    uV = mkVar["uSubRST", seqTyRST];
    phiV = mkVar["phiSubRST", tyFun[numTyRST, numTyRST]];
    nV = mkVar["nSubRST", numTyRST];
    th = HOL`Stdlib`Real`unfoldSubseqIndex[phiV];
    expected = mkEq[HOL`Stdlib`Real`subseqIndexTm[phiV], subseqIndexBodyRST[phiV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldSubseqIndex body"];

    th = HOL`Stdlib`Real`unfoldSubsequence[uV, phiV];
    expected = mkEq[HOL`Stdlib`Real`subsequenceTm[uV, phiV],
      subsequenceBodyRST[uV, phiV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldSubsequence body"];

    th = HOL`Stdlib`Real`unfoldPeak[uV, nV];
    expected = mkEq[HOL`Stdlib`Real`peakTm[uV, nV], peakBodyRST[uV, nV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldPeak body"]]];

HOLTest`runTests["stdlib/Real/Seq: subsequence theorem objects",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`subseqIndexMonoThm],
    "subseqIndexMonoThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`subseqIndexMonoThm], {},
    "subseqIndexMonoThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`subseqIndexGeSelfThm],
    "subseqIndexGeSelfThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`subseqIndexGeSelfThm], {},
    "subseqIndexGeSelfThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`notPeakExistsLaterThm],
    "notPeakExistsLaterThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`notPeakExistsLaterThm], {},
    "notPeakExistsLaterThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`eventuallyNotPeakThm],
    "eventuallyNotPeakThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`eventuallyNotPeakThm], {},
    "eventuallyNotPeakThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`existsMonoSubseqThm],
    "existsMonoSubseqThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`existsMonoSubseqThm], {},
    "existsMonoSubseqThm no hyps"]];

HOLTest`runTests["stdlib/Real/Seq: subsequence theorem shapes",
  Module[{uV, nV, mV, th, expected},
    uV = mkVar["uShapeRST", seqTyRST]; nV = mkVar["nShapeRST", numTyRST];
    mV = mkVar["mW", numTyRST];
    th = specAllRST[HOL`Stdlib`Real`notPeakExistsLaterThm, {uV, nV}];
    expected = impRST[notRST[HOL`Stdlib`Real`peakTm[uV, nV]],
      existsRST[mV, andRST[nLtRST[nV, mV],
        rLeRST[mkComb[uV, nV], mkComb[uV, mV]]]]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "notPeakExistsLater instantiated shape"];

    th = HOL`Bool`SPEC[uV, HOL`Stdlib`Real`existsMonoSubseqThm];
    expected = monoSubseqGoalRST[uV];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "existsMonoSubseq instantiated shape"]]];

HOLTest`runTests["stdlib/Real/Seq: constant peaks and identity index",
  Module[{cV, nV, idPhi, idSub, twoN, oneN, geAll, geTwo, monoAll, mono12,
          le12, expected},
    cV = mkVar["cPeakRST", realTyRST]; nV = mkVar["nPeakRST", numTyRST];
    assertConclRST["constant sequence peak", constPeakRST[cV, nV],
      HOL`Stdlib`Real`peakTm[constSeqRST[cV], nV]];

    nV = mkVar["nIdRST", numTyRST];
    idPhi = mkAbs[nV, nV];
    idSub = EQMP[HOL`Equal`SYM[betaCleanRST[
      HOL`Stdlib`Real`unfoldSubseqIndex[idPhi]]], HOL`Stdlib`Num`ltSucThm];
    twoN = natRST[2]; oneN = natRST[1];

    geAll = HOL`Bool`MP[
      HOL`Bool`SPEC[idPhi, HOL`Stdlib`Real`subseqIndexGeSelfThm], idSub];
    geTwo = betaCleanRST[HOL`Bool`SPEC[twoN, geAll]];
    expected = nLeRST[twoN, twoN];
    assertConclRST["identity ge self at two", geTwo, expected];

    monoAll = HOL`Bool`MP[
      HOL`Bool`SPEC[idPhi, HOL`Stdlib`Real`subseqIndexMonoThm], idSub];
    le12 = HOL`Auto`Arith`arithProve[nLeRST[oneN, twoN]];
    mono12 = betaCleanRST[HOL`Bool`MP[specAllRST[monoAll, {oneN, twoN}], le12]];
    expected = nLeRST[oneN, twoN];
    assertConclRST["identity mono one two", mono12, expected]]];
