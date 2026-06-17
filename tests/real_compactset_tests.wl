(* ::Package:: *)

(* Tests for M8.5 stdlib/Real/CompactSet.wl. *)

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

realTyRCST = mkType["real", {}];
numTyRCST = mkType["num", {}];
setTyRCST = tyFun[realTyRCST, boolTy];
setOfSetsTyRCST = tyFun[setTyRCST, boolTy];
setListTyRCST = HOL`Stdlib`List`listTy[setTyRCST];
seqTyRCST = tyFun[numTyRCST, realTyRCST];
seqCompactTyRCST = tyFun[setTyRCST, boolTy];
isCompactTyRCST = tyFun[setTyRCST, boolTy];

andRCST[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impRCST[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
orRCST[p_, q_] := mkComb[
  mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
notRCST[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
forallRCST[v_, body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[v], boolTy], boolTy]], mkAbs[v, body]];
existsRCST[v_, body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[typeOf[v], boolTy], boolTy]], mkAbs[v, body]];
setAppRCST[s_, x_] := mkComb[s, x];
setMemRCST[c_, v_] := mkComb[c, v];
memSetRCST[v_, vs_] := mkComb[
  mkComb[mkConst["MEM", tyFun[setTyRCST, tyFun[setListTyRCST, boolTy]]], v], vs];
seqAppRCST[u_, n_] := mkComb[u, n];
realLtRCST[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], x], y];
realLeRCST[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], x], y];
realNegRCST[x_] := mkComb[HOL`Stdlib`Real`realNegConst[], x];
realAbsRCST[x_] := mkComb[HOL`Stdlib`Real`realAbsConst[], x];
realInvRCST[x_] := mkComb[HOL`Stdlib`Real`realInvConst[], x];
natLeRCST[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], m], n];
sucRCST[n_] := mkComb[HOL`Stdlib`Num`sucConst[], n];
rnumNatRCST[n_] := mkComb[HOL`Stdlib`Real`realOfRatConst[],
  mkComb[HOL`Stdlib`Rat`ratOfIntConst[],
    mkComb[HOL`Stdlib`Int`intOfNumConst[], n]]];

allInSetRCST[sT_, uT_] :=
  Module[{nV},
    nV = mkVar["nRCST", numTyRCST];
    forallRCST[nV, setAppRCST[sT, seqAppRCST[uT, nV]]]
  ];

seqCompactBodyRCST[sT_] :=
  Module[{uV, lV},
    uV = mkVar["uRCST", seqTyRCST]; lV = mkVar["lRCST", realTyRCST];
    forallRCST[uV, impRCST[allInSetRCST[sT, uV],
      existsRCST[lV, andRCST[setAppRCST[sT, lV],
        HOL`Stdlib`Real`hasConvergentSubseqTm[uV, lV]]]]]
  ];

setCoversBodyRCST[cT_, sT_] :=
  Module[{xV, vV},
    xV = mkVar["xSetCoverRCST", realTyRCST];
    vV = mkVar["vSetCoverRCST", setTyRCST];
    forallRCST[xV, impRCST[setAppRCST[sT, xV],
      existsRCST[vV, andRCST[setMemRCST[cT, vV], setAppRCST[vV, xV]]]]]
  ];

setListSubcoverBodyRCST[cT_, sT_, vsT_] :=
  Module[{vV, xV},
    vV = mkVar["vSetListRCST", setTyRCST];
    xV = mkVar["xSetListRCST", realTyRCST];
    andRCST[
      forallRCST[vV, impRCST[memSetRCST[vV, vsT], setMemRCST[cT, vV]]],
      forallRCST[xV, impRCST[setAppRCST[sT, xV],
        existsRCST[vV, andRCST[memSetRCST[vV, vsT], setAppRCST[vV, xV]]]]]]
  ];

setFiniteSubcoverBodyRCST[cT_, sT_] :=
  Module[{vsV},
    vsV = mkVar["vsFiniteRCST", setListTyRCST];
    existsRCST[vsV, HOL`Stdlib`Real`setListSubcoverTm[cT, sT, vsV]]
  ];

isCompactBodyRCST[sT_] :=
  Module[{cV, vV},
    cV = mkVar["CCompactRCST", setOfSetsTyRCST];
    vV = mkVar["vCompactRCST", setTyRCST];
    forallRCST[cV,
      impRCST[forallRCST[vV,
          impRCST[setMemRCST[cV, vV], HOL`Stdlib`Real`isOpenTm[vV]]],
        impRCST[HOL`Stdlib`Real`setCoversTm[cV, sT],
          HOL`Stdlib`Real`setFiniteSubcoverTm[cV, sT]]]]
  ];

assertConclRCST[name_, th_, expected_] := (
  HOLTest`assertTrue[isThm[th], name <> " is thm"];
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

HOLTest`runTests["stdlib/Real/CompactSet: definition and unfold",
  Module[{sV, th, expected},
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`isSequentiallyCompactDefThm],
      "isSequentiallyCompactDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`isSequentiallyCompactDefThm], {},
      "isSequentiallyCompactDef no hyps"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`isSequentiallyCompactConst[]],
      seqCompactTyRCST, "isSequentiallyCompactConst type"];

    sV = mkVar["SRCST", setTyRCST];
    th = HOL`Stdlib`Real`unfoldIsSequentiallyCompact[sV];
    expected = mkEq[HOL`Stdlib`Real`isSequentiallyCompactTm[sV],
      seqCompactBodyRCST[sV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "isSequentiallyCompact unfold shape"]]];

HOLTest`runTests["stdlib/Real/CompactSet: theorem shapes",
  Module[{sV, uV, expectedBounded, expectedSeq},
    sV = mkVar["SShapeRCST", setTyRCST];
    uV = mkVar["uShapeRCST", seqTyRCST];

    expectedBounded = forallRCST[sV, forallRCST[uV,
      impRCST[HOL`Stdlib`Real`setBoundedTm[sV],
        impRCST[allInSetRCST[sV, uV],
          HOL`Stdlib`Real`seqBoundedTm[uV]]]]];
    assertConclRCST["seqBoundedOfSetBounded",
      HOL`Stdlib`Real`seqBoundedOfSetBoundedThm, expectedBounded];

    expectedSeq = forallRCST[sV,
      impRCST[HOL`Stdlib`Real`isClosedTm[sV],
        impRCST[HOL`Stdlib`Real`setBoundedTm[sV],
          HOL`Stdlib`Real`isSequentiallyCompactTm[sV]]]];
    assertConclRCST["sequentiallyCompactOfClosedBounded",
      HOL`Stdlib`Real`sequentiallyCompactOfClosedBoundedThm, expectedSeq]]];

HOLTest`runTests["stdlib/Real/CompactSet: bounded sequential direction shapes",
  Module[{sV, bV, xV, expectedExists, expectedLtAbs, expectedBounded},
    sV = mkVar["SBoundRCST", setTyRCST];
    bV = mkVar["BBoundRCST", realTyRCST];
    xV = mkVar["xBoundRCST", realTyRCST];

    expectedExists = forallRCST[sV, forallRCST[bV,
      impRCST[notRCST[HOL`Stdlib`Real`setBoundedTm[sV]],
        existsRCST[xV, andRCST[setAppRCST[sV, xV],
          orRCST[realLtRCST[xV, realNegRCST[bV]],
            realLtRCST[bV, xV]]]]]]];
    assertConclRCST["existsOutsideOfNotSetBounded",
      HOL`Stdlib`Real`existsOutsideOfNotSetBoundedThm, expectedExists];

    expectedLtAbs = forallRCST[xV, forallRCST[bV,
      impRCST[orRCST[realLtRCST[xV, realNegRCST[bV]], realLtRCST[bV, xV]],
        realLtRCST[bV, realAbsRCST[xV]]]]];
    assertConclRCST["ltAbsOfOutside",
      HOL`Stdlib`Real`ltAbsOfOutsideThm, expectedLtAbs];

    expectedBounded = forallRCST[sV,
      impRCST[HOL`Stdlib`Real`isSequentiallyCompactTm[sV],
        HOL`Stdlib`Real`setBoundedTm[sV]]];
    assertConclRCST["boundedOfSequentiallyCompact",
      HOL`Stdlib`Real`boundedOfSequentiallyCompactThm, expectedBounded]]];

HOLTest`runTests["stdlib/Real/CompactSet: analytic helper shapes",
  Module[{uV, phiV, lV, nV, mV, zeroR, expectedSubseq, expectedDef,
          expectedPos, expectedAnti, expectedTend},
    uV = mkVar["uAnalyticRCST", seqTyRCST];
    phiV = mkVar["phiAnalyticRCST", tyFun[numTyRCST, numTyRCST]];
    lV = mkVar["lAnalyticRCST", realTyRCST];
    nV = mkVar["nAnalyticRCST", numTyRCST];
    mV = mkVar["mAnalyticRCST", numTyRCST];
    zeroR = rnumNatRCST[HOL`Stdlib`Num`zeroConst[]];

    expectedSubseq = forallRCST[uV, forallRCST[phiV, forallRCST[lV,
      impRCST[HOL`Stdlib`Real`subseqIndexTm[phiV],
        impRCST[HOL`Stdlib`Real`tendstoTm[uV, lV],
          HOL`Stdlib`Real`tendstoTm[
            HOL`Stdlib`Real`subsequenceTm[uV, phiV], lV]]]]]];
    assertConclRCST["seqTendstoSubsequence",
      HOL`Stdlib`Real`seqTendstoSubsequenceThm, expectedSubseq];

    expectedDef = mkEq[HOL`Stdlib`Real`invSuccRadiusConst[],
      mkAbs[nV, realInvRCST[rnumNatRCST[sucRCST[nV]]]]];
    assertConclRCST["invSuccRadiusDef",
      HOL`Stdlib`Real`invSuccRadiusDefThm, expectedDef];

    expectedPos = forallRCST[nV,
      realLtRCST[zeroR, HOL`Stdlib`Real`invSuccRadiusTm[nV]]];
    assertConclRCST["invSuccRadiusPos",
      HOL`Stdlib`Real`invSuccRadiusPosThm, expectedPos];

    expectedAnti = forallRCST[mV, forallRCST[nV,
      impRCST[natLeRCST[mV, nV],
        realLeRCST[HOL`Stdlib`Real`invSuccRadiusTm[nV],
          HOL`Stdlib`Real`invSuccRadiusTm[mV]]]]];
    assertConclRCST["invSuccRadiusAntitone",
      HOL`Stdlib`Real`invSuccRadiusAntitoneThm, expectedAnti];

    expectedTend = HOL`Stdlib`Real`tendstoTm[
      HOL`Stdlib`Real`invSuccRadiusConst[], zeroR];
    assertConclRCST["invSuccRadiusTendstoZero",
      HOL`Stdlib`Real`invSuccRadiusTendstoZeroThm, expectedTend]]];

HOLTest`runTests["stdlib/Real/CompactSet: closed sequential compactness shapes",
  Module[{sV, forallSetConst, expectedClosed, expectedIff},
    sV = mkVar["SClosedSeqRCST", setTyRCST];
    forallSetConst = mkConst["∀", tyFun[tyFun[setTyRCST, boolTy], boolTy]];

    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`nearClosedPointMemThm],
      "nearClosedPointMem is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`nearClosedPointMemThm], {},
      "nearClosedPointMem no hyps"];
    HOLTest`assertTrue[aconv[concl[HOL`Stdlib`Real`nearClosedPointMemThm][[1]],
      forallSetConst], "nearClosedPointMem forall head"];

    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`nearClosedPointTendstoThm],
      "nearClosedPointTendsto is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`nearClosedPointTendstoThm], {},
      "nearClosedPointTendsto no hyps"];
    HOLTest`assertTrue[aconv[concl[HOL`Stdlib`Real`nearClosedPointTendstoThm][[1]],
      forallSetConst], "nearClosedPointTendsto forall head"];

    expectedClosed = forallRCST[sV,
      impRCST[HOL`Stdlib`Real`isSequentiallyCompactTm[sV],
        HOL`Stdlib`Real`isClosedTm[sV]]];
    assertConclRCST["closedOfSequentiallyCompact",
      HOL`Stdlib`Real`closedOfSequentiallyCompactThm, expectedClosed];

    expectedIff = forallRCST[sV,
      mkEq[HOL`Stdlib`Real`isSequentiallyCompactTm[sV],
        andRCST[HOL`Stdlib`Real`isClosedTm[sV],
          HOL`Stdlib`Real`setBoundedTm[sV]]]];
    assertConclRCST["sequentialCompactIffClosedBounded",
      HOL`Stdlib`Real`sequentialCompactIffClosedBoundedThm, expectedIff]]];

HOLTest`runTests["stdlib/Real/CompactSet: open-cover compactness vocab",
  Module[{cV, sV, vsV, th, expected},
    cV = mkVar["COpenCoverRCST", setOfSetsTyRCST];
    sV = mkVar["SOpenCoverRCST", setTyRCST];
    vsV = mkVar["VsOpenCoverRCST", setListTyRCST];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`setCoversConst[]],
      tyFun[setOfSetsTyRCST, tyFun[setTyRCST, boolTy]],
      "setCoversConst type"];
    th = HOL`Stdlib`Real`unfoldSetCovers[cV, sV];
    expected = mkEq[HOL`Stdlib`Real`setCoversTm[cV, sV],
      setCoversBodyRCST[cV, sV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "setCovers unfold shape"];

    th = HOL`Stdlib`Real`unfoldSetListSubcover[cV, sV, vsV];
    expected = mkEq[HOL`Stdlib`Real`setListSubcoverTm[cV, sV, vsV],
      setListSubcoverBodyRCST[cV, sV, vsV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "setListSubcover unfold shape"];

    th = HOL`Stdlib`Real`unfoldSetFiniteSubcover[cV, sV];
    expected = mkEq[HOL`Stdlib`Real`setFiniteSubcoverTm[cV, sV],
      setFiniteSubcoverBodyRCST[cV, sV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "setFiniteSubcover unfold shape"]]];

HOLTest`runTests["stdlib/Real/CompactSet: isCompact and open support",
  Module[{sV, lV, rV, xV, emptySet, expectedCompact, expectedOpenInt},
    sV = mkVar["SIsCompactRCST", setTyRCST];
    lV = mkVar["lOpenSupportRCST", realTyRCST];
    rV = mkVar["rOpenSupportRCST", realTyRCST];
    xV = mkVar["xEmptySupportRCST", realTyRCST];
    emptySet = mkAbs[xV, mkConst["F", boolTy]];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`isCompactConst[]],
      isCompactTyRCST, "isCompactConst type"];
    expectedCompact = mkEq[HOL`Stdlib`Real`isCompactTm[sV],
      isCompactBodyRCST[sV]];
    HOLTest`assertTrue[aconv[
      concl[HOL`Stdlib`Real`unfoldIsCompact[sV]], expectedCompact],
      "isCompact unfold shape"];

    assertConclRCST["isOpenEmpty", HOL`Stdlib`Real`isOpenEmptyThm,
      HOL`Stdlib`Real`isOpenTm[emptySet]];
    expectedOpenInt = forallRCST[lV, forallRCST[rV,
      HOL`Stdlib`Real`isOpenTm[
        mkComb[mkComb[HOL`Stdlib`Real`openIntervalConst[], lV], rV]]]];
    assertConclRCST["openIntervalIsOpen",
      HOL`Stdlib`Real`openIntervalIsOpenThm, expectedOpenInt]]];

HOLTest`runTests["stdlib/Real/CompactSet: memFilter",
  Module[{setOfSetsTy, setListTy, pV, xV, lV, memTm, filterTm, expected},
    setOfSetsTy = tyFun[setTyRCST, boolTy];
    setListTy = HOL`Stdlib`List`listTy[setTyRCST];
    pV = mkVar["pMemFilterRCST", setOfSetsTy];
    xV = mkVar["xMemFilterRCST", setTyRCST];
    lV = mkVar["lMemFilterRCST", setListTy];
    memTm[aT_, bsT_] := mkComb[mkComb[mkConst["MEM",
      tyFun[setTyRCST, tyFun[setListTy, boolTy]]], aT], bsT];
    filterTm[pT_, bsT_] := mkComb[mkComb[mkConst["FILTER",
      tyFun[setOfSetsTy, tyFun[setListTy, setListTy]]], pT], bsT];
    expected = forallRCST[pV, forallRCST[xV, forallRCST[lV,
      mkEq[memTm[xV, filterTm[pV, lV]],
        andRCST[mkComb[pV, xV], memTm[xV, lV]]]]]];
    assertConclRCST["memFilter", HOL`Stdlib`Real`memFilterThm, expected]]];
