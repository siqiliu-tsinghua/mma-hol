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
seqTyRCST = tyFun[numTyRCST, realTyRCST];
seqCompactTyRCST = tyFun[setTyRCST, boolTy];

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
