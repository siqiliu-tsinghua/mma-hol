(* ::Package:: *)

(* Tests for M8.4 stdlib/Real/Topology.wl. *)

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

realTyRTT = mkType["real", {}];
numTyRTT = mkType["num", {}];
setTyRTT = tyFun[realTyRTT, boolTy];
seqTyRTT = tyFun[numTyRTT, realTyRTT];
complTyRTT = tyFun[setTyRTT, setTyRTT];
setPredTyRTT = tyFun[setTyRTT, boolTy];
setBinTyRTT = tyFun[setTyRTT, tyFun[setTyRTT, boolTy]];

andRTT[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impRTT[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
notRTT[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
forallRTT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
existsRTT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
setAppRTT[s_, x_] := mkComb[s, x];
seqAppRTT[u_, n_] := mkComb[u, n];
natLeRTT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
realLeRTT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], a], b];
realLtRTT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], a], b];
realAddRTT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], a], b];
realNegRTT[a_] := mkComb[HOL`Stdlib`Real`realNegConst[], a];
realAbsRTT[a_] := mkComb[HOL`Stdlib`Real`realAbsConst[], a];
closedIntervalSetRTT[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Real`closedIntervalConst[], a], b];

specAllRTT[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

assertConclRTT[name_, th_, expected_] := (
  HOLTest`assertTrue[isThm[th], name <> " is thm"];
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

complBodyRTT[sT_] :=
  Module[{xV},
    xV = mkVar["xRTT", realTyRTT];
    mkAbs[xV, notRTT[setAppRTT[sT, xV]]]
  ];

relativeClosedBodyRTT[sT_, uT_] :=
  Module[{vV, xV},
    vV = mkVar["VRTT", setTyRTT]; xV = mkVar["xRTT", realTyRTT];
    existsRTT[vV, andRTT[HOL`Stdlib`Real`isClosedTm[vV],
      forallRTT[xV, mkEq[setAppRTT[uT, xV],
        andRTT[setAppRTT[sT, xV], setAppRTT[vV, xV]]]]]]
  ];

openSeqPredRTT[uT_, leftT_, rightT_] :=
  Module[{nV},
    nV = mkVar["nOpenRTT", numTyRTT];
    mkAbs[nV, HOL`Stdlib`Real`openIntervalTm[leftT, rightT, seqAppRTT[uT, nV]]]
  ];

HOLTest`runTests["stdlib/Real/Topology: definitions and unfolds",
  Module[{sV, uV, xV, defs, checks, th, expected},
    defs = {
      {"complDef", HOL`Stdlib`Real`complDefThm},
      {"isClosedDef", HOL`Stdlib`Real`isClosedDefThm},
      {"relativeClosedDef", HOL`Stdlib`Real`relativeClosedDefThm},
      {"closedInDef", HOL`Stdlib`Real`closedInDefThm}};
    Scan[Function[{entry},
      HOLTest`assertTrue[isThm[entry[[2]]], entry[[1]] <> " is thm"];
      HOLTest`assertEq[hyp[entry[[2]]], {}, entry[[1]] <> " no hyps"]], defs];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`complConst[]], complTyRTT,
      "complConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`isClosedConst[]], setPredTyRTT,
      "isClosedConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`relativeClosedConst[]], setBinTyRTT,
      "relativeClosedConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`closedInConst[]], setBinTyRTT,
      "closedInConst type"];

    sV = mkVar["SRTT", setTyRTT]; uV = mkVar["URTT", setTyRTT];
    xV = mkVar["xRTT", realTyRTT];
    checks = {
      {"compl", HOL`Stdlib`Real`unfoldCompl[sV],
        mkEq[HOL`Stdlib`Real`complTm[sV], complBodyRTT[sV]]},
      {"isClosed", HOL`Stdlib`Real`unfoldIsClosed[sV],
        mkEq[HOL`Stdlib`Real`isClosedTm[sV],
          HOL`Stdlib`Real`isOpenTm[HOL`Stdlib`Real`complTm[sV]]]},
      {"relativeClosed", HOL`Stdlib`Real`unfoldRelativeClosed[sV, uV],
        mkEq[HOL`Stdlib`Real`relativeClosedTm[sV, uV],
          relativeClosedBodyRTT[sV, uV]]},
      {"closedIn", HOL`Stdlib`Real`unfoldClosedIn[sV, uV],
        mkEq[HOL`Stdlib`Real`closedInTm[sV, uV],
          HOL`Stdlib`Real`relativeClosedTm[sV, uV]]}};
    Scan[Function[{entry},
      HOLTest`assertTrue[aconv[concl[entry[[2]]], entry[[3]]],
        entry[[1]] <> " unfold shape"]], checks];

    th = specAllRTT[HOL`Stdlib`Real`complMemThm, {sV, xV}];
    expected = mkEq[setAppRTT[HOL`Stdlib`Real`complTm[sV], xV],
      notRTT[setAppRTT[sV, xV]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "complMem shape"];

    th = HOL`Bool`SPEC[sV, HOL`Stdlib`Real`isClosedMemThm];
    expected = mkEq[HOL`Stdlib`Real`isClosedTm[sV],
      HOL`Stdlib`Real`isOpenTm[HOL`Stdlib`Real`complTm[sV]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "isClosedMem shape"];

    th = specAllRTT[HOL`Stdlib`Real`relativeClosedMemThm, {sV, uV}];
    expected = mkEq[HOL`Stdlib`Real`relativeClosedTm[sV, uV],
      relativeClosedBodyRTT[sV, uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "relativeClosedMem shape"];

    th = specAllRTT[HOL`Stdlib`Real`closedInMemThm, {sV, uV}];
    expected = mkEq[HOL`Stdlib`Real`closedInTm[sV, uV],
      HOL`Stdlib`Real`relativeClosedTm[sV, uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "closedInMem shape"]]];

HOLTest`runTests["stdlib/Real/Topology: theorem shapes",
  Module[{sV, uV, xV, aV, bV, th, expected},
    sV = mkVar["SShapeRTT", setTyRTT]; uV = mkVar["UShapeRTT", setTyRTT];
    xV = mkVar["xShapeRTT", realTyRTT];
    aV = mkVar["aShapeRTT", realTyRTT]; bV = mkVar["bShapeRTT", realTyRTT];

    th = HOL`Bool`SPEC[sV, HOL`Stdlib`Real`isClosedComplOpenThm];
    expected = mkEq[HOL`Stdlib`Real`isClosedTm[sV],
      HOL`Stdlib`Real`isOpenTm[HOL`Stdlib`Real`complTm[sV]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "isClosedComplOpen shape"];

    th = specAllRTT[HOL`Stdlib`Real`closedInSubsetThm, {sV, uV}];
    expected = impRTT[HOL`Stdlib`Real`closedInTm[sV, uV],
      forallRTT[xV, impRTT[setAppRTT[uV, xV], setAppRTT[sV, xV]]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "closedInSubset shape"];

    assertConclRTT["closedIntervalIsClosed",
      specAllRTT[HOL`Stdlib`Real`closedIntervalIsClosedThm, {aV, bV}],
      HOL`Stdlib`Real`isClosedTm[closedIntervalSetRTT[aV, bV]]]]];

HOLTest`runTests["stdlib/Real/Topology: sequential closed-set bridge shapes",
  Module[{sV, uV, lV, leftV, rightV, nV, pointExpected, limitExpected},
    sV = mkVar["SSeqRTT", setTyRTT];
    uV = mkVar["uSeqRTT", seqTyRTT];
    lV = mkVar["lSeqRTT", realTyRTT];
    leftV = mkVar["leftSeqRTT", realTyRTT];
    rightV = mkVar["rightSeqRTT", realTyRTT];
    nV = mkVar["nSeqRTT", numTyRTT];
    pointExpected = forallRTT[uV, forallRTT[lV, forallRTT[leftV, forallRTT[rightV,
      impRTT[HOL`Stdlib`Real`tendstoTm[uV, lV],
        impRTT[realLtRTT[leftV, lV],
          impRTT[realLtRTT[lV, rightV],
            HOL`Stdlib`Real`eventuallyTm[openSeqPredRTT[uV, leftV, rightV]]]]]]]]];
    assertConclRTT["pointInOpenIntervalOfTendsto",
      HOL`Stdlib`Real`pointInOpenIntervalOfTendstoThm, pointExpected];

    limitExpected = forallRTT[sV, forallRTT[uV, forallRTT[lV,
      impRTT[HOL`Stdlib`Real`isClosedTm[sV],
        impRTT[forallRTT[nV, setAppRTT[sV, seqAppRTT[uV, nV]]],
          impRTT[HOL`Stdlib`Real`tendstoTm[uV, lV],
            setAppRTT[sV, lV]]]]]]];
    assertConclRTT["limitMemOfClosed",
      HOL`Stdlib`Real`limitMemOfClosedThm, limitExpected]]];
