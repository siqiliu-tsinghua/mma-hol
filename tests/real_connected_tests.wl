(* ::Package:: *)

(* Tests for M8.3 stdlib/Real/Connected.wl. *)

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

realTyCNT = mkType["real", {}];
setTyCNT = tyFun[realTyCNT, boolTy];
openInTyCNT = tyFun[setTyCNT, tyFun[setTyCNT, boolTy]];
setPredTyCNT = tyFun[setTyCNT, boolTy];
setBinTyCNT = tyFun[setTyCNT, tyFun[setTyCNT, boolTy]];
setTriTyCNT = tyFun[setTyCNT, tyFun[setTyCNT, tyFun[setTyCNT, boolTy]]];
betweenTyCNT = tyFun[realTyCNT, tyFun[realTyCNT, tyFun[realTyCNT, boolTy]]];
rayTyCNT = tyFun[realTyCNT, setTyCNT];
traceTyCNT = tyFun[setTyCNT, tyFun[setTyCNT, setTyCNT]];

andCNT[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
orCNT[p_, q_] := mkComb[
  mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impCNT[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
notCNT[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
forallCNT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
existsCNT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
conjListCNT[{p_}] := p;
conjListCNT[{p_, rest__}] := andCNT[p, conjListCNT[{rest}]];
setAppCNT[s_, x_] := mkComb[s, x];
rLeCNT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], x], y];
rLtCNT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], x], y];

specAllCNT[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

assertConclCNT[name_, th_, expected_] := (
  HOLTest`assertTrue[isThm[th], name <> " is thm"];
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

openInBodyCNT[sT_, uT_] :=
  Module[{vV, xV},
    vV = mkVar["VCNT", setTyCNT]; xV = mkVar["xCNT", realTyCNT];
    existsCNT[vV, andCNT[HOL`Stdlib`Real`isOpenTm[vV],
      forallCNT[xV, mkEq[setAppCNT[uT, xV],
        andCNT[setAppCNT[sT, xV], setAppCNT[vV, xV]]]]]]
  ];

setNonemptyBodyCNT[sT_] :=
  Module[{xV},
    xV = mkVar["xCNT", realTyCNT];
    existsCNT[xV, setAppCNT[sT, xV]]
  ];

setDisjointBodyCNT[uT_, vT_] :=
  Module[{xV},
    xV = mkVar["xCNT", realTyCNT];
    forallCNT[xV, notCNT[andCNT[setAppCNT[uT, xV], setAppCNT[vT, xV]]]]
  ];

coversByTwoBodyCNT[sT_, uT_, vT_] :=
  Module[{xV},
    xV = mkVar["xCNT", realTyCNT];
    forallCNT[xV, mkEq[setAppCNT[sT, xV],
      orCNT[setAppCNT[uT, xV], setAppCNT[vT, xV]]]]
  ];

isSeparationBodyCNT[sT_, uT_, vT_] :=
  conjListCNT[{
    HOL`Stdlib`Real`openInTm[sT, uT],
    HOL`Stdlib`Real`openInTm[sT, vT],
    HOL`Stdlib`Real`setNonemptyTm[uT],
    HOL`Stdlib`Real`setNonemptyTm[vT],
    HOL`Stdlib`Real`coversByTwoTm[sT, uT, vT],
    HOL`Stdlib`Real`setDisjointTm[uT, vT]}];

isConnectedBodyCNT[sT_] :=
  Module[{uV, vV},
    uV = mkVar["UCNT", setTyCNT]; vV = mkVar["VCNT", setTyCNT];
    forallCNT[uV, forallCNT[vV, notCNT[HOL`Stdlib`Real`isSeparationTm[sT, uV, vV]]]]
  ];

betweenBodyCNT[xT_, yT_, zT_] :=
  andCNT[rLeCNT[xT, yT], rLeCNT[yT, zT]];

isIntervalSetBodyCNT[sT_] :=
  Module[{xV, yV, zV},
    xV = mkVar["xCNT", realTyCNT]; yV = mkVar["yCNT", realTyCNT];
    zV = mkVar["zCNT", realTyCNT];
    forallCNT[xV, forallCNT[yV, forallCNT[zV,
      impCNT[setAppCNT[sT, xV],
        impCNT[setAppCNT[sT, zV],
          impCNT[HOL`Stdlib`Real`betweenTm[xV, yV, zV], setAppCNT[sT, yV]]]]]]]
  ];

traceBodyCNT[sT_, vT_] :=
  Module[{xV},
    xV = mkVar["xCNT", realTyCNT];
    mkAbs[xV, andCNT[setAppCNT[sT, xV], setAppCNT[vT, xV]]]
  ];

emptySetCNT[] :=
  Module[{xV},
    xV = mkVar["xCNT", realTyCNT];
    mkAbs[xV, mkConst["F", boolTy]]
  ];

universalSetCNT[] :=
  Module[{xV},
    xV = mkVar["xCNT", realTyCNT];
    mkAbs[xV, mkConst["T", boolTy]]
  ];

singletonSetCNT[aT_] :=
  Module[{xV},
    xV = mkVar["xCNT", realTyCNT];
    mkAbs[xV, mkEq[xV, aT]]
  ];

openIntervalSetCNT[leftT_, rightT_] :=
  mkComb[mkComb[HOL`Stdlib`Real`openIntervalConst[], leftT], rightT];
closedIntervalSetCNT[leftT_, rightT_] :=
  mkComb[mkComb[HOL`Stdlib`Real`closedIntervalConst[], leftT], rightT];
openLowerSetCNT[cutT_] := mkComb[HOL`Stdlib`Real`openLowerRayConst[], cutT];
openUpperSetCNT[cutT_] := mkComb[HOL`Stdlib`Real`openUpperRayConst[], cutT];
closedLowerSetCNT[cutT_] := mkComb[HOL`Stdlib`Real`closedLowerRayConst[], cutT];
closedUpperSetCNT[cutT_] := mkComb[HOL`Stdlib`Real`closedUpperRayConst[], cutT];

HOLTest`runTests["stdlib/Real/Connected: definitions and unfolds",
  Module[{sV, uV, vV, xV, yV, zV, cutV, th, defs, checks},
    defs = {
      {"openInDef", HOL`Stdlib`Real`openInDefThm},
      {"setNonemptyDef", HOL`Stdlib`Real`setNonemptyDefThm},
      {"setDisjointDef", HOL`Stdlib`Real`setDisjointDefThm},
      {"coversByTwoDef", HOL`Stdlib`Real`coversByTwoDefThm},
      {"isSeparationDef", HOL`Stdlib`Real`isSeparationDefThm},
      {"isConnectedDef", HOL`Stdlib`Real`isConnectedDefThm},
      {"betweenDef", HOL`Stdlib`Real`betweenDefThm},
      {"isIntervalSetDef", HOL`Stdlib`Real`isIntervalSetDefThm},
      {"openLowerRayDef", HOL`Stdlib`Real`openLowerRayDefThm},
      {"openUpperRayDef", HOL`Stdlib`Real`openUpperRayDefThm},
      {"closedLowerRayDef", HOL`Stdlib`Real`closedLowerRayDefThm},
      {"closedUpperRayDef", HOL`Stdlib`Real`closedUpperRayDefThm},
      {"traceDef", HOL`Stdlib`Real`traceDefThm}};
    Scan[Function[{entry},
      HOLTest`assertTrue[isThm[entry[[2]]], entry[[1]] <> " is thm"];
      HOLTest`assertEq[hyp[entry[[2]]], {}, entry[[1]] <> " no hyps"]], defs];

    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`openInConst[]], openInTyCNT,
      "openInConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`coversByTwoConst[]], setTriTyCNT,
      "coversByTwoConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`betweenConst[]], betweenTyCNT,
      "betweenConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`openLowerRayConst[]], rayTyCNT,
      "openLowerRayConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`traceConst[]], traceTyCNT,
      "traceConst type"];

    sV = mkVar["SCNT", setTyCNT]; uV = mkVar["UCNT", setTyCNT];
    vV = mkVar["VCNT", setTyCNT]; xV = mkVar["xCNT", realTyCNT];
    yV = mkVar["yCNT", realTyCNT]; zV = mkVar["zCNT", realTyCNT];
    cutV = mkVar["cutCNT", realTyCNT];
    checks = {
      {"openIn", HOL`Stdlib`Real`unfoldOpenIn[sV, uV],
        mkEq[HOL`Stdlib`Real`openInTm[sV, uV], openInBodyCNT[sV, uV]]},
      {"setNonempty", HOL`Stdlib`Real`unfoldSetNonempty[sV],
        mkEq[HOL`Stdlib`Real`setNonemptyTm[sV], setNonemptyBodyCNT[sV]]},
      {"setDisjoint", HOL`Stdlib`Real`unfoldSetDisjoint[uV, vV],
        mkEq[HOL`Stdlib`Real`setDisjointTm[uV, vV], setDisjointBodyCNT[uV, vV]]},
      {"coversByTwo", HOL`Stdlib`Real`unfoldCoversByTwo[sV, uV, vV],
        mkEq[HOL`Stdlib`Real`coversByTwoTm[sV, uV, vV], coversByTwoBodyCNT[sV, uV, vV]]},
      {"isSeparation", HOL`Stdlib`Real`unfoldIsSeparation[sV, uV, vV],
        mkEq[HOL`Stdlib`Real`isSeparationTm[sV, uV, vV], isSeparationBodyCNT[sV, uV, vV]]},
      {"isConnected", HOL`Stdlib`Real`unfoldIsConnected[sV],
        mkEq[HOL`Stdlib`Real`isConnectedTm[sV], isConnectedBodyCNT[sV]]},
      {"between", HOL`Stdlib`Real`unfoldBetween[xV, yV, zV],
        mkEq[HOL`Stdlib`Real`betweenTm[xV, yV, zV], betweenBodyCNT[xV, yV, zV]]},
      {"isIntervalSet", HOL`Stdlib`Real`unfoldIsIntervalSet[sV],
        mkEq[HOL`Stdlib`Real`isIntervalSetTm[sV], isIntervalSetBodyCNT[sV]]},
      {"openLowerRay", HOL`Stdlib`Real`unfoldOpenLowerRay[cutV, xV],
        mkEq[HOL`Stdlib`Real`openLowerRayTm[cutV, xV], rLtCNT[xV, cutV]]},
      {"openUpperRay", HOL`Stdlib`Real`unfoldOpenUpperRay[cutV, xV],
        mkEq[HOL`Stdlib`Real`openUpperRayTm[cutV, xV], rLtCNT[cutV, xV]]},
      {"closedLowerRay", HOL`Stdlib`Real`unfoldClosedLowerRay[cutV, xV],
        mkEq[HOL`Stdlib`Real`closedLowerRayTm[cutV, xV], rLeCNT[xV, cutV]]},
      {"closedUpperRay", HOL`Stdlib`Real`unfoldClosedUpperRay[cutV, xV],
        mkEq[HOL`Stdlib`Real`closedUpperRayTm[cutV, xV], rLeCNT[cutV, xV]]},
      {"trace", HOL`Stdlib`Real`unfoldTrace[sV, vV],
        mkEq[HOL`Stdlib`Real`traceTm[sV, vV], traceBodyCNT[sV, vV]]}};
    Scan[Function[{entry},
      HOLTest`assertTrue[aconv[concl[entry[[2]]], entry[[3]]],
        entry[[1]] <> " unfold shape"]], checks];

    th = specAllCNT[HOL`Stdlib`Real`traceMemThm, {sV, vV, xV}];
    HOLTest`assertTrue[aconv[concl[th], mkEq[setAppCNT[HOL`Stdlib`Real`traceTm[sV, vV], xV],
      andCNT[setAppCNT[sV, xV], setAppCNT[vV, xV]]]], "traceMem shape"]]];

HOLTest`runTests["stdlib/Real/Connected: theorem shapes",
  Module[{sV, uV, vV, xV, yV, zV, cutV, leftV, rightV, aV, th, expected,
          intervalThms},
    sV = mkVar["SShapeCNT", setTyCNT]; uV = mkVar["UShapeCNT", setTyCNT];
    vV = mkVar["VShapeCNT", setTyCNT]; xV = mkVar["xShapeCNT", realTyCNT];
    yV = mkVar["yShapeCNT", realTyCNT]; zV = mkVar["zShapeCNT", realTyCNT];
    cutV = mkVar["cutShapeCNT", realTyCNT];
    leftV = mkVar["leftShapeCNT", realTyCNT]; rightV = mkVar["rightShapeCNT", realTyCNT];
    aV = mkVar["aShapeCNT", realTyCNT];

    th = specAllCNT[HOL`Stdlib`Real`openInSubsetThm, {sV, uV}];
    expected = impCNT[HOL`Stdlib`Real`openInTm[sV, uV],
      forallCNT[xV, impCNT[setAppCNT[uV, xV], setAppCNT[sV, xV]]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "openInSubset shape"];

    assertConclCNT["openLowerRayIsOpen",
      HOL`Bool`SPEC[cutV, HOL`Stdlib`Real`openLowerRayIsOpenThm],
      HOL`Stdlib`Real`isOpenTm[openLowerSetCNT[cutV]]];
    assertConclCNT["openUpperRayIsOpen",
      HOL`Bool`SPEC[cutV, HOL`Stdlib`Real`openUpperRayIsOpenThm],
      HOL`Stdlib`Real`isOpenTm[openUpperSetCNT[cutV]]];

    th = specAllCNT[HOL`Stdlib`Real`ltOrGtOfNeThm, {xV, yV}];
    expected = impCNT[notCNT[mkEq[xV, yV]], orCNT[rLtCNT[xV, yV], rLtCNT[yV, xV]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "ltOrGtOfNe shape"];

    th = specAllCNT[HOL`Stdlib`Real`existsRightBetweenThm, {xV, yV, zV}];
    expected = impCNT[rLtCNT[xV, yV], impCNT[rLtCNT[xV, zV],
      existsCNT[mkVar["dCNT", realTyCNT],
        andCNT[rLtCNT[xV, mkVar["dCNT", realTyCNT]],
          andCNT[rLeCNT[mkVar["dCNT", realTyCNT], yV],
            rLtCNT[mkVar["dCNT", realTyCNT], zV]]]]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "existsRightBetween shape"];

    th = specAllCNT[HOL`Stdlib`Real`isSeparationSymmThm, {sV, uV, vV}];
    expected = impCNT[HOL`Stdlib`Real`isSeparationTm[sV, uV, vV],
      HOL`Stdlib`Real`isSeparationTm[sV, vV, uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "isSeparationSymm shape"];

    assertConclCNT["connectedEmpty", HOL`Stdlib`Real`connectedEmptyThm,
      HOL`Stdlib`Real`isConnectedTm[emptySetCNT[]]];

    th = specAllCNT[HOL`Stdlib`Real`openInTraceThm, {sV, vV}];
    expected = impCNT[HOL`Stdlib`Real`isOpenTm[vV],
      HOL`Stdlib`Real`openInTm[sV, HOL`Stdlib`Real`traceTm[sV, vV]]];
    HOLTest`assertTrue[aconv[concl[th], expected], "openInTrace shape"];

    assertConclCNT["intervalSetOfConnected",
      specAllCNT[HOL`Stdlib`Real`intervalSetOfConnectedThm, {sV}],
      impCNT[HOL`Stdlib`Real`isConnectedTm[sV],
        HOL`Stdlib`Real`isIntervalSetTm[sV]]];

    intervalThms = {
      {"interval empty", HOL`Stdlib`Real`intervalSetEmptyThm,
        HOL`Stdlib`Real`isIntervalSetTm[emptySetCNT[]]},
      {"interval universal", HOL`Stdlib`Real`intervalSetUniversalThm,
        HOL`Stdlib`Real`isIntervalSetTm[universalSetCNT[]]},
      {"interval singleton", HOL`Bool`SPEC[aV, HOL`Stdlib`Real`intervalSetSingletonThm],
        HOL`Stdlib`Real`isIntervalSetTm[singletonSetCNT[aV]]},
      {"interval open", specAllCNT[HOL`Stdlib`Real`intervalSetOpenIntervalThm, {leftV, rightV}],
        HOL`Stdlib`Real`isIntervalSetTm[openIntervalSetCNT[leftV, rightV]]},
      {"interval closed", specAllCNT[HOL`Stdlib`Real`intervalSetClosedIntervalThm, {leftV, rightV}],
        HOL`Stdlib`Real`isIntervalSetTm[closedIntervalSetCNT[leftV, rightV]]},
      {"interval open lower", HOL`Bool`SPEC[cutV, HOL`Stdlib`Real`intervalSetOpenLowerRayThm],
        HOL`Stdlib`Real`isIntervalSetTm[openLowerSetCNT[cutV]]},
      {"interval open upper", HOL`Bool`SPEC[cutV, HOL`Stdlib`Real`intervalSetOpenUpperRayThm],
        HOL`Stdlib`Real`isIntervalSetTm[openUpperSetCNT[cutV]]},
      {"interval closed lower", HOL`Bool`SPEC[cutV, HOL`Stdlib`Real`intervalSetClosedLowerRayThm],
        HOL`Stdlib`Real`isIntervalSetTm[closedLowerSetCNT[cutV]]},
      {"interval closed upper", HOL`Bool`SPEC[cutV, HOL`Stdlib`Real`intervalSetClosedUpperRayThm],
        HOL`Stdlib`Real`isIntervalSetTm[closedUpperSetCNT[cutV]]}};
    Scan[Function[{entry}, assertConclCNT[entry[[1]], entry[[2]], entry[[3]]]],
      intervalThms]]];
