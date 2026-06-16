(* M8.3 / stdlib/Real/Connected.wl - connectedness and interval-set basics. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`Arith`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

openInDefThm::usage = "openInDefThm - |- openIn = (lambda S U. exists V. isOpen V /\\ forall x. U x = (S x /\\ V x)).";
openInConst::usage = "openInConst[] - openIn : (real -> bool) -> (real -> bool) -> bool.";
openInTm::usage = "openInTm[S, U] - builds openIn S U.";
unfoldOpenIn::usage = "unfoldOpenIn[S, U] - proves the beta-reduced openIn definition at S and U.";
openInMemThm::usage = "openInMemThm - |- forall S U. openIn S U = (exists V. isOpen V /\\ forall x. U x = (S x /\\ V x)).";

setNonemptyDefThm::usage = "setNonemptyDefThm - |- setNonempty = (lambda S. exists x. S x).";
setNonemptyConst::usage = "setNonemptyConst[] - setNonempty : (real -> bool) -> bool.";
setNonemptyTm::usage = "setNonemptyTm[S] - builds setNonempty S.";
unfoldSetNonempty::usage = "unfoldSetNonempty[S] - proves the beta-reduced setNonempty definition at S.";
setNonemptyMemThm::usage = "setNonemptyMemThm - |- forall S. setNonempty S = (exists x. S x).";

setDisjointDefThm::usage = "setDisjointDefThm - |- setDisjoint = (lambda U V. forall x. ~(U x /\\ V x)).";
setDisjointConst::usage = "setDisjointConst[] - setDisjoint : (real -> bool) -> (real -> bool) -> bool.";
setDisjointTm::usage = "setDisjointTm[U, V] - builds setDisjoint U V.";
unfoldSetDisjoint::usage = "unfoldSetDisjoint[U, V] - proves the beta-reduced setDisjoint definition at U and V.";
setDisjointMemThm::usage = "setDisjointMemThm - |- forall U V. setDisjoint U V = (forall x. ~(U x /\\ V x)).";

coversByTwoDefThm::usage = "coversByTwoDefThm - |- coversByTwo = (lambda S U V. forall x. S x = (U x \\/ V x)).";
coversByTwoConst::usage = "coversByTwoConst[] - coversByTwo : (real -> bool) -> (real -> bool) -> (real -> bool) -> bool.";
coversByTwoTm::usage = "coversByTwoTm[S, U, V] - builds coversByTwo S U V.";
unfoldCoversByTwo::usage = "unfoldCoversByTwo[S, U, V] - proves the beta-reduced coversByTwo definition at S, U, and V.";
coversByTwoMemThm::usage = "coversByTwoMemThm - |- forall S U V. coversByTwo S U V = (forall x. S x = (U x \\/ V x)).";

isSeparationDefThm::usage = "isSeparationDefThm - |- isSeparation = (lambda S U V. openIn S U /\\ openIn S V /\\ setNonempty U /\\ setNonempty V /\\ coversByTwo S U V /\\ setDisjoint U V).";
isSeparationConst::usage = "isSeparationConst[] - isSeparation : (real -> bool) -> (real -> bool) -> (real -> bool) -> bool.";
isSeparationTm::usage = "isSeparationTm[S, U, V] - builds isSeparation S U V.";
unfoldIsSeparation::usage = "unfoldIsSeparation[S, U, V] - proves the beta-reduced isSeparation definition at S, U, and V.";
isSeparationMemThm::usage = "isSeparationMemThm - |- forall S U V. isSeparation S U V = (... six conjuncts ...).";

isConnectedDefThm::usage = "isConnectedDefThm - |- isConnected = (lambda S. forall U V. ~(isSeparation S U V)).";
isConnectedConst::usage = "isConnectedConst[] - isConnected : (real -> bool) -> bool.";
isConnectedTm::usage = "isConnectedTm[S] - builds isConnected S.";
unfoldIsConnected::usage = "unfoldIsConnected[S] - proves the beta-reduced isConnected definition at S.";
isConnectedMemThm::usage = "isConnectedMemThm - |- forall S. isConnected S = (forall U V. ~(isSeparation S U V)).";

betweenDefThm::usage = "betweenDefThm - |- between = (lambda x y z. realLe x y /\\ realLe y z).";
betweenConst::usage = "betweenConst[] - between : real -> real -> real -> bool.";
betweenTm::usage = "betweenTm[x, y, z] - builds between x y z.";
unfoldBetween::usage = "unfoldBetween[x, y, z] - proves the beta-reduced between definition at x, y, and z.";
betweenMemThm::usage = "betweenMemThm - |- forall x y z. between x y z = (realLe x y /\\ realLe y z).";

isIntervalSetDefThm::usage = "isIntervalSetDefThm - |- isIntervalSet = (lambda S. forall x y z. S x ==> S z ==> between x y z ==> S y).";
isIntervalSetConst::usage = "isIntervalSetConst[] - isIntervalSet : (real -> bool) -> bool.";
isIntervalSetTm::usage = "isIntervalSetTm[S] - builds isIntervalSet S.";
unfoldIsIntervalSet::usage = "unfoldIsIntervalSet[S] - proves the beta-reduced isIntervalSet definition at S.";
isIntervalSetMemThm::usage = "isIntervalSetMemThm - |- forall S. isIntervalSet S = (forall x y z. S x ==> S z ==> between x y z ==> S y).";

openLowerRayDefThm::usage = "openLowerRayDefThm - |- openLowerRay = (lambda cut x. realLt x cut).";
openLowerRayConst::usage = "openLowerRayConst[] - openLowerRay : real -> real -> bool.";
openLowerRayTm::usage = "openLowerRayTm[cut, x] - builds openLowerRay cut x.";
unfoldOpenLowerRay::usage = "unfoldOpenLowerRay[cut, x] - proves the beta-reduced openLowerRay definition at cut and x.";
openLowerRayMemThm::usage = "openLowerRayMemThm - |- forall cut x. openLowerRay cut x = realLt x cut.";

openUpperRayDefThm::usage = "openUpperRayDefThm - |- openUpperRay = (lambda cut x. realLt cut x).";
openUpperRayConst::usage = "openUpperRayConst[] - openUpperRay : real -> real -> bool.";
openUpperRayTm::usage = "openUpperRayTm[cut, x] - builds openUpperRay cut x.";
unfoldOpenUpperRay::usage = "unfoldOpenUpperRay[cut, x] - proves the beta-reduced openUpperRay definition at cut and x.";
openUpperRayMemThm::usage = "openUpperRayMemThm - |- forall cut x. openUpperRay cut x = realLt cut x.";

closedLowerRayDefThm::usage = "closedLowerRayDefThm - |- closedLowerRay = (lambda cut x. realLe x cut).";
closedLowerRayConst::usage = "closedLowerRayConst[] - closedLowerRay : real -> real -> bool.";
closedLowerRayTm::usage = "closedLowerRayTm[cut, x] - builds closedLowerRay cut x.";
unfoldClosedLowerRay::usage = "unfoldClosedLowerRay[cut, x] - proves the beta-reduced closedLowerRay definition at cut and x.";
closedLowerRayMemThm::usage = "closedLowerRayMemThm - |- forall cut x. closedLowerRay cut x = realLe x cut.";

closedUpperRayDefThm::usage = "closedUpperRayDefThm - |- closedUpperRay = (lambda cut x. realLe cut x).";
closedUpperRayConst::usage = "closedUpperRayConst[] - closedUpperRay : real -> real -> bool.";
closedUpperRayTm::usage = "closedUpperRayTm[cut, x] - builds closedUpperRay cut x.";
unfoldClosedUpperRay::usage = "unfoldClosedUpperRay[cut, x] - proves the beta-reduced closedUpperRay definition at cut and x.";
closedUpperRayMemThm::usage = "closedUpperRayMemThm - |- forall cut x. closedUpperRay cut x = realLe cut x.";

traceDefThm::usage = "traceDefThm - |- trace = (lambda S V. lambda x. S x /\\ V x).";
traceConst::usage = "traceConst[] - trace : (real -> bool) -> (real -> bool) -> (real -> bool).";
traceTm::usage = "traceTm[S, V] - builds trace S V.";
unfoldTrace::usage = "unfoldTrace[S, V] - proves the beta-reduced trace definition at S and V.";
traceMemThm::usage = "traceMemThm - |- forall S V x. trace S V x = (S x /\\ V x).";

openInSubsetThm::usage = "openInSubsetThm - |- forall S U. openIn S U ==> forall x. U x ==> S x.";
openLowerRayIsOpenThm::usage = "openLowerRayIsOpenThm - |- forall cut. isOpen (openLowerRay cut).";
openUpperRayIsOpenThm::usage = "openUpperRayIsOpenThm - |- forall cut. isOpen (openUpperRay cut).";
ltOrGtOfNeThm::usage = "ltOrGtOfNeThm - |- forall x y. ~(x = y) ==> realLt x y \\/ realLt y x.";
existsRightBetweenThm::usage = "existsRightBetweenThm - |- forall x y z. realLt x y ==> realLt x z ==> exists d. realLt x d /\\ realLe d y /\\ realLt d z.";
isSeparationSymmThm::usage = "isSeparationSymmThm - |- forall S U V. isSeparation S U V ==> isSeparation S V U.";
connectedEmptyThm::usage = "connectedEmptyThm - |- isConnected (lambda x. F).";
openInTraceThm::usage = "openInTraceThm - |- forall S V. isOpen V ==> openIn S (trace S V).";

intervalSetEmptyThm::usage = "intervalSetEmptyThm - |- isIntervalSet (lambda x. F).";
intervalSetUniversalThm::usage = "intervalSetUniversalThm - |- isIntervalSet (lambda x. T).";
intervalSetSingletonThm::usage = "intervalSetSingletonThm - |- forall a. isIntervalSet (lambda x. x = a).";
intervalSetOpenIntervalThm::usage = "intervalSetOpenIntervalThm - |- forall left right. isIntervalSet (openInterval left right).";
intervalSetClosedIntervalThm::usage = "intervalSetClosedIntervalThm - |- forall left right. isIntervalSet (closedInterval left right).";
intervalSetOpenLowerRayThm::usage = "intervalSetOpenLowerRayThm - |- forall cut. isIntervalSet (openLowerRay cut).";
intervalSetOpenUpperRayThm::usage = "intervalSetOpenUpperRayThm - |- forall cut. isIntervalSet (openUpperRay cut).";
intervalSetClosedLowerRayThm::usage = "intervalSetClosedLowerRayThm - |- forall cut. isIntervalSet (closedLowerRay cut).";
intervalSetClosedUpperRayThm::usage = "intervalSetClosedUpperRayThm - |- forall cut. isIntervalSet (closedUpperRay cut).";

Begin["`Private`"];

connectedRealTy = mkType["real", {}];
connectedSetTy = tyFun[connectedRealTy, boolTy];
openInTy = tyFun[connectedSetTy, tyFun[connectedSetTy, boolTy]];
setNonemptyTy = tyFun[connectedSetTy, boolTy];
setDisjointTy = tyFun[connectedSetTy, tyFun[connectedSetTy, boolTy]];
coversByTwoTy = tyFun[connectedSetTy, tyFun[connectedSetTy, tyFun[connectedSetTy, boolTy]]];
isSeparationTy = coversByTwoTy;
isConnectedTy = tyFun[connectedSetTy, boolTy];
betweenTy = tyFun[connectedRealTy, tyFun[connectedRealTy, tyFun[connectedRealTy, boolTy]]];
isIntervalSetTy = tyFun[connectedSetTy, boolTy];
connectedRayTy = tyFun[connectedRealTy, connectedSetTy];
traceTy = tyFun[connectedSetTy, tyFun[connectedSetTy, connectedSetTy]];

connectedAndConst[] := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
connectedOrConst[] := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
connectedImpConst[] := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
connectedNotConst[] := mkConst["¬", tyFun[boolTy, boolTy]];
connectedTrueTm[] := mkConst["T", boolTy];
connectedFalseTm[] := mkConst["F", boolTy];
connectedConjTm[pT_, qT_] := mkComb[mkComb[connectedAndConst[], pT], qT];
connectedDisjTm[pT_, qT_] := mkComb[mkComb[connectedOrConst[], pT], qT];
connectedImpTm[pT_, qT_] := mkComb[mkComb[connectedImpConst[], pT], qT];
connectedNotTm[pT_] := mkComb[connectedNotConst[], pT];
connectedForallTm[vT_, bodyT_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];
connectedExistsTm[vT_, bodyT_] :=
  mkComb[mkConst["∃", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];
connectedConjList[{pT_}] := pT;
connectedConjList[{pT_, restT__}] := connectedConjTm[pT, connectedConjList[{restT}]];
connectedForallList[vars_List, bodyT_] :=
  Fold[Function[{accT, vT}, connectedForallTm[vT, accT]], bodyT, Reverse[vars]];
connectedSpecAll[th_, terms_List] :=
  Fold[Function[{accTh, termT}, HOL`Bool`SPEC[termT, accTh]], th, terms];

connectedSetApp[sT_, xT_] := mkComb[sT, xT];
connectedRealLe[aT_, bT_] := mkComb[mkComb[realLeConst[], aT], bT];
connectedRealLt[aT_, bT_] := mkComb[mkComb[realLtConst[], aT], bT];
connectedRealAdd[aT_, bT_] := mkComb[mkComb[realAddConst[], aT], bT];
connectedRealNeg[aT_] := mkComb[realNegConst[], aT];
connectedZeroNum[] := HOL`Stdlib`Num`zeroConst[];
connectedSucNum[nT_] := mkComb[HOL`Stdlib`Num`sucConst[], nT];
connectedOneNum[] := connectedSucNum[connectedZeroNum[]];
connectedIntOfNum[nT_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], nT];
connectedRatOfInt[zT_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], zT];
connectedRealOfRat[qT_] := mkComb[realOfRatConst[], qT];
connectedOneReal[] := connectedRealOfRat[connectedRatOfInt[connectedIntOfNum[connectedOneNum[]]]];
connectedRealSubOne[xT_] := connectedRealAdd[xT, connectedRealNeg[connectedOneReal[]]];
connectedRealAddOne[xT_] := connectedRealAdd[xT, connectedOneReal[]];

connectedRealLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqLeft], eqRight];
connectedRealLtCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], eqLeft], eqRight];

connectedApplyDef[defTh_, args_List] :=
  Fold[Function[{accTh, argT}, Module[{stepTh},
    stepTh = HOL`Equal`APTHM[accTh, argT];
    TRANS[stepTh, HOL`Equal`BETACONV[concl[stepTh][[2]]]]
  ]], defTh, args];

connectedOpenInBody[sT_, uT_] :=
  Module[{vV, xV},
    vV = mkVar["vCn", connectedSetTy]; xV = mkVar["xCn", connectedRealTy];
    connectedExistsTm[vV, connectedConjTm[isOpenTm[vV],
      connectedForallTm[xV, mkEq[connectedSetApp[uT, xV],
        connectedConjTm[connectedSetApp[sT, xV], connectedSetApp[vV, xV]]]]]]
  ];

connectedSetNonemptyBody[sT_] :=
  Module[{xV},
    xV = mkVar["xCn", connectedRealTy];
    connectedExistsTm[xV, connectedSetApp[sT, xV]]
  ];

connectedSetDisjointBody[uT_, vT_] :=
  Module[{xV},
    xV = mkVar["xCn", connectedRealTy];
    connectedForallTm[xV, connectedNotTm[
      connectedConjTm[connectedSetApp[uT, xV], connectedSetApp[vT, xV]]]]
  ];

connectedCoversByTwoBody[sT_, uT_, vT_] :=
  Module[{xV},
    xV = mkVar["xCn", connectedRealTy];
    connectedForallTm[xV, mkEq[connectedSetApp[sT, xV],
      connectedDisjTm[connectedSetApp[uT, xV], connectedSetApp[vT, xV]]]]
  ];

connectedIsSeparationBody[sT_, uT_, vT_] :=
  connectedConjList[{
    openInTm[sT, uT],
    openInTm[sT, vT],
    setNonemptyTm[uT],
    setNonemptyTm[vT],
    coversByTwoTm[sT, uT, vT],
    setDisjointTm[uT, vT]}];

connectedIsConnectedBody[sT_] :=
  Module[{uV, vV},
    uV = mkVar["uCn", connectedSetTy]; vV = mkVar["vCn", connectedSetTy];
    connectedForallTm[uV, connectedForallTm[vV,
      connectedNotTm[isSeparationTm[sT, uV, vV]]]]
  ];

connectedBetweenBody[xT_, yT_, zT_] :=
  connectedConjTm[connectedRealLe[xT, yT], connectedRealLe[yT, zT]];

connectedIsIntervalSetBody[sT_] :=
  Module[{xV, yV, zV},
    xV = mkVar["xCn", connectedRealTy]; yV = mkVar["yCn", connectedRealTy];
    zV = mkVar["zCn", connectedRealTy];
    connectedForallTm[xV, connectedForallTm[yV, connectedForallTm[zV,
      connectedImpTm[connectedSetApp[sT, xV],
        connectedImpTm[connectedSetApp[sT, zV],
          connectedImpTm[betweenTm[xV, yV, zV], connectedSetApp[sT, yV]]]]]]]
  ];

connectedTraceBody[sT_, vT_] :=
  Module[{xV},
    xV = mkVar["xCn", connectedRealTy];
    mkAbs[xV, connectedConjTm[connectedSetApp[sT, xV], connectedSetApp[vT, xV]]]
  ];

openInDefThm =
  Module[{sV, uV},
    sV = mkVar["S", connectedSetTy]; uV = mkVar["U", connectedSetTy];
    newDefinition[mkEq[mkVar["openIn", openInTy],
      mkAbs[sV, mkAbs[uV, connectedOpenInBody[sV, uV]]]]]
  ];

openInConst[] := mkConst["openIn", openInTy];
openInTm[sT_, uT_] := mkComb[mkComb[openInConst[], sT], uT];
unfoldOpenIn[sT_, uT_] := connectedApplyDef[openInDefThm, {sT, uT}];
openInMemThm =
  Module[{sV, uV},
    sV = mkVar["S", connectedSetTy]; uV = mkVar["U", connectedSetTy];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, unfoldOpenIn[sV, uV]]]
  ];

setNonemptyDefThm =
  Module[{sV},
    sV = mkVar["S", connectedSetTy];
    newDefinition[mkEq[mkVar["setNonempty", setNonemptyTy],
      mkAbs[sV, connectedSetNonemptyBody[sV]]]]
  ];

setNonemptyConst[] := mkConst["setNonempty", setNonemptyTy];
setNonemptyTm[sT_] := mkComb[setNonemptyConst[], sT];
unfoldSetNonempty[sT_] := connectedApplyDef[setNonemptyDefThm, {sT}];
setNonemptyMemThm =
  Module[{sV},
    sV = mkVar["S", connectedSetTy];
    HOL`Bool`GEN[sV, unfoldSetNonempty[sV]]
  ];

setDisjointDefThm =
  Module[{uV, vV},
    uV = mkVar["U", connectedSetTy]; vV = mkVar["V", connectedSetTy];
    newDefinition[mkEq[mkVar["setDisjoint", setDisjointTy],
      mkAbs[uV, mkAbs[vV, connectedSetDisjointBody[uV, vV]]]]]
  ];

setDisjointConst[] := mkConst["setDisjoint", setDisjointTy];
setDisjointTm[uT_, vT_] := mkComb[mkComb[setDisjointConst[], uT], vT];
unfoldSetDisjoint[uT_, vT_] := connectedApplyDef[setDisjointDefThm, {uT, vT}];
setDisjointMemThm =
  Module[{uV, vV},
    uV = mkVar["U", connectedSetTy]; vV = mkVar["V", connectedSetTy];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[vV, unfoldSetDisjoint[uV, vV]]]
  ];

coversByTwoDefThm =
  Module[{sV, uV, vV},
    sV = mkVar["S", connectedSetTy]; uV = mkVar["U", connectedSetTy];
    vV = mkVar["V", connectedSetTy];
    newDefinition[mkEq[mkVar["coversByTwo", coversByTwoTy],
      mkAbs[sV, mkAbs[uV, mkAbs[vV, connectedCoversByTwoBody[sV, uV, vV]]]]]]
  ];

coversByTwoConst[] := mkConst["coversByTwo", coversByTwoTy];
coversByTwoTm[sT_, uT_, vT_] :=
  mkComb[mkComb[mkComb[coversByTwoConst[], sT], uT], vT];
unfoldCoversByTwo[sT_, uT_, vT_] :=
  connectedApplyDef[coversByTwoDefThm, {sT, uT, vT}];
coversByTwoMemThm =
  Module[{sV, uV, vV},
    sV = mkVar["S", connectedSetTy]; uV = mkVar["U", connectedSetTy];
    vV = mkVar["V", connectedSetTy];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, HOL`Bool`GEN[vV,
      unfoldCoversByTwo[sV, uV, vV]]]]
  ];

isSeparationDefThm =
  Module[{sV, uV, vV},
    sV = mkVar["S", connectedSetTy]; uV = mkVar["U", connectedSetTy];
    vV = mkVar["V", connectedSetTy];
    newDefinition[mkEq[mkVar["isSeparation", isSeparationTy],
      mkAbs[sV, mkAbs[uV, mkAbs[vV, connectedIsSeparationBody[sV, uV, vV]]]]]]
  ];

isSeparationConst[] := mkConst["isSeparation", isSeparationTy];
isSeparationTm[sT_, uT_, vT_] :=
  mkComb[mkComb[mkComb[isSeparationConst[], sT], uT], vT];
unfoldIsSeparation[sT_, uT_, vT_] :=
  connectedApplyDef[isSeparationDefThm, {sT, uT, vT}];
isSeparationMemThm =
  Module[{sV, uV, vV},
    sV = mkVar["S", connectedSetTy]; uV = mkVar["U", connectedSetTy];
    vV = mkVar["V", connectedSetTy];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, HOL`Bool`GEN[vV,
      unfoldIsSeparation[sV, uV, vV]]]]
  ];

isConnectedDefThm =
  Module[{sV},
    sV = mkVar["S", connectedSetTy];
    newDefinition[mkEq[mkVar["isConnected", isConnectedTy],
      mkAbs[sV, connectedIsConnectedBody[sV]]]]
  ];

isConnectedConst[] := mkConst["isConnected", isConnectedTy];
isConnectedTm[sT_] := mkComb[isConnectedConst[], sT];
unfoldIsConnected[sT_] := connectedApplyDef[isConnectedDefThm, {sT}];
isConnectedMemThm =
  Module[{sV},
    sV = mkVar["S", connectedSetTy];
    HOL`Bool`GEN[sV, unfoldIsConnected[sV]]
  ];

betweenDefThm =
  Module[{xV, yV, zV},
    xV = mkVar["x", connectedRealTy]; yV = mkVar["y", connectedRealTy];
    zV = mkVar["z", connectedRealTy];
    newDefinition[mkEq[mkVar["between", betweenTy],
      mkAbs[xV, mkAbs[yV, mkAbs[zV, connectedBetweenBody[xV, yV, zV]]]]]]
  ];

betweenConst[] := mkConst["between", betweenTy];
betweenTm[xT_, yT_, zT_] := mkComb[mkComb[mkComb[betweenConst[], xT], yT], zT];
unfoldBetween[xT_, yT_, zT_] := connectedApplyDef[betweenDefThm, {xT, yT, zT}];
betweenMemThm =
  Module[{xV, yV, zV},
    xV = mkVar["x", connectedRealTy]; yV = mkVar["y", connectedRealTy];
    zV = mkVar["z", connectedRealTy];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      unfoldBetween[xV, yV, zV]]]]
  ];

isIntervalSetDefThm =
  Module[{sV},
    sV = mkVar["S", connectedSetTy];
    newDefinition[mkEq[mkVar["isIntervalSet", isIntervalSetTy],
      mkAbs[sV, connectedIsIntervalSetBody[sV]]]]
  ];

isIntervalSetConst[] := mkConst["isIntervalSet", isIntervalSetTy];
isIntervalSetTm[sT_] := mkComb[isIntervalSetConst[], sT];
unfoldIsIntervalSet[sT_] := connectedApplyDef[isIntervalSetDefThm, {sT}];
isIntervalSetMemThm =
  Module[{sV},
    sV = mkVar["S", connectedSetTy];
    HOL`Bool`GEN[sV, unfoldIsIntervalSet[sV]]
  ];

openLowerRayDefThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    newDefinition[mkEq[mkVar["openLowerRay", connectedRayTy],
      mkAbs[cutV, mkAbs[xV, connectedRealLt[xV, cutV]]]]]
  ];

openLowerRayConst[] := mkConst["openLowerRay", connectedRayTy];
openLowerRayTm[cutT_, xT_] := mkComb[mkComb[openLowerRayConst[], cutT], xT];
unfoldOpenLowerRay[cutT_, xT_] := connectedApplyDef[openLowerRayDefThm, {cutT, xT}];
openLowerRayMemThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    HOL`Bool`GEN[cutV, HOL`Bool`GEN[xV, unfoldOpenLowerRay[cutV, xV]]]
  ];

openUpperRayDefThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    newDefinition[mkEq[mkVar["openUpperRay", connectedRayTy],
      mkAbs[cutV, mkAbs[xV, connectedRealLt[cutV, xV]]]]]
  ];

openUpperRayConst[] := mkConst["openUpperRay", connectedRayTy];
openUpperRayTm[cutT_, xT_] := mkComb[mkComb[openUpperRayConst[], cutT], xT];
unfoldOpenUpperRay[cutT_, xT_] := connectedApplyDef[openUpperRayDefThm, {cutT, xT}];
openUpperRayMemThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    HOL`Bool`GEN[cutV, HOL`Bool`GEN[xV, unfoldOpenUpperRay[cutV, xV]]]
  ];

traceDefThm =
  Module[{sV, vV},
    sV = mkVar["S", connectedSetTy]; vV = mkVar["V", connectedSetTy];
    newDefinition[mkEq[mkVar["trace", traceTy],
      mkAbs[sV, mkAbs[vV, connectedTraceBody[sV, vV]]]]]
  ];

traceConst[] := mkConst["trace", traceTy];
traceTm[sT_, vT_] := mkComb[mkComb[traceConst[], sT], vT];
unfoldTrace[sT_, vT_] := connectedApplyDef[traceDefThm, {sT, vT}];
traceMemThm =
  Module[{sV, vV, xV, traceAt},
    sV = mkVar["S", connectedSetTy]; vV = mkVar["V", connectedSetTy];
    xV = mkVar["x", connectedRealTy];
    traceAt = TRANS[
      HOL`Equal`APTHM[unfoldTrace[sV, vV], xV],
      HOL`Equal`BETACONV[connectedSetApp[connectedTraceBody[sV, vV], xV]]];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[vV, HOL`Bool`GEN[xV, traceAt]]]
  ];

closedLowerRayDefThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    newDefinition[mkEq[mkVar["closedLowerRay", connectedRayTy],
      mkAbs[cutV, mkAbs[xV, connectedRealLe[xV, cutV]]]]]
  ];

closedLowerRayConst[] := mkConst["closedLowerRay", connectedRayTy];
closedLowerRayTm[cutT_, xT_] := mkComb[mkComb[closedLowerRayConst[], cutT], xT];
unfoldClosedLowerRay[cutT_, xT_] :=
  connectedApplyDef[closedLowerRayDefThm, {cutT, xT}];
closedLowerRayMemThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    HOL`Bool`GEN[cutV, HOL`Bool`GEN[xV, unfoldClosedLowerRay[cutV, xV]]]
  ];

closedUpperRayDefThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    newDefinition[mkEq[mkVar["closedUpperRay", connectedRayTy],
      mkAbs[cutV, mkAbs[xV, connectedRealLe[cutV, xV]]]]]
  ];

closedUpperRayConst[] := mkConst["closedUpperRay", connectedRayTy];
closedUpperRayTm[cutT_, xT_] := mkComb[mkComb[closedUpperRayConst[], cutT], xT];
unfoldClosedUpperRay[cutT_, xT_] :=
  connectedApplyDef[closedUpperRayDefThm, {cutT, xT}];
closedUpperRayMemThm =
  Module[{cutV, xV},
    cutV = mkVar["cut", connectedRealTy]; xV = mkVar["x", connectedRealTy];
    HOL`Bool`GEN[cutV, HOL`Bool`GEN[xV, unfoldClosedUpperRay[cutV, xV]]]
  ];

connectedSeparationParts[sepTh_] :=
  Module[{r1, r2, r3, r4},
    r1 = HOL`Bool`CONJUNCT2[sepTh];
    r2 = HOL`Bool`CONJUNCT2[r1];
    r3 = HOL`Bool`CONJUNCT2[r2];
    r4 = HOL`Bool`CONJUNCT2[r3];
    {HOL`Bool`CONJUNCT1[sepTh],
      HOL`Bool`CONJUNCT1[r1],
      HOL`Bool`CONJUNCT1[r2],
      HOL`Bool`CONJUNCT1[r3],
      HOL`Bool`CONJUNCT1[r4],
      HOL`Bool`CONJUNCT2[r4]}
  ];

connectedRightBetweenExists[xT_, yT_, zT_] :=
  Module[{dV},
    dV = mkVar["dCn", connectedRealTy];
    connectedExistsTm[dV, connectedConjTm[connectedRealLt[xT, dV],
      connectedConjTm[connectedRealLe[dV, yT], connectedRealLt[dV, zT]]]]
  ];

connectedOpenLowerSet[cutT_] := mkComb[openLowerRayConst[], cutT];
connectedOpenUpperSet[cutT_] := mkComb[openUpperRayConst[], cutT];
connectedClosedLowerSet[cutT_] := mkComb[closedLowerRayConst[], cutT];
connectedClosedUpperSet[cutT_] := mkComb[closedUpperRayConst[], cutT];
connectedOpenIntervalSet[leftT_, rightT_] := mkComb[mkComb[openIntervalConst[], leftT], rightT];
connectedClosedIntervalSet[leftT_, rightT_] :=
  mkComb[mkComb[closedIntervalConst[], leftT], rightT];

connectedIsOpenExists[uT_, xT_] :=
  Module[{leftV, rightV, yV},
    leftV = mkVar["leftCn", connectedRealTy]; rightV = mkVar["rightCn", connectedRealTy];
    yV = mkVar["yCn", connectedRealTy];
    connectedExistsTm[leftV, connectedExistsTm[rightV,
      connectedConjTm[connectedRealLt[leftV, xT],
        connectedConjTm[connectedRealLt[xT, rightV],
          connectedForallTm[yV, connectedImpTm[openIntervalTm[leftV, rightV, yV],
            connectedSetApp[uT, yV]]]]]]]
  ];

openInSubsetThm =
  Module[{sV, uV, xV, vV, hOpenTm, hOpen, opened, hBodyTm, hBody, allEq,
          hUTm, hU, eqAt, conjAt, sAt, point, allX, chosen},
    sV = mkVar["SCn", connectedSetTy]; uV = mkVar["UCn", connectedSetTy];
    xV = mkVar["xCn", connectedRealTy]; vV = mkVar["vCn", connectedSetTy];
    hOpenTm = openInTm[sV, uV]; hOpen = ASSUME[hOpenTm];
    opened = EQMP[unfoldOpenIn[sV, uV], hOpen];
    hBodyTm = connectedConjTm[isOpenTm[vV],
      connectedForallTm[xV, mkEq[connectedSetApp[uV, xV],
        connectedConjTm[connectedSetApp[sV, xV], connectedSetApp[vV, xV]]]]];
    hBody = ASSUME[hBodyTm];
    allEq = HOL`Bool`CONJUNCT2[hBody];
    hUTm = connectedSetApp[uV, xV]; hU = ASSUME[hUTm];
    eqAt = HOL`Bool`SPEC[xV, allEq];
    conjAt = EQMP[eqAt, hU];
    sAt = HOL`Bool`CONJUNCT1[conjAt];
    point = HOL`Bool`DISCH[hUTm, sAt];
    allX = HOL`Bool`GEN[xV, point];
    chosen = HOL`Bool`CHOOSE[vV, opened, allX];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, HOL`Bool`DISCH[hOpenTm, chosen]]]
  ];

openLowerRayIsOpenThm =
  Module[{cutV, xV, yV, raySet, hxTm, hx, leftT, rightT, hIntTm, hInt,
          intBody, yLtCut, foldedY, allY, leftLtX, xLtCut, body, exRight,
          exLeft, point, allX, folded},
    cutV = mkVar["cutCn", connectedRealTy]; xV = mkVar["xCn", connectedRealTy];
    yV = mkVar["yCn", connectedRealTy];
    raySet = connectedOpenLowerSet[cutV];
    hxTm = openLowerRayTm[cutV, xV]; hx = ASSUME[hxTm];
    leftT = connectedRealSubOne[xV]; rightT = cutV;
    hIntTm = openIntervalTm[leftT, rightT, yV]; hInt = ASSUME[hIntTm];
    intBody = EQMP[unfoldOpenInterval[leftT, rightT, yV], hInt];
    yLtCut = HOL`Bool`CONJUNCT2[intBody];
    foldedY = EQMP[HOL`Equal`SYM[unfoldOpenLowerRay[cutV, yV]], yLtCut];
    allY = HOL`Bool`GEN[yV, HOL`Bool`DISCH[hIntTm, foldedY]];
    leftLtX = HOL`Auto`RealArith`realArithProve[connectedRealLt[leftT, xV]];
    xLtCut = EQMP[unfoldOpenLowerRay[cutV, xV], hx];
    body = HOL`Bool`CONJ[leftLtX, HOL`Bool`CONJ[xLtCut, allY]];
    exRight = HOL`Bool`EXISTS[
      connectedExistsTm[mkVar["rightCn", connectedRealTy],
        connectedConjTm[connectedRealLt[leftT, xV],
          connectedConjTm[connectedRealLt[xV, mkVar["rightCn", connectedRealTy]],
            connectedForallTm[yV, connectedImpTm[
              openIntervalTm[leftT, mkVar["rightCn", connectedRealTy], yV],
              openLowerRayTm[cutV, yV]]]]]], rightT, body];
    exLeft = HOL`Bool`EXISTS[connectedIsOpenExists[raySet, xV], leftT, exRight];
    point = HOL`Bool`DISCH[hxTm, exLeft];
    allX = HOL`Bool`GEN[xV, point];
    folded = EQMP[HOL`Equal`SYM[unfoldIsOpen[raySet]], allX];
    HOL`Bool`GEN[cutV, folded]
  ];

openUpperRayIsOpenThm =
  Module[{cutV, xV, yV, raySet, hxTm, hx, leftT, rightT, hIntTm, hInt,
          intBody, cutLtY, foldedY, allY, xLtRight, cutLtX, body, exRight,
          exLeft, point, allX, folded},
    cutV = mkVar["cutCn", connectedRealTy]; xV = mkVar["xCn", connectedRealTy];
    yV = mkVar["yCn", connectedRealTy];
    raySet = connectedOpenUpperSet[cutV];
    hxTm = openUpperRayTm[cutV, xV]; hx = ASSUME[hxTm];
    leftT = cutV; rightT = connectedRealAddOne[xV];
    hIntTm = openIntervalTm[leftT, rightT, yV]; hInt = ASSUME[hIntTm];
    intBody = EQMP[unfoldOpenInterval[leftT, rightT, yV], hInt];
    cutLtY = HOL`Bool`CONJUNCT1[intBody];
    foldedY = EQMP[HOL`Equal`SYM[unfoldOpenUpperRay[cutV, yV]], cutLtY];
    allY = HOL`Bool`GEN[yV, HOL`Bool`DISCH[hIntTm, foldedY]];
    cutLtX = EQMP[unfoldOpenUpperRay[cutV, xV], hx];
    xLtRight = HOL`Auto`RealArith`realArithProve[connectedRealLt[xV, rightT]];
    body = HOL`Bool`CONJ[cutLtX, HOL`Bool`CONJ[xLtRight, allY]];
    exRight = HOL`Bool`EXISTS[
      connectedExistsTm[mkVar["rightCn", connectedRealTy],
        connectedConjTm[connectedRealLt[leftT, xV],
          connectedConjTm[connectedRealLt[xV, mkVar["rightCn", connectedRealTy]],
            connectedForallTm[yV, connectedImpTm[
              openIntervalTm[leftT, mkVar["rightCn", connectedRealTy], yV],
              openUpperRayTm[cutV, yV]]]]]], rightT, body];
    exLeft = HOL`Bool`EXISTS[connectedIsOpenExists[raySet, xV], leftT, exRight];
    point = HOL`Bool`DISCH[hxTm, exLeft];
    allX = HOL`Bool`GEN[xV, point];
    folded = EQMP[HOL`Equal`SYM[unfoldIsOpen[raySet]], allX];
    HOL`Bool`GEN[cutV, folded]
  ];

ltOrGtOfNeThm =
  Module[{xV, yV, hNeTm, hNe, goalTm, total, hLeXYTm, hLeXY, hLeYXTm,
          hLeYX, eqXY, falseT, leYXBranch, hNotLeYX, ltXY, notLeYXBranch,
          branchXY, hLeYXTm2, hLeYX2, hLeXYTm2, hLeXY2, eqXY2, falseT2,
          leXYBranch, hNotLeXY, ltYX, notLeXYBranch, branchYX, body},
    xV = mkVar["xCn", connectedRealTy]; yV = mkVar["yCn", connectedRealTy];
    hNeTm = connectedNotTm[mkEq[xV, yV]]; hNe = ASSUME[hNeTm];
    goalTm = connectedDisjTm[connectedRealLt[xV, yV], connectedRealLt[yV, xV]];
    total = connectedSpecAll[realLeTotalThm, {xV, yV}];

    hLeXYTm = connectedRealLe[xV, yV]; hLeXY = ASSUME[hLeXYTm];
    hLeYXTm = connectedRealLe[yV, xV]; hLeYX = ASSUME[hLeYXTm];
    eqXY = HOL`Bool`MP[
      HOL`Bool`MP[connectedSpecAll[realLeAntisymThm, {xV, yV}], hLeXY], hLeYX];
    falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[hNe], eqXY];
    leYXBranch = HOL`Bool`CONTR[goalTm, falseT];
    hNotLeYX = ASSUME[connectedNotTm[hLeYXTm]];
    ltXY = EQMP[connectedSpecAll[HOL`Auto`RealArith`realNotLeLtThm, {yV, xV}],
      hNotLeYX];
    notLeYXBranch = HOL`Bool`DISJ1[ltXY, connectedRealLt[yV, xV]];
    branchXY = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[hLeYXTm],
      leYXBranch, notLeYXBranch];

    hLeYXTm2 = connectedRealLe[yV, xV]; hLeYX2 = ASSUME[hLeYXTm2];
    hLeXYTm2 = connectedRealLe[xV, yV]; hLeXY2 = ASSUME[hLeXYTm2];
    eqXY2 = HOL`Bool`MP[
      HOL`Bool`MP[connectedSpecAll[realLeAntisymThm, {xV, yV}], hLeXY2], hLeYX2];
    falseT2 = HOL`Bool`MP[HOL`Bool`NOTELIM[hNe], eqXY2];
    leXYBranch = HOL`Bool`CONTR[goalTm, falseT2];
    hNotLeXY = ASSUME[connectedNotTm[hLeXYTm2]];
    ltYX = EQMP[connectedSpecAll[HOL`Auto`RealArith`realNotLeLtThm, {xV, yV}],
      hNotLeXY];
    notLeXYBranch = HOL`Bool`DISJ2[ltYX, connectedRealLt[xV, yV]];
    branchYX = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[hLeXYTm2],
      leXYBranch, notLeXYBranch];

    body = HOL`Bool`DISJCASES[total, branchXY, branchYX];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[hNeTm, body]]]
  ];

existsRightBetweenThm =
  Module[{xV, yV, zV, hXYTm, hXZTm, hXY, hXZ, hyzTm, goalTm, d1, d2, hYZ,
          left1, leXY, leMidY, midLtY, midLtZ, body1, ex1, hNotYZ, total,
          hYZcase, falseYZ, branchYZ, hZY, branchZY, zLeY, left2, leXZ,
          leMidZ, midLtZ2, midLeY, body2, ex2, body},
    xV = mkVar["xCn", connectedRealTy]; yV = mkVar["yCn", connectedRealTy];
    zV = mkVar["zCn", connectedRealTy];
    hXYTm = connectedRealLt[xV, yV]; hXZTm = connectedRealLt[xV, zV];
    hXY = ASSUME[hXYTm]; hXZ = ASSUME[hXZTm];
    hyzTm = connectedRealLe[yV, zV];
    goalTm = connectedRightBetweenExists[xV, yV, zV];

    hYZ = ASSUME[hyzTm]; d1 = midpointTm[xV, yV];
    left1 = HOL`Bool`MP[connectedSpecAll[leftLtMidpointThm, {xV, yV}], hXY];
    leXY = HOL`Bool`MP[connectedSpecAll[realLtImpLeThm, {xV, yV}], hXY];
    leMidY = HOL`Bool`MP[connectedSpecAll[midpointLeRightThm, {xV, yV}], leXY];
    midLtY = HOL`Bool`MP[connectedSpecAll[midpointLtRightThm, {xV, yV}], hXY];
    midLtZ = HOL`Bool`MP[
      HOL`Bool`MP[connectedSpecAll[realLtLeTransThm, {d1, yV, zV}], midLtY], hYZ];
    body1 = HOL`Bool`CONJ[left1, HOL`Bool`CONJ[leMidY, midLtZ]];
    ex1 = HOL`Bool`EXISTS[goalTm, d1, body1];

    hNotYZ = ASSUME[connectedNotTm[hyzTm]];
    total = connectedSpecAll[realLeTotalThm, {yV, zV}];
    hYZcase = ASSUME[hyzTm];
    falseYZ = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotYZ], hYZcase];
    branchYZ = HOL`Bool`CONTR[connectedRealLe[zV, yV], falseYZ];
    hZY = ASSUME[connectedRealLe[zV, yV]];
    branchZY = hZY;
    zLeY = HOL`Bool`DISJCASES[total, branchYZ, branchZY];
    d2 = midpointTm[xV, zV];
    left2 = HOL`Bool`MP[connectedSpecAll[leftLtMidpointThm, {xV, zV}], hXZ];
    leXZ = HOL`Bool`MP[connectedSpecAll[realLtImpLeThm, {xV, zV}], hXZ];
    leMidZ = HOL`Bool`MP[connectedSpecAll[midpointLeRightThm, {xV, zV}], leXZ];
    midLeY = HOL`Bool`MP[
      HOL`Bool`MP[connectedSpecAll[realLeTransThm, {d2, zV, yV}], leMidZ], zLeY];
    midLtZ2 = HOL`Bool`MP[connectedSpecAll[midpointLtRightThm, {xV, zV}], hXZ];
    body2 = HOL`Bool`CONJ[left2, HOL`Bool`CONJ[midLeY, midLtZ2]];
    ex2 = HOL`Bool`EXISTS[goalTm, d2, body2];

    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[hyzTm], ex1, ex2];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[hXYTm, HOL`Bool`DISCH[hXZTm, body]]]]]
  ];

connectedSwapCovers[sT_, uT_, vT_, coversTh_] :=
  Module[{xV, allOld, oldAt, newEq, taut, allNew},
    xV = mkVar["xCn", connectedRealTy];
    allOld = EQMP[unfoldCoversByTwo[sT, uT, vT], coversTh];
    oldAt = HOL`Bool`SPEC[xV, allOld];
    newEq = mkEq[connectedSetApp[sT, xV],
      connectedDisjTm[connectedSetApp[vT, xV], connectedSetApp[uT, xV]]];
    taut = HOL`Auto`PropTaut`propTaut[connectedImpTm[concl[oldAt], newEq]];
    allNew = HOL`Bool`GEN[xV, HOL`Bool`MP[taut, oldAt]];
    EQMP[HOL`Equal`SYM[unfoldCoversByTwo[sT, vT, uT]], allNew]
  ];

connectedSwapDisjoint[uT_, vT_, disjointTh_] :=
  Module[{xV, allOld, oldAt, newNot, taut, allNew},
    xV = mkVar["xCn", connectedRealTy];
    allOld = EQMP[unfoldSetDisjoint[uT, vT], disjointTh];
    oldAt = HOL`Bool`SPEC[xV, allOld];
    newNot = connectedNotTm[
      connectedConjTm[connectedSetApp[vT, xV], connectedSetApp[uT, xV]]];
    taut = HOL`Auto`PropTaut`propTaut[connectedImpTm[concl[oldAt], newNot]];
    allNew = HOL`Bool`GEN[xV, HOL`Bool`MP[taut, oldAt]];
    EQMP[HOL`Equal`SYM[unfoldSetDisjoint[vT, uT]], allNew]
  ];

isSeparationSymmThm =
  Module[{sV, uV, vV, hSepTm, hSep, opened, parts, swappedCovers,
          swappedDisjoint, body, folded},
    sV = mkVar["SCn", connectedSetTy]; uV = mkVar["UCn", connectedSetTy];
    vV = mkVar["VCn", connectedSetTy];
    hSepTm = isSeparationTm[sV, uV, vV]; hSep = ASSUME[hSepTm];
    opened = EQMP[unfoldIsSeparation[sV, uV, vV], hSep];
    parts = connectedSeparationParts[opened];
    swappedCovers = connectedSwapCovers[sV, uV, vV, parts[[5]]];
    swappedDisjoint = connectedSwapDisjoint[uV, vV, parts[[6]]];
    body = HOL`Bool`CONJ[parts[[2]], HOL`Bool`CONJ[parts[[1]],
      HOL`Bool`CONJ[parts[[4]], HOL`Bool`CONJ[parts[[3]],
        HOL`Bool`CONJ[swappedCovers, swappedDisjoint]]]]];
    folded = EQMP[HOL`Equal`SYM[unfoldIsSeparation[sV, vV, uV]], body];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, HOL`Bool`GEN[vV,
      HOL`Bool`DISCH[hSepTm, folded]]]]
  ];

connectedEmptySet[] :=
  Module[{xV},
    xV = mkVar["xCn", connectedRealTy];
    mkAbs[xV, connectedFalseTm[]]
  ];

connectedUniversalSet[] :=
  Module[{xV},
    xV = mkVar["xCn", connectedRealTy];
    mkAbs[xV, connectedTrueTm[]]
  ];

connectedSingletonSet[aT_] :=
  Module[{xV},
    xV = mkVar["xCn", connectedRealTy];
    mkAbs[xV, mkEq[xV, aT]]
  ];

connectedEmptyThm =
  Module[{emptySet, uV, vV, xV, hSepTm, hSep, opened, parts, nonempty,
          existsU, hUTm, hU, subsetAll, subsetAt, emptyAt, falseT, chosen,
          notSep, allUV, folded},
    emptySet = connectedEmptySet[];
    uV = mkVar["UCn", connectedSetTy]; vV = mkVar["VCn", connectedSetTy];
    xV = mkVar["xEmptyCn", connectedRealTy];
    hSepTm = isSeparationTm[emptySet, uV, vV]; hSep = ASSUME[hSepTm];
    opened = EQMP[unfoldIsSeparation[emptySet, uV, vV], hSep];
    parts = connectedSeparationParts[opened];
    nonempty = parts[[3]];
    existsU = EQMP[unfoldSetNonempty[uV], nonempty];
    hUTm = connectedSetApp[uV, xV]; hU = ASSUME[hUTm];
    subsetAll = HOL`Bool`MP[connectedSpecAll[openInSubsetThm, {emptySet, uV}], parts[[1]]];
    subsetAt = HOL`Bool`SPEC[xV, subsetAll];
    emptyAt = HOL`Bool`MP[subsetAt, hU];
    falseT = EQMP[HOL`Equal`BETACONV[connectedSetApp[emptySet, xV]], emptyAt];
    chosen = HOL`Bool`CHOOSE[xV, existsU, falseT];
    notSep = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[hSepTm, chosen]];
    allUV = HOL`Bool`GEN[uV, HOL`Bool`GEN[vV, notSep]];
    folded = EQMP[HOL`Equal`SYM[unfoldIsConnected[emptySet]], allUV];
    folded
  ];

connectedIntervalSetFromBody[setT_, bodyTh_] :=
  EQMP[HOL`Equal`SYM[unfoldIsIntervalSet[setT]], bodyTh];

connectedIntervalBody[setT_, proofMaker_] :=
  Module[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb, sy, point},
    xV = mkVar["xIvCn", connectedRealTy]; yV = mkVar["yIvCn", connectedRealTy];
    zV = mkVar["zIvCn", connectedRealTy];
    hxTm = connectedSetApp[setT, xV]; hzTm = connectedSetApp[setT, zV];
    hbTm = betweenTm[xV, yV, zV];
    hx = ASSUME[hxTm]; hz = ASSUME[hzTm]; hb = ASSUME[hbTm];
    sy = proofMaker[xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb];
    point = HOL`Bool`DISCH[hxTm,
      HOL`Bool`DISCH[hzTm, HOL`Bool`DISCH[hbTm, sy]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV, point]]]
  ];

connectedBetweenParts[hBetween_] :=
  Module[{opened},
    opened = EQMP[unfoldBetween[
      concl[hBetween][[1, 2, 2]], concl[hBetween][[1, 2]], concl[hBetween][[2, 2]]],
      hBetween];
    {HOL`Bool`CONJUNCT1[opened], HOL`Bool`CONJUNCT2[opened]}
  ];

intervalSetEmptyThm =
  Module[{setT, body},
    setT = connectedEmptySet[];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      HOL`Bool`CONTR[connectedSetApp[setT, yV],
        EQMP[HOL`Equal`BETACONV[hxTm], hx]]]];
    connectedIntervalSetFromBody[setT, body]
  ];

intervalSetUniversalThm =
  Module[{setT, body},
    setT = connectedUniversalSet[];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      EQMP[HOL`Equal`SYM[HOL`Equal`BETACONV[connectedSetApp[setT, yV]]],
        HOL`Bool`TRUTH]]];
    connectedIntervalSetFromBody[setT, body]
  ];

intervalSetSingletonThm =
  Module[{aV, setT, body},
    aV = mkVar["aCn", connectedRealTy]; setT = connectedSingletonSet[aV];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      Module[{hxEq, hzEq, betweenParts, leXY, leYZ, leAY, leYA, yEqA},
        hxEq = EQMP[HOL`Equal`BETACONV[hxTm], hx];
        hzEq = EQMP[HOL`Equal`BETACONV[hzTm], hz];
        betweenParts = EQMP[unfoldBetween[xV, yV, zV], hb];
        leXY = HOL`Bool`CONJUNCT1[betweenParts];
        leYZ = HOL`Bool`CONJUNCT2[betweenParts];
        leAY = EQMP[connectedRealLeCong[hxEq, REFL[yV]], leXY];
        leYA = EQMP[connectedRealLeCong[REFL[yV], hzEq], leYZ];
        yEqA = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLeAntisymThm, {yV, aV}], leYA], leAY];
        EQMP[HOL`Equal`SYM[HOL`Equal`BETACONV[connectedSetApp[setT, yV]]], yEqA]
      ]]];
    HOL`Bool`GEN[aV, connectedIntervalSetFromBody[setT, body]]
  ];

intervalSetOpenIntervalThm =
  Module[{leftV, rightV, setT, body},
    leftV = mkVar["leftCn", connectedRealTy]; rightV = mkVar["rightCn", connectedRealTy];
    setT = connectedOpenIntervalSet[leftV, rightV];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      Module[{hxOpen, hzOpen, betweenOpen, leXY, leYZ, leftLtX, zLtRight,
          leftLtY, yLtRight, both},
        hxOpen = EQMP[unfoldOpenInterval[leftV, rightV, xV], hx];
        hzOpen = EQMP[unfoldOpenInterval[leftV, rightV, zV], hz];
        betweenOpen = EQMP[unfoldBetween[xV, yV, zV], hb];
        leXY = HOL`Bool`CONJUNCT1[betweenOpen]; leYZ = HOL`Bool`CONJUNCT2[betweenOpen];
        leftLtX = HOL`Bool`CONJUNCT1[hxOpen]; zLtRight = HOL`Bool`CONJUNCT2[hzOpen];
        leftLtY = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLtLeTransThm, {leftV, xV, yV}], leftLtX], leXY];
        yLtRight = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLeLtTransThm, {yV, zV, rightV}], leYZ], zLtRight];
        both = HOL`Bool`CONJ[leftLtY, yLtRight];
        EQMP[HOL`Equal`SYM[unfoldOpenInterval[leftV, rightV, yV]], both]
      ]]];
    HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, connectedIntervalSetFromBody[setT, body]]]
  ];

intervalSetClosedIntervalThm =
  Module[{leftV, rightV, setT, body},
    leftV = mkVar["leftCn", connectedRealTy]; rightV = mkVar["rightCn", connectedRealTy];
    setT = connectedClosedIntervalSet[leftV, rightV];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      Module[{hxClosed, hzClosed, betweenClosed, leXY, leYZ, leftLeX, zLeRight,
          leftLeY, yLeRight, both},
        hxClosed = EQMP[unfoldClosedInterval[leftV, rightV, xV], hx];
        hzClosed = EQMP[unfoldClosedInterval[leftV, rightV, zV], hz];
        betweenClosed = EQMP[unfoldBetween[xV, yV, zV], hb];
        leXY = HOL`Bool`CONJUNCT1[betweenClosed]; leYZ = HOL`Bool`CONJUNCT2[betweenClosed];
        leftLeX = HOL`Bool`CONJUNCT1[hxClosed]; zLeRight = HOL`Bool`CONJUNCT2[hzClosed];
        leftLeY = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLeTransThm, {leftV, xV, yV}], leftLeX], leXY];
        yLeRight = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLeTransThm, {yV, zV, rightV}], leYZ], zLeRight];
        both = HOL`Bool`CONJ[leftLeY, yLeRight];
        EQMP[HOL`Equal`SYM[unfoldClosedInterval[leftV, rightV, yV]], both]
      ]]];
    HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, connectedIntervalSetFromBody[setT, body]]]
  ];

intervalSetOpenLowerRayThm =
  Module[{cutV, setT, body},
    cutV = mkVar["cutCn", connectedRealTy]; setT = connectedOpenLowerSet[cutV];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      Module[{hzOpen, betweenOpen, leYZ, yLtCut},
        hzOpen = EQMP[unfoldOpenLowerRay[cutV, zV], hz];
        betweenOpen = EQMP[unfoldBetween[xV, yV, zV], hb];
        leYZ = HOL`Bool`CONJUNCT2[betweenOpen];
        yLtCut = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLeLtTransThm, {yV, zV, cutV}], leYZ], hzOpen];
        EQMP[HOL`Equal`SYM[unfoldOpenLowerRay[cutV, yV]], yLtCut]
      ]]];
    HOL`Bool`GEN[cutV, connectedIntervalSetFromBody[setT, body]]
  ];

intervalSetOpenUpperRayThm =
  Module[{cutV, setT, body},
    cutV = mkVar["cutCn", connectedRealTy]; setT = connectedOpenUpperSet[cutV];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      Module[{hxOpen, betweenOpen, leXY, cutLtY},
        hxOpen = EQMP[unfoldOpenUpperRay[cutV, xV], hx];
        betweenOpen = EQMP[unfoldBetween[xV, yV, zV], hb];
        leXY = HOL`Bool`CONJUNCT1[betweenOpen];
        cutLtY = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLtLeTransThm, {cutV, xV, yV}], hxOpen], leXY];
        EQMP[HOL`Equal`SYM[unfoldOpenUpperRay[cutV, yV]], cutLtY]
      ]]];
    HOL`Bool`GEN[cutV, connectedIntervalSetFromBody[setT, body]]
  ];

intervalSetClosedLowerRayThm =
  Module[{cutV, setT, body},
    cutV = mkVar["cutCn", connectedRealTy]; setT = connectedClosedLowerSet[cutV];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      Module[{hzClosed, betweenClosed, leYZ, yLeCut},
        hzClosed = EQMP[unfoldClosedLowerRay[cutV, zV], hz];
        betweenClosed = EQMP[unfoldBetween[xV, yV, zV], hb];
        leYZ = HOL`Bool`CONJUNCT2[betweenClosed];
        yLeCut = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLeTransThm, {yV, zV, cutV}], leYZ], hzClosed];
        EQMP[HOL`Equal`SYM[unfoldClosedLowerRay[cutV, yV]], yLeCut]
      ]]];
    HOL`Bool`GEN[cutV, connectedIntervalSetFromBody[setT, body]]
  ];

intervalSetClosedUpperRayThm =
  Module[{cutV, setT, body},
    cutV = mkVar["cutCn", connectedRealTy]; setT = connectedClosedUpperSet[cutV];
    body = connectedIntervalBody[setT, Function[{xV, yV, zV, hxTm, hzTm, hbTm, hx, hz, hb},
      Module[{hxClosed, betweenClosed, leXY, cutLeY},
        hxClosed = EQMP[unfoldClosedUpperRay[cutV, xV], hx];
        betweenClosed = EQMP[unfoldBetween[xV, yV, zV], hb];
        leXY = HOL`Bool`CONJUNCT1[betweenClosed];
        cutLeY = HOL`Bool`MP[
          HOL`Bool`MP[connectedSpecAll[realLeTransThm, {cutV, xV, yV}], hxClosed], leXY];
        EQMP[HOL`Equal`SYM[unfoldClosedUpperRay[cutV, yV]], cutLeY]
      ]]];
    HOL`Bool`GEN[cutV, connectedIntervalSetFromBody[setT, body]]
  ];

connectedTraceAt[sT_, vT_, xT_] := connectedSpecAll[traceMemThm, {sT, vT, xT}];

openInTraceThm =
  Module[{sV, vV, xV, traceSet, hOpenTm, hOpen, allX, body, existsTrace,
          folded},
    sV = mkVar["SCn", connectedSetTy]; vV = mkVar["VCn", connectedSetTy];
    xV = mkVar["xTraceCn", connectedRealTy];
    traceSet = traceTm[sV, vV];
    hOpenTm = isOpenTm[vV]; hOpen = ASSUME[hOpenTm];
    allX = HOL`Bool`GEN[xV, connectedTraceAt[sV, vV, xV]];
    body = HOL`Bool`CONJ[hOpen, allX];
    existsTrace = HOL`Bool`EXISTS[connectedOpenInBody[sV, traceSet], vV, body];
    folded = EQMP[HOL`Equal`SYM[unfoldOpenIn[sV, traceSet]], existsTrace];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[vV, HOL`Bool`DISCH[hOpenTm, folded]]]
  ];

End[];

EndPackage[];
