(* M8.4 / stdlib/Real/Topology.wl - closed-set topology vocabulary. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`Arith`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

complDefThm::usage = "complDefThm - |- compl = (lambda S. lambda x. ~(S x)).";
complConst::usage = "complConst[] - compl : (real -> bool) -> (real -> bool).";
complTm::usage = "complTm[S] - builds compl S.";
unfoldCompl::usage = "unfoldCompl[S] - proves the beta-reduced compl definition at S.";
complMemThm::usage = "complMemThm - |- forall S x. compl S x = ~(S x).";

isClosedDefThm::usage = "isClosedDefThm - |- isClosed = (lambda S. isOpen (compl S)).";
isClosedConst::usage = "isClosedConst[] - isClosed : (real -> bool) -> bool.";
isClosedTm::usage = "isClosedTm[S] - builds isClosed S.";
unfoldIsClosed::usage = "unfoldIsClosed[S] - proves the beta-reduced isClosed definition at S.";
isClosedMemThm::usage = "isClosedMemThm - |- forall S. isClosed S = isOpen (compl S).";

relativeClosedDefThm::usage = "relativeClosedDefThm - |- relativeClosed = (lambda S U. exists V. isClosed V /\\ forall x. U x = (S x /\\ V x)).";
relativeClosedConst::usage = "relativeClosedConst[] - relativeClosed : (real -> bool) -> (real -> bool) -> bool.";
relativeClosedTm::usage = "relativeClosedTm[S, U] - builds relativeClosed S U.";
unfoldRelativeClosed::usage = "unfoldRelativeClosed[S, U] - proves the beta-reduced relativeClosed definition at S and U.";
relativeClosedMemThm::usage = "relativeClosedMemThm - |- forall S U. relativeClosed S U = (exists V. isClosed V /\\ forall x. U x = (S x /\\ V x)).";

closedInDefThm::usage = "closedInDefThm - |- closedIn = relativeClosed.";
closedInConst::usage = "closedInConst[] - closedIn : (real -> bool) -> (real -> bool) -> bool.";
closedInTm::usage = "closedInTm[S, U] - builds closedIn S U.";
unfoldClosedIn::usage = "unfoldClosedIn[S, U] - proves closedIn S U = relativeClosed S U.";
closedInMemThm::usage = "closedInMemThm - |- forall S U. closedIn S U = relativeClosed S U.";

isClosedComplOpenThm::usage = "isClosedComplOpenThm - |- forall S. isClosed S = isOpen (compl S).";
closedInSubsetThm::usage = "closedInSubsetThm - |- forall S U. closedIn S U ==> forall x. U x ==> S x.";
closedIntervalIsClosedThm::usage = "closedIntervalIsClosedThm - |- forall a b. isClosed (closedInterval a b).";

Begin["`Private`"];

topoRealTy = mkType["real", {}];
topoSetTy = tyFun[topoRealTy, boolTy];
complTy = tyFun[topoSetTy, topoSetTy];
isClosedTy = tyFun[topoSetTy, boolTy];
relativeClosedTy = tyFun[topoSetTy, tyFun[topoSetTy, boolTy]];
closedInTy = relativeClosedTy;

topoAndConst[] := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
topoImpConst[] := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
topoNotConst[] := mkConst["¬", tyFun[boolTy, boolTy]];
topoConjTm[pT_, qT_] := mkComb[mkComb[topoAndConst[], pT], qT];
topoImpTm[pT_, qT_] := mkComb[mkComb[topoImpConst[], pT], qT];
topoNotTm[pT_] := mkComb[topoNotConst[], pT];
topoForallTm[vT_, bodyT_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];
topoExistsTm[vT_, bodyT_] :=
  mkComb[mkConst["∃", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];

topoSetApp[sT_, xT_] := mkComb[sT, xT];
topoRealLe[aT_, bT_] := mkComb[mkComb[realLeConst[], aT], bT];
topoRealLt[aT_, bT_] := mkComb[mkComb[realLtConst[], aT], bT];
topoRealAdd[aT_, bT_] := mkComb[mkComb[realAddConst[], aT], bT];
topoRealNeg[aT_] := mkComb[realNegConst[], aT];
topoZeroNum[] := HOL`Stdlib`Num`zeroConst[];
topoSucNum[nT_] := mkComb[HOL`Stdlib`Num`sucConst[], nT];
topoOneNum[] := topoSucNum[topoZeroNum[]];
topoIntOfNum[nT_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], nT];
topoRatOfInt[zT_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], zT];
topoRealOfRat[qT_] := mkComb[realOfRatConst[], qT];
topoOneReal[] := topoRealOfRat[topoRatOfInt[topoIntOfNum[topoOneNum[]]]];
topoRealSubOne[xT_] := topoRealAdd[xT, topoRealNeg[topoOneReal[]]];
topoRealAddOne[xT_] := topoRealAdd[xT, topoOneReal[]];

topoSpecAll[th_, terms_List] :=
  Fold[Function[{accTh, termT}, HOL`Bool`SPEC[termT, accTh]], th, terms];

topoApplyDef[defTh_, args_List] :=
  Fold[Function[{accTh, argT}, Module[{stepTh},
    stepTh = HOL`Equal`APTHM[accTh, argT];
    TRANS[stepTh, HOL`Equal`BETACONV[concl[stepTh][[2]]]]
  ]], defTh, args];

topoComplBody[sT_] :=
  Module[{xV},
    xV = mkVar["xTp", topoRealTy];
    mkAbs[xV, topoNotTm[topoSetApp[sT, xV]]]
  ];

topoRelativeClosedBody[sT_, uT_] :=
  Module[{vV, xV},
    vV = mkVar["vTp", topoSetTy]; xV = mkVar["xTp", topoRealTy];
    topoExistsTm[vV, topoConjTm[isClosedTm[vV],
      topoForallTm[xV, mkEq[topoSetApp[uT, xV],
        topoConjTm[topoSetApp[sT, xV], topoSetApp[vV, xV]]]]]]
  ];

topoClosedIntervalSet[aT_, bT_] := mkComb[mkComb[closedIntervalConst[], aT], bT];

topoIsOpenExists[uT_, xT_] :=
  Module[{leftV, rightV, yV},
    leftV = mkVar["leftTp", topoRealTy]; rightV = mkVar["rightTp", topoRealTy];
    yV = mkVar["yTp", topoRealTy];
    topoExistsTm[leftV, topoExistsTm[rightV,
      topoConjTm[topoRealLt[leftV, xT],
        topoConjTm[topoRealLt[xT, rightV],
          topoForallTm[yV, topoImpTm[openIntervalTm[leftV, rightV, yV],
            topoSetApp[uT, yV]]]]]]]
  ];

topoNotAndLeft[thNotP_, qT_] :=
  Module[{pT, conjT, hConj, falseTh},
    pT = concl[thNotP][[2]];
    conjT = topoConjTm[pT, qT];
    hConj = ASSUME[conjT];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], HOL`Bool`CONJUNCT1[hConj]];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[conjT, falseTh]]
  ];

topoNotAndRight[pT_, thNotQ_] :=
  Module[{qT, conjT, hConj, falseTh},
    qT = concl[thNotQ][[2]];
    conjT = topoConjTm[pT, qT];
    hConj = ASSUME[conjT];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotQ], HOL`Bool`CONJUNCT2[hConj]];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[conjT, falseTh]]
  ];

topoNotRightOfConj[thNotConj_, thP_, qT_] :=
  Module[{hQ, falseTh},
    hQ = ASSUME[qT];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotConj], HOL`Bool`CONJ[thP, hQ]];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[qT, falseTh]]
  ];

topoFoldComplClosedInterval[aT_, bT_, xT_, thNotConj_] :=
  Module[{closedSet, closedMem, notClosed},
    closedSet = topoClosedIntervalSet[aT, bT];
    closedMem = topoSpecAll[closedIntervalMemThm, {aT, bT, xT}];
    notClosed = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[topoNotConst[], closedMem]], thNotConj];
    EQMP[HOL`Equal`SYM[topoSpecAll[complMemThm, {closedSet, xT}]], notClosed]
  ];

complDefThm =
  Module[{sV},
    sV = mkVar["S", topoSetTy];
    newDefinition[mkEq[mkVar["compl", complTy], mkAbs[sV, topoComplBody[sV]]]]
  ];

complConst[] := mkConst["compl", complTy];
complTm[sT_] := mkComb[complConst[], sT];
unfoldCompl[sT_] := topoApplyDef[complDefThm, {sT}];
complMemThm =
  Module[{sV, xV, atX},
    sV = mkVar["S", topoSetTy]; xV = mkVar["x", topoRealTy];
    atX = TRANS[HOL`Equal`APTHM[unfoldCompl[sV], xV],
      HOL`Equal`BETACONV[topoSetApp[topoComplBody[sV], xV]]];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[xV, atX]]
  ];

isClosedDefThm =
  Module[{sV},
    sV = mkVar["S", topoSetTy];
    newDefinition[mkEq[mkVar["isClosed", isClosedTy],
      mkAbs[sV, isOpenTm[complTm[sV]]]]]
  ];

isClosedConst[] := mkConst["isClosed", isClosedTy];
isClosedTm[sT_] := mkComb[isClosedConst[], sT];
unfoldIsClosed[sT_] := topoApplyDef[isClosedDefThm, {sT}];
isClosedMemThm =
  Module[{sV},
    sV = mkVar["S", topoSetTy];
    HOL`Bool`GEN[sV, unfoldIsClosed[sV]]
  ];
isClosedComplOpenThm = isClosedMemThm;

relativeClosedDefThm =
  Module[{sV, uV},
    sV = mkVar["S", topoSetTy]; uV = mkVar["U", topoSetTy];
    newDefinition[mkEq[mkVar["relativeClosed", relativeClosedTy],
      mkAbs[sV, mkAbs[uV, topoRelativeClosedBody[sV, uV]]]]]
  ];

relativeClosedConst[] := mkConst["relativeClosed", relativeClosedTy];
relativeClosedTm[sT_, uT_] := mkComb[mkComb[relativeClosedConst[], sT], uT];
unfoldRelativeClosed[sT_, uT_] := topoApplyDef[relativeClosedDefThm, {sT, uT}];
relativeClosedMemThm =
  Module[{sV, uV},
    sV = mkVar["S", topoSetTy]; uV = mkVar["U", topoSetTy];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, unfoldRelativeClosed[sV, uV]]]
  ];

closedInDefThm =
  newDefinition[mkEq[mkVar["closedIn", closedInTy], relativeClosedConst[]]];

closedInConst[] := mkConst["closedIn", closedInTy];
closedInTm[sT_, uT_] := mkComb[mkComb[closedInConst[], sT], uT];
unfoldClosedIn[sT_, uT_] :=
  Module[{s1, s2},
    s1 = HOL`Equal`APTHM[closedInDefThm, sT];
    s2 = HOL`Equal`APTHM[s1, uT];
    s2
  ];
closedInMemThm =
  Module[{sV, uV},
    sV = mkVar["S", topoSetTy]; uV = mkVar["U", topoSetTy];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, unfoldClosedIn[sV, uV]]]
  ];

closedInSubsetThm =
  Module[{sV, uV, xV, vV, hClosedTm, hClosed, openedAlias, opened,
          hBodyTm, hBody, allEq, hUTm, hU, eqAt, conjAt, sAt, point,
          allX, chosen},
    sV = mkVar["STp", topoSetTy]; uV = mkVar["UTp", topoSetTy];
    xV = mkVar["xTp", topoRealTy]; vV = mkVar["vTp", topoSetTy];
    hClosedTm = closedInTm[sV, uV]; hClosed = ASSUME[hClosedTm];
    openedAlias = EQMP[unfoldClosedIn[sV, uV], hClosed];
    opened = EQMP[unfoldRelativeClosed[sV, uV], openedAlias];
    hBodyTm = topoConjTm[isClosedTm[vV],
      topoForallTm[xV, mkEq[topoSetApp[uV, xV],
        topoConjTm[topoSetApp[sV, xV], topoSetApp[vV, xV]]]]];
    hBody = ASSUME[hBodyTm];
    allEq = HOL`Bool`CONJUNCT2[hBody];
    hUTm = topoSetApp[uV, xV]; hU = ASSUME[hUTm];
    eqAt = HOL`Bool`SPEC[xV, allEq];
    conjAt = EQMP[eqAt, hU];
    sAt = HOL`Bool`CONJUNCT1[conjAt];
    point = HOL`Bool`DISCH[hUTm, sAt];
    allX = HOL`Bool`GEN[xV, point];
    chosen = HOL`Bool`CHOOSE[vV, opened, allX];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, HOL`Bool`DISCH[hClosedTm, chosen]]]
  ];

closedIntervalIsClosedThm =
  Module[{aV, bV, xV, yV, closedSet, complSet, hXTm, hX, notClosedX,
          closedMemX, notConjX, leAXTm, em, hLeAX, hNotLeAXTm, hNotLeAX,
          leftT, rightT, hIntTm, hInt, intBody, yLtA, notLeAY, notConjY,
          foldedY, allY, leftLtX, xLtA, body, exRight, exLeft,
          notLeBranch, xLeBTm, notLeXB, bLtX, bLtY, notLeYB, xLtRight,
          leBranch, point, allX, opened, closed},
    aV = mkVar["a", topoRealTy]; bV = mkVar["b", topoRealTy];
    xV = mkVar["xTp", topoRealTy]; yV = mkVar["yTp", topoRealTy];
    closedSet = topoClosedIntervalSet[aV, bV];
    complSet = complTm[closedSet];
    hXTm = topoSetApp[complSet, xV]; hX = ASSUME[hXTm];
    notClosedX = EQMP[topoSpecAll[complMemThm, {closedSet, xV}], hX];
    closedMemX = topoSpecAll[closedIntervalMemThm, {aV, bV, xV}];
    notConjX = EQMP[HOL`Equal`APTERM[topoNotConst[], closedMemX], notClosedX];
    leAXTm = topoRealLe[aV, xV];
    em = HOL`Bool`EXCLUDEDMIDDLE[leAXTm];

    hNotLeAXTm = topoNotTm[leAXTm]; hNotLeAX = ASSUME[hNotLeAXTm];
    xLtA = EQMP[topoSpecAll[HOL`Auto`RealArith`realNotLeLtThm, {aV, xV}], hNotLeAX];
    leftT = topoRealSubOne[xV]; rightT = aV;
    hIntTm = openIntervalTm[leftT, rightT, yV]; hInt = ASSUME[hIntTm];
    intBody = EQMP[unfoldOpenInterval[leftT, rightT, yV], hInt];
    yLtA = HOL`Bool`CONJUNCT2[intBody];
    notLeAY = EQMP[topoSpecAll[realLtNotLeThm, {yV, aV}], yLtA];
    notConjY = topoNotAndLeft[notLeAY, topoRealLe[yV, bV]];
    foldedY = topoFoldComplClosedInterval[aV, bV, yV, notConjY];
    allY = HOL`Bool`GEN[yV, HOL`Bool`DISCH[hIntTm, foldedY]];
    leftLtX = HOL`Auto`RealArith`realArithProve[topoRealLt[leftT, xV]];
    body = HOL`Bool`CONJ[leftLtX, HOL`Bool`CONJ[xLtA, allY]];
    exRight = HOL`Bool`EXISTS[
      topoExistsTm[mkVar["rightTp", topoRealTy],
        topoConjTm[topoRealLt[leftT, xV],
          topoConjTm[topoRealLt[xV, mkVar["rightTp", topoRealTy]],
            topoForallTm[yV, topoImpTm[
              openIntervalTm[leftT, mkVar["rightTp", topoRealTy], yV],
              topoSetApp[complSet, yV]]]]]], rightT, body];
    exLeft = HOL`Bool`EXISTS[topoIsOpenExists[complSet, xV], leftT, exRight];
    notLeBranch = exLeft;

    hLeAX = ASSUME[leAXTm];
    xLeBTm = topoRealLe[xV, bV];
    notLeXB = topoNotRightOfConj[notConjX, hLeAX, xLeBTm];
    bLtX = EQMP[topoSpecAll[HOL`Auto`RealArith`realNotLeLtThm, {xV, bV}], notLeXB];
    leftT = bV; rightT = topoRealAddOne[xV];
    hIntTm = openIntervalTm[leftT, rightT, yV]; hInt = ASSUME[hIntTm];
    intBody = EQMP[unfoldOpenInterval[leftT, rightT, yV], hInt];
    bLtY = HOL`Bool`CONJUNCT1[intBody];
    notLeYB = EQMP[topoSpecAll[realLtNotLeThm, {bV, yV}], bLtY];
    notConjY = topoNotAndRight[topoRealLe[aV, yV], notLeYB];
    foldedY = topoFoldComplClosedInterval[aV, bV, yV, notConjY];
    allY = HOL`Bool`GEN[yV, HOL`Bool`DISCH[hIntTm, foldedY]];
    xLtRight = HOL`Auto`RealArith`realArithProve[topoRealLt[xV, rightT]];
    body = HOL`Bool`CONJ[bLtX, HOL`Bool`CONJ[xLtRight, allY]];
    exRight = HOL`Bool`EXISTS[
      topoExistsTm[mkVar["rightTp", topoRealTy],
        topoConjTm[topoRealLt[leftT, xV],
          topoConjTm[topoRealLt[xV, mkVar["rightTp", topoRealTy]],
            topoForallTm[yV, topoImpTm[
              openIntervalTm[leftT, mkVar["rightTp", topoRealTy], yV],
              topoSetApp[complSet, yV]]]]]], rightT, body];
    exLeft = HOL`Bool`EXISTS[topoIsOpenExists[complSet, xV], leftT, exRight];
    leBranch = exLeft;

    point = HOL`Bool`DISCH[hXTm, HOL`Bool`DISJCASES[em, leBranch, notLeBranch]];
    allX = HOL`Bool`GEN[xV, point];
    opened = EQMP[HOL`Equal`SYM[unfoldIsOpen[complSet]], allX];
    closed = EQMP[HOL`Equal`SYM[unfoldIsClosed[closedSet]], opened];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, closed]]
  ];

End[];
EndPackage[];
