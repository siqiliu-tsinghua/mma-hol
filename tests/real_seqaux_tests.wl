(* ::Package:: *)

(* Tests for M8.2 stdlib/Real/SeqAux.wl - dyadic sequence auxiliaries. *)

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

numTyRSAT = mkType["num", {}];
realTyRSAT = mkType["real", {}];

zeroNumRSAT[] := HOL`Stdlib`Num`zeroConst[];
sucNumRSAT[n_] := mkComb[HOL`Stdlib`Num`sucConst[], n];
oneNumRSAT[] := sucNumRSAT[zeroNumRSAT[]];
twoNumRSAT[] := sucNumRSAT[oneNumRSAT[]];
intOfNumRSAT[nT_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], nT];
ratOfIntRSAT[zT_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], zT];
realOfRatRSAT[qT_] := mkComb[HOL`Stdlib`Real`realOfRatConst[], qT];
natRealRSAT[nT_] := realOfRatRSAT[ratOfIntRSAT[intOfNumRSAT[nT]]];
zeroRealRSAT[] := natRealRSAT[zeroNumRSAT[]];
oneRealRSAT[] := natRealRSAT[oneNumRSAT[]];
twoRealRSAT[] := natRealRSAT[twoNumRSAT[]];
dyadicRSAT[nT_] := HOL`Stdlib`Real`dyadicTm[nT];
realMulRSAT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realMulConst[], x], y];
realAddRSAT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], x], y];
realInvRSAT[x_] := mkComb[HOL`Stdlib`Real`realInvConst[], x];
realLeRSAT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], x], y];
realLtRSAT[x_, y_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], x], y];
andRSAT[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impRSAT[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
existsRSAT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
forallRSAT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];

specAllRSAT[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

assertConclRSAT[name_, th_, expected_] := (
  HOLTest`assertTrue[isThm[th], name <> " is thm"];
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

HOLTest`runTests["stdlib/Real/SeqAux: dyadic definitions and theorem shapes",
  Module[{nV, lV, epsV, recExpected, stepExpected, archExpected,
          concreteN, concreteSucc},
    nV = mkVar["n", numTyRSAT];
    lV = mkVar["L", realTyRSAT];
    epsV = mkVar["eps", realTyRSAT];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`dyadicConst[]],
      tyFun[numTyRSAT, realTyRSAT], "dyadicConst type"];
    HOLTest`assertTrue[aconv[HOL`Stdlib`Real`dyadicTm[nV], dyadicRSAT[nV]],
      "dyadicTm builder"];
    recExpected = andRSAT[mkEq[dyadicRSAT[zeroNumRSAT[]], oneRealRSAT[]],
      forallRSAT[nV, mkEq[dyadicRSAT[sucNumRSAT[nV]],
        realMulRSAT[dyadicRSAT[nV], twoRealRSAT[]]]]];
    assertConclRSAT["dyadicRecSpecThm", HOL`Stdlib`Real`dyadicRecSpecThm,
      recExpected];
    assertConclRSAT["dyadicZeroThm", HOL`Stdlib`Real`dyadicZeroThm,
      mkEq[dyadicRSAT[zeroNumRSAT[]], oneRealRSAT[]]];
    concreteN = oneNumRSAT[];
    concreteSucc = specAllRSAT[HOL`Stdlib`Real`dyadicSuccThm, {concreteN}];
    assertConclRSAT["dyadicSuccThm numeral", concreteSucc,
      mkEq[dyadicRSAT[sucNumRSAT[concreteN]],
        realMulRSAT[dyadicRSAT[concreteN], twoRealRSAT[]]]];
    stepExpected = mkEq[dyadicRSAT[sucNumRSAT[nV]],
      realAddRSAT[dyadicRSAT[nV], dyadicRSAT[nV]]];
    assertConclRSAT["dyadicSuccAddThm", specAllRSAT[HOL`Stdlib`Real`dyadicSuccAddThm, {nV}],
      stepExpected];
    assertConclRSAT["dyadicPosThm", specAllRSAT[HOL`Stdlib`Real`dyadicPosThm, {nV}],
      realLtRSAT[zeroRealRSAT[], dyadicRSAT[nV]]];
    assertConclRSAT["oneLeDyadicThm", specAllRSAT[HOL`Stdlib`Real`oneLeDyadicThm, {nV}],
      realLeRSAT[oneRealRSAT[], dyadicRSAT[nV]]];
    assertConclRSAT["natLeDyadicThm", specAllRSAT[HOL`Stdlib`Real`natLeDyadicThm, {nV}],
      realLeRSAT[natRealRSAT[nV], dyadicRSAT[nV]]];
    assertConclRSAT["existsDyadicGtThm", specAllRSAT[HOL`Stdlib`Real`existsDyadicGtThm, {lV}],
      existsRSAT[nV, realLtRSAT[lV, dyadicRSAT[nV]]]];
    archExpected = impRSAT[realLeRSAT[zeroRealRSAT[], lV],
      impRSAT[realLtRSAT[zeroRealRSAT[], epsV],
        existsRSAT[nV, realLtRSAT[realMulRSAT[lV, realInvRSAT[dyadicRSAT[nV]]], epsV]]]];
    assertConclRSAT["dyadicArchThm", specAllRSAT[HOL`Stdlib`Real`dyadicArchThm, {lV, epsV}],
      archExpected]
  ]
]

realNegRSAT[x_] := mkComb[HOL`Stdlib`Real`realNegConst[], x];
realAbsRSAT[x_] := mkComb[HOL`Stdlib`Real`realAbsConst[], x];
realLtCongRSAT[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Real`realLtConst[], eqLeft], eqRight];

HOLTest`runTests["stdlib/Real/SeqAux: nested interval helper shapes",
  Module[{aV, bV, xV, yV, epsV, len, intervalExpected, lengthExpected,
          z0, z1, z2, intervalInst, hAx, hXb, hAy, hYb, hLen,
          concreteInterval, lengthInst, hLe, closeArg, dropZero, lenNonneg,
          absDrop, absPos, absEq, lenLt, hClose, concreteLength},
    aV = mkVar["a", realTyRSAT]; bV = mkVar["b", realTyRSAT];
    xV = mkVar["x", realTyRSAT]; yV = mkVar["y", realTyRSAT];
    epsV = mkVar["eps", realTyRSAT];
    len = realAddRSAT[bV, realNegRSAT[aV]];
    intervalExpected = impRSAT[realLeRSAT[aV, xV],
      impRSAT[realLeRSAT[xV, bV],
        impRSAT[realLeRSAT[aV, yV],
          impRSAT[realLeRSAT[yV, bV],
            impRSAT[realLtRSAT[len, epsV],
              realLtRSAT[realAbsRSAT[realAddRSAT[xV, realNegRSAT[yV]]], epsV]]]]]];
    assertConclRSAT["intervalPointsCloseThm",
      specAllRSAT[HOL`Stdlib`Real`intervalPointsCloseThm, {aV, bV, xV, yV, epsV}],
      intervalExpected];
    lengthExpected = impRSAT[realLeRSAT[aV, bV],
      impRSAT[realLtRSAT[
        realAbsRSAT[realAddRSAT[len, realNegRSAT[zeroRealRSAT[]]]], epsV],
        realLtRSAT[len, epsV]]];
    assertConclRSAT["lengthLtOfCloseThm",
      specAllRSAT[HOL`Stdlib`Real`lengthLtOfCloseThm, {aV, bV, epsV}],
      lengthExpected];
    z0 = zeroRealRSAT[]; z1 = oneRealRSAT[]; z2 = twoRealRSAT[];
    intervalInst = specAllRSAT[HOL`Stdlib`Real`intervalPointsCloseThm,
      {z0, z1, z0, z1, z2}];
    hAx = HOL`Auto`RealArith`rnumLe[0, 0];
    hXb = HOL`Auto`RealArith`rnumLe[0, 1];
    hAy = HOL`Auto`RealArith`rnumLe[0, 1];
    hYb = HOL`Auto`RealArith`rnumLe[1, 1];
    hLen = HOL`Auto`RealArith`realArithProve[
      realLtRSAT[realAddRSAT[z1, realNegRSAT[z0]], z2]];
    concreteInterval = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`MP[intervalInst, hAx], hXb], hAy], hYb], hLen];
    assertConclRSAT["intervalPointsCloseThm concrete", concreteInterval,
      realLtRSAT[realAbsRSAT[realAddRSAT[z0, realNegRSAT[z1]]], z2]];
    lengthInst = specAllRSAT[HOL`Stdlib`Real`lengthLtOfCloseThm, {z0, z1, z2}];
    hLe = HOL`Auto`RealArith`rnumLe[0, 1];
    len = realAddRSAT[z1, realNegRSAT[z0]];
    closeArg = realAddRSAT[len, realNegRSAT[z0]];
    dropZero = HOL`Auto`RealArith`realArithProve[mkEq[closeArg, len]];
    lenNonneg = HOL`Auto`RealArith`realArithProve[realLeRSAT[z0, len]];
    absDrop = HOL`Equal`APTERM[HOL`Stdlib`Real`realAbsConst[], dropZero];
    absPos = HOL`Bool`MP[HOL`Bool`SPEC[len, HOL`Stdlib`Real`realAbsPosThm], lenNonneg];
    absEq = HOL`Kernel`TRANS[absDrop, absPos];
    lenLt = HOL`Auto`RealArith`realArithProve[realLtRSAT[len, z2]];
    hClose = HOL`Kernel`EQMP[realLtCongRSAT[HOL`Equal`SYM[absEq], HOL`Kernel`REFL[z2]], lenLt];
    concreteLength = HOL`Bool`MP[HOL`Bool`MP[lengthInst, hLe], hClose];
    assertConclRSAT["lengthLtOfCloseThm concrete", concreteLength,
      realLtRSAT[realAddRSAT[z1, realNegRSAT[z0]], z2]]
  ]
]
