(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Num`"];
Needs["HOL`Stdlib`Int`"];
Needs["HOL`Stdlib`Rat`"];
Needs["HOL`Stdlib`Real`"];
Needs["HOL`Auto`RealArith`"];

numTyRAT = mkType["num", {}];
realTyRAT = mkType["real", {}];

natT[n_Integer] := Nest[mkComb[HOL`Stdlib`Num`sucConst[], #] &,
  HOL`Stdlib`Num`zeroConst[], n];
intOfNumT[nT_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], nT];
ratOfIntT[zT_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], zT];
realOfRatT[qT_] := mkComb[HOL`Stdlib`Real`realOfRatConst[], qT];
rnumT[n_Integer] := realOfRatT[ratOfIntT[intOfNumT[natT[n]]]];
rAddT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], a], b];
rMulT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realMulConst[], a], b];
rLeT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], a], b];
rLtT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], a], b];
notT[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
conjT[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
specAllT[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

assertThmConcl[name_String, th_, expected_] := (
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

HOLTest`runTests["auto/RealArith: ground real arithmetic",
  assertThmConcl["rnumAdd 2 3", HOL`Auto`RealArith`rnumAdd[2, 3],
    mkEq[rAddT[rnumT[2], rnumT[3]], rnumT[5]]];
  assertThmConcl["rnumAdd 7 5", HOL`Auto`RealArith`rnumAdd[7, 5],
    mkEq[rAddT[rnumT[7], rnumT[5]], rnumT[12]]];
  assertThmConcl["rnumAdd 0 4", HOL`Auto`RealArith`rnumAdd[0, 4],
    mkEq[rAddT[rnumT[0], rnumT[4]], rnumT[4]]];
  assertThmConcl["rnumMul 2 3", HOL`Auto`RealArith`rnumMul[2, 3],
    mkEq[rMulT[rnumT[2], rnumT[3]], rnumT[6]]];
  assertThmConcl["rnumMul 6 7", HOL`Auto`RealArith`rnumMul[6, 7],
    mkEq[rMulT[rnumT[6], rnumT[7]], rnumT[42]]];
  assertThmConcl["rnumMul 0 5", HOL`Auto`RealArith`rnumMul[0, 5],
    mkEq[rMulT[rnumT[0], rnumT[5]], rnumT[0]]];
  assertThmConcl["rnumLe 3 9", HOL`Auto`RealArith`rnumLe[3, 9],
    rLeT[rnumT[3], rnumT[9]]];
  assertThmConcl["rnumLe 4 4", HOL`Auto`RealArith`rnumLe[4, 4],
    rLeT[rnumT[4], rnumT[4]]];
  assertThmConcl["rnumLt 1 3", HOL`Auto`RealArith`rnumLt[1, 3],
    rLtT[rnumT[1], rnumT[3]]];
  assertThmConcl["rnumNotLe 9 2", HOL`Auto`RealArith`rnumNotLe[9, 2],
    notT[rLeT[rnumT[9], rnumT[2]]]];
  assertThmConcl["rnumPos 2", HOL`Auto`RealArith`rnumPos[2],
    rLtT[rnumT[0], rnumT[2]]];
  assertThmConcl["rnumNonneg 0", HOL`Auto`RealArith`rnumNonneg[0],
    rLeT[rnumT[0], rnumT[0]]]];

HOLTest`runTests["auto/RealArith: ground domain errors",
  HOLTest`assertThrows[HOL`Auto`RealArith`rnumLe[5, 1], "realarith-ground",
    "rnumLe rejects descending"];
  HOLTest`assertThrows[HOL`Auto`RealArith`rnumLt[3, 3], "realarith-ground",
    "rnumLt rejects equality"];
  HOLTest`assertThrows[HOL`Auto`RealArith`rnumPos[0], "realarith-ground",
    "rnumPos rejects zero"]];

HOLTest`runTests["auto/RealArith: ordered-field add lemmas",
  Module[{th, res},
    th = HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLeAddMonoRThm,
        {rnumT[1], rnumT[2], rnumT[5]}],
      HOL`Auto`RealArith`rnumLe[2, 5]];
    assertThmConcl["realLeAddMonoRThm", th,
      rLeT[rAddT[rnumT[1], rnumT[2]], rAddT[rnumT[1], rnumT[5]]]];

    th = HOL`Bool`MP[HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLeAddMono2Thm,
        {rnumT[1], rnumT[3], rnumT[2], rnumT[5]}],
      HOL`Auto`RealArith`rnumLe[1, 3]], HOL`Auto`RealArith`rnumLe[2, 5]];
    assertThmConcl["realLeAddMono2Thm", th,
      rLeT[rAddT[rnumT[1], rnumT[2]], rAddT[rnumT[3], rnumT[5]]]];

    th = HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLtAddMonoRThm,
        {rnumT[1], rnumT[2], rnumT[5]}],
      HOL`Auto`RealArith`rnumLt[2, 5]];
    assertThmConcl["realLtAddMonoRThm", th,
      rLtT[rAddT[rnumT[1], rnumT[2]], rAddT[rnumT[1], rnumT[5]]]];

    th = HOL`Bool`MP[HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLtLeAddMonoThm,
        {rnumT[1], rnumT[3], rnumT[2], rnumT[5]}],
      HOL`Auto`RealArith`rnumLt[1, 3]], HOL`Auto`RealArith`rnumLe[2, 5]];
    assertThmConcl["realLtLeAddMonoThm", th,
      rLtT[rAddT[rnumT[1], rnumT[2]], rAddT[rnumT[3], rnumT[5]]]];

    th = HOL`Bool`MP[HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLeLtAddMonoThm,
        {rnumT[1], rnumT[3], rnumT[2], rnumT[5]}],
      HOL`Auto`RealArith`rnumLe[1, 3]], HOL`Auto`RealArith`rnumLt[2, 5]];
    assertThmConcl["realLeLtAddMonoThm", th,
      rLtT[rAddT[rnumT[1], rnumT[2]], rAddT[rnumT[3], rnumT[5]]]];

    th = HOL`Bool`MP[HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLtAddMono2Thm,
        {rnumT[1], rnumT[3], rnumT[2], rnumT[5]}],
      HOL`Auto`RealArith`rnumLt[1, 3]], HOL`Auto`RealArith`rnumLt[2, 5]];
    assertThmConcl["realLtAddMono2Thm", th,
      rLtT[rAddT[rnumT[1], rnumT[2]], rAddT[rnumT[3], rnumT[5]]]]
  ]];

HOLTest`runTests["auto/RealArith: ordered-field order and cancellation lemmas",
  Module[{xV, th, eqTh, res},
    xV = mkVar["xRAT", realTyRAT];
    th = HOL`Bool`SPEC[xV, HOL`Auto`RealArith`realLtIrreflThm];
    assertThmConcl["realLtIrreflThm", th, notT[rLtT[xV, xV]]];

    eqTh = specAllT[HOL`Auto`RealArith`realNotLeLtThm,
      {rnumT[3], rnumT[1]}];
    th = EQMP[eqTh, HOL`Auto`RealArith`rnumNotLe[3, 1]];
    assertThmConcl["realNotLeLtThm", th, rLtT[rnumT[1], rnumT[3]]];

    eqTh = HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLeMulCancelThm,
        {rnumT[2], rnumT[1], rnumT[3]}],
      HOL`Auto`RealArith`rnumPos[2]];
    th = EQMP[HOL`Equal`SYM[eqTh], HOL`Auto`RealArith`rnumLe[1, 3]];
    assertThmConcl["realLeMulCancelThm", th,
      rLeT[rMulT[rnumT[2], rnumT[1]], rMulT[rnumT[2], rnumT[3]]]];

    eqTh = HOL`Bool`MP[
      specAllT[HOL`Auto`RealArith`realLtMulCancelThm,
        {rnumT[2], rnumT[1], rnumT[3]}],
      HOL`Auto`RealArith`rnumPos[2]];
    th = EQMP[HOL`Equal`SYM[eqTh], HOL`Auto`RealArith`rnumLt[1, 3]];
    assertThmConcl["realLtMulCancelThm", th,
      rLtT[rMulT[rnumT[2], rnumT[1]], rMulT[rnumT[2], rnumT[3]]]];

    eqTh = specAllT[HOL`Auto`RealArith`realEqIffLeLeThm,
      {rnumT[4], rnumT[4]}];
    th = EQMP[eqTh, REFL[rnumT[4]]];
    assertThmConcl["realEqIffLeLeThm", th,
      conjT[rLeT[rnumT[4], rnumT[4]], rLeT[rnumT[4], rnumT[4]]]]
  ]];

rNegT[x_] := mkComb[HOL`Stdlib`Real`realNegConst[], x];
rInvT[x_] := mkComb[HOL`Stdlib`Real`realInvConst[], x];
rAbsT[x_] := mkComb[HOL`Stdlib`Real`realAbsConst[], x];

realConstT[c_Integer] :=
  If[c >= 0, rnumT[c], rNegT[rnumT[-c]]];

realSummandT[c_Integer, x_] :=
  Which[
    c > 0, rMulT[rnumT[c], x],
    c < 0, rNegT[rMulT[rnumT[-c], x]],
    True, rnumT[0]
  ];

rightRealSumT[{x_}] := x;
rightRealSumT[xs_List] :=
  Fold[rAddT[#2, #1] &, Last[xs], Reverse[Most[xs]]];

canonRealT[c_Integer, pairs_List] :=
  Module[{clean, sorted, terms},
    clean = Select[pairs, #[[1]] =!= 0 &];
    sorted = Sort[clean,
      Order[stripOrigin[#1[[2]]], stripOrigin[#2[[2]]]] === 1 &];
    terms = Prepend[(realSummandT[#[[1]], #[[2]]] &) /@ sorted,
      realConstT[c]];
    rightRealSumT[terms]
  ];

assertRealConv[name_String, input_, expected_] :=
  Module[{th},
    th = HOL`Auto`RealArith`realLinNormConv[input];
    HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
    HOLTest`assertTrue[aconv[concl[th], mkEq[input, expected]],
      name <> " concl"]
  ];

assertAtomConv[name_String, input_, expected_] :=
  Module[{th},
    th = HOL`Auto`RealArith`realAtomNormConv[input];
    HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
    HOLTest`assertTrue[aconv[concl[th], mkEq[input, expected]],
      name <> " concl"]
  ];

HOLTest`runTests["auto/RealArith: realLinNormConv canonical forms",
  Module[{x, y, z, ax, halfX},
    x = mkVar["xRLN", realTyRAT];
    y = mkVar["yRLN", realTyRAT];
    z = mkVar["zRLN", realTyRAT];
    ax = rAbsT[z];
    halfX = rMulT[x, rInvT[rnumT[2]]];

    assertRealConv["literal add", rAddT[rnumT[2], rnumT[3]], rnumT[5]];
    assertRealConv["single var", x, canonRealT[0, {{1, x}}]];
    assertRealConv["x plus x", rAddT[x, x], canonRealT[0, {{2, x}}]];
    assertRealConv["sort y plus x", rAddT[y, x],
      canonRealT[0, {{1, y}, {1, x}}]];
    assertRealConv["weighted merge plus const",
      rAddT[rAddT[rMulT[rnumT[2], x], rMulT[rnumT[3], x]], rnumT[1]],
      canonRealT[1, {{5, x}}]];
    assertRealConv["neg x plus x", rAddT[rNegT[x], x], rnumT[0]];
    assertRealConv["scale sum", rMulT[rnumT[2], rAddT[x, y]],
      canonRealT[0, {{2, x}, {2, y}}]];
    assertRealConv["neg of signed sum", rNegT[rAddT[x, rNegT[y]]],
      canonRealT[0, {{-1, x}, {1, y}}]];
    assertRealConv["half plus half", rAddT[halfX, halfX],
      canonRealT[0, {{1, x}}]];
    assertRealConv["realAbs opaque merge", rAddT[rMulT[rnumT[2], ax], ax],
      canonRealT[0, {{3, ax}}]];

    HOLTest`assertThrows[HOL`Auto`RealArith`realLinNormConv[halfX],
      "realarith-norm", "x over two rejected as final form"];
    HOLTest`assertThrows[HOL`Auto`RealArith`realLinNormConv[natT[1]],
      "realarith-norm", "num term rejected"]
  ]];

HOLTest`runTests["auto/RealArith: realAtomNormConv canonical atoms",
  Module[{x, y, atom, expected, th, got},
    x = mkVar["xRAN", realTyRAT];
    y = mkVar["yRAN", realTyRAT];

    atom = rLeT[x, y];
    expected = rLeT[canonRealT[0, {{1, x}}], canonRealT[0, {{1, y}}]];
    assertAtomConv["le var atom", atom, expected];

    atom = rLtT[x, y];
    expected = rLtT[canonRealT[0, {{1, x}}], canonRealT[0, {{1, y}}]];
    assertAtomConv["lt var atom", atom, expected];

    atom = rLtT[rAddT[x, rNegT[y]], rnumT[3]];
    expected = rLtT[canonRealT[0, {{1, x}}], canonRealT[3, {{1, y}}]];
    assertAtomConv["balance negative right", atom, expected];

    atom = rLeT[rMulT[x, rInvT[rnumT[2]]], y];
    expected = rLeT[canonRealT[0, {{1, x}}], canonRealT[0, {{2, y}}]];
    assertAtomConv["clear denominator", atom, expected];

    atom = rLeT[
      rAddT[rMulT[rnumT[2], x], rNegT[rMulT[rnumT[3], y]]],
      rAddT[rnumT[1], rNegT[x]]];
    expected = rLeT[canonRealT[0, {{3, x}}], canonRealT[1, {{3, y}}]];
    assertAtomConv["balance both sides", atom, expected];

    atom = rLeT[x, y];
    th = HOL`Auto`RealArith`realAtomNormConv[atom];
    got = EQMP[th, ASSUME[atom]];
    HOLTest`assertEq[hyp[got], {atom}, "EQMP sanity hyp"];
    HOLTest`assertTrue[aconv[concl[got],
      rLeT[canonRealT[0, {{1, x}}], canonRealT[0, {{1, y}}]]],
      "EQMP sanity concl"]
  ]];

HOLTest`runTests["auto/RealArith: Stage 2 lemmas",
  Module[{leEq, ltEq, shifted, base},
    leEq = specAllT[HOL`Auto`RealArith`realLeAddCancelThm,
      {rnumT[1], rnumT[2], rnumT[3]}];
    shifted = EQMP[HOL`Equal`SYM[leEq], HOL`Auto`RealArith`rnumLe[1, 2]];
    assertThmConcl["realLeAddCancel backward", shifted,
      rLeT[rAddT[rnumT[1], rnumT[3]], rAddT[rnumT[2], rnumT[3]]]];
    base = EQMP[leEq, shifted];
    assertThmConcl["realLeAddCancel forward", base,
      rLeT[rnumT[1], rnumT[2]]];

    ltEq = specAllT[HOL`Auto`RealArith`realLtAddCancelThm,
      {rnumT[1], rnumT[2], rnumT[3]}];
    shifted = EQMP[HOL`Equal`SYM[ltEq], HOL`Auto`RealArith`rnumLt[1, 2]];
    assertThmConcl["realLtAddCancel backward", shifted,
      rLtT[rAddT[rnumT[1], rnumT[3]], rAddT[rnumT[2], rnumT[3]]]];
    base = EQMP[ltEq, shifted];
    assertThmConcl["realLtAddCancel forward", base,
      rLtT[rnumT[1], rnumT[2]]];

    assertThmConcl["rnumNe 2 3", HOL`Auto`RealArith`rnumNe[2, 3],
      notT[mkEq[rnumT[2], rnumT[3]]]]
  ]];
