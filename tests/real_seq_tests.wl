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
Needs["HOL`Auto`RealArith`"];

numTyRST = mkType["num", {}];
realTyRST = mkType["real", {}];
seqTyRST = tyFun[numTyRST, realTyRST];

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
rLtRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], a], b];
nLeRST[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
impRST[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
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
    "tendstoConvergentThm no hyps"]];

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
