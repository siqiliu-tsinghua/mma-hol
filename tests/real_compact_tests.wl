(* ::Package:: *)

(* Tests for M8.2 stdlib/Real/Compact.wl - sequential compactness. *)

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

numTyRCT = mkType["num", {}];
realTyRCT = mkType["real", {}];
seqTyRCT = tyFun[numTyRCT, realTyRCT];
numFunTyRCT = tyFun[numTyRCT, numTyRCT];

rLeRCT[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], a], b];
andRCT[p_, q_] := mkComb[
  mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
orRCT[p_, q_] := mkComb[
  mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impRCT[p_, q_] := mkComb[
  mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
forallRCT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
existsRCT[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];

specAllRCT[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

betaCleanRCT[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

assertConclRCT[name_, th_, expected_] := (
  HOLTest`assertTrue[isThm[th], name <> " is thm"];
  HOLTest`assertEq[hyp[th], {}, name <> " no hyps"];
  HOLTest`assertTrue[aconv[concl[th], expected], name <> " concl"]);

constSeqRCT[cT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRCT];
    mkAbs[nV, cT]
  ];

seqBoundedAllRCT[uT_, loT_, hiT_] :=
  Module[{nV},
    nV = mkVar["n", numTyRCT];
    forallRCT[nV, andRCT[
      rLeRCT[loT, mkComb[uT, nV]],
      rLeRCT[mkComb[uT, nV], hiT]]]
  ];

seqBoundedBodyRCT[uT_] :=
  Module[{loV, hiV},
    loV = mkVar["lo", realTyRCT]; hiV = mkVar["hi", realTyRCT];
    existsRCT[loV, existsRCT[hiV, seqBoundedAllRCT[uT, loV, hiV]]]
  ];

hasConvergentSubseqBodyRCT[uT_, lT_] :=
  Module[{phiV, subSeq},
    phiV = mkVar["phi", numFunTyRCT];
    subSeq = HOL`Stdlib`Real`subsequenceTm[uT, phiV];
    existsRCT[phiV, andRCT[HOL`Stdlib`Real`subseqIndexTm[phiV],
      HOL`Stdlib`Real`tendstoTm[subSeq, lT]]]
  ];

bwGoalRCT[uT_] :=
  Module[{lV},
    lV = mkVar["l", realTyRCT];
    existsRCT[lV, HOL`Stdlib`Real`hasConvergentSubseqTm[uT, lV]]
  ];

monoSubseqBodyRCT[uT_, phiT_] :=
  Module[{subSeq},
    subSeq = HOL`Stdlib`Real`subsequenceTm[uT, phiT];
    andRCT[HOL`Stdlib`Real`subseqIndexTm[phiT],
      orRCT[HOL`Stdlib`Real`monoIncTm[subSeq], HOL`Stdlib`Real`monoDecTm[subSeq]]]
  ];

constSeqBoundedRCT[cT_] :=
  Module[{nV, seq, clean, outerEx, betaLo, innerEx, leCC, allN, exHi, exLo},
    nV = mkVar["n", numTyRCT]; seq = constSeqRCT[cT];
    clean = betaCleanRCT[HOL`Stdlib`Real`unfoldSeqBounded[seq]];
    outerEx = concl[clean][[2]];
    betaLo = HOL`Equal`BETACONV[mkComb[outerEx[[2]], cT]];
    innerEx = concl[betaLo][[2]];
    leCC = HOL`Bool`SPEC[cT, HOL`Stdlib`Real`realLeReflThm];
    allN = HOL`Bool`GEN[nV, HOL`Bool`CONJ[leCC, leCC]];
    exHi = HOL`Bool`EXISTS[innerEx, cT, allN];
    exLo = HOL`Bool`EXISTS[outerEx, cT, exHi];
    EQMP[HOL`Equal`SYM[clean], exLo]
  ];

HOLTest`runTests["stdlib/Real/Compact: definitions and builders",
  Module[{uV, lV, th, expected},
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`seqBoundedDefThm], {},
      "seqBoundedDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`seqBoundedDefThm],
      "seqBoundedDef is thm"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Real`hasConvergentSubseqDefThm], {},
      "hasConvergentSubseqDef no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Real`hasConvergentSubseqDefThm],
      "hasConvergentSubseqDef is thm"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`seqBoundedConst[]],
      tyFun[seqTyRCT, boolTy], "seqBoundedConst type"];
    HOLTest`assertEq[typeOf[HOL`Stdlib`Real`hasConvergentSubseqConst[]],
      tyFun[seqTyRCT, tyFun[realTyRCT, boolTy]], "hasConvergentSubseqConst type"];

    uV = mkVar["uCompactRCT", seqTyRCT]; lV = mkVar["lCompactRCT", realTyRCT];
    th = HOL`Stdlib`Real`unfoldSeqBounded[uV];
    expected = mkEq[HOL`Stdlib`Real`seqBoundedTm[uV], seqBoundedBodyRCT[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected], "unfoldSeqBounded body"];

    th = HOL`Stdlib`Real`unfoldHasConvergentSubseq[uV, lV];
    expected = mkEq[HOL`Stdlib`Real`hasConvergentSubseqTm[uV, lV],
      hasConvergentSubseqBodyRCT[uV, lV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "unfoldHasConvergentSubseq body"]]];

HOLTest`runTests["stdlib/Real/Compact: theorem objects",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`Private`seqBoundedSubseqAboveThm],
    "seqBoundedSubseqAboveThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`Private`seqBoundedSubseqAboveThm], {},
    "seqBoundedSubseqAboveThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`Private`seqBoundedSubseqBelowThm],
    "seqBoundedSubseqBelowThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`Private`seqBoundedSubseqBelowThm], {},
    "seqBoundedSubseqBelowThm no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`bwSequentialThm],
    "bwSequentialThm is thm"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`bwSequentialThm], {},
    "bwSequentialThm no hyps"]];

HOLTest`runTests["stdlib/Real/Compact: theorem shapes",
  Module[{uV, phiV, subSeq, th, expected},
    uV = mkVar["uShapeRCT", seqTyRCT];
    phiV = mkVar["phiShapeRCT", numFunTyRCT];
    subSeq = HOL`Stdlib`Real`subsequenceTm[uV, phiV];

    th = specAllRCT[HOL`Stdlib`Real`Private`seqBoundedSubseqAboveThm, {uV, phiV}];
    expected = impRCT[HOL`Stdlib`Real`seqBoundedTm[uV],
      HOL`Stdlib`Real`seqBddAboveTm[subSeq]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "seqBoundedSubseqAbove instantiated shape"];

    th = specAllRCT[HOL`Stdlib`Real`Private`seqBoundedSubseqBelowThm, {uV, phiV}];
    expected = impRCT[HOL`Stdlib`Real`seqBoundedTm[uV],
      HOL`Stdlib`Real`seqBddBelowTm[subSeq]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "seqBoundedSubseqBelow instantiated shape"];

    th = HOL`Bool`SPEC[uV, HOL`Stdlib`Real`bwSequentialThm];
    expected = impRCT[HOL`Stdlib`Real`seqBoundedTm[uV], bwGoalRCT[uV]];
    HOLTest`assertTrue[aconv[concl[th], expected],
      "bwSequential instantiated shape"]]];

HOLTest`runTests["stdlib/Real/Compact: constant sequence boundedness",
  Module[{cV, cSeq, bounded, inst, th, expected},
    cV = mkVar["cCompactRCT", realTyRCT];
    cSeq = constSeqRCT[cV];
    bounded = constSeqBoundedRCT[cV];
    expected = HOL`Stdlib`Real`seqBoundedTm[cSeq];
    assertConclRCT["constant seqBounded", bounded, expected];

    inst = HOL`Bool`SPEC[cSeq, HOL`Stdlib`Real`bwSequentialThm];
    th = HOL`Bool`MP[inst, bounded];
    expected = bwGoalRCT[cSeq];
    assertConclRCT["constant bwSequential", th, expected]]];

(* NOTE: no testExit[] here — the runners (run_all/run_fast/dev) call it once
   centrally; a per-file testExit[] would Exit[] the process and truncate
   run_all (it passes dev.wls only because that runs this file last). *)
