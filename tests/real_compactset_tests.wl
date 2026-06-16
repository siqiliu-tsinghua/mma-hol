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
forallRCST[v_, body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[v], boolTy], boolTy]], mkAbs[v, body]];
existsRCST[v_, body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[typeOf[v], boolTy], boolTy]], mkAbs[v, body]];
setAppRCST[s_, x_] := mkComb[s, x];
seqAppRCST[u_, n_] := mkComb[u, n];

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
