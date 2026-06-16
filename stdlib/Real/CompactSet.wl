(* M8.5 / stdlib/Real/CompactSet.wl - sequential compactness for real sets. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`Arith`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

isSequentiallyCompactDefThm::usage = "isSequentiallyCompactDefThm - |- isSequentiallyCompact = (lambda S. forall u. (forall n. S (u n)) ==> exists l. S l /\\ hasConvergentSubseq u l).";
isSequentiallyCompactConst::usage = "isSequentiallyCompactConst[] - isSequentiallyCompact : (real -> bool) -> bool.";
isSequentiallyCompactTm::usage = "isSequentiallyCompactTm[S] - builds isSequentiallyCompact S.";
unfoldIsSequentiallyCompact::usage = "unfoldIsSequentiallyCompact[S] - proves the beta-reduced isSequentiallyCompact definition at S.";

seqBoundedOfSetBoundedThm::usage = "seqBoundedOfSetBoundedThm - |- forall S u. setBounded S ==> (forall n. S (u n)) ==> seqBounded u.";
sequentiallyCompactOfClosedBoundedThm::usage = "sequentiallyCompactOfClosedBoundedThm - |- forall S. isClosed S ==> setBounded S ==> isSequentiallyCompact S.";

Begin["`Private`"];

csetRealTy = mkType["real", {}];
csetNumTy = mkType["num", {}];
csetSeqTy = tyFun[csetNumTy, csetRealTy];
csetNumFunTy = tyFun[csetNumTy, csetNumTy];
csetSetTy = tyFun[csetRealTy, boolTy];
isSequentiallyCompactTy = tyFun[csetSetTy, boolTy];

csetAndConst[] := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
csetImpConst[] := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
csetConjTm[pT_, qT_] := mkComb[mkComb[csetAndConst[], pT], qT];
csetImpTm[pT_, qT_] := mkComb[mkComb[csetImpConst[], pT], qT];
csetForallTm[vT_, bodyT_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];
csetExistsTm[vT_, bodyT_] :=
  mkComb[mkConst["∃", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];

csetSetApp[sT_, xT_] := mkComb[sT, xT];
csetSeqApp[uT_, nT_] := mkComb[uT, nT];
csetRealLe[aT_, bT_] := mkComb[mkComb[realLeConst[], aT], bT];

csetSpecAll[th_, ts_List] :=
  Fold[Function[{accTh, termT}, HOL`Bool`SPEC[termT, accTh]], th, ts];

csetApplyDef[defTh_, args_List] :=
  Fold[Function[{accTh, argT}, Module[{stepTh},
    stepTh = HOL`Equal`APTHM[accTh, argT];
    TRANS[stepTh, HOL`Equal`BETACONV[concl[stepTh][[2]]]]
  ]], defTh, args];

csetSetBoundedAll[sT_, loT_, hiT_] :=
  Module[{xV},
    xV = mkVar["xCset", csetRealTy];
    csetForallTm[xV, csetImpTm[csetSetApp[sT, xV],
      csetConjTm[csetRealLe[loT, xV], csetRealLe[xV, hiT]]]]
  ];

csetSeqBoundedAll[uT_, loT_, hiT_] :=
  Module[{nV},
    nV = mkVar["nCset", csetNumTy];
    csetForallTm[nV, csetConjTm[
      csetRealLe[loT, csetSeqApp[uT, nV]],
      csetRealLe[csetSeqApp[uT, nV], hiT]]]
  ];

csetAllInSet[sT_, uT_] :=
  Module[{nV},
    nV = mkVar["nCset", csetNumTy];
    csetForallTm[nV, csetSetApp[sT, csetSeqApp[uT, nV]]]
  ];

csetHasConvergentSubseqBody[uT_, lT_] :=
  Module[{phiV, subSeq},
    phiV = mkVar["phiCset", csetNumFunTy];
    subSeq = subsequenceTm[uT, phiV];
    csetExistsTm[phiV, csetConjTm[subseqIndexTm[phiV], tendstoTm[subSeq, lT]]]
  ];

csetSeqCompactGoal[sT_, uT_] :=
  Module[{lV},
    lV = mkVar["lCset", csetRealTy];
    csetExistsTm[lV, csetConjTm[csetSetApp[sT, lV],
      hasConvergentSubseqTm[uT, lV]]]
  ];

csetIsSequentiallyCompactBody[sT_] :=
  Module[{uV},
    uV = mkVar["uCset", csetSeqTy];
    csetForallTm[uV, csetImpTm[csetAllInSet[sT, uV],
      csetSeqCompactGoal[sT, uV]]]
  ];

csetSubsequenceAppEq[uT_, phiT_, nT_] :=
  Module[{unf, app},
    unf = unfoldSubsequence[uT, phiT];
    app = HOL`Equal`APTHM[unf, nT];
    TRANS[app, HOL`Equal`BETACONV[concl[app][[2]]]]
  ];

isSequentiallyCompactDefThm =
  Module[{sV},
    sV = mkVar["S", csetSetTy];
    newDefinition[mkEq[mkVar["isSequentiallyCompact", isSequentiallyCompactTy],
      mkAbs[sV, csetIsSequentiallyCompactBody[sV]]]]
  ];

isSequentiallyCompactConst[] := mkConst["isSequentiallyCompact", isSequentiallyCompactTy];
isSequentiallyCompactTm[sT_] := mkComb[isSequentiallyCompactConst[], sT];
unfoldIsSequentiallyCompact[sT_] :=
  csetApplyDef[isSequentiallyCompactDefThm, {sT}];

seqBoundedOfSetBoundedThm =
  Module[{sV, uV, loW, hiW, nW, hBoundTm, hBound, hAllTm, hAll,
          openBound, hBoundsTm, hBounds, memN, boundsN, allN,
          cleanSeqBounded, outerEx, betaLo, innerEx, exHi, exLo,
          folded, chooseHi, chooseLo},
    sV = mkVar["S", csetSetTy]; uV = mkVar["u", csetSeqTy];
    loW = mkVar["loCsetW", csetRealTy]; hiW = mkVar["hiCsetW", csetRealTy];
    nW = mkVar["nCsetW", csetNumTy];
    hBoundTm = setBoundedTm[sV]; hBound = ASSUME[hBoundTm];
    hAllTm = csetAllInSet[sV, uV]; hAll = ASSUME[hAllTm];
    openBound = EQMP[unfoldSetBounded[sV], hBound];
    hBoundsTm = csetSetBoundedAll[sV, loW, hiW]; hBounds = ASSUME[hBoundsTm];
    memN = HOL`Bool`SPEC[nW, hAll];
    boundsN = HOL`Bool`MP[HOL`Bool`SPEC[csetSeqApp[uV, nW], hBounds], memN];
    allN = HOL`Bool`GEN[nW, boundsN];
    cleanSeqBounded = unfoldSeqBounded[uV];
    outerEx = concl[cleanSeqBounded][[2]];
    betaLo = HOL`Equal`BETACONV[mkComb[outerEx[[2]], loW]];
    innerEx = concl[betaLo][[2]];
    exHi = HOL`Bool`EXISTS[innerEx, hiW, allN];
    exLo = HOL`Bool`EXISTS[outerEx, loW, exHi];
    folded = EQMP[HOL`Equal`SYM[cleanSeqBounded], exLo];
    chooseHi = HOL`Bool`CHOOSE[hiW, ASSUME[csetExistsTm[hiW, hBoundsTm]], folded];
    chooseLo = HOL`Bool`CHOOSE[loW, openBound, chooseHi];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[uV, HOL`Bool`DISCH[hBoundTm,
      HOL`Bool`DISCH[hAllTm, chooseLo]]]]
  ];

sequentiallyCompactOfClosedBoundedThm =
  Module[{sV, uV, lW, phiW, nW, subSeq, hClosedTm, hClosed, hBoundTm,
          hBound, hAllTm, hAll, seqBdd, convEx, hHasTm, hHas, openHas,
          hBodyTm, hBody, idxTh, tendTh, subEq, sOrig, sSub, subAll,
          limitTh, cleanHas, hasBody, hasFolded, bodyConj, exL, choosePhi,
          chooseL, allU, folded},
    sV = mkVar["S", csetSetTy]; uV = mkVar["u", csetSeqTy];
    lW = mkVar["lCsetW", csetRealTy]; phiW = mkVar["phiCsetW", csetNumFunTy];
    nW = mkVar["nCsetW", csetNumTy];
    subSeq = subsequenceTm[uV, phiW];
    hClosedTm = isClosedTm[sV]; hClosed = ASSUME[hClosedTm];
    hBoundTm = setBoundedTm[sV]; hBound = ASSUME[hBoundTm];
    hAllTm = csetAllInSet[sV, uV]; hAll = ASSUME[hAllTm];
    seqBdd = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[seqBoundedOfSetBoundedThm, {sV, uV}], hBound], hAll];
    convEx = HOL`Bool`MP[HOL`Bool`SPEC[uV, bwSequentialThm], seqBdd];
    hHasTm = hasConvergentSubseqTm[uV, lW]; hHas = ASSUME[hHasTm];
    openHas = EQMP[unfoldHasConvergentSubseq[uV, lW], hHas];
    hBodyTm = csetConjTm[subseqIndexTm[phiW], tendstoTm[subSeq, lW]];
    hBody = ASSUME[hBodyTm];
    idxTh = HOL`Bool`CONJUNCT1[hBody];
    tendTh = HOL`Bool`CONJUNCT2[hBody];
    subEq = csetSubsequenceAppEq[uV, phiW, nW];
    sOrig = HOL`Bool`SPEC[csetSeqApp[phiW, nW], hAll];
    sSub = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[sV, subEq]], sOrig];
    subAll = HOL`Bool`GEN[nW, sSub];
    limitTh = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[limitMemOfClosedThm, {sV, subSeq, lW}], hClosed], subAll], tendTh];
    cleanHas = unfoldHasConvergentSubseq[uV, lW];
    hasBody = HOL`Bool`EXISTS[concl[cleanHas][[2]], phiW,
      HOL`Bool`CONJ[idxTh, tendTh]];
    hasFolded = EQMP[HOL`Equal`SYM[cleanHas], hasBody];
    bodyConj = HOL`Bool`CONJ[limitTh, hasFolded];
    exL = HOL`Bool`EXISTS[csetSeqCompactGoal[sV, uV], lW, bodyConj];
    choosePhi = HOL`Bool`CHOOSE[phiW, openHas, exL];
    chooseL = HOL`Bool`CHOOSE[lW, convEx, choosePhi];
    allU = HOL`Bool`GEN[uV, HOL`Bool`DISCH[hAllTm, chooseL]];
    folded = EQMP[HOL`Equal`SYM[unfoldIsSequentiallyCompact[sV]], allU];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hClosedTm,
      HOL`Bool`DISCH[hBoundTm, folded]]]
  ];

End[];
EndPackage[];
