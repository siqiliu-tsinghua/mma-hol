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
natRealLeThm::usage = "natRealLeThm - |- forall m n. m <= n ==> realLe (&R(&Q(&Z m))) (&R(&Q(&Z n))).";
existsOutsideOfNotSetBoundedThm::usage = "existsOutsideOfNotSetBoundedThm - |- forall S B. ~(setBounded S) ==> exists x. S x /\\ (realLt x (realNeg B) \\/ realLt B x).";
ltAbsOfOutsideThm::usage = "ltAbsOfOutsideThm - |- forall x B. realLt x (realNeg B) \\/ realLt B x ==> realLt B (realAbs x).";
unboundedEscapePointDefThm::usage = "unboundedEscapePointDefThm - |- unboundedEscapePoint = (lambda S n. @x. S x /\\ (realLt x (realNeg (&R(&Q(&Z(SUC n))))) \\/ realLt (&R(&Q(&Z(SUC n)))) x)).";
unboundedEscapePointConst::usage = "unboundedEscapePointConst[] - unboundedEscapePoint : (real -> bool) -> num -> real.";
unboundedEscapePointTm::usage = "unboundedEscapePointTm[S] - builds unboundedEscapePoint S.";
unfoldUnboundedEscapePoint::usage = "unfoldUnboundedEscapePoint[S] - proves the beta-reduced unboundedEscapePoint definition at S.";
unboundedEscapePointMemThm::usage = "unboundedEscapePointMemThm - |- forall S. ~(setBounded S) ==> forall n. S (unboundedEscapePoint S n).";
unboundedEscapePointOutsideThm::usage = "unboundedEscapePointOutsideThm - |- forall S. ~(setBounded S) ==> forall n. realLt (unboundedEscapePoint S n) (realNeg (&R(&Q(&Z(SUC n))))) \\/ realLt (&R(&Q(&Z(SUC n)))) (unboundedEscapePoint S n).";
boundedOfSequentiallyCompactThm::usage = "boundedOfSequentiallyCompactThm - |- forall S. isSequentiallyCompact S ==> setBounded S.";

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

csetOrConst[] := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
csetNotConst[] := mkConst["¬", tyFun[boolTy, boolTy]];
csetOrTm[pT_, qT_] := mkComb[mkComb[csetOrConst[], pT], qT];
csetNotTm[pT_] := mkComb[csetNotConst[], pT];
csetRealLt[aT_, bT_] := mkComb[mkComb[realLtConst[], aT], bT];
csetRealNeg[xT_] := mkComb[realNegConst[], xT];
csetRealAbs[xT_] := mkComb[realAbsConst[], xT];
csetNatLe[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], aT], bT];
csetNatAdd[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], aT], bT];
csetSucNum[nT_] := mkComb[HOL`Stdlib`Num`sucConst[], nT];
csetRnumNat[nT_] := realOfRatTm[ratOfIntTm[intOfNumTm[nT]]];
csetSelectConst[ty_] := mkConst["@", tyFun[tyFun[ty, boolTy], ty]];
csetForallList[vs_List, bodyT_] :=
  Fold[Function[{accT, vT}, csetForallTm[vT, accT]], bodyT, Reverse[vs]];
csetRealLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqLeft], eqRight];
csetRealLtCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], eqLeft], eqRight];
csetBetaClean[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

csetOutsideOnly[xT_, bT_] :=
  csetOrTm[csetRealLt[xT, csetRealNeg[bT]], csetRealLt[bT, xT]];
csetOutsideBody[sT_, bT_, xT_] :=
  csetConjTm[csetSetApp[sT, xT], csetOutsideOnly[xT, bT]];
csetEscapeThreshold[nT_] := csetRnumNat[csetSucNum[nT]];
csetUnboundedEscapePred[sT_, nT_] :=
  Module[{xV},
    xV = mkVar["xCsetEscape", csetRealTy];
    mkAbs[xV, csetOutsideBody[sT, csetEscapeThreshold[nT], xV]]
  ];
csetUnboundedEscapeSelect[sT_, nT_] :=
  mkComb[csetSelectConst[csetRealTy], csetUnboundedEscapePred[sT, nT]];
csetUnboundedEscapeApp[sT_, nT_] :=
  csetSeqApp[unboundedEscapePointTm[sT], nT];
csetUnboundedEscapePointAppEq[sT_, nT_] :=
  Module[{unf, app},
    unf = unfoldUnboundedEscapePoint[sT];
    app = HOL`Equal`APTHM[unf, nT];
    csetBetaClean[TRANS[app, HOL`Equal`BETACONV[concl[app][[2]]]]]
  ];
natRealLeThm =
  Module[{mV, nV, hLeTm, hLe, mZ, nZ, mQ, nQ, intLe, ratLe, realLe},
    mV = mkVar["m", csetNumTy]; nV = mkVar["n", csetNumTy];
    hLeTm = csetNatLe[mV, nV]; hLe = ASSUME[hLeTm];
    mZ = intOfNumTm[mV]; nZ = intOfNumTm[nV];
    mQ = ratOfIntTm[mZ]; nQ = ratOfIntTm[nZ];
    intLe = EQMP[HOL`Equal`SYM[
      csetSpecAll[HOL`Stdlib`Int`intOfNumLeThm, {mV, nV}]], hLe];
    ratLe = EQMP[HOL`Equal`SYM[
      csetSpecAll[HOL`Stdlib`Rat`ratOfIntLeThm, {mZ, nZ}]], intLe];
    realLe = EQMP[HOL`Equal`SYM[
      csetSpecAll[realOfRatLeThm, {mQ, nQ}]], ratLe];
    HOL`Bool`GEN[mV, HOL`Bool`GEN[nV, HOL`Bool`DISCH[hLeTm, realLe]]]
  ];

existsOutsideOfNotSetBoundedThm =
  Module[{sV, bV, xV, goalTm, hNotBoundTm, hNotBound, body},
    sV = mkVar["S", csetSetTy]; bV = mkVar["B", csetRealTy];
    xV = mkVar["xCsetOutside", csetRealTy];
    goalTm = csetExistsTm[xV, csetOutsideBody[sV, bV, xV]];
    hNotBoundTm = csetNotTm[setBoundedTm[sV]];
    hNotBound = ASSUME[hNotBoundTm];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[goalTm],
      ASSUME[goalTm],
      Module[{hNoGoal, hMemTm, hMem, outTm, hOut, exOut, falseOut,
              notOut, leftTm, rightTm, hLeft, falseLeft, notLeft,
              hRight, falseRight, notRight, loTm, leLoXTm, hNotLeLoX,
              ltXLo, falseLeLoX, leLoX, leXBTm, hNotLeXB, ltBX,
              falseLeXB, leXB, allX, cleanSetBounded, outerEx, betaLo,
              innerEx, exHi, exLo, folded, falseBound},
        hNoGoal = ASSUME[csetNotTm[goalTm]];
        hMemTm = csetSetApp[sV, xV]; hMem = ASSUME[hMemTm];
        outTm = csetOutsideOnly[xV, bV]; hOut = ASSUME[outTm];
        exOut = HOL`Bool`EXISTS[goalTm, xV, HOL`Bool`CONJ[hMem, hOut]];
        falseOut = HOL`Bool`MP[HOL`Bool`NOTELIM[hNoGoal], exOut];
        notOut = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[outTm, falseOut]];
        loTm = csetRealNeg[bV];
        leftTm = csetRealLt[xV, loTm]; rightTm = csetRealLt[bV, xV];
        hLeft = ASSUME[leftTm];
        falseLeft = HOL`Bool`MP[HOL`Bool`NOTELIM[notOut],
          HOL`Bool`DISJ1[hLeft, rightTm]];
        notLeft = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[leftTm, falseLeft]];
        hRight = ASSUME[rightTm];
        falseRight = HOL`Bool`MP[HOL`Bool`NOTELIM[notOut],
          HOL`Bool`DISJ2[hRight, leftTm]];
        notRight = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[rightTm, falseRight]];
        leLoXTm = csetRealLe[loTm, xV];
        hNotLeLoX = ASSUME[csetNotTm[leLoXTm]];
        ltXLo = EQMP[
          csetSpecAll[HOL`Auto`RealArith`realNotLeLtThm, {loTm, xV}],
          hNotLeLoX];
        falseLeLoX = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeft], ltXLo];
        leLoX = HOL`Bool`CCONTR[leLoXTm, falseLeLoX];
        leXBTm = csetRealLe[xV, bV];
        hNotLeXB = ASSUME[csetNotTm[leXBTm]];
        ltBX = EQMP[
          csetSpecAll[HOL`Auto`RealArith`realNotLeLtThm, {xV, bV}],
          hNotLeXB];
        falseLeXB = HOL`Bool`MP[HOL`Bool`NOTELIM[notRight], ltBX];
        leXB = HOL`Bool`CCONTR[leXBTm, falseLeXB];
        allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hMemTm, HOL`Bool`CONJ[leLoX, leXB]]];
        cleanSetBounded = unfoldSetBounded[sV];
        outerEx = concl[cleanSetBounded][[2]];
        betaLo = HOL`Equal`BETACONV[mkComb[outerEx[[2]], loTm]];
        innerEx = concl[betaLo][[2]];
        exHi = HOL`Bool`EXISTS[innerEx, bV, allX];
        exLo = HOL`Bool`EXISTS[outerEx, loTm, exHi];
        folded = EQMP[HOL`Equal`SYM[cleanSetBounded], exLo];
        falseBound = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotBound], folded];
        HOL`Bool`CCONTR[goalTm, falseBound]
      ]];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[hNotBoundTm, body]]]
  ];

ltAbsOfOutsideThm =
  Module[{xV, bV, outTm, hOut, leftTm, rightTm, goalTm, body},
    xV = mkVar["x", csetRealTy]; bV = mkVar["B", csetRealTy];
    outTm = csetOutsideOnly[xV, bV];
    hOut = ASSUME[outTm];
    leftTm = csetRealLt[xV, csetRealNeg[bV]];
    rightTm = csetRealLt[bV, xV];
    goalTm = csetRealLt[bV, csetRealAbs[xV]];
    body = HOL`Bool`DISJCASES[hOut,
      Module[{hLeft, targetTm, leNegXBTm, hLeNegXB, leNeg, leNegX,
              notLeNegBX, falseLe, notLe, bLtNegX, negLeAbs},
        hLeft = ASSUME[leftTm];
        targetTm = csetRealLt[bV, csetRealNeg[xV]];
        leNegXBTm = csetRealLe[csetRealNeg[xV], bV];
        hLeNegXB = ASSUME[leNegXBTm];
        leNeg = HOL`Bool`MP[
          csetSpecAll[realLeNegThm, {csetRealNeg[xV], bV}], hLeNegXB];
        leNegX = EQMP[csetRealLeCong[REFL[csetRealNeg[bV]],
          HOL`Bool`SPEC[xV, realNegNegThm]], leNeg];
        notLeNegBX = EQMP[
          csetSpecAll[realLtNotLeThm, {xV, csetRealNeg[bV]}], hLeft];
        falseLe = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeNegBX], leNegX];
        notLe = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[leNegXBTm, falseLe]];
        bLtNegX = EQMP[HOL`Equal`SYM[
          csetSpecAll[realLtNotLeThm, {bV, csetRealNeg[xV]}]], notLe];
        negLeAbs = HOL`Bool`SPEC[xV, realNegLeAbsThm];
        HOL`Bool`MP[HOL`Bool`MP[
          csetSpecAll[realLtLeTransThm,
            {bV, csetRealNeg[xV], csetRealAbs[xV]}], bLtNegX], negLeAbs]
      ],
      Module[{hRight, xLeAbs},
        hRight = ASSUME[rightTm];
        xLeAbs = HOL`Bool`SPEC[xV, realLeAbsSelfThm];
        HOL`Bool`MP[HOL`Bool`MP[
          csetSpecAll[realLtLeTransThm,
            {bV, xV, csetRealAbs[xV]}], hRight], xLeAbs]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[outTm, body]]]
  ];

unboundedEscapePointDefThm =
  Module[{sV, nV},
    sV = mkVar["S", csetSetTy]; nV = mkVar["n", csetNumTy];
    newDefinition[mkEq[mkVar["unboundedEscapePoint", tyFun[csetSetTy, csetSeqTy]],
      mkAbs[sV, mkAbs[nV, csetUnboundedEscapeSelect[sV, nV]]]]]
  ];

unboundedEscapePointConst[] :=
  mkConst["unboundedEscapePoint", tyFun[csetSetTy, csetSeqTy]];
unboundedEscapePointTm[sT_] := mkComb[unboundedEscapePointConst[], sT];
unfoldUnboundedEscapePoint[sT_] :=
  csetBetaClean[csetApplyDef[unboundedEscapePointDefThm, {sT}]];

unboundedEscapePointMemThm =
  Module[{sV, nV, hNotTm, hNot, threshold, predLam, exOutside, sat,
          memAtSelect, appEq, memEq, memAtApp, allN},
    sV = mkVar["S", csetSetTy]; nV = mkVar["n", csetNumTy];
    hNotTm = csetNotTm[setBoundedTm[sV]]; hNot = ASSUME[hNotTm];
    threshold = csetEscapeThreshold[nV];
    predLam = csetUnboundedEscapePred[sV, nV];
    exOutside = HOL`Bool`MP[
      csetSpecAll[existsOutsideOfNotSetBoundedThm, {sV, threshold}], hNot];
    sat = csetBetaClean[HOL`Stdlib`Num`selectOfExists[predLam, exOutside]];
    memAtSelect = HOL`Bool`CONJUNCT1[sat];
    appEq = csetUnboundedEscapePointAppEq[sV, nV];
    memEq = HOL`Equal`APTERM[sV, HOL`Equal`SYM[appEq]];
    memAtApp = EQMP[memEq, memAtSelect];
    allN = HOL`Bool`GEN[nV, memAtApp];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hNotTm, allN]]
  ];

unboundedEscapePointOutsideThm =
  Module[{sV, nV, hNotTm, hNot, threshold, predLam, exOutside, sat,
          outAtSelect, appEq, xW, outLam, outEq, outAtApp, allN},
    sV = mkVar["S", csetSetTy]; nV = mkVar["n", csetNumTy];
    hNotTm = csetNotTm[setBoundedTm[sV]]; hNot = ASSUME[hNotTm];
    threshold = csetEscapeThreshold[nV];
    predLam = csetUnboundedEscapePred[sV, nV];
    exOutside = HOL`Bool`MP[
      csetSpecAll[existsOutsideOfNotSetBoundedThm, {sV, threshold}], hNot];
    sat = csetBetaClean[HOL`Stdlib`Num`selectOfExists[predLam, exOutside]];
    outAtSelect = HOL`Bool`CONJUNCT2[sat];
    appEq = csetUnboundedEscapePointAppEq[sV, nV];
    xW = mkVar["xCsetOutRewrite", csetRealTy];
    outLam = mkAbs[xW, csetOutsideOnly[xW, threshold]];
    outEq = csetBetaClean[HOL`Equal`APTERM[outLam, HOL`Equal`SYM[appEq]]];
    outAtApp = EQMP[outEq, outAtSelect];
    allN = HOL`Bool`GEN[nV, outAtApp];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hNotTm, allN]]
  ];

boundedOfSequentiallyCompactThm =
  Module[{sV, hSCTm, hSC, boundTm, body},
    sV = mkVar["S", csetSetTy];
    hSCTm = isSequentiallyCompactTm[sV]; hSC = ASSUME[hSCTm];
    boundTm = setBoundedTm[sV];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[boundTm],
      ASSUME[boundTm],
      Module[{hNotBoundTm, hNotBound, uTm, hAllU, openSC, seqEx, lW,
              hLBodyTm, hLBody, hHas, openHas, phiW, subSeq, hPhiBodyTm,
              hPhiBody, hIdx, hTend, evBounded, exB, bW, hBBodyTm, hBBody,
              hEv, boundPred, exN, nW, hAllCloseTm, hAllClose, mW, archEx,
              hArchTm, hArch, kTm, phiK, hNK, hMK, hKPhi, kVar, pVar,
              hMPhiStep, hMPhi, hNatRealLe, hBThreshold, hOut, hAbs,
              hBAbs, hCloseRaw, hClose, subEq, hCloseU, hLoop, hNoLoop,
              falseTh, chooseM, chooseN, chooseB, choosePhi, chooseL},
        hNotBoundTm = csetNotTm[boundTm]; hNotBound = ASSUME[hNotBoundTm];
        uTm = unboundedEscapePointTm[sV];
        hAllU = HOL`Bool`MP[HOL`Bool`SPEC[sV, unboundedEscapePointMemThm],
          hNotBound];
        openSC = EQMP[unfoldIsSequentiallyCompact[sV], hSC];
        seqEx = HOL`Bool`MP[HOL`Bool`SPEC[uTm, openSC], hAllU];
        lW = mkVar["lCsetBounded", csetRealTy];
        hLBodyTm = csetConjTm[csetSetApp[sV, lW],
          hasConvergentSubseqTm[uTm, lW]];
        hLBody = ASSUME[hLBodyTm];
        hHas = HOL`Bool`CONJUNCT2[hLBody];
        openHas = EQMP[unfoldHasConvergentSubseq[uTm, lW], hHas];
        phiW = mkVar["phiCsetBounded", csetNumFunTy];
        subSeq = subsequenceTm[uTm, phiW];
        hPhiBodyTm = csetConjTm[subseqIndexTm[phiW], tendstoTm[subSeq, lW]];
        hPhiBody = ASSUME[hPhiBodyTm];
        hIdx = HOL`Bool`CONJUNCT1[hPhiBody];
        hTend = HOL`Bool`CONJUNCT2[hPhiBody];
        evBounded = HOL`Bool`MP[
          csetSpecAll[seqTendstoEventuallyBoundedThm, {subSeq, lW}], hTend];
        exB = csetBetaClean[EQMP[unfoldEventuallyBounded[subSeq], evBounded]];
        bW = mkVar["BCsetBounded", csetRealTy];
        hBBodyTm = concl[HOL`Equal`BETACONV[mkComb[concl[exB][[2]], bW]]][[2]];
        hBBody = ASSUME[hBBodyTm];
        hEv = HOL`Bool`CONJUNCT2[hBBody];
        boundPred = concl[hEv][[2]];
        exN = csetBetaClean[EQMP[unfoldEventually[boundPred], hEv]];
        nW = mkVar["NCsetBounded", csetNumTy];
        hAllCloseTm = concl[HOL`Equal`BETACONV[mkComb[concl[exN][[2]], nW]]][[2]];
        hAllClose = ASSUME[hAllCloseTm];
        archEx = HOL`Bool`SPEC[bW, realArchThm];
        mW = mkVar["mCsetBounded", csetNumTy];
        hArchTm = csetRealLt[bW, csetRnumNat[mW]];
        hArch = ASSUME[hArchTm];
        kTm = csetNatAdd[nW, mW];
        phiK = csetSeqApp[phiW, kTm];
        hNK = csetSpecAll[HOL`Auto`Arith`arithProve[
          csetForallList[{nW, mW}, csetNatLe[nW, csetNatAdd[nW, mW]]]],
          {nW, mW}];
        hMK = csetSpecAll[HOL`Auto`Arith`arithProve[
          csetForallList[{nW, mW}, csetNatLe[mW, csetNatAdd[nW, mW]]]],
          {nW, mW}];
        hKPhi = HOL`Bool`SPEC[kTm, HOL`Bool`MP[
          HOL`Bool`SPEC[phiW, subseqIndexGeSelfThm], hIdx]];
        kVar = mkVar["KCsetBounded", csetNumTy];
        pVar = mkVar["pCsetBounded", csetNumTy];
        hMPhiStep = csetSpecAll[HOL`Auto`Arith`arithProve[
          csetForallList[{mW, kVar, pVar},
            csetImpTm[csetNatLe[mW, kVar],
              csetImpTm[csetNatLe[kVar, pVar],
                csetNatLe[mW, csetSucNum[pVar]]]]]], {mW, kTm, phiK}];
        hMPhi = HOL`Bool`MP[HOL`Bool`MP[hMPhiStep, hMK], hKPhi];
        hNatRealLe = HOL`Bool`MP[
          csetSpecAll[natRealLeThm, {mW, csetSucNum[phiK]}], hMPhi];
        hBThreshold = HOL`Bool`MP[HOL`Bool`MP[
          csetSpecAll[realLtLeTransThm,
            {bW, csetRnumNat[mW], csetEscapeThreshold[phiK]}],
          hArch], hNatRealLe];
        hOut = HOL`Bool`SPEC[phiK, HOL`Bool`MP[
          HOL`Bool`SPEC[sV, unboundedEscapePointOutsideThm], hNotBound]];
        hAbs = HOL`Bool`MP[
          csetSpecAll[ltAbsOfOutsideThm,
            {csetSeqApp[uTm, phiK], csetEscapeThreshold[phiK]}], hOut];
        hBAbs = HOL`Bool`MP[HOL`Bool`MP[
          csetSpecAll[realLtTransThm,
            {bW, csetEscapeThreshold[phiK],
              csetRealAbs[csetSeqApp[uTm, phiK]]}], hBThreshold], hAbs];
        hCloseRaw = HOL`Bool`MP[HOL`Bool`SPEC[kTm, hAllClose], hNK];
        hClose = csetBetaClean[hCloseRaw];
        subEq = csetSubsequenceAppEq[uTm, phiW, kTm];
        hCloseU = EQMP[csetRealLtCong[HOL`Equal`APTERM[realAbsConst[], subEq],
          REFL[bW]], hClose];
        hLoop = HOL`Bool`MP[HOL`Bool`MP[
          csetSpecAll[realLtTransThm,
            {bW, csetRealAbs[csetSeqApp[uTm, phiK]], bW}], hBAbs], hCloseU];
        hNoLoop = HOL`Bool`SPEC[bW, HOL`Auto`RealArith`realLtIrreflThm];
        falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[hNoLoop], hLoop];
        chooseM = HOL`Bool`CHOOSE[mW, archEx, falseTh];
        chooseN = HOL`Bool`CHOOSE[nW, exN, chooseM];
        chooseB = HOL`Bool`CHOOSE[bW, exB, chooseN];
        choosePhi = HOL`Bool`CHOOSE[phiW, openHas, chooseB];
        chooseL = HOL`Bool`CHOOSE[lW, seqEx, choosePhi];
        HOL`Bool`CONTR[boundTm, chooseL]
      ]];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hSCTm, body]]
  ];

End[];
EndPackage[];
