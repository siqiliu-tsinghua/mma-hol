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
seqTendstoSubsequenceThm::usage = "seqTendstoSubsequenceThm - |- forall u phi l. subseqIndex phi ==> tendsto u l ==> tendsto (subsequence u phi) l.";
invSuccRadiusDefThm::usage = "invSuccRadiusDefThm - |- invSuccRadius = (lambda n. realInv (&R(&Q(&Z(SUC n))))).";
invSuccRadiusConst::usage = "invSuccRadiusConst[] - invSuccRadius : num -> real.";
invSuccRadiusTm::usage = "invSuccRadiusTm[n] - builds invSuccRadius n.";
unfoldInvSuccRadius::usage = "unfoldInvSuccRadius[n] - proves the beta-reduced invSuccRadius definition at n.";
natSuccPosThm::usage = "natSuccPosThm - |- forall n. realLt 0 (&R(&Q(&Z(SUC n)))).";
invSuccRadiusPosThm::usage = "invSuccRadiusPosThm - |- forall n. realLt 0 (invSuccRadius n).";
invSuccRadiusAntitoneThm::usage = "invSuccRadiusAntitoneThm - |- forall m n. m <= n ==> realLe (invSuccRadius n) (invSuccRadius m).";
invSuccRadiusTendstoZeroThm::usage = "invSuccRadiusTendstoZeroThm - |- tendsto invSuccRadius 0.";
existsMemIntervalOfNoComplNeighborhoodThm::usage = "existsMemIntervalOfNoComplNeighborhoodThm - |- forall S x left right. ~(exists a b. realLt a x /\\ realLt x b /\\ forall y. openInterval a b y ==> compl S y) ==> realLt left x ==> realLt x right ==> exists y. S y /\\ openInterval left right y.";
nearClosedPointDefThm::usage = "nearClosedPointDefThm - |- nearClosedPoint = (lambda S x n. @y. S y /\\ openInterval (x + --(invSuccRadius n)) (x + invSuccRadius n) y).";
nearClosedPointConst::usage = "nearClosedPointConst[] - nearClosedPoint : (real -> bool) -> real -> num -> real.";
nearClosedPointTm::usage = "nearClosedPointTm[S, x] - builds nearClosedPoint S x.";
unfoldNearClosedPoint::usage = "unfoldNearClosedPoint[S, x] - proves the beta-reduced nearClosedPoint definition at S and x.";
nearClosedPointMemThm::usage = "nearClosedPointMemThm - |- forall S x. ~(exists a b. realLt a x /\\ realLt x b /\\ forall y. openInterval a b y ==> compl S y) ==> forall n. S (nearClosedPoint S x n).";
nearClosedPointIntervalThm::usage = "nearClosedPointIntervalThm - |- forall S x. ~(exists a b. realLt a x /\\ realLt x b /\\ forall y. openInterval a b y ==> compl S y) ==> forall n. openInterval (x + --(invSuccRadius n)) (x + invSuccRadius n) (nearClosedPoint S x n).";
nearClosedPointTendstoThm::usage = "nearClosedPointTendstoThm - |- forall S x. ~(exists a b. realLt a x /\\ realLt x b /\\ forall y. openInterval a b y ==> compl S y) ==> tendsto (nearClosedPoint S x) x.";
closedOfSequentiallyCompactThm::usage = "closedOfSequentiallyCompactThm - |- forall S. isSequentiallyCompact S ==> isClosed S.";
sequentialCompactIffClosedBoundedThm::usage = "sequentialCompactIffClosedBoundedThm - |- forall S. isSequentiallyCompact S = (isClosed S /\\ setBounded S).";
setCoversDefThm::usage = "setCoversDefThm - |- setCovers = (lambda C S. forall x. S x ==> exists V. C V /\\ V x).";
setCoversConst::usage = "setCoversConst[] - setCovers : ((real -> bool) -> bool) -> (real -> bool) -> bool.";
setCoversTm::usage = "setCoversTm[C, S] - builds setCovers C S.";
unfoldSetCovers::usage = "unfoldSetCovers[C, S] - proves the beta-reduced setCovers definition at C and S.";
setListSubcoverDefThm::usage = "setListSubcoverDefThm - |- setListSubcover = (lambda C S Vs. (forall V. MEM V Vs ==> C V) /\\ forall x. S x ==> exists V. MEM V Vs /\\ V x).";
setListSubcoverConst::usage = "setListSubcoverConst[] - setListSubcover : ((real -> bool) -> bool) -> (real -> bool) -> (real -> bool) list -> bool.";
setListSubcoverTm::usage = "setListSubcoverTm[C, S, Vs] - builds setListSubcover C S Vs.";
unfoldSetListSubcover::usage = "unfoldSetListSubcover[C, S, Vs] - proves the beta-reduced setListSubcover definition at C, S, and Vs.";
setFiniteSubcoverDefThm::usage = "setFiniteSubcoverDefThm - |- setFiniteSubcover = (lambda C S. exists Vs. setListSubcover C S Vs).";
setFiniteSubcoverConst::usage = "setFiniteSubcoverConst[] - setFiniteSubcover : ((real -> bool) -> bool) -> (real -> bool) -> bool.";
setFiniteSubcoverTm::usage = "setFiniteSubcoverTm[C, S] - builds setFiniteSubcover C S.";
unfoldSetFiniteSubcover::usage = "unfoldSetFiniteSubcover[C, S] - proves the beta-reduced setFiniteSubcover definition at C and S.";
isCompactDefThm::usage = "isCompactDefThm - |- isCompact = (lambda S. forall C. (forall V. C V ==> isOpen V) ==> setCovers C S ==> setFiniteSubcover C S).";
isCompactConst::usage = "isCompactConst[] - isCompact : (real -> bool) -> bool.";
isCompactTm::usage = "isCompactTm[S] - builds isCompact S.";
unfoldIsCompact::usage = "unfoldIsCompact[S] - proves the beta-reduced isCompact definition at S.";
isOpenEmptyThm::usage = "isOpenEmptyThm - |- isOpen (lambda x. F).";
openIntervalIsOpenThm::usage = "openIntervalIsOpenThm - |- forall l r. isOpen (openInterval l r).";
memFilterThm::usage = "memFilterThm - |- forall p x l. MEM x (FILTER p l) = (p x /\\ MEM x l) (at element type real->bool).";
closedIntervalSetCompactThm::usage = "closedIntervalSetCompactThm - |- forall a b C. realLe a b ==> (forall V. C V ==> isOpen V) ==> setCovers C (closedInterval a b) ==> setFiniteSubcover C (closedInterval a b).";
compactOfClosedBoundedThm::usage = "compactOfClosedBoundedThm - |- forall S. isClosed S ==> setBounded S ==> isCompact S.";
centerCoverDefThm::usage = "centerCoverDefThm - |- centerCover = (lambda V. exists c. V = openInterval (c + --1) (c + 1)).";
centerCoverConst::usage = "centerCoverConst[] - centerCover : ((real -> bool) -> bool).";
centerCoverTm::usage = "centerCoverTm[] - builds centerCover.";
centerCoverMemThm::usage = "centerCoverMemThm - |- forall V. centerCover V = (exists c. V = openInterval (c + --1) (c + 1)).";
centerCoverOpenThm::usage = "centerCoverOpenThm - |- forall V. centerCover V ==> isOpen V.";
centerCoverCoversThm::usage = "centerCoverCoversThm - |- forall S. setCovers centerCover S.";
boundedOfFiniteIntervalCoverThm::usage = "boundedOfFiniteIntervalCoverThm - |- forall Vs. (forall V. MEM V Vs ==> centerCover V) ==> exists lo hi. forall x. (exists V. MEM V Vs /\\ V x) ==> realLe lo x /\\ realLe x hi.";
boundedOfCompactThm::usage = "boundedOfCompactThm - |- forall S. isCompact S ==> setBounded S.";

Begin["`Private`"];

csetRealTy = mkType["real", {}];
csetNumTy = mkType["num", {}];
csetSeqTy = tyFun[csetNumTy, csetRealTy];
csetNumFunTy = tyFun[csetNumTy, csetNumTy];
csetSetTy = tyFun[csetRealTy, boolTy];
csetSetOfSetsTy = tyFun[csetSetTy, boolTy];
csetSetListTy = HOL`Stdlib`List`listTy[csetSetTy];
isSequentiallyCompactTy = tyFun[csetSetTy, boolTy];
setCoversTy = tyFun[csetSetOfSetsTy, tyFun[csetSetTy, boolTy]];
setListSubcoverTy = tyFun[csetSetOfSetsTy,
  tyFun[csetSetTy, tyFun[csetSetListTy, boolTy]]];
isCompactTy = tyFun[csetSetTy, boolTy];

csetAndConst[] := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
csetImpConst[] := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
csetConjTm[pT_, qT_] := mkComb[mkComb[csetAndConst[], pT], qT];
csetImpTm[pT_, qT_] := mkComb[mkComb[csetImpConst[], pT], qT];
csetForallTm[vT_, bodyT_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];
csetExistsTm[vT_, bodyT_] :=
  mkComb[mkConst["∃", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];

csetSetApp[sT_, xT_] := mkComb[sT, xT];
csetSetMem[cT_, vT_] := mkComb[cT, vT];
csetSetAppV[vT_, xT_] := mkComb[vT, xT];
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

csetNatLt[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], aT], bT];
csetRealInv[xT_] := mkComb[realInvConst[], xT];
csetRealMul[aT_, bT_] := realMulTm[aT, bT];
csetOneReal[] := realOfRatTm[oneQ[]];

csetRealAddCongLeft[eq_, cT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], eq], REFL[cT]];
csetRealMulCongLeft[eq_, cT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realMulConst[], eq], REFL[cT]];
csetRealMulCongRight[cT_, eq_] :=
  HOL`Equal`APTERM[mkComb[realMulConst[], cT], eq];
csetRealAbsCong[eq_] := HOL`Equal`APTERM[realAbsConst[], eq];

csetSeqLimitAtom[aT_, lT_, epsT_, nT_] :=
  csetRealLt[csetRealAbs[realAddTm[csetSeqApp[aT, nT], realNegTm[lT]]], epsT];

csetLtImpLeRule[ltTh_] :=
  Module[{aT, bT},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]];
    HOL`Bool`MP[csetSpecAll[realLtImpLeThm, {aT, bT}], ltTh]
  ];

csetMulLeRightRule[leTh_, cNonneg_] :=
  Module[{aT, bT, cT, mono, leftComm, rightComm},
    aT = concl[leTh][[1, 2]]; bT = concl[leTh][[2]]; cT = concl[cNonneg][[2]];
    mono = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[realLeMulMonoThm, {aT, bT, cT}], cNonneg], leTh];
    leftComm = csetSpecAll[realMulCommThm, {cT, aT}];
    rightComm = csetSpecAll[realMulCommThm, {cT, bT}];
    EQMP[csetRealLeCong[leftComm, rightComm], mono]
  ];

csetMulLtRightRule[ltTh_, cPos_] :=
  Module[{aT, bT, cT, mono, leftComm, rightComm},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]]; cT = concl[cPos][[2]];
    mono = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[realLtMulMonoThm, {aT, bT, cT}], cPos], ltTh];
    leftComm = csetSpecAll[realMulCommThm, {cT, aT}];
    rightComm = csetSpecAll[realMulCommThm, {cT, bT}];
    EQMP[csetRealLtCong[leftComm, rightComm], mono]
  ];

csetMulOneLeft[xT_] :=
  TRANS[csetSpecAll[realMulCommThm, {csetOneReal[], xT}],
    HOL`Bool`SPEC[xT, realMulOneThm]];

csetAddNegZeroThm =
  Module[{zV},
    zV = mkVar["zCsetDropZero", csetRealTy];
    HOL`Auto`RealArith`realArithProve[
      csetForallTm[zV, mkEq[realAddTm[zV, realNegTm[zeroRealTm[]]], zV]]]
  ];

csetNatZeroLtSuccThm =
  Module[{nV},
    nV = mkVar["nCsetZeroLtSucc", csetNumTy];
    HOL`Auto`Arith`arithProve[
      csetForallTm[nV, csetNatLt[zeroN[], csetSucNum[nV]]]]
  ];

csetNatLeTransThm =
  Module[{aV, bV, cV},
    aV = mkVar["aCsetNatLeTrans", csetNumTy];
    bV = mkVar["bCsetNatLeTrans", csetNumTy];
    cV = mkVar["cCsetNatLeTrans", csetNumTy];
    HOL`Auto`Arith`arithProve[csetForallList[{aV, bV, cV},
      csetImpTm[csetNatLe[aV, bV],
        csetImpTm[csetNatLe[bV, cV], csetNatLe[aV, cV]]]]]
  ];

csetNatLeToLeSuccThm =
  Module[{mV, nV},
    mV = mkVar["mCsetLeSucc", csetNumTy];
    nV = mkVar["nCsetLeSucc", csetNumTy];
    HOL`Auto`Arith`arithProve[csetForallList[{mV, nV},
      csetImpTm[csetNatLe[mV, nV], csetNatLe[mV, csetSucNum[nV]]]]]
  ];

csetNatSuccLeMonoThm =
  Module[{mV, nV},
    mV = mkVar["mCsetSuccLe", csetNumTy];
    nV = mkVar["nCsetSuccLe", csetNumTy];
    HOL`Auto`Arith`arithProve[csetForallList[{mV, nV},
      csetImpTm[csetNatLe[mV, nV], csetNatLe[csetSucNum[mV], csetSucNum[nV]]]]]
  ];

seqTendstoSubsequenceThm =
  Module[{uV, phiV, lV, eV, nV, n0W, pW, hIdxTm, hIdx, hTendTm,
          hTend, subSeq, openTend, hEpsTm, hEps, exN, hAllTm, hAll,
          hLeTm, hLe, phiN, hNLePhiStep, hNLePhi, closeRaw, subEq,
          argEq, absEq, closeSub, allN, exGoal, chosenN, epsBody, folded},
    uV = mkVar["u", csetSeqTy]; phiV = mkVar["phi", csetNumFunTy];
    lV = mkVar["l", csetRealTy]; eV = mkVar["eCsetSubseq", csetRealTy];
    nV = mkVar["nCsetSubseq", csetNumTy]; n0W = mkVar["NCsetSubseq", csetNumTy];
    pW = mkVar["pCsetSubseq", csetNumTy];
    hIdxTm = subseqIndexTm[phiV]; hIdx = ASSUME[hIdxTm];
    hTendTm = tendstoTm[uV, lV]; hTend = ASSUME[hTendTm];
    subSeq = subsequenceTm[uV, phiV];
    openTend = EQMP[unfoldTendsto[uV, lV], hTend];
    hEpsTm = csetRealLt[zeroRealTm[], eV]; hEps = ASSUME[hEpsTm];
    exN = HOL`Bool`MP[HOL`Bool`SPEC[eV, openTend], hEps];
    hAllTm = concl[HOL`Equal`BETACONV[mkComb[concl[exN][[2]], n0W]]][[2]];
    hAll = ASSUME[hAllTm];
    hLeTm = csetNatLe[n0W, nV]; hLe = ASSUME[hLeTm];
    phiN = csetSeqApp[phiV, nV];
    hNLePhiStep = csetSpecAll[csetNatLeTransThm, {n0W, nV, phiN}];
    hNLePhi = HOL`Bool`MP[HOL`Bool`MP[hNLePhiStep, hLe],
      HOL`Bool`SPEC[nV, HOL`Bool`MP[HOL`Bool`SPEC[phiV, subseqIndexGeSelfThm], hIdx]]];
    closeRaw = HOL`Bool`MP[HOL`Bool`SPEC[phiN, hAll], hNLePhi];
    subEq = csetSubsequenceAppEq[uV, phiV, nV];
    argEq = csetRealAddCongLeft[HOL`Equal`SYM[subEq], realNegTm[lV]];
    absEq = csetRealAbsCong[argEq];
    closeSub = EQMP[csetRealLtCong[absEq, REFL[eV]], closeRaw];
    allN = HOL`Bool`GEN[nV, HOL`Bool`DISCH[hLeTm, closeSub]];
    exGoal = HOL`Bool`EXISTS[csetExistsTm[n0W,
      csetForallTm[nV, csetImpTm[csetNatLe[n0W, nV],
        csetSeqLimitAtom[subSeq, lV, eV, nV]]]], n0W, allN];
    chosenN = HOL`Bool`CHOOSE[n0W, exN, exGoal];
    epsBody = HOL`Bool`GEN[eV, HOL`Bool`DISCH[hEpsTm, chosenN]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[subSeq, lV]], epsBody];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[phiV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[hIdxTm, HOL`Bool`DISCH[hTendTm, folded]]]]]
  ];

invSuccRadiusDefThm =
  Module[{nV},
    nV = mkVar["n", csetNumTy];
    newDefinition[mkEq[mkVar["invSuccRadius", csetSeqTy],
      mkAbs[nV, csetRealInv[csetRnumNat[csetSucNum[nV]]]]]]
  ];

invSuccRadiusConst[] := mkConst["invSuccRadius", csetSeqTy];
invSuccRadiusTm[nT_] := csetSeqApp[invSuccRadiusConst[], nT];
unfoldInvSuccRadius[nT_] :=
  Module[{app},
    app = HOL`Equal`APTHM[invSuccRadiusDefThm, nT];
    TRANS[app, HOL`Equal`BETACONV[concl[app][[2]]]]
  ];

natSuccPosThm =
  Module[{nV, sucN, intLtEq, ratLtEq, realLtEq, natLt, intLt, ratLt,
          realLt},
    nV = mkVar["n", csetNumTy]; sucN = csetSucNum[nV];
    intLtEq = csetSpecAll[intOfNumLtThm, {zeroN[], sucN}];
    ratLtEq = csetSpecAll[ratOfIntLtThm, {intOfNumTm[zeroN[]], intOfNumTm[sucN]}];
    realLtEq = csetSpecAll[realOfRatLtThm,
      {ratOfIntTm[intOfNumTm[zeroN[]]], ratOfIntTm[intOfNumTm[sucN]]}];
    natLt = HOL`Bool`SPEC[nV, csetNatZeroLtSuccThm];
    intLt = EQMP[HOL`Equal`SYM[intLtEq], natLt];
    ratLt = EQMP[HOL`Equal`SYM[ratLtEq], intLt];
    realLt = EQMP[HOL`Equal`SYM[realLtEq], ratLt];
    HOL`Bool`GEN[nV, realLt]
  ];

invSuccRadiusPosThm =
  Module[{nV, mT, posM, invPos, unfoldN, body},
    nV = mkVar["n", csetNumTy]; mT = csetRnumNat[csetSucNum[nV]];
    posM = HOL`Bool`SPEC[nV, natSuccPosThm];
    invPos = HOL`Bool`MP[HOL`Bool`SPEC[mT, seqRealInvPositiveThm], posM];
    unfoldN = unfoldInvSuccRadius[nV];
    body = EQMP[csetRealLtCong[REFL[zeroRealTm[]], HOL`Equal`SYM[unfoldN]], invPos];
    HOL`Bool`GEN[nV, body]
  ];

invSuccRadiusAntitoneThm =
  Module[{mV, nV, hLeTm, hLe, aT, bT, invA, invB, hSucLe, hAB, aPos,
          bPos, aNe, bNe, invAPos, invBPos, invANonneg, invBNonneg,
          leAInvBInvB, bInv, leAInvBOne, leScaledRaw, lhsAssoc,
          invAAToOne, lhsPair, lhsEq, rhsEq, leInvBInvA, unfoldM,
          unfoldN, body},
    mV = mkVar["m", csetNumTy]; nV = mkVar["n", csetNumTy];
    hLeTm = csetNatLe[mV, nV]; hLe = ASSUME[hLeTm];
    aT = csetRnumNat[csetSucNum[mV]]; bT = csetRnumNat[csetSucNum[nV]];
    invA = csetRealInv[aT]; invB = csetRealInv[bT];
    hSucLe = HOL`Bool`MP[csetSpecAll[csetNatSuccLeMonoThm, {mV, nV}], hLe];
    hAB = HOL`Bool`MP[csetSpecAll[natRealLeThm,
      {csetSucNum[mV], csetSucNum[nV]}], hSucLe];
    aPos = HOL`Bool`SPEC[mV, natSuccPosThm];
    bPos = HOL`Bool`SPEC[nV, natSuccPosThm];
    aNe = HOL`Bool`MP[HOL`Bool`SPEC[aT, seqArithPosNeZeroThm], aPos];
    bNe = HOL`Bool`MP[HOL`Bool`SPEC[bT, seqArithPosNeZeroThm], bPos];
    invAPos = HOL`Bool`MP[HOL`Bool`SPEC[aT, seqRealInvPositiveThm], aPos];
    invBPos = HOL`Bool`MP[HOL`Bool`SPEC[bT, seqRealInvPositiveThm], bPos];
    invANonneg = csetLtImpLeRule[invAPos];
    invBNonneg = csetLtImpLeRule[invBPos];
    leAInvBInvB = csetMulLeRightRule[hAB, invBNonneg];
    bInv = HOL`Bool`MP[HOL`Bool`SPEC[bT, realMulInvThm], bNe];
    leAInvBOne = EQMP[csetRealLeCong[REFL[csetRealMul[aT, invB]], bInv],
      leAInvBInvB];
    leScaledRaw = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[realLeMulMonoThm,
        {csetRealMul[aT, invB], csetOneReal[], invA}], invANonneg], leAInvBOne];
    lhsAssoc = HOL`Equal`SYM[csetSpecAll[realMulAssocThm, {invA, aT, invB}]];
    invAAToOne = TRANS[csetSpecAll[realMulCommThm, {invA, aT}],
      HOL`Bool`MP[HOL`Bool`SPEC[aT, realMulInvThm], aNe]];
    lhsPair = csetRealMulCongLeft[invAAToOne, invB];
    lhsEq = TRANS[lhsAssoc, TRANS[lhsPair, csetMulOneLeft[invB]]];
    rhsEq = HOL`Bool`SPEC[invA, realMulOneThm];
    leInvBInvA = EQMP[csetRealLeCong[lhsEq, rhsEq], leScaledRaw];
    unfoldM = unfoldInvSuccRadius[mV];
    unfoldN = unfoldInvSuccRadius[nV];
    body = EQMP[csetRealLeCong[HOL`Equal`SYM[unfoldN], HOL`Equal`SYM[unfoldM]],
      leInvBInvA];
    HOL`Bool`GEN[mV, HOL`Bool`GEN[nV, HOL`Bool`DISCH[hLeTm, body]]]
  ];

invSuccRadiusTendstoZeroThm =
  Module[{eV, mW, nV, hEpsTm, hEps, archEx, hArchTm, hArch, hLeTm,
          hLe, mLeSucN, mRealLe, bigM, invBigM, bigMPos, bigMNe,
          epsNe, invE, hInvELtM, mulLt, oneLtEM, invBigMPos,
          finalLtRaw, leftEq, rhsAssoc, rhsInv, rhsCong, rhsEq,
          invBigMLtE, invNonneg, absInv, unfoldN, dropZero, argEq,
          absEq, closeN, allN, exN, chosenM, epsBody, folded},
    eV = mkVar["eCsetInvSucc", csetRealTy]; mW = mkVar["mCsetInvSucc", csetNumTy];
    nV = mkVar["nCsetInvSucc", csetNumTy];
    hEpsTm = csetRealLt[zeroRealTm[], eV]; hEps = ASSUME[hEpsTm];
    invE = csetRealInv[eV];
    archEx = HOL`Bool`SPEC[invE, realArchThm];
    hArchTm = csetRealLt[invE, csetRnumNat[mW]]; hArch = ASSUME[hArchTm];
    hLeTm = csetNatLe[mW, nV]; hLe = ASSUME[hLeTm];
    bigM = csetRnumNat[csetSucNum[nV]]; invBigM = csetRealInv[bigM];
    mLeSucN = HOL`Bool`MP[csetSpecAll[csetNatLeToLeSuccThm, {mW, nV}], hLe];
    mRealLe = HOL`Bool`MP[csetSpecAll[natRealLeThm, {mW, csetSucNum[nV]}],
      mLeSucN];
    hInvELtM = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[realLtLeTransThm, {invE, csetRnumNat[mW], bigM}],
      hArch], mRealLe];
    epsNe = HOL`Bool`MP[HOL`Bool`SPEC[eV, seqArithPosNeZeroThm], hEps];
    bigMPos = HOL`Bool`SPEC[nV, natSuccPosThm];
    bigMNe = HOL`Bool`MP[HOL`Bool`SPEC[bigM, seqArithPosNeZeroThm], bigMPos];
    mulLt = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[realLtMulMonoThm, {invE, bigM, eV}], hEps], hInvELtM];
    oneLtEM = EQMP[csetRealLtCong[
      HOL`Bool`MP[HOL`Bool`SPEC[eV, realMulInvThm], epsNe],
      REFL[csetRealMul[eV, bigM]]], mulLt];
    invBigMPos = HOL`Bool`MP[HOL`Bool`SPEC[bigM, seqRealInvPositiveThm], bigMPos];
    finalLtRaw = csetMulLtRightRule[oneLtEM, invBigMPos];
    leftEq = csetMulOneLeft[invBigM];
    rhsAssoc = csetSpecAll[realMulAssocThm, {eV, bigM, invBigM}];
    rhsInv = HOL`Bool`MP[HOL`Bool`SPEC[bigM, realMulInvThm], bigMNe];
    rhsCong = csetRealMulCongRight[eV, rhsInv];
    rhsEq = TRANS[rhsAssoc, TRANS[rhsCong, HOL`Bool`SPEC[eV, realMulOneThm]]];
    invBigMLtE = EQMP[csetRealLtCong[leftEq, rhsEq], finalLtRaw];
    invNonneg = csetLtImpLeRule[invBigMPos];
    absInv = HOL`Bool`MP[HOL`Bool`SPEC[invBigM, realAbsPosThm], invNonneg];
    unfoldN = unfoldInvSuccRadius[nV];
    dropZero = HOL`Bool`SPEC[invBigM, csetAddNegZeroThm];
    argEq = TRANS[csetRealAddCongLeft[unfoldN, realNegTm[zeroRealTm[]]], dropZero];
    absEq = TRANS[csetRealAbsCong[argEq], absInv];
    closeN = EQMP[csetRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], invBigMLtE];
    allN = HOL`Bool`GEN[nV, HOL`Bool`DISCH[hLeTm, closeN]];
    exN = HOL`Bool`EXISTS[csetExistsTm[mW,
      csetForallTm[nV, csetImpTm[csetNatLe[mW, nV],
        csetSeqLimitAtom[invSuccRadiusConst[], zeroRealTm[], eV, nV]]]], mW, allN];
    chosenM = HOL`Bool`CHOOSE[mW, archEx, exN];
    epsBody = HOL`Bool`GEN[eV, HOL`Bool`DISCH[hEpsTm, chosenM]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[invSuccRadiusConst[], zeroRealTm[]]],
      epsBody];
    folded
  ];

csetRealAdd[aT_, bT_] := realAddTm[aT, bT];

csetNeighGoal[sT_, xT_] :=
  Module[{aV, bV, yV},
    aV = mkVar["aNbhd", csetRealTy];
    bV = mkVar["bNbhd", csetRealTy];
    yV = mkVar["yNbhd", csetRealTy];
    csetExistsTm[aV, csetExistsTm[bV,
      csetConjTm[csetRealLt[aV, xT],
        csetConjTm[csetRealLt[xT, bV],
          csetForallTm[yV, csetImpTm[openIntervalTm[aV, bV, yV],
            csetSetApp[complTm[sT], yV]]]]]]]
  ];

csetNearClosedPointLo[xT_, nT_] :=
  csetRealAdd[xT, csetRealNeg[invSuccRadiusTm[nT]]];
csetNearClosedPointHi[xT_, nT_] :=
  csetRealAdd[xT, invSuccRadiusTm[nT]];
csetNearPred[sT_, xT_, nT_] :=
  Module[{yW, loT, hiT},
    yW = mkVar["yCsetNear", csetRealTy];
    loT = csetNearClosedPointLo[xT, nT];
    hiT = csetNearClosedPointHi[xT, nT];
    mkAbs[yW, csetConjTm[csetSetApp[sT, yW],
      openIntervalTm[loT, hiT, yW]]]
  ];
csetNearClosedPointSelect[sT_, xT_, nT_] :=
  mkComb[csetSelectConst[csetRealTy], csetNearPred[sT, xT, nT]];

csetSubRadiusLtCenterThm =
  Module[{xV, rV},
    xV = mkVar["xCsetSubRadius", csetRealTy];
    rV = mkVar["rCsetSubRadius", csetRealTy];
    HOL`Auto`RealArith`realArithProve[csetForallList[{xV, rV},
      csetImpTm[csetRealLt[zeroRealTm[], rV],
        csetRealLt[csetRealAdd[xV, csetRealNeg[rV]], xV]]]]
  ];

csetCenterLtAddRadiusThm =
  Module[{xV, rV},
    xV = mkVar["xCsetAddRadius", csetRealTy];
    rV = mkVar["rCsetAddRadius", csetRealTy];
    HOL`Auto`RealArith`realArithProve[csetForallList[{xV, rV},
      csetImpTm[csetRealLt[zeroRealTm[], rV],
        csetRealLt[xV, csetRealAdd[xV, rV]]]]]
  ];

existsMemIntervalOfNoComplNeighborhoodThm =
  Module[{sV, xV, leftV, rightV, zV, neighTm, goalTm, hNoTm, hNo,
          hLeftTm, hLeft, hRightTm, hRight, body},
    sV = mkVar["S", csetSetTy]; xV = mkVar["x", csetRealTy];
    leftV = mkVar["left", csetRealTy]; rightV = mkVar["right", csetRealTy];
    zV = mkVar["zNbhd", csetRealTy];
    neighTm = csetNeighGoal[sV, xV];
    goalTm = csetExistsTm[zV, csetConjTm[csetSetApp[sV, zV],
      openIntervalTm[leftV, rightV, zV]]];
    hNoTm = csetNotTm[neighTm]; hNo = ASSUME[hNoTm];
    hLeftTm = csetRealLt[leftV, xV]; hLeft = ASSUME[hLeftTm];
    hRightTm = csetRealLt[xV, rightV]; hRight = ASSUME[hRightTm];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[goalTm],
      ASSUME[goalTm],
      Module[{hNoGoal, hIntTm, hInt, hSzTm, hSz, exGoal, falseGoal,
              notSz, complAtZ, allZ, betaLeft, innerEx, exRight,
              exLeft, falseNeigh},
        hNoGoal = ASSUME[csetNotTm[goalTm]];
        hIntTm = openIntervalTm[leftV, rightV, zV]; hInt = ASSUME[hIntTm];
        hSzTm = csetSetApp[sV, zV]; hSz = ASSUME[hSzTm];
        exGoal = HOL`Bool`EXISTS[goalTm, zV, HOL`Bool`CONJ[hSz, hInt]];
        falseGoal = HOL`Bool`MP[HOL`Bool`NOTELIM[hNoGoal], exGoal];
        notSz = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[hSzTm, falseGoal]];
        complAtZ = EQMP[HOL`Equal`SYM[csetSpecAll[complMemThm, {sV, zV}]], notSz];
        allZ = HOL`Bool`GEN[zV, HOL`Bool`DISCH[hIntTm, complAtZ]];
        betaLeft = HOL`Equal`BETACONV[mkComb[neighTm[[2]], leftV]];
        innerEx = concl[betaLeft][[2]];
        exRight = HOL`Bool`EXISTS[innerEx, rightV,
          HOL`Bool`CONJ[hLeft, HOL`Bool`CONJ[hRight, allZ]]];
        exLeft = HOL`Bool`EXISTS[neighTm, leftV, exRight];
        falseNeigh = HOL`Bool`MP[HOL`Bool`NOTELIM[hNo], exLeft];
        HOL`Bool`CCONTR[goalTm, falseNeigh]
      ]];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[xV, HOL`Bool`GEN[leftV,
      HOL`Bool`GEN[rightV, HOL`Bool`DISCH[hNoTm,
        HOL`Bool`DISCH[hLeftTm, HOL`Bool`DISCH[hRightTm, body]]]]]]]
  ];

nearClosedPointDefThm =
  Module[{sV, xV, nV},
    sV = mkVar["S", csetSetTy]; xV = mkVar["x", csetRealTy];
    nV = mkVar["n", csetNumTy];
    newDefinition[mkEq[mkVar["nearClosedPoint",
      tyFun[csetSetTy, tyFun[csetRealTy, csetSeqTy]]],
      mkAbs[sV, mkAbs[xV, mkAbs[nV,
        csetNearClosedPointSelect[sV, xV, nV]]]]]]
  ];

nearClosedPointConst[] :=
  mkConst["nearClosedPoint", tyFun[csetSetTy, tyFun[csetRealTy, csetSeqTy]]];
nearClosedPointTm[sT_, xT_] := mkComb[mkComb[nearClosedPointConst[], sT], xT];
unfoldNearClosedPoint[sT_, xT_] :=
  csetBetaClean[csetApplyDef[nearClosedPointDefThm, {sT, xT}]];
csetNearClosedPointAppEq[sT_, xT_, nT_] :=
  Module[{unf, app},
    unf = unfoldNearClosedPoint[sT, xT];
    app = HOL`Equal`APTHM[unf, nT];
    csetBetaClean[TRANS[app, HOL`Equal`BETACONV[concl[app][[2]]]]]
  ];

nearClosedPointMemThm =
  Module[{sV, xV, nV, hNoTm, hNo, radiusT, loT, hiT, rPos, loBound,
          hiBound, exMem, predLam, sat, memAtSelect, appEq, memEq,
          memAtApp, allN},
    sV = mkVar["S", csetSetTy]; xV = mkVar["x", csetRealTy];
    nV = mkVar["n", csetNumTy];
    hNoTm = csetNotTm[csetNeighGoal[sV, xV]]; hNo = ASSUME[hNoTm];
    radiusT = invSuccRadiusTm[nV];
    loT = csetNearClosedPointLo[xV, nV];
    hiT = csetNearClosedPointHi[xV, nV];
    rPos = HOL`Bool`SPEC[nV, invSuccRadiusPosThm];
    loBound = HOL`Bool`MP[csetSpecAll[csetSubRadiusLtCenterThm,
      {xV, radiusT}], rPos];
    hiBound = HOL`Bool`MP[csetSpecAll[csetCenterLtAddRadiusThm,
      {xV, radiusT}], rPos];
    exMem = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[existsMemIntervalOfNoComplNeighborhoodThm,
        {sV, xV, loT, hiT}], hNo], loBound], hiBound];
    predLam = csetNearPred[sV, xV, nV];
    sat = csetBetaClean[HOL`Stdlib`Num`selectOfExists[predLam, exMem]];
    memAtSelect = HOL`Bool`CONJUNCT1[sat];
    appEq = csetNearClosedPointAppEq[sV, xV, nV];
    memEq = HOL`Equal`APTERM[sV, HOL`Equal`SYM[appEq]];
    memAtApp = EQMP[memEq, memAtSelect];
    allN = HOL`Bool`GEN[nV, memAtApp];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[xV, HOL`Bool`DISCH[hNoTm, allN]]]
  ];

nearClosedPointIntervalThm =
  Module[{sV, xV, nV, hNoTm, hNo, radiusT, loT, hiT, rPos, loBound,
          hiBound, exMem, predLam, sat, intAtSelect, appEq, wW, intLam,
          intEq, intAtApp, allN},
    sV = mkVar["S", csetSetTy]; xV = mkVar["x", csetRealTy];
    nV = mkVar["n", csetNumTy];
    hNoTm = csetNotTm[csetNeighGoal[sV, xV]]; hNo = ASSUME[hNoTm];
    radiusT = invSuccRadiusTm[nV];
    loT = csetNearClosedPointLo[xV, nV];
    hiT = csetNearClosedPointHi[xV, nV];
    rPos = HOL`Bool`SPEC[nV, invSuccRadiusPosThm];
    loBound = HOL`Bool`MP[csetSpecAll[csetSubRadiusLtCenterThm,
      {xV, radiusT}], rPos];
    hiBound = HOL`Bool`MP[csetSpecAll[csetCenterLtAddRadiusThm,
      {xV, radiusT}], rPos];
    exMem = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[existsMemIntervalOfNoComplNeighborhoodThm,
        {sV, xV, loT, hiT}], hNo], loBound], hiBound];
    predLam = csetNearPred[sV, xV, nV];
    sat = csetBetaClean[HOL`Stdlib`Num`selectOfExists[predLam, exMem]];
    intAtSelect = HOL`Bool`CONJUNCT2[sat];
    appEq = csetNearClosedPointAppEq[sV, xV, nV];
    wW = mkVar["wCsetNearRewrite", csetRealTy];
    intLam = mkAbs[wW, openIntervalTm[loT, hiT, wW]];
    intEq = csetBetaClean[HOL`Equal`APTERM[intLam, HOL`Equal`SYM[appEq]]];
    intAtApp = EQMP[intEq, intAtSelect];
    allN = HOL`Bool`GEN[nV, intAtApp];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[xV, HOL`Bool`DISCH[hNoTm, allN]]]
  ];

nearClosedPointTendstoThm =
  Module[{sV, xV, eV, bigNW, nV, hNoTm, hNo, uT, hEpsTm, hEps,
          openInvTend, exN, hAllTm, hAll, hLeTm, hLe, hRadiusAbs,
          radiusT, dropZero, absArgEq, rPos, rNonneg, absPos, absEq,
          radiusLtE, loT, hiT, uN, hInt, intBody, loBound, hiBound,
          absLtR, closeN, allN, exGoal, chosenN, epsBody, folded},
    sV = mkVar["S", csetSetTy]; xV = mkVar["x", csetRealTy];
    eV = mkVar["eCsetNear", csetRealTy];
    bigNW = mkVar["bigN", csetNumTy];
    nV = mkVar["nCsetNearTend", csetNumTy];
    hNoTm = csetNotTm[csetNeighGoal[sV, xV]]; hNo = ASSUME[hNoTm];
    uT = nearClosedPointTm[sV, xV];
    hEpsTm = csetRealLt[zeroRealTm[], eV]; hEps = ASSUME[hEpsTm];
    openInvTend = EQMP[unfoldTendsto[invSuccRadiusConst[], zeroRealTm[]],
      invSuccRadiusTendstoZeroThm];
    exN = HOL`Bool`MP[HOL`Bool`SPEC[eV, openInvTend], hEps];
    hAllTm = concl[HOL`Equal`BETACONV[mkComb[concl[exN][[2]], bigNW]]][[2]];
    hAll = ASSUME[hAllTm];
    hLeTm = csetNatLe[bigNW, nV]; hLe = ASSUME[hLeTm];
    hRadiusAbs = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAll], hLe];
    radiusT = invSuccRadiusTm[nV];
    dropZero = HOL`Bool`SPEC[radiusT, csetAddNegZeroThm];
    absArgEq = csetRealAbsCong[dropZero];
    rPos = HOL`Bool`SPEC[nV, invSuccRadiusPosThm];
    rNonneg = csetLtImpLeRule[rPos];
    absPos = HOL`Bool`MP[HOL`Bool`SPEC[radiusT, realAbsPosThm], rNonneg];
    absEq = TRANS[absArgEq, absPos];
    radiusLtE = EQMP[csetRealLtCong[absEq, REFL[eV]], hRadiusAbs];
    loT = csetNearClosedPointLo[xV, nV];
    hiT = csetNearClosedPointHi[xV, nV];
    uN = csetSeqApp[uT, nV];
    hInt = HOL`Bool`SPEC[nV, HOL`Bool`MP[
      csetSpecAll[nearClosedPointIntervalThm, {sV, xV}], hNo]];
    intBody = EQMP[unfoldOpenInterval[loT, hiT, uN], hInt];
    loBound = HOL`Bool`CONJUNCT1[intBody];
    hiBound = HOL`Bool`CONJUNCT2[intBody];
    absLtR = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[realAbsSubLtThm, {uN, xV, radiusT}], loBound], hiBound];
    closeN = HOL`Bool`MP[HOL`Bool`MP[
      csetSpecAll[realLtTransThm,
        {csetRealAbs[csetRealAdd[uN, csetRealNeg[xV]]], radiusT, eV}],
      absLtR], radiusLtE];
    allN = HOL`Bool`GEN[nV, HOL`Bool`DISCH[hLeTm, closeN]];
    exGoal = HOL`Bool`EXISTS[csetExistsTm[bigNW,
      csetForallTm[nV, csetImpTm[csetNatLe[bigNW, nV],
        csetSeqLimitAtom[uT, xV, eV, nV]]]], bigNW, allN];
    chosenN = HOL`Bool`CHOOSE[bigNW, exN, exGoal];
    epsBody = HOL`Bool`GEN[eV, HOL`Bool`DISCH[hEpsTm, chosenN]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[uT, xV]], epsBody];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[xV, HOL`Bool`DISCH[hNoTm, folded]]]
  ];

closedOfSequentiallyCompactThm =
  Module[{sV, xV, hSCTm, hSC, complSet, hComplXTm, hComplX, hNotSx,
          neighTm, openAll, openCompl, closed},
    sV = mkVar["S", csetSetTy]; xV = mkVar["xCsetClosed", csetRealTy];
    hSCTm = isSequentiallyCompactTm[sV]; hSC = ASSUME[hSCTm];
    complSet = complTm[sV];
    hComplXTm = csetSetApp[complSet, xV]; hComplX = ASSUME[hComplXTm];
    hNotSx = EQMP[csetSpecAll[complMemThm, {sV, xV}], hComplX];
    neighTm = csetNeighGoal[sV, xV];
    openAll = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hComplXTm,
      HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[neighTm],
        ASSUME[neighTm],
        Module[{hNoTm, hNo, uT, huS, huTend, openSC, seqEx, lW,
                hLBodyTm, hLBody, hLS, hHas, openHas, phiW, subSeq,
                hPhiBodyTm, hPhiBody, hIdx, hTend, subTendX, lEqX,
                hSx, falseTh, contrNeigh, choosePhi, chooseL},
          hNoTm = csetNotTm[neighTm]; hNo = ASSUME[hNoTm];
          uT = nearClosedPointTm[sV, xV];
          huS = HOL`Bool`MP[csetSpecAll[nearClosedPointMemThm, {sV, xV}], hNo];
          huTend = HOL`Bool`MP[csetSpecAll[nearClosedPointTendstoThm,
            {sV, xV}], hNo];
          openSC = EQMP[unfoldIsSequentiallyCompact[sV], hSC];
          seqEx = HOL`Bool`MP[HOL`Bool`SPEC[uT, openSC], huS];
          lW = mkVar["lClosed", csetRealTy];
          hLBodyTm = csetConjTm[csetSetApp[sV, lW],
            hasConvergentSubseqTm[uT, lW]];
          hLBody = ASSUME[hLBodyTm];
          hLS = HOL`Bool`CONJUNCT1[hLBody];
          hHas = HOL`Bool`CONJUNCT2[hLBody];
          openHas = EQMP[unfoldHasConvergentSubseq[uT, lW], hHas];
          phiW = mkVar["phiClosed", csetNumFunTy];
          subSeq = subsequenceTm[uT, phiW];
          hPhiBodyTm = csetConjTm[subseqIndexTm[phiW], tendstoTm[subSeq, lW]];
          hPhiBody = ASSUME[hPhiBodyTm];
          hIdx = HOL`Bool`CONJUNCT1[hPhiBody];
          hTend = HOL`Bool`CONJUNCT2[hPhiBody];
          subTendX = HOL`Bool`MP[HOL`Bool`MP[
            csetSpecAll[seqTendstoSubsequenceThm, {uT, phiW, xV}],
            hIdx], huTend];
          lEqX = HOL`Bool`MP[HOL`Bool`MP[
            csetSpecAll[tendstoUniqueThm, {subSeq, lW, xV}], hTend], subTendX];
          hSx = EQMP[HOL`Equal`APTERM[sV, lEqX], hLS];
          falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotSx], hSx];
          contrNeigh = HOL`Bool`CONTR[neighTm, falseTh];
          choosePhi = HOL`Bool`CHOOSE[phiW, openHas, contrNeigh];
          chooseL = HOL`Bool`CHOOSE[lW, seqEx, choosePhi];
          chooseL
        ]]]];
    openCompl = EQMP[HOL`Equal`SYM[unfoldIsOpen[complSet]], openAll];
    closed = EQMP[HOL`Equal`SYM[unfoldIsClosed[sV]], openCompl];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hSCTm, closed]]
  ];

sequentialCompactIffClosedBoundedThm =
  Module[{sV, hSCTm, hSC, hCBTm, hCB, closedBoundedFromSC, scFromCB, eqTh},
    sV = mkVar["SIffCset", csetSetTy];
    hSCTm = isSequentiallyCompactTm[sV]; hSC = ASSUME[hSCTm];
    hCBTm = csetConjTm[isClosedTm[sV], setBoundedTm[sV]];
    hCB = ASSUME[hCBTm];
    closedBoundedFromSC = HOL`Bool`CONJ[
      HOL`Bool`MP[HOL`Bool`SPEC[sV, closedOfSequentiallyCompactThm], hSC],
      HOL`Bool`MP[HOL`Bool`SPEC[sV, boundedOfSequentiallyCompactThm], hSC]];
    scFromCB = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[sV, sequentiallyCompactOfClosedBoundedThm],
      HOL`Bool`CONJUNCT1[hCB]], HOL`Bool`CONJUNCT2[hCB]];
    eqTh = HOL`Kernel`DEDUCTANTISYM[scFromCB, closedBoundedFromSC];
    HOL`Bool`GEN[sV, eqTh]
  ];

csetFalseTm[] := mkConst["F", boolTy];
csetEmptyRealSet[] := Module[{xV},
  xV = mkVar["xEmptyCset", csetRealTy];
  mkAbs[xV, csetFalseTm[]]
  ];
csetOpenIntervalSet[aT_, bT_] := mkComb[mkComb[openIntervalConst[], aT], bT];
csetMemConstAt[ty_] := mkConst["MEM",
  tyFun[ty, tyFun[HOL`Stdlib`List`listTy[ty], boolTy]]];
csetMemTmAt[ty_, xT_, xsT_] := mkComb[mkComb[csetMemConstAt[ty], xT], xsT];

csetOpenWitnessBody[uT_, xT_, leftT_, rightT_] :=
  Module[{yV},
    yV = mkVar["yOpenCset", csetRealTy];
    csetConjTm[csetRealLt[leftT, xT],
      csetConjTm[csetRealLt[xT, rightT],
        csetForallTm[yV, csetImpTm[openIntervalTm[leftT, rightT, yV],
          csetSetApp[uT, yV]]]]]
  ];
csetIsOpenExists[uT_, xT_] :=
  Module[{leftV, rightV},
    leftV = mkVar["leftOpenCset", csetRealTy];
    rightV = mkVar["rightOpenCset", csetRealTy];
    csetExistsTm[leftV, csetExistsTm[rightV,
      csetOpenWitnessBody[uT, xT, leftV, rightV]]]
  ];

csetSetCoversBody[cT_, sT_] :=
  Module[{xV, vV},
    xV = mkVar["xSc", csetRealTy]; vV = mkVar["vSc", csetSetTy];
    csetForallTm[xV, csetImpTm[csetSetApp[sT, xV],
      csetExistsTm[vV, csetConjTm[csetSetMem[cT, vV],
        csetSetAppV[vV, xV]]]]]
  ];
csetSetListSubcoverBody[cT_, sT_, vsT_] :=
  Module[{vV, xV, memV},
    vV = mkVar["vSl", csetSetTy]; xV = mkVar["xSl", csetRealTy];
    memV = csetMemTmAt[csetSetTy, vV, vsT];
    csetConjTm[
      csetForallTm[vV, csetImpTm[memV, csetSetMem[cT, vV]]],
      csetForallTm[xV, csetImpTm[csetSetApp[sT, xV],
        csetExistsTm[vV, csetConjTm[csetMemTmAt[csetSetTy, vV, vsT],
          csetSetAppV[vV, xV]]]]]]
  ];
csetSetFiniteSubcoverBody[cT_, sT_] :=
  Module[{vsV},
    vsV = mkVar["vsSf", csetSetListTy];
    csetExistsTm[vsV, setListSubcoverTm[cT, sT, vsV]]
  ];
csetIsCompactBody[sT_] :=
  Module[{cV, vV},
    cV = mkVar["CCompact", csetSetOfSetsTy];
    vV = mkVar["vCompact", csetSetTy];
    csetForallTm[cV,
      csetImpTm[csetForallTm[vV,
          csetImpTm[csetSetMem[cV, vV], isOpenTm[vV]]],
        csetImpTm[setCoversTm[cV, sT], setFiniteSubcoverTm[cV, sT]]]]
  ];

setCoversDefThm =
  Module[{cV, sV},
    cV = mkVar["C", csetSetOfSetsTy]; sV = mkVar["S", csetSetTy];
    newDefinition[mkEq[mkVar["setCovers", setCoversTy],
      mkAbs[cV, mkAbs[sV, csetSetCoversBody[cV, sV]]]]]
  ];
setCoversConst[] := mkConst["setCovers", setCoversTy];
setCoversTm[cT_, sT_] := mkComb[mkComb[setCoversConst[], cT], sT];
unfoldSetCovers[cT_, sT_] := csetApplyDef[setCoversDefThm, {cT, sT}];

setListSubcoverDefThm =
  Module[{cV, sV, vsV},
    cV = mkVar["C", csetSetOfSetsTy]; sV = mkVar["S", csetSetTy];
    vsV = mkVar["Vs", csetSetListTy];
    newDefinition[mkEq[mkVar["setListSubcover", setListSubcoverTy],
      mkAbs[cV, mkAbs[sV, mkAbs[vsV,
        csetSetListSubcoverBody[cV, sV, vsV]]]]]]
  ];
setListSubcoverConst[] := mkConst["setListSubcover", setListSubcoverTy];
setListSubcoverTm[cT_, sT_, vsT_] :=
  mkComb[mkComb[mkComb[setListSubcoverConst[], cT], sT], vsT];
unfoldSetListSubcover[cT_, sT_, vsT_] :=
  csetApplyDef[setListSubcoverDefThm, {cT, sT, vsT}];

setFiniteSubcoverDefThm =
  Module[{cV, sV},
    cV = mkVar["C", csetSetOfSetsTy]; sV = mkVar["S", csetSetTy];
    newDefinition[mkEq[mkVar["setFiniteSubcover", setCoversTy],
      mkAbs[cV, mkAbs[sV, csetSetFiniteSubcoverBody[cV, sV]]]]]
  ];
setFiniteSubcoverConst[] := mkConst["setFiniteSubcover", setCoversTy];
setFiniteSubcoverTm[cT_, sT_] :=
  mkComb[mkComb[setFiniteSubcoverConst[], cT], sT];
unfoldSetFiniteSubcover[cT_, sT_] :=
  csetApplyDef[setFiniteSubcoverDefThm, {cT, sT}];

isCompactDefThm =
  Module[{sV},
    sV = mkVar["S", csetSetTy];
    newDefinition[mkEq[mkVar["isCompact", isCompactTy],
      mkAbs[sV, csetIsCompactBody[sV]]]]
  ];
isCompactConst[] := mkConst["isCompact", isCompactTy];
isCompactTm[sT_] := mkComb[isCompactConst[], sT];
unfoldIsCompact[sT_] := csetApplyDef[isCompactDefThm, {sT}];

isOpenEmptyThm =
  Module[{emptySet, xV, point, allX},
    emptySet = csetEmptyRealSet[];
    xV = mkVar["xEmptyOpen", csetRealTy];
    point = csetBetaClean[HOL`Auto`PropTaut`propTaut[
      csetImpTm[csetFalseTm[], csetIsOpenExists[emptySet, xV]]]];
    allX = HOL`Bool`GEN[xV, point];
    EQMP[HOL`Equal`SYM[csetBetaClean[unfoldIsOpen[emptySet]]], allX]
  ];

openIntervalIsOpenThm =
  Module[{lV, rV, xV, yV, openSet, hXTm, hX, openedX, inner,
          body, exRight, exLeft, allX, folded},
    lV = mkVar["l", csetRealTy]; rV = mkVar["r", csetRealTy];
    xV = mkVar["xOpenInterval", csetRealTy];
    yV = mkVar["yOpenCset", csetRealTy];
    openSet = csetOpenIntervalSet[lV, rV];
    hXTm = openIntervalTm[lV, rV, xV]; hX = ASSUME[hXTm];
    openedX = EQMP[unfoldOpenInterval[lV, rV, xV], hX];
    inner = HOL`Bool`GEN[yV, HOL`Bool`DISCH[openIntervalTm[lV, rV, yV],
      ASSUME[openIntervalTm[lV, rV, yV]]]];
    body = HOL`Bool`CONJ[HOL`Bool`CONJUNCT1[openedX],
      HOL`Bool`CONJ[HOL`Bool`CONJUNCT2[openedX], inner]];
    exRight = HOL`Bool`EXISTS[
      csetExistsTm[mkVar["rightOpenCset", csetRealTy],
        csetOpenWitnessBody[openSet, xV, lV,
          mkVar["rightOpenCset", csetRealTy]]], rV, body];
    exLeft = HOL`Bool`EXISTS[csetIsOpenExists[openSet, xV], lV, exRight];
    allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hXTm, exLeft]];
    folded = EQMP[HOL`Equal`SYM[unfoldIsOpen[openSet]], allX];
    HOL`Bool`GEN[lV, HOL`Bool`GEN[rV, folded]]
  ];

csetListTyAt = csetSetListTy;
csetNilAt[] := mkConst["NIL", csetListTyAt];
csetConsConstAt[] :=
  mkConst["CONS", tyFun[csetSetTy, tyFun[csetListTyAt, csetListTyAt]]];
csetConsTmAt[hT_, tT_] := mkComb[mkComb[csetConsConstAt[], hT], tT];
csetFilterConstAt[] :=
  mkConst["FILTER", tyFun[csetSetOfSetsTy, tyFun[csetListTyAt, csetListTyAt]]];
csetFilterTmAt[pT_, lT_] := mkComb[mkComb[csetFilterConstAt[], pT], lT];
csetMemXFun[xT_] := mkComb[csetMemConstAt[csetSetTy], xT];
csetCondListConst[] := HOL`Bool`condConst[csetListTyAt];

memFilterThm =
  Module[{pV, xV, lV, wV, mV, memX, filterP, pxConj, predBody, predLam,
          induction, base, ihTm, ih, py, em, filterCons, memXFilterCons,
          memConsXM, pxConjCongr, condTInst, condFInst, branchT, branchF,
          stepEq, step, allL, bodyL},
    pV = mkVar["p", csetSetOfSetsTy]; xV = mkVar["xMemFilter", csetSetTy];
    lV = mkVar["lMemFilter", csetListTyAt];
    wV = mkVar["wMemFilter", csetSetTy]; mV = mkVar["mMemFilter", csetListTyAt];
    memX[lT_] := csetMemTmAt[csetSetTy, xV, lT];
    filterP[lT_] := csetFilterTmAt[pV, lT];
    pxConj[qT_] := csetConjTm[mkComb[pV, xV], qT];
    predBody[lT_] := mkEq[memX[filterP[lT]], pxConj[memX[lT]]];
    predLam = mkAbs[lV, predBody[lV]];
    induction = HOL`Bool`ISPEC[predLam, HOL`Stdlib`List`listInductionThm];

    base = Module[{filterNil, memNil, lhsF, conjMemNil, rhsF, baseBeta},
      filterNil = HOL`Bool`ISPEC[pV, HOL`Stdlib`List`filterNilThm];
      memNil = HOL`Bool`ISPEC[xV, HOL`Stdlib`List`memNilThm];
      lhsF = TRANS[HOL`Equal`APTERM[csetMemXFun[xV], filterNil], memNil];
      conjMemNil = HOL`Equal`APTERM[
        mkComb[csetAndConst[], mkComb[pV, xV]], memNil];
      rhsF = TRANS[conjMemNil, HOL`Auto`PropTaut`propTaut[
        mkEq[pxConj[csetFalseTm[]], csetFalseTm[]]]];
      baseBeta = TRANS[lhsF, SYM[rhsF]];
      EQMP[SYM[HOL`Equal`BETACONV[mkComb[predLam, csetNilAt[]]]], baseBeta]
    ];

    ihTm = mkComb[predLam, mV];
    ih = EQMP[HOL`Equal`BETACONV[ihTm], ASSUME[ihTm]];
    py = mkComb[pV, wV];
    em = HOL`Bool`EXCLUDEDMIDDLE[py];
    filterCons = HOL`Bool`SPEC[mV, HOL`Bool`SPEC[wV,
      HOL`Bool`ISPEC[pV, HOL`Stdlib`List`filterConsThm]]];
    memXFilterCons = HOL`Equal`APTERM[csetMemXFun[xV], filterCons];
    memConsXM = HOL`Bool`SPEC[mV, HOL`Bool`SPEC[wV,
      HOL`Bool`ISPEC[xV, HOL`Stdlib`List`memConsThm]]];
    pxConjCongr = HOL`Equal`APTERM[mkComb[csetAndConst[], mkComb[pV, xV]],
      SYM[memConsXM]];
    condTInst = HOL`Bool`ISPEC[filterP[mV],
      HOL`Bool`ISPEC[csetConsTmAt[wV, filterP[mV]], HOL`Bool`condTThm]];
    condFInst = HOL`Bool`ISPEC[filterP[mV],
      HOL`Bool`ISPEC[csetConsTmAt[wV, filterP[mV]], HOL`Bool`condFThm]];

    branchT = Module[{hPy, pyT, condArgEq, condEqA, memConsFilter, ihOr,
                      hXY, pEqXY, pxThm, pxFromEq, tautTm, eqTaut},
      hPy = ASSUME[py]; pyT = HOL`Bool`EQTINTRO[hPy];
      condArgEq = HOL`Equal`APTHM[HOL`Equal`APTHM[
        HOL`Equal`APTERM[csetCondListConst[], pyT],
        csetConsTmAt[wV, filterP[mV]]], filterP[mV]];
      condEqA = TRANS[condArgEq, condTInst];
      memConsFilter = HOL`Bool`SPEC[filterP[mV], HOL`Bool`SPEC[wV,
        HOL`Bool`ISPEC[xV, HOL`Stdlib`List`memConsThm]]];
      ihOr = HOL`Equal`APTERM[mkComb[csetOrConst[], mkEq[xV, wV]], ih];
      hXY = ASSUME[mkEq[xV, wV]];
      pEqXY = HOL`Equal`APTERM[pV, hXY];
      pxThm = EQMP[SYM[pEqXY], hPy];
      pxFromEq = HOL`Bool`DISCH[mkEq[xV, wV], pxThm];
      tautTm = csetImpTm[csetImpTm[mkEq[xV, wV], mkComb[pV, xV]],
        mkEq[csetOrTm[mkEq[xV, wV], pxConj[memX[mV]]],
          pxConj[csetOrTm[mkEq[xV, wV], memX[mV]]]]];
      eqTaut = HOL`Bool`MP[HOL`Auto`PropTaut`propTaut[tautTm], pxFromEq];
      TRANS[memXFilterCons, TRANS[HOL`Equal`APTERM[csetMemXFun[xV], condEqA],
        TRANS[memConsFilter, TRANS[ihOr, TRANS[eqTaut, pxConjCongr]]]]]
    ];

    branchF = Module[{hNotPy, pyF, condArgEq, condEqB, memXFilterM,
                      npEqXY, npxThm, notPxFromEq, tautTm, eqTaut},
      hNotPy = ASSUME[csetNotTm[py]];
      pyF = EQMP[HOL`Auto`PropTaut`propTaut[mkEq[csetNotTm[py],
        mkEq[py, csetFalseTm[]]]], hNotPy];
      condArgEq = HOL`Equal`APTHM[HOL`Equal`APTHM[
        HOL`Equal`APTERM[csetCondListConst[], pyF],
        csetConsTmAt[wV, filterP[mV]]], filterP[mV]];
      condEqB = TRANS[condArgEq, condFInst];
      memXFilterM = TRANS[memXFilterCons,
        TRANS[HOL`Equal`APTERM[csetMemXFun[xV], condEqB], ih]];
      npEqXY = HOL`Equal`APTERM[pV, ASSUME[mkEq[xV, wV]]];
      npxThm = EQMP[SYM[HOL`Equal`APTERM[csetNotConst[], npEqXY]], hNotPy];
      notPxFromEq = HOL`Bool`DISCH[mkEq[xV, wV], npxThm];
      tautTm = csetImpTm[csetImpTm[mkEq[xV, wV], csetNotTm[mkComb[pV, xV]]],
        mkEq[pxConj[memX[mV]], pxConj[csetOrTm[mkEq[xV, wV], memX[mV]]]]];
      eqTaut = HOL`Bool`MP[HOL`Auto`PropTaut`propTaut[tautTm], notPxFromEq];
      TRANS[memXFilterM, TRANS[eqTaut, pxConjCongr]]
    ];

    stepEq = HOL`Bool`DISJCASES[em, branchT, branchF];
    step = HOL`Bool`GEN[wV, HOL`Bool`GEN[mV, HOL`Bool`DISCH[ihTm,
      EQMP[SYM[HOL`Equal`BETACONV[mkComb[predLam, csetConsTmAt[wV, mV]]]],
        stepEq]]]];
    allL = HOL`Bool`MP[induction, HOL`Bool`CONJ[base, step]];
    bodyL = HOL`Bool`GEN[lV, EQMP[HOL`Equal`BETACONV[mkComb[predLam, lV]],
      HOL`Bool`SPEC[lV, allL]]];
    HOL`Bool`GEN[pV, HOL`Bool`GEN[xV, bodyL]]
  ];

csetClosedIntervalSet[aT_, bT_] := mkComb[mkComb[closedIntervalConst[], aT], bT];
csetCondSetConst[] := HOL`Bool`condConst[csetSetTy];
csetClampFamily[cT_] :=
  Module[{vCl},
    vCl = mkVar["vCl", csetSetTy];
    mkAbs[vCl, mkComb[mkComb[mkComb[csetCondSetConst[],
      csetSetMem[cT, vCl]], vCl], csetEmptyRealSet[]]]
  ];
csetEqfIntro[thNotP_] :=
  Module[{pT, pToF, fToP},
    pT = concl[thNotP][[2]];
    pToF = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], ASSUME[pT]];
    fToP = HOL`Bool`CONTR[pT, ASSUME[csetFalseTm[]]];
    HOL`Kernel`DEDUCTANTISYM[fToP, pToF]
  ];
csetClampHit[cT_, vT_, hCV_] :=
  Module[{clampT, beta, condEq},
    clampT = csetClampFamily[cT];
    beta = HOL`Equal`BETACONV[mkComb[clampT, vT]];
    condEq = TRANS[HOL`Equal`APTHM[HOL`Equal`APTHM[
        HOL`Equal`APTERM[csetCondSetConst[], HOL`Bool`EQTINTRO[hCV]],
        vT], csetEmptyRealSet[]],
      HOL`Bool`ISPEC[csetEmptyRealSet[],
        HOL`Bool`ISPEC[vT, HOL`Bool`condTThm]]];
    TRANS[beta, condEq]
  ];
csetClampMiss[cT_, vT_, hNotCV_] :=
  Module[{clampT, beta, condEq},
    clampT = csetClampFamily[cT];
    beta = HOL`Equal`BETACONV[mkComb[clampT, vT]];
    condEq = TRANS[HOL`Equal`APTHM[HOL`Equal`APTHM[
        HOL`Equal`APTERM[csetCondSetConst[], csetEqfIntro[hNotCV]],
        vT], csetEmptyRealSet[]],
      HOL`Bool`ISPEC[csetEmptyRealSet[],
        HOL`Bool`ISPEC[vT, HOL`Bool`condFThm]]];
    TRANS[beta, condEq]
  ];
csetFilterMemEq[cT_, vT_, vsT_] :=
  csetSpecAll[memFilterThm, {cT, vT, vsT}];
csetFilterMemIntro[cT_, vT_, vsT_, hCV_, hMem_] :=
  EQMP[HOL`Equal`SYM[csetFilterMemEq[cT, vT, vsT]],
    HOL`Bool`CONJ[hCV, hMem]];
csetFilteredMembersInC[cT_, vsT_] :=
  Module[{vF, hMemTm, hMem, memEq, memConj, cV},
    vF = mkVar["vFilterMember", csetSetTy];
    hMemTm = csetMemTmAt[csetSetTy, vF, csetFilterTmAt[cT, vsT]];
    hMem = ASSUME[hMemTm];
    memEq = csetFilterMemEq[cT, vF, vsT];
    memConj = EQMP[memEq, hMem];
    cV = HOL`Bool`CONJUNCT1[memConj];
    HOL`Bool`GEN[vF, HOL`Bool`DISCH[hMemTm, cV]]
  ];
csetPrimeCover[sT_, cT_] :=
  Module[{vCp},
    vCp = mkVar["vCp", csetSetTy];
    mkAbs[vCp, csetOrTm[mkEq[vCp, complTm[sT]], csetSetMem[cT, vCp]]]
  ];

closedIntervalSetCompactThm =
  Module[{aV, bV, cV, vOpen, hLeTm, hLe, hCopenTm, hCopen, ivSet,
          hCovTm, hCov, clampT, hUopen, hUcov, hFin, openFin, jsBridge,
          hListTm, hList, filterJs, memberAll, coverAll, listBody,
          listFolded, cleanFinite, exFinite, result},
    aV = mkVar["aHBBridge", csetRealTy]; bV = mkVar["bHBBridge", csetRealTy];
    cV = mkVar["CHBBridge", csetSetOfSetsTy];
    vOpen = mkVar["vOpenHBBridge", csetSetTy];
    hLeTm = csetRealLe[aV, bV]; hLe = ASSUME[hLeTm];
    hCopenTm = csetForallTm[vOpen,
      csetImpTm[csetSetMem[cV, vOpen], isOpenTm[vOpen]]];
    hCopen = ASSUME[hCopenTm];
    ivSet = csetClosedIntervalSet[aV, bV];
    hCovTm = setCoversTm[cV, ivSet]; hCov = ASSUME[hCovTm];
    clampT = csetClampFamily[cV];

    hUopen = Module[{vU, cvTm, hCv, hNotCvTm, hNotCv, em, hitEq,
        missEq, openV, trueBranch, falseBranch},
      vU = mkVar["vClampOpen", csetSetTy];
      cvTm = csetSetMem[cV, vU]; hCv = ASSUME[cvTm];
      hNotCvTm = csetNotTm[cvTm]; hNotCv = ASSUME[hNotCvTm];
      hitEq = csetClampHit[cV, vU, hCv];
      missEq = csetClampMiss[cV, vU, hNotCv];
      openV = HOL`Bool`MP[HOL`Bool`SPEC[vU, hCopen], hCv];
      trueBranch = EQMP[HOL`Equal`SYM[
        HOL`Equal`APTERM[isOpenConst[], hitEq]], openV];
      falseBranch = EQMP[HOL`Equal`SYM[
        HOL`Equal`APTERM[isOpenConst[], missEq]], isOpenEmptyThm];
      em = HOL`Bool`EXCLUDEDMIDDLE[cvTm];
      HOL`Bool`GEN[vU, HOL`Bool`DISJCASES[em, trueBranch, falseBranch]]
    ];

    hUcov = Module[{xCov, vCov, hIvTm, hIv, setCovBody, covEx,
        hBodyTm, hBody, hCV, hVX, hitEq, clampVX, exBody, exCov,
        chooseV, allX},
      xCov = mkVar["xClampCover", csetRealTy];
      vCov = mkVar["vCovHBBridge", csetSetTy];
      hIvTm = csetSetApp[ivSet, xCov]; hIv = ASSUME[hIvTm];
      setCovBody = EQMP[unfoldSetCovers[cV, ivSet], hCov];
      covEx = HOL`Bool`MP[HOL`Bool`SPEC[xCov, setCovBody], hIv];
      hBodyTm = csetConjTm[csetSetMem[cV, vCov],
        csetSetAppV[vCov, xCov]];
      hBody = ASSUME[hBodyTm];
      hCV = HOL`Bool`CONJUNCT1[hBody];
      hVX = HOL`Bool`CONJUNCT2[hBody];
      hitEq = csetClampHit[cV, vCov, hCV];
      clampVX = EQMP[HOL`Equal`SYM[HOL`Equal`APTHM[hitEq, xCov]], hVX];
      exBody = csetExistsTm[vCov, csetSetAppV[mkComb[clampT, vCov], xCov]];
      exCov = HOL`Bool`EXISTS[exBody, vCov, clampVX];
      chooseV = HOL`Bool`CHOOSE[vCov, covEx, exCov];
      allX = HOL`Bool`GEN[xCov, HOL`Bool`DISCH[hIvTm, chooseV]];
      EQMP[HOL`Equal`SYM[unfoldCovers[clampT, ivSet]], allX]
    ];

    hFin = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV,
        HOL`Bool`ISPEC[clampT, compactnessPrincipleThm]]], hLe],
      hUopen], hUcov];
    openFin = EQMP[unfoldFiniteSubcover[clampT, ivSet], hFin];
    jsBridge = mkVar["jsBridge", csetSetListTy];
    hListTm = listSubcoverTm[clampT, ivSet, jsBridge];
    hList = ASSUME[hListTm];
    filterJs = csetFilterTmAt[cV, jsBridge];
    memberAll = csetFilteredMembersInC[cV, jsBridge];

    coverAll = Module[{xList, iBridge, hIvTm, hIv, listBodyOld,
        listEx, hOldTm, hOld, hMemI, hClampIx, ciTm, hCi, hitEq,
        ixTh, memFilter, exGoal, exI},
      xList = mkVar["xBridgeCover", csetRealTy];
      iBridge = mkVar["iBridge", csetSetTy];
      hIvTm = csetSetApp[ivSet, xList]; hIv = ASSUME[hIvTm];
      listBodyOld = EQMP[unfoldListSubcover[clampT, ivSet, jsBridge], hList];
      listEx = HOL`Bool`MP[HOL`Bool`SPEC[xList, listBodyOld], hIv];
      hOldTm = csetConjTm[csetMemTmAt[csetSetTy, iBridge, jsBridge],
        csetSetAppV[mkComb[clampT, iBridge], xList]];
      hOld = ASSUME[hOldTm];
      hMemI = HOL`Bool`CONJUNCT1[hOld];
      hClampIx = HOL`Bool`CONJUNCT2[hOld];
      ciTm = csetSetMem[cV, iBridge];
      hCi = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[ciTm],
        ASSUME[ciTm],
        Module[{hNotCiTm, hNotCi, missEq, emptyIx, emptyFalse, falseTh},
          hNotCiTm = csetNotTm[ciTm]; hNotCi = ASSUME[hNotCiTm];
          missEq = csetClampMiss[cV, iBridge, hNotCi];
          emptyIx = EQMP[HOL`Equal`APTHM[missEq, xList], hClampIx];
          emptyFalse = HOL`Equal`BETACONV[csetSetAppV[csetEmptyRealSet[], xList]];
          falseTh = EQMP[emptyFalse, emptyIx];
          HOL`Bool`CONTR[ciTm, falseTh]
        ]];
      hitEq = csetClampHit[cV, iBridge, hCi];
      ixTh = EQMP[HOL`Equal`APTHM[hitEq, xList], hClampIx];
      memFilter = csetFilterMemIntro[cV, iBridge, jsBridge, hCi, hMemI];
      exGoal = csetExistsTm[iBridge, csetConjTm[
        csetMemTmAt[csetSetTy, iBridge, filterJs],
        csetSetAppV[iBridge, xList]]];
      exI = HOL`Bool`EXISTS[exGoal, iBridge,
        HOL`Bool`CONJ[memFilter, ixTh]];
      HOL`Bool`GEN[xList, HOL`Bool`DISCH[hIvTm,
        HOL`Bool`CHOOSE[iBridge, listEx, exI]]]
    ];

    listBody = HOL`Bool`CONJ[memberAll, coverAll];
    listFolded = EQMP[HOL`Equal`SYM[
      unfoldSetListSubcover[cV, ivSet, filterJs]], listBody];
    cleanFinite = unfoldSetFiniteSubcover[cV, ivSet];
    exFinite = HOL`Bool`EXISTS[concl[cleanFinite][[2]], filterJs, listFolded];
    result = HOL`Bool`CHOOSE[jsBridge, openFin,
      EQMP[HOL`Equal`SYM[cleanFinite], exFinite]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hCopenTm,
        HOL`Bool`DISCH[hCovTm, result]]]]]]
  ];

compactOfClosedBoundedThm =
  Module[{sV, cV, vOpen, xNon, hClosedTm, hClosed, hBddTm, hBdd,
          hCopenTm, hCopen, hCovTm, hCov, nonemptyTm, emptyBranch,
          nonemptyBranch, finiteBody, compactBody, folded},
    sV = mkVar["SCompactProd", csetSetTy];
    cV = mkVar["CCompactProd", csetSetOfSetsTy];
    vOpen = mkVar["vOpenCompactProd", csetSetTy];
    hClosedTm = isClosedTm[sV]; hClosed = ASSUME[hClosedTm];
    hBddTm = setBoundedTm[sV]; hBdd = ASSUME[hBddTm];
    hCopenTm = csetForallTm[vOpen,
      csetImpTm[csetSetMem[cV, vOpen], isOpenTm[vOpen]]];
    hCopen = ASSUME[hCopenTm];
    hCovTm = setCoversTm[cV, sV]; hCov = ASSUME[hCovTm];
    xNon = mkVar["xNonemptyCompact", csetRealTy];
    nonemptyTm = csetExistsTm[xNon, csetSetApp[sV, xNon]];

    emptyBranch = Module[{hEmptyTm, hEmpty, nilT, memberAll, coverAll,
        listBody, listFolded, cleanFinite, exFinite},
      hEmptyTm = csetNotTm[nonemptyTm]; hEmpty = ASSUME[hEmptyTm];
      nilT = csetNilAt[];
      memberAll = Module[{vNil, hMemTm, hMem, memNil, falseTh},
        vNil = mkVar["vNilCompact", csetSetTy];
        hMemTm = csetMemTmAt[csetSetTy, vNil, nilT]; hMem = ASSUME[hMemTm];
        memNil = HOL`Bool`ISPEC[vNil, HOL`Stdlib`List`memNilThm];
        falseTh = EQMP[memNil, hMem];
        HOL`Bool`GEN[vNil, HOL`Bool`DISCH[hMemTm,
          HOL`Bool`CONTR[csetSetMem[cV, vNil], falseTh]]]
      ];
      coverAll = Module[{xEmpty, vEmpty, hSxTm, hSx, exS, falseTh, exCover},
        xEmpty = mkVar["xEmptyCompact", csetRealTy];
        vEmpty = mkVar["vEmptyCompact", csetSetTy];
        hSxTm = csetSetApp[sV, xEmpty]; hSx = ASSUME[hSxTm];
        exS = HOL`Bool`EXISTS[nonemptyTm, xEmpty, hSx];
        falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[hEmpty], exS];
        exCover = csetExistsTm[vEmpty, csetConjTm[
          csetMemTmAt[csetSetTy, vEmpty, nilT],
          csetSetAppV[vEmpty, xEmpty]]];
        HOL`Bool`GEN[xEmpty, HOL`Bool`DISCH[hSxTm,
          HOL`Bool`CONTR[exCover, falseTh]]]
      ];
      listBody = HOL`Bool`CONJ[memberAll, coverAll];
      listFolded = EQMP[HOL`Equal`SYM[
        unfoldSetListSubcover[cV, sV, nilT]], listBody];
      cleanFinite = unfoldSetFiniteSubcover[cV, sV];
      exFinite = HOL`Bool`EXISTS[concl[cleanFinite][[2]], nilT, listFolded];
      EQMP[HOL`Equal`SYM[cleanFinite], exFinite]
    ];

    nonemptyBranch = Module[{hNonempty, openBound, loW, hiW, xS, hBoundsTm,
        hBounds, hXSTm, hXS, boundsXS, loLeXS, xsLeHi, loLeHi, ivSet,
        cPrime, hPrimeOpen, hPrimeCov, primeFinite, openPrimeFin, vsProd,
        hPrimeListTm, hPrimeList, filterVs, memberAll, coverAll, listBody,
        listFolded, cleanFinite, exFinite, result, chooseXS, chooseHi,
        chooseLo},
      hNonempty = ASSUME[nonemptyTm];
      openBound = EQMP[unfoldSetBounded[sV], hBdd];
      loW = mkVar["loCompactProd", csetRealTy];
      hiW = mkVar["hiCompactProd", csetRealTy];
      xS = mkVar["xS", csetRealTy];
      hBoundsTm = csetSetBoundedAll[sV, loW, hiW];
      hBounds = ASSUME[hBoundsTm];
      hXSTm = csetSetApp[sV, xS]; hXS = ASSUME[hXSTm];
      boundsXS = HOL`Bool`MP[HOL`Bool`SPEC[xS, hBounds], hXS];
      loLeXS = HOL`Bool`CONJUNCT1[boundsXS];
      xsLeHi = HOL`Bool`CONJUNCT2[boundsXS];
      loLeHi = HOL`Bool`MP[HOL`Bool`MP[
        csetSpecAll[realLeTransThm, {loW, xS, hiW}], loLeXS], xsLeHi];
      ivSet = csetClosedIntervalSet[loW, hiW];
      cPrime = csetPrimeCover[sV, cV];

      hPrimeOpen = Module[{vPrime, hCpTm, hCp, cpEq, disj, leftTm,
          rightTm, leftBranch, rightBranch},
        vPrime = mkVar["vPrimeOpen", csetSetTy];
        hCpTm = csetSetMem[cPrime, vPrime]; hCp = ASSUME[hCpTm];
        cpEq = HOL`Equal`BETACONV[mkComb[cPrime, vPrime]];
        disj = EQMP[cpEq, hCp];
        leftTm = mkEq[vPrime, complTm[sV]];
        rightTm = csetSetMem[cV, vPrime];
        leftBranch = Module[{hEq, openCompl},
          hEq = ASSUME[leftTm];
          openCompl = EQMP[csetSpecAll[isClosedComplOpenThm, {sV}], hClosed];
          EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[isOpenConst[], hEq]], openCompl]
        ];
        rightBranch = HOL`Bool`MP[HOL`Bool`SPEC[vPrime, hCopen],
          ASSUME[rightTm]];
        HOL`Bool`GEN[vPrime, HOL`Bool`DISCH[hCpTm,
          HOL`Bool`DISJCASES[disj, leftBranch, rightBranch]]]
      ];

      hPrimeCov = Module[{xCov, vCov, hIvTm, hIv, sxTm, emS,
          trueBranch, falseBranch, allX},
        xCov = mkVar["xPrimeCover", csetRealTy];
        vCov = mkVar["vPrimeCov", csetSetTy];
        hIvTm = csetSetApp[ivSet, xCov]; hIv = ASSUME[hIvTm];
        sxTm = csetSetApp[sV, xCov];
        trueBranch = Module[{hSx, setCovBody, covEx, hBodyTm, hBody,
            hCV, hVX, cpEq, cPrimeV, exGoal},
          hSx = ASSUME[sxTm];
          setCovBody = EQMP[unfoldSetCovers[cV, sV], hCov];
          covEx = HOL`Bool`MP[HOL`Bool`SPEC[xCov, setCovBody], hSx];
          hBodyTm = csetConjTm[csetSetMem[cV, vCov],
            csetSetAppV[vCov, xCov]];
          hBody = ASSUME[hBodyTm];
          hCV = HOL`Bool`CONJUNCT1[hBody];
          hVX = HOL`Bool`CONJUNCT2[hBody];
          cpEq = HOL`Equal`BETACONV[mkComb[cPrime, vCov]];
          cPrimeV = EQMP[HOL`Equal`SYM[cpEq],
            HOL`Bool`DISJ2[hCV, mkEq[vCov, complTm[sV]]]];
          exGoal = csetExistsTm[vCov, csetConjTm[
            csetSetMem[cPrime, vCov], csetSetAppV[vCov, xCov]]];
          HOL`Bool`CHOOSE[vCov, covEx, HOL`Bool`EXISTS[exGoal, vCov,
            HOL`Bool`CONJ[cPrimeV, hVX]]]
        ];
        falseBranch = Module[{hNotSxTm, hNotSx, complAtX, cpEq, cPrimeCompl,
            complS, exGoal},
          hNotSxTm = csetNotTm[sxTm]; hNotSx = ASSUME[hNotSxTm];
          complS = complTm[sV];
          complAtX = EQMP[HOL`Equal`SYM[csetSpecAll[complMemThm,
            {sV, xCov}]], hNotSx];
          cpEq = HOL`Equal`BETACONV[mkComb[cPrime, complS]];
          cPrimeCompl = EQMP[HOL`Equal`SYM[cpEq],
            HOL`Bool`DISJ1[REFL[complS], csetSetMem[cV, complS]]];
          exGoal = csetExistsTm[vCov, csetConjTm[
            csetSetMem[cPrime, vCov], csetSetAppV[vCov, xCov]]];
          HOL`Bool`EXISTS[exGoal, complS,
            HOL`Bool`CONJ[cPrimeCompl, complAtX]]
        ];
        emS = HOL`Bool`EXCLUDEDMIDDLE[sxTm];
        allX = HOL`Bool`GEN[xCov, HOL`Bool`DISCH[hIvTm,
          HOL`Bool`DISJCASES[emS, trueBranch, falseBranch]]];
        EQMP[HOL`Equal`SYM[unfoldSetCovers[cPrime, ivSet]], allX]
      ];

      primeFinite = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
        csetSpecAll[closedIntervalSetCompactThm, {loW, hiW, cPrime}],
        loLeHi], hPrimeOpen], hPrimeCov];
      openPrimeFin = EQMP[unfoldSetFiniteSubcover[cPrime, ivSet], primeFinite];
      vsProd = mkVar["vsProd", csetSetListTy];
      hPrimeListTm = setListSubcoverTm[cPrime, ivSet, vsProd];
      hPrimeList = ASSUME[hPrimeListTm];
      filterVs = csetFilterTmAt[cV, vsProd];
      memberAll = csetFilteredMembersInC[cV, vsProd];
      coverAll = Module[{xCover, vProd, hSxTm, hSx, boundsX, ivX,
          primeListBody, primeMembers, primeCovers, exPrime, hBodyTm,
          hBody, hMemV, hVX, cPrimeV, cpEq, disj, leftTm, rightTm,
          leftBranch, rightBranch, goalEx},
        xCover = mkVar["xProdCover", csetRealTy];
        vProd = mkVar["vProd", csetSetTy];
        hSxTm = csetSetApp[sV, xCover]; hSx = ASSUME[hSxTm];
        boundsX = HOL`Bool`MP[HOL`Bool`SPEC[xCover, hBounds], hSx];
        ivX = EQMP[HOL`Equal`SYM[unfoldClosedInterval[loW, hiW, xCover]],
          boundsX];
        primeListBody = EQMP[
          unfoldSetListSubcover[cPrime, ivSet, vsProd], hPrimeList];
        primeMembers = HOL`Bool`CONJUNCT1[primeListBody];
        primeCovers = HOL`Bool`CONJUNCT2[primeListBody];
        exPrime = HOL`Bool`MP[HOL`Bool`SPEC[xCover, primeCovers], ivX];
        hBodyTm = csetConjTm[csetMemTmAt[csetSetTy, vProd, vsProd],
          csetSetAppV[vProd, xCover]];
        hBody = ASSUME[hBodyTm];
        hMemV = HOL`Bool`CONJUNCT1[hBody];
        hVX = HOL`Bool`CONJUNCT2[hBody];
        cPrimeV = HOL`Bool`MP[HOL`Bool`SPEC[vProd, primeMembers], hMemV];
        cpEq = HOL`Equal`BETACONV[mkComb[cPrime, vProd]];
        disj = EQMP[cpEq, cPrimeV];
        leftTm = mkEq[vProd, complTm[sV]];
        rightTm = csetSetMem[cV, vProd];
        goalEx = csetExistsTm[vProd, csetConjTm[
          csetMemTmAt[csetSetTy, vProd, filterVs],
          csetSetAppV[vProd, xCover]]];
        leftBranch = Module[{hEq, complVX, notSX, falseTh},
          hEq = ASSUME[leftTm];
          complVX = EQMP[HOL`Equal`APTHM[hEq, xCover], hVX];
          notSX = EQMP[csetSpecAll[complMemThm, {sV, xCover}], complVX];
          falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notSX], hSx];
          HOL`Bool`CONTR[goalEx, falseTh]
        ];
        rightBranch = Module[{hCV, memFilter},
          hCV = ASSUME[rightTm];
          memFilter = csetFilterMemIntro[cV, vProd, vsProd, hCV, hMemV];
          HOL`Bool`EXISTS[goalEx, vProd, HOL`Bool`CONJ[memFilter, hVX]]
        ];
        HOL`Bool`GEN[xCover, HOL`Bool`DISCH[hSxTm,
          HOL`Bool`CHOOSE[vProd, exPrime,
            HOL`Bool`DISJCASES[disj, leftBranch, rightBranch]]]]
      ];
      listBody = HOL`Bool`CONJ[memberAll, coverAll];
      listFolded = EQMP[HOL`Equal`SYM[
        unfoldSetListSubcover[cV, sV, filterVs]], listBody];
      cleanFinite = unfoldSetFiniteSubcover[cV, sV];
      exFinite = HOL`Bool`EXISTS[concl[cleanFinite][[2]], filterVs, listFolded];
      result = HOL`Bool`CHOOSE[vsProd, openPrimeFin,
        EQMP[HOL`Equal`SYM[cleanFinite], exFinite]];
      chooseXS = HOL`Bool`CHOOSE[xS, hNonempty, result];
      chooseHi = HOL`Bool`CHOOSE[hiW,
        ASSUME[csetExistsTm[hiW, hBoundsTm]], chooseXS];
      chooseLo = HOL`Bool`CHOOSE[loW, openBound, chooseHi];
      chooseLo
    ];

    finiteBody = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[nonemptyTm],
      nonemptyBranch, emptyBranch];
    compactBody = HOL`Bool`GEN[cV, HOL`Bool`DISCH[hCopenTm,
      HOL`Bool`DISCH[hCovTm, finiteBody]]];
    folded = EQMP[HOL`Equal`SYM[unfoldIsCompact[sV]], compactBody];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hClosedTm,
      HOL`Bool`DISCH[hBddTm, folded]]]
  ];

csetSubOne[xT_] := csetRealAdd[xT, csetRealNeg[csetOneReal[]]];
csetAddOne[xT_] := csetRealAdd[xT, csetOneReal[]];
csetUnitInterval[cT_] := csetOpenIntervalSet[csetSubOne[cT], csetAddOne[cT]];
csetRealMin[xT_, yT_] := mkComb[mkComb[realMinConst[], xT], yT];
csetRealMax[xT_, yT_] := mkComb[mkComb[realMaxConst[], xT], yT];

csetMemNilEq[xT_] := HOL`Bool`ISPEC[xT, HOL`Stdlib`List`memNilThm];
csetMemConsEq[xT_, yT_, xsT_] :=
  HOL`Bool`SPEC[xsT, HOL`Bool`SPEC[yT,
    HOL`Bool`ISPEC[xT, HOL`Stdlib`List`memConsThm]]];

csetCenterCoverBody[vT_] :=
  Module[{cV},
    cV = mkVar["cCenter", csetRealTy];
    csetExistsTm[cV, mkEq[vT, csetUnitInterval[cV]]]
  ];
csetCenterCoverAll[vsT_] :=
  Module[{vV},
    vV = mkVar["vCenterAll", csetSetTy];
    csetForallTm[vV, csetImpTm[csetMemTmAt[csetSetTy, vV, vsT],
      csetSetMem[centerCoverTm[], vV]]]
  ];
csetFiniteCoverHitBody[vsT_, xT_, vT_] :=
  csetConjTm[csetMemTmAt[csetSetTy, vT, vsT], csetSetAppV[vT, xT]];
csetFiniteCoverHit[vsT_, xT_] :=
  Module[{vV},
    vV = mkVar["vFiniteHit", csetSetTy];
    csetExistsTm[vV, csetFiniteCoverHitBody[vsT, xT, vV]]
  ];
csetFiniteCoverAll[vsT_, loT_, hiT_] :=
  Module[{xV},
    xV = mkVar["xFiniteBound", csetRealTy];
    csetForallTm[xV, csetImpTm[csetFiniteCoverHit[vsT, xV],
      csetConjTm[csetRealLe[loT, xV], csetRealLe[xV, hiT]]]]
  ];
csetFiniteCoverBoundExists[vsT_] :=
  Module[{loV, hiV},
    loV = mkVar["loFiniteBound", csetRealTy];
    hiV = mkVar["hiFiniteBound", csetRealTy];
    csetExistsTm[loV, csetExistsTm[hiV,
      csetFiniteCoverAll[vsT, loV, hiV]]]
  ];
csetFiniteIntervalPredBody[vsT_] :=
  csetImpTm[csetCenterCoverAll[vsT], csetFiniteCoverBoundExists[vsT]];

centerCoverDefThm =
  Module[{vV},
    vV = mkVar["vCenter", csetSetTy];
    newDefinition[mkEq[mkVar["centerCover", csetSetOfSetsTy],
      mkAbs[vV, csetCenterCoverBody[vV]]]]
  ];
centerCoverConst[] := mkConst["centerCover", csetSetOfSetsTy];
centerCoverTm[] := centerCoverConst[];

centerCoverMemThm =
  Module[{vV, app, beta},
    vV = mkVar["vCenterMem", csetSetTy];
    app = HOL`Equal`APTHM[centerCoverDefThm, vV];
    beta = TRANS[app, HOL`Equal`BETACONV[concl[app][[2]]]];
    HOL`Bool`GEN[vV, beta]
  ];

centerCoverOpenThm =
  Module[{vV, hCenterTm, hCenter, opened, cV, hEqTm, hEq,
          openInt, openV, body},
    vV = mkVar["vCenterOpen", csetSetTy];
    hCenterTm = csetSetMem[centerCoverTm[], vV]; hCenter = ASSUME[hCenterTm];
    opened = EQMP[HOL`Bool`SPEC[vV, centerCoverMemThm], hCenter];
    cV = mkVar["cOpen", csetRealTy];
    hEqTm = mkEq[vV, csetUnitInterval[cV]]; hEq = ASSUME[hEqTm];
    openInt = csetSpecAll[openIntervalIsOpenThm,
      {csetSubOne[cV], csetAddOne[cV]}];
    openV = EQMP[HOL`Equal`APTERM[isOpenConst[], HOL`Equal`SYM[hEq]],
      openInt];
    body = HOL`Bool`CHOOSE[cV, opened, openV];
    HOL`Bool`GEN[vV, HOL`Bool`DISCH[hCenterTm, body]]
  ];

centerCoverCoversThm =
  Module[{sV, xV, vT, hSxTm, hSx, centerEq, centerEx, centerAtV,
          leftLt, rightLt, intAtX, hitV, exGoal, allX, folded},
    sV = mkVar["SCenterCover", csetSetTy];
    xV = mkVar["xCenterCover", csetRealTy];
    vT = csetUnitInterval[xV];
    hSxTm = csetSetApp[sV, xV]; hSx = ASSUME[hSxTm];
    centerEq = HOL`Bool`SPEC[vT, centerCoverMemThm];
    centerEx = HOL`Bool`EXISTS[csetCenterCoverBody[vT], xV, REFL[vT]];
    centerAtV = EQMP[HOL`Equal`SYM[centerEq], centerEx];
    leftLt = HOL`Bool`SPEC[xV, HOL`Auto`RealArith`realArithProve[
      csetForallTm[xV, csetRealLt[csetSubOne[xV], xV]]]];
    rightLt = HOL`Bool`SPEC[xV, HOL`Auto`RealArith`realArithProve[
      csetForallTm[xV, csetRealLt[xV, csetAddOne[xV]]]]];
    intAtX = EQMP[HOL`Equal`SYM[
      unfoldOpenInterval[csetSubOne[xV], csetAddOne[xV], xV]],
      HOL`Bool`CONJ[leftLt, rightLt]];
    hitV = HOL`Bool`CONJ[centerAtV, intAtX];
    exGoal = csetExistsTm[mkVar["vSc", csetSetTy],
      csetConjTm[csetSetMem[centerCoverTm[], mkVar["vSc", csetSetTy]],
        csetSetAppV[mkVar["vSc", csetSetTy], xV]]];
    allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hSxTm,
      HOL`Bool`EXISTS[exGoal, vT, hitV]]];
    folded = EQMP[HOL`Equal`SYM[unfoldSetCovers[centerCoverTm[], sV]], allX];
    HOL`Bool`GEN[sV, folded]
  ];

boundedOfFiniteIntervalCoverThm =
  Module[{vsV, v0V, restV, predLam, induction, base, step, allVs, bodyVs},
    vsV = mkVar["VsFiniteBound", csetSetListTy];
    v0V = mkVar["v0FiniteBound", csetSetTy];
    restV = mkVar["restFiniteBound", csetSetListTy];
    predLam = mkAbs[vsV, csetFiniteIntervalPredBody[vsV]];
    induction = HOL`Bool`ISPEC[predLam, HOL`Stdlib`List`listInductionThm];

    base = Module[{nilT, hAllTm, hAll, loZ, hiZ, xV, hHitTm, hHit,
        vHit, hBodyTm, hBody, hMem, memNil, falseTh, point, allX,
        exHi, exLo, body},
      nilT = csetNilAt[];
      hAllTm = csetCenterCoverAll[nilT]; hAll = ASSUME[hAllTm];
      loZ = zeroRealTm[]; hiZ = zeroRealTm[];
      xV = mkVar["xBaseFinite", csetRealTy];
      hHitTm = csetFiniteCoverHit[nilT, xV]; hHit = ASSUME[hHitTm];
      vHit = mkVar["vFiniteHit", csetSetTy];
      hBodyTm = csetFiniteCoverHitBody[nilT, xV, vHit];
      hBody = ASSUME[hBodyTm];
      hMem = HOL`Bool`CONJUNCT1[hBody];
      memNil = csetMemNilEq[vHit];
      falseTh = EQMP[memNil, hMem];
      point = HOL`Bool`CHOOSE[vHit, hHit,
        HOL`Bool`CONTR[
          csetConjTm[csetRealLe[loZ, xV], csetRealLe[xV, hiZ]], falseTh]];
      allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hHitTm, point]];
      exHi = HOL`Bool`EXISTS[
        csetExistsTm[mkVar["hiFiniteBound", csetRealTy],
          csetFiniteCoverAll[nilT, loZ,
            mkVar["hiFiniteBound", csetRealTy]]], hiZ, allX];
      exLo = HOL`Bool`EXISTS[csetFiniteCoverBoundExists[nilT], loZ, exHi];
      body = HOL`Bool`DISCH[hAllTm, exLo];
      EQMP[HOL`Equal`SYM[HOL`Equal`BETACONV[mkComb[predLam, nilT]]], body]
    ];

    step = Module[{ihTm, ih, consT, hAllTm, hAll, restAll, restBound,
        memV0Cons, hV0Center, centerExists, loRest, hiRest, hRestBoundTm,
        hRestBound, cV, hV0EqTm, hV0Eq, loT, hiT, xV, hHitTm, hHit,
        vHit, hBodyTm, hBody, hMemCons, hVx, memOpen, branchEq,
        branchRest, point, allX, exHi, exLo, chooseC, chooseHi, chooseLo,
        body},
      ihTm = mkComb[predLam, restV];
      ih = EQMP[HOL`Equal`BETACONV[ihTm], ASSUME[ihTm]];
      consT = csetConsTmAt[v0V, restV];
      hAllTm = csetCenterCoverAll[consT]; hAll = ASSUME[hAllTm];
      restAll = Module[{vRest, hMemRestTm, hMemRest, memConsRest,
          centerRest},
        vRest = mkVar["vRestFinite", csetSetTy];
        hMemRestTm = csetMemTmAt[csetSetTy, vRest, restV];
        hMemRest = ASSUME[hMemRestTm];
        memConsRest = EQMP[HOL`Equal`SYM[
          csetMemConsEq[vRest, v0V, restV]],
          HOL`Bool`DISJ2[hMemRest, mkEq[vRest, v0V]]];
        centerRest = HOL`Bool`MP[HOL`Bool`SPEC[vRest, hAll], memConsRest];
        HOL`Bool`GEN[vRest, HOL`Bool`DISCH[hMemRestTm, centerRest]]
      ];
      restBound = HOL`Bool`MP[ih, restAll];
      memV0Cons = EQMP[HOL`Equal`SYM[csetMemConsEq[v0V, v0V, restV]],
        HOL`Bool`DISJ1[REFL[v0V], csetMemTmAt[csetSetTy, v0V, restV]]];
      hV0Center = HOL`Bool`MP[HOL`Bool`SPEC[v0V, hAll], memV0Cons];
      centerExists = EQMP[HOL`Bool`SPEC[v0V, centerCoverMemThm], hV0Center];
      loRest = mkVar["loRest", csetRealTy];
      hiRest = mkVar["hiRest", csetRealTy];
      hRestBoundTm = csetFiniteCoverAll[restV, loRest, hiRest];
      hRestBound = ASSUME[hRestBoundTm];
      cV = mkVar["cStep", csetRealTy];
      hV0EqTm = mkEq[v0V, csetUnitInterval[cV]];
      hV0Eq = ASSUME[hV0EqTm];
      loT = csetRealMin[csetSubOne[cV], loRest];
      hiT = csetRealMax[csetAddOne[cV], hiRest];
      xV = mkVar["xStepFinite", csetRealTy];
      hHitTm = csetFiniteCoverHit[consT, xV]; hHit = ASSUME[hHitTm];
      vHit = mkVar["vFiniteHit", csetSetTy];
      hBodyTm = csetFiniteCoverHitBody[consT, xV, vHit];
      hBody = ASSUME[hBodyTm];
      hMemCons = HOL`Bool`CONJUNCT1[hBody];
      hVx = HOL`Bool`CONJUNCT2[hBody];
      memOpen = EQMP[csetMemConsEq[vHit, v0V, restV], hMemCons];
      branchEq = Module[{hEqTm, hEq, v0x, intervalX, intervalBody,
          leftLt, rightLt, subLeX, loLeSub, loLeX, xLeAdd, addLeHi,
          xLeHi},
        hEqTm = mkEq[vHit, v0V]; hEq = ASSUME[hEqTm];
        v0x = EQMP[HOL`Equal`APTHM[hEq, xV], hVx];
        intervalX = EQMP[HOL`Equal`APTHM[hV0Eq, xV], v0x];
        intervalBody = EQMP[unfoldOpenInterval[csetSubOne[cV],
          csetAddOne[cV], xV], intervalX];
        leftLt = HOL`Bool`CONJUNCT1[intervalBody];
        rightLt = HOL`Bool`CONJUNCT2[intervalBody];
        subLeX = HOL`Bool`MP[csetSpecAll[realLtImpLeThm,
          {csetSubOne[cV], xV}], leftLt];
        loLeSub = csetSpecAll[realMinLeLeftThm, {csetSubOne[cV], loRest}];
        loLeX = HOL`Bool`MP[HOL`Bool`MP[csetSpecAll[realLeTransThm,
          {loT, csetSubOne[cV], xV}], loLeSub], subLeX];
        xLeAdd = HOL`Bool`MP[csetSpecAll[realLtImpLeThm,
          {xV, csetAddOne[cV]}], rightLt];
        addLeHi = csetSpecAll[realLeMaxLeftThm, {csetAddOne[cV], hiRest}];
        xLeHi = HOL`Bool`MP[HOL`Bool`MP[csetSpecAll[realLeTransThm,
          {xV, csetAddOne[cV], hiT}], xLeAdd], addLeHi];
        HOL`Bool`CONJ[loLeX, xLeHi]
      ];
      branchRest = Module[{hMemRestTm, hMemRest, restHit, restBounds,
          loRestLeX, xLeHiRest, loLeRest, restLeHi, loLeX, xLeHi},
        hMemRestTm = csetMemTmAt[csetSetTy, vHit, restV];
        hMemRest = ASSUME[hMemRestTm];
        restHit = HOL`Bool`EXISTS[csetFiniteCoverHit[restV, xV], vHit,
          HOL`Bool`CONJ[hMemRest, hVx]];
        restBounds = HOL`Bool`MP[HOL`Bool`SPEC[xV, hRestBound], restHit];
        loRestLeX = HOL`Bool`CONJUNCT1[restBounds];
        xLeHiRest = HOL`Bool`CONJUNCT2[restBounds];
        loLeRest = csetSpecAll[realMinLeRightThm,
          {csetSubOne[cV], loRest}];
        restLeHi = csetSpecAll[realLeMaxRightThm, {csetAddOne[cV], hiRest}];
        loLeX = HOL`Bool`MP[HOL`Bool`MP[csetSpecAll[realLeTransThm,
          {loT, loRest, xV}], loLeRest], loRestLeX];
        xLeHi = HOL`Bool`MP[HOL`Bool`MP[csetSpecAll[realLeTransThm,
          {xV, hiRest, hiT}], xLeHiRest], restLeHi];
        HOL`Bool`CONJ[loLeX, xLeHi]
      ];
      point = HOL`Bool`CHOOSE[vHit, hHit,
        HOL`Bool`DISJCASES[memOpen, branchEq, branchRest]];
      allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hHitTm, point]];
      exHi = HOL`Bool`EXISTS[
        csetExistsTm[mkVar["hiFiniteBound", csetRealTy],
          csetFiniteCoverAll[consT, loT,
            mkVar["hiFiniteBound", csetRealTy]]], hiT, allX];
      exLo = HOL`Bool`EXISTS[csetFiniteCoverBoundExists[consT], loT, exHi];
      chooseC = HOL`Bool`CHOOSE[cV, centerExists, exLo];
      chooseHi = HOL`Bool`CHOOSE[hiRest,
        ASSUME[csetExistsTm[hiRest,
          csetFiniteCoverAll[restV, loRest, hiRest]]], chooseC];
      chooseLo = HOL`Bool`CHOOSE[loRest, restBound, chooseHi];
      body = HOL`Bool`DISCH[hAllTm, chooseLo];
      HOL`Bool`GEN[v0V, HOL`Bool`GEN[restV, HOL`Bool`DISCH[ihTm,
        EQMP[HOL`Equal`SYM[HOL`Equal`BETACONV[mkComb[predLam, consT]]],
          body]]]]
    ];

    allVs = HOL`Bool`MP[induction, HOL`Bool`CONJ[base, step]];
    bodyVs = HOL`Bool`GEN[vsV,
      EQMP[HOL`Equal`BETACONV[mkComb[predLam, vsV]],
        HOL`Bool`SPEC[vsV, allVs]]];
    bodyVs
  ];

boundedOfCompactThm =
  Module[{sV, hCompactTm, hCompact, openCompact, finiteCover,
          openFinite, vsV, hListTm, hList, listBody, hMemC, hCovS,
          boundEx, loV, hiV, hBoundTm, hBound, xV, hSxTm, hSx,
          hitX, boundsX, allX, exHi, exLo, folded, chooseHi, chooseLo,
          chooseVs},
    sV = mkVar["SBoundedCompact", csetSetTy];
    hCompactTm = isCompactTm[sV]; hCompact = ASSUME[hCompactTm];
    openCompact = EQMP[unfoldIsCompact[sV], hCompact];
    finiteCover = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[centerCoverTm[], openCompact], centerCoverOpenThm],
      HOL`Bool`SPEC[sV, centerCoverCoversThm]];
    openFinite = EQMP[unfoldSetFiniteSubcover[centerCoverTm[], sV], finiteCover];
    vsV = mkVar["vsBound", csetSetListTy];
    hListTm = setListSubcoverTm[centerCoverTm[], sV, vsV];
    hList = ASSUME[hListTm];
    listBody = EQMP[unfoldSetListSubcover[centerCoverTm[], sV, vsV], hList];
    hMemC = HOL`Bool`CONJUNCT1[listBody];
    hCovS = HOL`Bool`CONJUNCT2[listBody];
    boundEx = HOL`Bool`MP[HOL`Bool`SPEC[vsV,
      boundedOfFiniteIntervalCoverThm], hMemC];
    loV = mkVar["loBoundedCompact", csetRealTy];
    hiV = mkVar["hiBoundedCompact", csetRealTy];
    hBoundTm = csetFiniteCoverAll[vsV, loV, hiV];
    hBound = ASSUME[hBoundTm];
    xV = mkVar["xBoundedCompact", csetRealTy];
    hSxTm = csetSetApp[sV, xV]; hSx = ASSUME[hSxTm];
    hitX = HOL`Bool`MP[HOL`Bool`SPEC[xV, hCovS], hSx];
    boundsX = HOL`Bool`MP[HOL`Bool`SPEC[xV, hBound], hitX];
    allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hSxTm, boundsX]];
    exHi = HOL`Bool`EXISTS[
      csetExistsTm[mkVar["hiCset", csetRealTy],
        csetSetBoundedAll[sV, loV, mkVar["hiCset", csetRealTy]]],
      hiV, allX];
    exLo = HOL`Bool`EXISTS[concl[unfoldSetBounded[sV]][[2]], loV, exHi];
    folded = EQMP[HOL`Equal`SYM[unfoldSetBounded[sV]], exLo];
    chooseHi = HOL`Bool`CHOOSE[hiV,
      ASSUME[csetExistsTm[hiV, hBoundTm]], folded];
    chooseLo = HOL`Bool`CHOOSE[loV, boundEx, chooseHi];
    chooseVs = HOL`Bool`CHOOSE[vsV, openFinite, chooseLo];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hCompactTm, chooseVs]]
  ];

End[];
EndPackage[];
