(* M8.2 / stdlib/Real/Compact.wl - compactness principles for real sequences. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`Arith`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

seqBoundedDefThm::usage = "seqBoundedDefThm - |- seqBounded = (lambda u. exists lo. exists hi. forall n. realLe lo (u n) /\\ realLe (u n) hi).";
seqBoundedConst::usage = "seqBoundedConst[] - seqBounded : (num -> real) -> bool.";
seqBoundedTm::usage = "seqBoundedTm[u] - builds seqBounded u.";
unfoldSeqBounded::usage = "unfoldSeqBounded[u] - proves the beta-reduced seqBounded definition at u.";

hasConvergentSubseqDefThm::usage = "hasConvergentSubseqDefThm - |- hasConvergentSubseq = (lambda u l. exists phi. subseqIndex phi /\\ tendsto (subsequence u phi) l).";
hasConvergentSubseqConst::usage = "hasConvergentSubseqConst[] - hasConvergentSubseq : (num -> real) -> real -> bool.";
hasConvergentSubseqTm::usage = "hasConvergentSubseqTm[u, l] - builds hasConvergentSubseq u l.";
unfoldHasConvergentSubseq::usage = "unfoldHasConvergentSubseq[u, l] - proves the beta-reduced hasConvergentSubseq definition at u and l.";

bwSequentialThm::usage = "bwSequentialThm - |- forall u. seqBounded u ==> exists l. hasConvergentSubseq u l.";

listInfiniteDefThm::usage = "listInfiniteDefThm - |- listInfinite = (lambda S. forall xs. exists x. S x /\\ ~(MEM x xs)).";
listInfiniteConst::usage = "listInfiniteConst[] - listInfinite : (real -> bool) -> bool.";
listInfiniteTm::usage = "listInfiniteTm[S] - builds listInfinite S.";
unfoldListInfinite::usage = "unfoldListInfinite[S] - proves the beta-reduced listInfinite definition at S.";

setBoundedDefThm::usage = "setBoundedDefThm - |- setBounded = (lambda S. exists lo. exists hi. forall x. S x ==> realLe lo x /\\ realLe x hi).";
setBoundedConst::usage = "setBoundedConst[] - setBounded : (real -> bool) -> bool.";
setBoundedTm::usage = "setBoundedTm[S] - builds setBounded S.";
unfoldSetBounded::usage = "unfoldSetBounded[S] - proves the beta-reduced setBounded definition at S.";

distDefThm::usage = "distDefThm - |- dist = (lambda y x. realAbs (realAdd y (realNeg x))).";
distConst::usage = "distConst[] - dist : real -> real -> real.";
distTm::usage = "distTm[y, x] - builds dist y x.";
unfoldDist::usage = "unfoldDist[y, x] - proves the beta-reduced dist definition at y and x.";

accumulationPointDefThm::usage = "accumulationPointDefThm - |- accumulationPoint = (lambda S x. forall eps. 0 < eps ==> exists y. S y /\\ ~(y = x) /\\ dist y x < eps).";
accumulationPointConst::usage = "accumulationPointConst[] - accumulationPoint : (real -> bool) -> real -> bool.";
accumulationPointTm::usage = "accumulationPointTm[S, x] - builds accumulationPoint S x.";
unfoldAccumulationPoint::usage = "unfoldAccumulationPoint[S, x] - proves the beta-reduced accumulationPoint definition at S and x.";

openIntervalDefThm::usage = "openIntervalDefThm - |- openInterval = (lambda left right x. realLt left x /\\ realLt x right).";
openIntervalConst::usage = "openIntervalConst[] - openInterval : real -> real -> real -> bool.";
openIntervalTm::usage = "openIntervalTm[left, right, x] - builds openInterval left right x.";
unfoldOpenInterval::usage = "unfoldOpenInterval[left, right, x] - proves the beta-reduced openInterval definition at left, right, and x.";
openIntervalMemThm::usage = "openIntervalMemThm - |- forall left right x. openInterval left right x = (realLt left x /\\ realLt x right).";

closedIntervalDefThm::usage = "closedIntervalDefThm - |- closedInterval = (lambda left right x. realLe left x /\\ realLe x right).";
closedIntervalConst::usage = "closedIntervalConst[] - closedInterval : real -> real -> real -> bool.";
closedIntervalTm::usage = "closedIntervalTm[left, right, x] - builds closedInterval left right x.";
unfoldClosedInterval::usage = "unfoldClosedInterval[left, right, x] - proves the beta-reduced closedInterval definition at left, right, and x.";
closedIntervalMemThm::usage = "closedIntervalMemThm - |- forall left right x. closedInterval left right x = (realLe left x /\\ realLe x right).";

isOpenDefThm::usage = "isOpenDefThm - |- isOpen = (lambda U. forall x. U x ==> exists left right. realLt left x /\\ realLt x right /\\ forall y. openInterval left right y ==> U y).";
isOpenConst::usage = "isOpenConst[] - isOpen : (real -> bool) -> bool.";
isOpenTm::usage = "isOpenTm[U] - builds isOpen U.";
unfoldIsOpen::usage = "unfoldIsOpen[U] - proves the beta-reduced isOpen definition at U.";

coversDefThm::usage = "coversDefThm - |- covers = (lambda U S. forall x. S x ==> exists i. U i x).";
coversConst::usage = "coversConst[] - covers : (iota -> real -> bool) -> (real -> bool) -> bool.";
coversTm::usage = "coversTm[U, S] - builds covers U S.";
unfoldCovers::usage = "unfoldCovers[U, S] - proves the beta-reduced covers definition at U and S.";

listSubcoverDefThm::usage = "listSubcoverDefThm - |- listSubcover = (lambda U S js. forall x. S x ==> exists i. MEM i js /\\ U i x).";
listSubcoverConst::usage = "listSubcoverConst[] - listSubcover : (iota -> real -> bool) -> (real -> bool) -> iota list -> bool.";
listSubcoverTm::usage = "listSubcoverTm[U, S, js] - builds listSubcover U S js.";
unfoldListSubcover::usage = "unfoldListSubcover[U, S, js] - proves the beta-reduced listSubcover definition at U, S, and js.";

finiteSubcoverDefThm::usage = "finiteSubcoverDefThm - |- finiteSubcover = (lambda U S. exists js. listSubcover U S js).";
finiteSubcoverConst::usage = "finiteSubcoverConst[] - finiteSubcover : (iota -> real -> bool) -> (real -> bool) -> bool.";
finiteSubcoverTm::usage = "finiteSubcoverTm[U, S] - builds finiteSubcover U S.";
unfoldFiniteSubcover::usage = "unfoldFiniteSubcover[U, S] - proves the beta-reduced finiteSubcover definition at U and S.";

midpointDefThm::usage = "midpointDefThm - |- midpoint = (lambda a b. realMul (realAdd a b) (realInv 2)).";
midpointConst::usage = "midpointConst[] - midpoint : real -> real -> real.";
midpointTm::usage = "midpointTm[a, b] - builds midpoint a b.";
unfoldMidpoint::usage = "unfoldMidpoint[a, b] - proves the beta-reduced midpoint definition at a and b.";
leftLeMidpointThm::usage = "leftLeMidpointThm - |- forall a b. realLe a b ==> realLe a (midpoint a b).";
midpointLeRightThm::usage = "midpointLeRightThm - |- forall a b. realLe a b ==> realLe (midpoint a b) b.";
leftLtMidpointThm::usage = "leftLtMidpointThm - |- forall a b. realLt a b ==> realLt a (midpoint a b).";
midpointLtRightThm::usage = "midpointLtRightThm - |- forall a b. realLt a b ==> realLt (midpoint a b) b.";
midpointSubLeftThm::usage = "midpointSubLeftThm - |- forall a b. midpoint a b - a = (b - a) * inv 2.";
rightSubMidpointThm::usage = "rightSubMidpointThm - |- forall a b. b - midpoint a b = (b - a) * inv 2.";

memAppendLeftThm::usage = "memAppendLeftThm - |- forall i js ks. MEM i js ==> MEM i (APPEND js ks).";
memAppendRightThm::usage = "memAppendRightThm - |- forall i js ks. MEM i ks ==> MEM i (APPEND js ks).";

noFiniteSubcoverDefThm::usage = "noFiniteSubcoverDefThm - |- noFiniteSubcover = (lambda U a b. ~(finiteSubcover U (closedInterval a b))).";
noFiniteSubcoverConst::usage = "noFiniteSubcoverConst[] - noFiniteSubcover : (iota -> real -> bool) -> real -> real -> bool.";
noFiniteSubcoverTm::usage = "noFiniteSubcoverTm[U, a, b] - builds noFiniteSubcover U a b.";
unfoldNoFiniteSubcover::usage = "unfoldNoFiniteSubcover[U, a, b] - proves the beta-reduced noFiniteSubcover definition at U, a, and b.";

combineHalfSubcoverThm::usage = "combineHalfSubcoverThm - combines list subcovers of adjacent closed intervals by APPEND.";
finiteSubcoverOfHalvesThm::usage = "finiteSubcoverOfHalvesThm - combines finite subcovers of adjacent closed intervals.";
rightHalfBadThm::usage = "rightHalfBadThm - if [a,b] has no finite subcover and [a,m] has one, then [m,b] has no finite subcover.";

badIntervalDefThm::usage = "badIntervalDefThm - |- badInterval = (lambda U a b. realLe a b /\\ noFiniteSubcover U a b).";
badIntervalConst::usage = "badIntervalConst[] - badInterval : (iota -> real -> bool) -> real -> real -> bool.";
badIntervalTm::usage = "badIntervalTm[U, a, b] - builds badInterval U a b.";
unfoldBadInterval::usage = "unfoldBadInterval[U, a, b] - proves the beta-reduced badInterval definition at U, a, and b.";

stepIntervalDefThm::usage = "stepIntervalDefThm - bisection step choosing the right half when the left half has a finite subcover.";
stepIntervalConst::usage = "stepIntervalConst[] - stepInterval : (iota -> real -> bool) -> real # real -> real # real.";
stepIntervalTm::usage = "stepIntervalTm[U, p] - builds stepInterval U p.";
unfoldStepInterval::usage = "unfoldStepInterval[U, p] - proves the beta-reduced stepInterval definition at U and p.";

bisectIntervalDefThm::usage = "bisectIntervalDefThm - epsilon-selected num recursion for repeatedly bisecting a bad interval.";
bisectIntervalConst::usage = "bisectIntervalConst[] - bisectInterval : (iota -> real -> bool) -> real -> real -> num -> real # real.";
bisectIntervalTm::usage = "bisectIntervalTm[U, left, right] - builds bisectInterval U left right.";
unfoldBisectInterval::usage = "unfoldBisectInterval[U, left, right] - proves the deep-beta-reduced bisectInterval definition at U, left, and right.";
bisectRecSpecThm::usage = "bisectRecSpecThm - |- forall U left right. bisectInterval U left right 0 = (left,right) /\\ forall n. bisectInterval U left right (SUC n) = stepInterval U (bisectInterval U left right n).";

lowerDefThm::usage = "lowerDefThm - |- lower = (lambda U left right n. FST (bisectInterval U left right n)).";
lowerConst::usage = "lowerConst[] - lower : (iota -> real -> bool) -> real -> real -> num -> real.";
lowerTm::usage = "lowerTm[U, left, right] - builds lower U left right.";
unfoldLower::usage = "unfoldLower[U, left, right, n] - proves the beta-reduced lower definition at U, left, right, and n.";
upperDefThm::usage = "upperDefThm - |- upper = (lambda U left right n. SND (bisectInterval U left right n)).";
upperConst::usage = "upperConst[] - upper : (iota -> real -> bool) -> real -> real -> num -> real.";
upperTm::usage = "upperTm[U, left, right] - builds upper U left right.";
unfoldUpper::usage = "unfoldUpper[U, left, right, n] - proves the beta-reduced upper definition at U, left, right, and n.";

lowerZeroThm::usage = "lowerZeroThm - |- forall U left right. lower U left right 0 = left.";
upperZeroThm::usage = "upperZeroThm - |- forall U left right. upper U left right 0 = right.";
lowerSuccRightThm::usage = "lowerSuccRightThm - finite left half implies lower at SUC is the midpoint.";
upperSuccRightThm::usage = "upperSuccRightThm - finite left half implies upper at SUC is unchanged.";
lowerSuccLeftThm::usage = "lowerSuccLeftThm - non-finite left half implies lower at SUC is unchanged.";
upperSuccLeftThm::usage = "upperSuccLeftThm - non-finite left half implies upper at SUC is the midpoint.";
badIntervalsThm::usage = "badIntervalsThm - every interval produced by bisection is bad when the initial interval is bad.";
intervalOrderThm::usage = "intervalOrderThm - bisection lower endpoints stay below upper endpoints.";
lowerStepLeThm::usage = "lowerStepLeThm - bisection lower endpoint sequence is stepwise monotone.";
upperStepLeThm::usage = "upperStepLeThm - bisection upper endpoint sequence is stepwise antitone.";
lowerMonoThm::usage = "lowerMonoThm - bisection lower endpoint sequence is monotone.";
upperAntitoneThm::usage = "upperAntitoneThm - bisection upper endpoint sequence is antitone.";
nestedIntervalsThm::usage = "nestedIntervalsThm - bisection lower/upper sequences form nestedIntervals.";
intervalLengthDefThm::usage = "intervalLengthDefThm - |- length = (lambda U left right n. upper U left right n + -(lower U left right n)).";
intervalLengthConst::usage = "intervalLengthConst[] - length : (iota -> real -> bool) -> real -> real -> num -> real.";
intervalLengthTm::usage = "intervalLengthTm[U, left, right] - builds length U left right.";
compactLengthAt::usage = "compactLengthAt[U, left, right, n] - builds length U left right n.";
unfoldIntervalLength::usage = "unfoldIntervalLength[U, left, right, n] - proves the beta-reduced length definition at U, left, right, and n.";
lengthZeroThm::usage = "lengthZeroThm - |- forall U left right. length U left right 0 = right - left.";
lengthSuccThm::usage = "lengthSuccThm - |- forall U left right n. length U left right (SUC n) = length U left right n * inv 2.";
lengthInvariantThm::usage = "lengthInvariantThm - |- forall U left right n. dyadic n * length U left right n = right - left.";
lengthFormulaThm::usage = "lengthFormulaThm - |- forall U left right n. length U left right n = (right - left) * inv (dyadic n).";
lengthNonnegThm::usage = "lengthNonnegThm - nonnegative interval lengths under the bad bisection hypotheses.";
lengthDecreaseThm::usage = "lengthDecreaseThm - bisection interval lengths decrease along the sequence.";
lengthsToZeroThm::usage = "lengthsToZeroThm - bad bisection interval lengths tend to zero.";

freshListDefThm::usage = "freshListDefThm - epsilon-selected num recursion for fresh finite prefixes.";
freshListConst::usage = "freshListConst[] - freshList : (real -> bool) -> num -> real list.";
freshListTm::usage = "freshListTm[S] - builds freshList S.";
unfoldFreshList::usage = "unfoldFreshList[S] - proves the deep-beta-reduced freshList definition at S.";

freshSeqDefThm::usage = "freshSeqDefThm - freshSeq S n is the selected fresh point for freshList S n.";
freshSeqConst::usage = "freshSeqConst[] - freshSeq : (real -> bool) -> num -> real.";
freshSeqTm::usage = "freshSeqTm[S] - builds freshSeq S.";
unfoldFreshSeq::usage = "unfoldFreshSeq[S, n] - proves the beta-reduced freshSeq definition at S and n.";

freshListRecSpecThm::usage = "freshListRecSpecThm - |- forall S. freshList S 0 = NIL /\\ forall n. freshList S (SUC n) = CONS (freshSeq S n) (freshList S n).";
freshSeqMemThm::usage = "freshSeqMemThm - |- forall S. listInfinite S ==> forall n. S (freshSeq S n).";
freshSeqNotMemThm::usage = "freshSeqNotMemThm - |- forall S. listInfinite S ==> forall n. ~(MEM (freshSeq S n) (freshList S n)).";
freshSeqMemFreshListOfLtThm::usage = "freshSeqMemFreshListOfLtThm - |- forall S m n. m < n ==> MEM (freshSeq S m) (freshList S n).";
freshSeqNeOfLtThm::usage = "freshSeqNeOfLtThm - |- forall S. listInfinite S ==> forall m n. m < n ==> ~(freshSeq S n = freshSeq S m).";
freshSeqBoundedThm::usage = "freshSeqBoundedThm - |- forall S. listInfinite S ==> setBounded S ==> seqBounded (freshSeq S).";
freshLimitIsAccumThm::usage = "freshLimitIsAccumThm - |- forall S phi l. listInfinite S ==> subseqIndex phi ==> tendsto (subsequence (freshSeq S) phi) l ==> accumulationPoint S l.";
accumulationPrincipleThm::usage = "accumulationPrincipleThm - |- forall S. setBounded S ==> listInfinite S ==> exists x. accumulationPoint S x.";

Begin["`Private`"];

compactSeqTy = tyFun[numTy, realTy];
compactNumFunTy = tyFun[numTy, numTy];
compactSetTy = tyFun[realTy, boolTy];
compactRealListTy = HOL`Stdlib`List`listTy[realTy];
iotaTy = mkVarType["iota"];
compactIotaListTy = HOL`Stdlib`List`listTy[iotaTy];
seqBoundedTy = tyFun[compactSeqTy, boolTy];
hasConvergentSubseqTy = tyFun[compactSeqTy, tyFun[realTy, boolTy]];
listInfiniteTy = tyFun[compactSetTy, boolTy];
setBoundedTy = tyFun[compactSetTy, boolTy];
distTy = tyFun[realTy, tyFun[realTy, realTy]];
accumulationPointTy = tyFun[compactSetTy, tyFun[realTy, boolTy]];
openIntervalTy = tyFun[realTy, tyFun[realTy, compactSetTy]];
closedIntervalTy = openIntervalTy;
isOpenTy = tyFun[compactSetTy, boolTy];
compactCoverTyAt[ty_] := tyFun[ty, compactSetTy];
compactCoverTy = compactCoverTyAt[iotaTy];
compactCoversTyAt[ty_] := tyFun[compactCoverTyAt[ty], tyFun[compactSetTy, boolTy]];
coversTy = compactCoversTyAt[iotaTy];
compactListSubcoverTyAt[ty_] := tyFun[compactCoverTyAt[ty],
  tyFun[compactSetTy, tyFun[HOL`Stdlib`List`listTy[ty], boolTy]]];
listSubcoverTy = compactListSubcoverTyAt[iotaTy];
finiteSubcoverTy = coversTy;
freshListTy = tyFun[compactSetTy, tyFun[numTy, compactRealListTy]];
freshSeqTy = tyFun[compactSetTy, tyFun[numTy, realTy]];

compactRealLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqLeft], eqRight];

compactOrTm[pT_, qT_] :=
  mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], pT], qT];

compactSpecAll[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

compactBetaClean[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

compactForallList[vs_List, body_] :=
  Fold[Function[{acc, v}, forallTm[v, acc]], body, Reverse[vs]];

compactImpList[hs_List, body_] :=
  Fold[Function[{acc, h}, impTm[h, acc]], body, Reverse[hs]];

compactNatLt[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], aT], bT];
compactNatLe[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], aT], bT];

compactSeqBoundedAll[uT_, loT_, hiT_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    forallTm[nV, conjTm[
      realLeTm[loT, mkComb[uT, nV]],
      realLeTm[mkComb[uT, nV], hiT]]]
  ];

compactSeqBoundedBody[uT_] :=
  Module[{loV, hiV},
    loV = mkVar["lo", realTy]; hiV = mkVar["hi", realTy];
    existsTm[loV, existsTm[hiV, compactSeqBoundedAll[uT, loV, hiV]]]
  ];

compactHasConvergentSubseqBody[uT_, lT_] :=
  Module[{phiV, subSeq},
    phiV = mkVar["phi", compactNumFunTy];
    subSeq = subsequenceTm[uT, phiV];
    existsTm[phiV, conjTm[subseqIndexTm[phiV], tendstoTm[subSeq, lT]]]
  ];

compactBwGoal[uT_] :=
  Module[{lV},
    lV = mkVar["l", realTy];
    existsTm[lV, hasConvergentSubseqTm[uT, lV]]
  ];

compactSelectTm[ty_, predT_] :=
  mkComb[mkConst["@", tyFun[tyFun[ty, boolTy], ty]], predT];

compactNilReal[] := mkConst["NIL", compactRealListTy];
compactConsReal[] := mkConst["CONS",
  tyFun[realTy, tyFun[compactRealListTy, compactRealListTy]]];
compactMemRealConst[] := mkConst["MEM",
  tyFun[realTy, tyFun[compactRealListTy, boolTy]]];
compactMemTm[xT_, xsT_] := mkComb[mkComb[compactMemRealConst[], xT], xsT];
compactMemConstAt[ty_] := mkConst["MEM",
  tyFun[ty, tyFun[HOL`Stdlib`List`listTy[ty], boolTy]]];
compactMemTmAt[ty_, xT_, xsT_] := mkComb[mkComb[compactMemConstAt[ty], xT], xsT];
compactNotTm[pT_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], pT];

compactRealAbs[xT_] := mkComb[realAbsConst[], xT];

compactListInst[th_] := HOL`Kernel`INSTTYPE[{mkVarType["A"] -> realTy}, th];

compactMemConsEq[xT_, yT_, xsT_] :=
  compactSpecAll[compactListInst[HOL`Stdlib`List`memConsThm], {xT, yT, xsT}];

compactMemNilEq[xT_] :=
  HOL`Bool`SPEC[xT, compactListInst[HOL`Stdlib`List`memNilThm]];

compactMemCong[eqHead_, eqList_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[compactMemRealConst[], eqHead], eqList];

compactConsCong[eqHead_, eqTail_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[compactConsReal[], eqHead], eqTail];

compactRealLtCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], eqLeft], eqRight];

compactFreshPred[S_, xsT_] :=
  Module[{xFr},
    xFr = mkVar["xFr", realTy];
    mkAbs[xFr, conjTm[mkComb[S, xFr], compactNotTm[compactMemTm[xFr, xsT]]]]
  ];

compactFreshChoice[S_, xsT_] := compactSelectTm[realTy, compactFreshPred[S, xsT]];

compactFreshStepFun[S_] :=
  Module[{xsStep},
    xsStep = mkVar["xsStep", compactRealListTy];
    mkAbs[xsStep, mkComb[mkComb[compactConsReal[], compactFreshChoice[S, xsStep]], xsStep]]
  ];

compactFreshListRecPred[S_] :=
  Module[{gRec, nRec, fT},
    gRec = mkVar["gRecFresh", tyFun[numTy, compactRealListTy]];
    nRec = mkVar["nRecFresh", numTy];
    fT = compactFreshStepFun[S];
    mkAbs[gRec, conjTm[mkEq[mkComb[gRec, zeroN[]], compactNilReal[]],
      forallTm[nRec, mkEq[mkComb[gRec, sucT[nRec]], mkComb[fT, mkComb[gRec, nRec]]]]]]
  ];

compactListInfiniteBody[S_] :=
  Module[{xsV, xV},
    xsV = mkVar["xs", compactRealListTy]; xV = mkVar["x", realTy];
    forallTm[xsV, existsTm[xV,
      conjTm[mkComb[S, xV], compactNotTm[compactMemTm[xV, xsV]]]]]
  ];

compactSetBoundedAll[S_, loT_, hiT_] :=
  Module[{xV},
    xV = mkVar["x", realTy];
    forallTm[xV, impTm[mkComb[S, xV],
      conjTm[realLeTm[loT, xV], realLeTm[xV, hiT]]]]
  ];

compactSetBoundedBody[S_] :=
  Module[{loV, hiV},
    loV = mkVar["lo", realTy]; hiV = mkVar["hi", realTy];
    existsTm[loV, existsTm[hiV, compactSetBoundedAll[S, loV, hiV]]]
  ];

compactDistBody[yT_, xT_] := compactRealAbs[realAddTm[yT, realNegTm[xT]]];

compactAccumulationBody[S_, xT_] :=
  Module[{epsV, yV},
    epsV = mkVar["eps", realTy]; yV = mkVar["y", realTy];
    forallTm[epsV, impTm[realLtTm[zeroRealTm[], epsV],
      existsTm[yV, conjTm[mkComb[S, yV],
        conjTm[compactNotTm[mkEq[yV, xT]],
          realLtTm[distTm[yV, xT], epsV]]]]]]
  ];

compactOpenIntervalBody[leftT_, rightT_, xT_] :=
  conjTm[realLtTm[leftT, xT], realLtTm[xT, rightT]];

compactClosedIntervalBody[leftT_, rightT_, xT_] :=
  conjTm[realLeTm[leftT, xT], realLeTm[xT, rightT]];

compactIsOpenBody[uT_] :=
  Module[{xV, leftV, rightV, yV},
    xV = mkVar["x", realTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; yV = mkVar["y", realTy];
    forallTm[xV, impTm[mkComb[uT, xV],
      existsTm[leftV, existsTm[rightV,
        conjTm[realLtTm[leftV, xV],
          conjTm[realLtTm[xV, rightV],
            forallTm[yV, impTm[openIntervalTm[leftV, rightV, yV],
              mkComb[uT, yV]]]]]]]]]
  ];

compactCoverIndexTy[uT_] := typeOf[uT][[2, 1]];
compactCoverApp[uT_, iT_, xT_] := mkComb[mkComb[uT, iT], xT];

compactCoversBodyAt[ty_, uT_, sT_] :=
  Module[{xV, iV},
    xV = mkVar["x", realTy]; iV = mkVar["i", ty];
    forallTm[xV, impTm[mkComb[sT, xV],
      existsTm[iV, compactCoverApp[uT, iV, xV]]]]
  ];

compactListSubcoverBodyAt[ty_, uT_, sT_, jsT_] :=
  Module[{xV, iV},
    xV = mkVar["x", realTy]; iV = mkVar["i", ty];
    forallTm[xV, impTm[mkComb[sT, xV],
      existsTm[iV, conjTm[compactMemTmAt[ty, iV, jsT],
        compactCoverApp[uT, iV, xV]]]]]
  ];

compactFiniteSubcoverBodyAt[ty_, uT_, sT_] :=
  Module[{jsV},
    jsV = mkVar["js", HOL`Stdlib`List`listTy[ty]];
    existsTm[jsV, listSubcoverTm[uT, sT, jsV]]
  ];

compactSubsequenceAppEq[uT_, phiT_, nT_] :=
  Module[{unf, app},
    unf = unfoldSubsequence[uT, phiT];
    app = HOL`Equal`APTHM[unf, nT];
    TRANS[app, HOL`Equal`BETACONV[concl[app][[2]]]]
  ];

seqBoundedDefThm =
  Module[{uV},
    uV = mkVar["u", compactSeqTy];
    newDefinition[mkEq[mkVar["seqBounded", seqBoundedTy],
      mkAbs[uV, compactSeqBoundedBody[uV]]]]
  ];

seqBoundedConst[] := mkConst["seqBounded", seqBoundedTy];
seqBoundedTm[uT_] := mkComb[seqBoundedConst[], uT];

unfoldSeqBounded[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[seqBoundedDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

hasConvergentSubseqDefThm =
  Module[{uV, lV},
    uV = mkVar["u", compactSeqTy]; lV = mkVar["l", realTy];
    newDefinition[mkEq[mkVar["hasConvergentSubseq", hasConvergentSubseqTy],
      mkAbs[uV, mkAbs[lV, compactHasConvergentSubseqBody[uV, lV]]]]]
  ];

hasConvergentSubseqConst[] := mkConst["hasConvergentSubseq", hasConvergentSubseqTy];
hasConvergentSubseqTm[uT_, lT_] := mkComb[mkComb[hasConvergentSubseqConst[], uT], lT];

unfoldHasConvergentSubseq[uT_, lT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[hasConvergentSubseqDefThm, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, lT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

listInfiniteDefThm =
  Module[{sV},
    sV = mkVar["S", compactSetTy];
    newDefinition[mkEq[mkVar["listInfinite", listInfiniteTy],
      mkAbs[sV, compactListInfiniteBody[sV]]]]
  ];

listInfiniteConst[] := mkConst["listInfinite", listInfiniteTy];
listInfiniteTm[sT_] := mkComb[listInfiniteConst[], sT];

unfoldListInfinite[sT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[listInfiniteDefThm, sT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

setBoundedDefThm =
  Module[{sV},
    sV = mkVar["S", compactSetTy];
    newDefinition[mkEq[mkVar["setBounded", setBoundedTy],
      mkAbs[sV, compactSetBoundedBody[sV]]]]
  ];

setBoundedConst[] := mkConst["setBounded", setBoundedTy];
setBoundedTm[sT_] := mkComb[setBoundedConst[], sT];

unfoldSetBounded[sT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[setBoundedDefThm, sT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

distDefThm =
  Module[{yV, xV},
    yV = mkVar["y", realTy]; xV = mkVar["x", realTy];
    newDefinition[mkEq[mkVar["dist", distTy],
      mkAbs[yV, mkAbs[xV, compactDistBody[yV, xV]]]]]
  ];

distConst[] := mkConst["dist", distTy];
distTm[yT_, xT_] := mkComb[mkComb[distConst[], yT], xT];

unfoldDist[yT_, xT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[distDefThm, yT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, xT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

accumulationPointDefThm =
  Module[{sV, xV},
    sV = mkVar["S", compactSetTy]; xV = mkVar["x", realTy];
    newDefinition[mkEq[mkVar["accumulationPoint", accumulationPointTy],
      mkAbs[sV, mkAbs[xV, compactAccumulationBody[sV, xV]]]]]
  ];

accumulationPointConst[] := mkConst["accumulationPoint", accumulationPointTy];
accumulationPointTm[sT_, xT_] := mkComb[mkComb[accumulationPointConst[], sT], xT];

unfoldAccumulationPoint[sT_, xT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[accumulationPointDefThm, sT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, xT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

openIntervalDefThm =
  Module[{leftV, rightV, xV},
    leftV = mkVar["left", realTy]; rightV = mkVar["right", realTy];
    xV = mkVar["x", realTy];
    newDefinition[mkEq[mkVar["openInterval", openIntervalTy],
      mkAbs[leftV, mkAbs[rightV, mkAbs[xV,
        compactOpenIntervalBody[leftV, rightV, xV]]]]]]
  ];

openIntervalConst[] := mkConst["openInterval", openIntervalTy];
openIntervalTm[leftT_, rightT_, xT_] :=
  mkComb[mkComb[mkComb[openIntervalConst[], leftT], rightT], xT];

unfoldOpenInterval[leftT_, rightT_, xT_] :=
  Module[{s1, s1b, s2, s2b, s3},
    s1 = HOL`Equal`APTHM[openIntervalDefThm, leftT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, rightT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, xT];
    TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]]
  ];

openIntervalMemThm =
  Module[{leftV, rightV, xV},
    leftV = mkVar["left", realTy]; rightV = mkVar["right", realTy];
    xV = mkVar["x", realTy];
    HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[xV,
      unfoldOpenInterval[leftV, rightV, xV]]]]
  ];

closedIntervalDefThm =
  Module[{leftV, rightV, xV},
    leftV = mkVar["left", realTy]; rightV = mkVar["right", realTy];
    xV = mkVar["x", realTy];
    newDefinition[mkEq[mkVar["closedInterval", closedIntervalTy],
      mkAbs[leftV, mkAbs[rightV, mkAbs[xV,
        compactClosedIntervalBody[leftV, rightV, xV]]]]]]
  ];

closedIntervalConst[] := mkConst["closedInterval", closedIntervalTy];
closedIntervalTm[leftT_, rightT_, xT_] :=
  mkComb[mkComb[mkComb[closedIntervalConst[], leftT], rightT], xT];

unfoldClosedInterval[leftT_, rightT_, xT_] :=
  Module[{s1, s1b, s2, s2b, s3},
    s1 = HOL`Equal`APTHM[closedIntervalDefThm, leftT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, rightT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, xT];
    TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]]
  ];

closedIntervalMemThm =
  Module[{leftV, rightV, xV},
    leftV = mkVar["left", realTy]; rightV = mkVar["right", realTy];
    xV = mkVar["x", realTy];
    HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[xV,
      unfoldClosedInterval[leftV, rightV, xV]]]]
  ];

isOpenDefThm =
  Module[{uV},
    uV = mkVar["U", compactSetTy];
    newDefinition[mkEq[mkVar["isOpen", isOpenTy],
      mkAbs[uV, compactIsOpenBody[uV]]]]
  ];

isOpenConst[] := mkConst["isOpen", isOpenTy];
isOpenTm[uT_] := mkComb[isOpenConst[], uT];

unfoldIsOpen[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[isOpenDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

coversDefThm =
  Module[{uV, sV},
    uV = mkVar["U", compactCoverTy]; sV = mkVar["S", compactSetTy];
    newDefinition[mkEq[mkVar["covers", coversTy],
      mkAbs[uV, mkAbs[sV, compactCoversBodyAt[iotaTy, uV, sV]]]]]
  ];

coversConst[] := mkConst["covers", coversTy];
compactCoversConstAt[ty_] := mkConst["covers", compactCoversTyAt[ty]];
coversTm[uT_, sT_] := mkComb[mkComb[compactCoversConstAt[compactCoverIndexTy[uT]], uT], sT];

unfoldCovers[uT_, sT_] :=
  Module[{def, s1, s1b, s2},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, coversDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, sT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

listSubcoverDefThm =
  Module[{uV, sV, jsV},
    uV = mkVar["U", compactCoverTy]; sV = mkVar["S", compactSetTy];
    jsV = mkVar["js", compactIotaListTy];
    newDefinition[mkEq[mkVar["listSubcover", listSubcoverTy],
      mkAbs[uV, mkAbs[sV, mkAbs[jsV,
        compactListSubcoverBodyAt[iotaTy, uV, sV, jsV]]]]]]
  ];

listSubcoverConst[] := mkConst["listSubcover", listSubcoverTy];
compactListSubcoverConstAt[ty_] := mkConst["listSubcover", compactListSubcoverTyAt[ty]];
listSubcoverTm[uT_, sT_, jsT_] :=
  mkComb[mkComb[mkComb[compactListSubcoverConstAt[compactCoverIndexTy[uT]], uT], sT], jsT];

unfoldListSubcover[uT_, sT_, jsT_] :=
  Module[{def, s1, s1b, s2, s2b, s3},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, listSubcoverDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, sT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, jsT];
    TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]]
  ];

finiteSubcoverDefThm =
  Module[{uV, sV},
    uV = mkVar["U", compactCoverTy]; sV = mkVar["S", compactSetTy];
    newDefinition[mkEq[mkVar["finiteSubcover", finiteSubcoverTy],
      mkAbs[uV, mkAbs[sV, compactFiniteSubcoverBodyAt[iotaTy, uV, sV]]]]]
  ];

finiteSubcoverConst[] := mkConst["finiteSubcover", finiteSubcoverTy];
compactFiniteSubcoverConstAt[ty_] := mkConst["finiteSubcover", compactCoversTyAt[ty]];
finiteSubcoverTm[uT_, sT_] :=
  mkComb[mkComb[compactFiniteSubcoverConstAt[compactCoverIndexTy[uT]], uT], sT];

unfoldFiniteSubcover[uT_, sT_] :=
  Module[{def, s1, s1b, s2},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, finiteSubcoverDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, sT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

freshListDefThm =
  Module[{sV},
    sV = mkVar["S", compactSetTy];
    newDefinition[mkEq[mkVar["freshList", freshListTy],
      mkAbs[sV, compactSelectTm[tyFun[numTy, compactRealListTy],
        compactFreshListRecPred[sV]]]]]
  ];

freshListConst[] := mkConst["freshList", freshListTy];
freshListTm[sT_] := mkComb[freshListConst[], sT];

unfoldFreshList[sT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[freshListDefThm, sT];
    compactBetaClean[TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]]
  ];

freshSeqDefThm =
  Module[{sV, nV},
    sV = mkVar["S", compactSetTy]; nV = mkVar["n", numTy];
    newDefinition[mkEq[mkVar["freshSeq", freshSeqTy],
      mkAbs[sV, mkAbs[nV, compactFreshChoice[sV, mkComb[freshListTm[sV], nV]]]]]]
  ];

freshSeqConst[] := mkConst["freshSeq", freshSeqTy];
freshSeqTm[sT_] := mkComb[freshSeqConst[], sT];

unfoldFreshSeq[sT_, nT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[freshSeqDefThm, sT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, nT];
    compactBetaClean[TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]]
  ];

freshListRecSpecThm =
  Module[{sV, nW, iter, exIter, sat, folded, zeroEq, stepRawAll, stepRaw,
          seqEq, consEq, step, stepAll},
    sV = mkVar["S", compactSetTy]; nW = mkVar["nW", numTy];
    iter = HOL`Kernel`INSTTYPE[{tyVar["A"] -> compactRealListTy},
      HOL`Stdlib`Num`numIterationThm];
    exIter = compactBetaClean[
      HOL`Bool`SPEC[compactFreshStepFun[sV],
        HOL`Bool`SPEC[compactNilReal[], iter]]];
    sat = HOL`Stdlib`Num`selectOfExists[compactFreshListRecPred[sV], exIter];
    folded = compactBetaClean[HOL`Drule`SUBS[{HOL`Equal`SYM[unfoldFreshList[sV]]}, sat]];
    zeroEq = HOL`Bool`CONJUNCT1[folded];
    stepRawAll = HOL`Bool`CONJUNCT2[folded];
    stepRaw = HOL`Bool`SPEC[nW, stepRawAll];
    seqEq = HOL`Equal`SYM[unfoldFreshSeq[sV, nW]];
    consEq = compactConsCong[seqEq, REFL[mkComb[freshListTm[sV], nW]]];
    step = TRANS[stepRaw, consEq];
    stepAll = HOL`Bool`GEN[nW, step];
    HOL`Bool`GEN[sV, HOL`Bool`CONJ[zeroEq, stepAll]]
  ];

compactFreshListZeroEq[sT_] :=
  HOL`Bool`CONJUNCT1[HOL`Bool`SPEC[sT, freshListRecSpecThm]];

compactFreshListSucEq[sT_, nT_] :=
  compactBetaClean[HOL`Bool`SPEC[nT,
    HOL`Bool`CONJUNCT2[HOL`Bool`SPEC[sT, freshListRecSpecThm]]]];

compactFreshSelectSpec[sT_, nT_, hInfTh_] :=
  Module[{openInf, exAt},
    openInf = EQMP[unfoldListInfinite[sT], hInfTh];
    exAt = HOL`Bool`SPEC[mkComb[freshListTm[sT], nT], openInf];
    compactBetaClean[HOL`Stdlib`Num`selectOfExists[
      compactFreshPred[sT, mkComb[freshListTm[sT], nT]], exAt]]
  ];

freshSeqMemThm =
  Module[{sV, nW, hInfTm, hInf, spec, memChoice, seqEq, predEq, memSeq,
          allN},
    sV = mkVar["S", compactSetTy]; nW = mkVar["nW", numTy];
    hInfTm = listInfiniteTm[sV]; hInf = ASSUME[hInfTm];
    spec = compactFreshSelectSpec[sV, nW, hInf];
    memChoice = HOL`Bool`CONJUNCT1[spec];
    seqEq = HOL`Equal`SYM[unfoldFreshSeq[sV, nW]];
    predEq = HOL`Equal`APTERM[sV, seqEq];
    memSeq = EQMP[predEq, memChoice];
    allN = HOL`Bool`GEN[nW, memSeq];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hInfTm, allN]]
  ];

freshSeqNotMemThm =
  Module[{sV, nW, hInfTm, hInf, fln, spec, notChoice, seqEq, memEq, notEq,
          notSeq, allN},
    sV = mkVar["S", compactSetTy]; nW = mkVar["nW", numTy];
    hInfTm = listInfiniteTm[sV]; hInf = ASSUME[hInfTm];
    fln = mkComb[freshListTm[sV], nW];
    spec = compactFreshSelectSpec[sV, nW, hInf];
    notChoice = HOL`Bool`CONJUNCT2[spec];
    seqEq = HOL`Equal`SYM[unfoldFreshSeq[sV, nW]];
    memEq = compactMemCong[seqEq, REFL[fln]];
    notEq = HOL`Equal`APTERM[mkConst["¬", tyFun[boolTy, boolTy]], memEq];
    notSeq = EQMP[notEq, notChoice];
    allN = HOL`Bool`GEN[nW, notSeq];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hInfTm, allN]]
  ];

compactMemFreshListSucFromDisj[sT_, mT_, nT_, disjTh_] :=
  Module[{xM, xN, flN, flSuc, consList, memConsEq, memCons, flSucEq, memFold},
    xM = mkComb[freshSeqTm[sT], mT]; xN = mkComb[freshSeqTm[sT], nT];
    flN = mkComb[freshListTm[sT], nT]; flSuc = mkComb[freshListTm[sT], sucT[nT]];
    consList = mkComb[mkComb[compactConsReal[], xN], flN];
    memConsEq = compactMemConsEq[xM, xN, flN];
    memCons = EQMP[HOL`Equal`SYM[memConsEq], disjTh];
    flSucEq = compactFreshListSucEq[sT, nT];
    memFold = compactMemCong[REFL[xM], HOL`Equal`SYM[flSucEq]];
    EQMP[memFold, memCons]
  ];

freshSeqMemFreshListOfLtThm =
  Module[{sV, mV, nV, nInd, mW, nP, mP, fs, fl, pLam, baseHypTm, baseHyp,
          baseFalse, baseGoal, basePoint, base, ihTm, ih, hLtTm, hLt, mLeN,
          caseTh, hEqTm, hEq, xEq, disjEq, branchEq, hLtMnTm, hLtMn,
          tailMem, disjLt, branchLt, stepPoint, stepForM, stepAll, indSpec,
          indAll, hFinalTm, hFinal, finalPoint},
    sV = mkVar["S", compactSetTy]; mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    nInd = mkVar["nInd", numTy]; mW = mkVar["mW", numTy];
    fs = freshSeqTm[sV]; fl = freshListTm[sV];
    pLam = Module[{nQ, mQ},
      nQ = mkVar["nQ", numTy]; mQ = mkVar["mQ", numTy];
      mkAbs[nQ, forallTm[mQ, impTm[compactNatLt[mQ, nQ],
        compactMemTm[mkComb[fs, mQ], mkComb[fl, nQ]]]]]
    ];

    baseHypTm = compactNatLt[mW, zeroN[]]; baseHyp = ASSUME[baseHypTm];
    baseFalse = HOL`Bool`MP[
      HOL`Bool`NOTELIM[HOL`Bool`SPEC[mW, HOL`Stdlib`Num`notLtZeroThm]], baseHyp];
    baseGoal = compactMemTm[mkComb[fs, mW], mkComb[fl, zeroN[]]];
    basePoint = HOL`Bool`CONTR[baseGoal, baseFalse];
    base = HOL`Bool`GEN[mW, HOL`Bool`DISCH[baseHypTm, basePoint]];

    ihTm = forallTm[mW, impTm[compactNatLt[mW, nInd],
      compactMemTm[mkComb[fs, mW], mkComb[fl, nInd]]]];
    ih = ASSUME[ihTm];
    hLtTm = compactNatLt[mW, sucT[nInd]]; hLt = ASSUME[hLtTm];
    mLeN = HOL`Bool`MP[
      compactSpecAll[HOL`Stdlib`Num`ltSucEqLeqThm, {mW, nInd}], hLt];
    caseTh = HOL`Bool`MP[
      compactSpecAll[HOL`Stdlib`Num`leqCaseEqLtThm, {mW, nInd}], mLeN];

    hEqTm = mkEq[mW, nInd]; hEq = ASSUME[hEqTm];
    xEq = HOL`Equal`APTERM[fs, hEq];
    disjEq = HOL`Bool`DISJ1[xEq,
      compactMemTm[mkComb[fs, mW], mkComb[fl, nInd]]];
    branchEq = compactMemFreshListSucFromDisj[sV, mW, nInd, disjEq];

    hLtMnTm = compactNatLt[mW, nInd]; hLtMn = ASSUME[hLtMnTm];
    tailMem = HOL`Bool`MP[HOL`Bool`SPEC[mW, ih], hLtMn];
    disjLt = HOL`Bool`DISJ2[tailMem, mkEq[mkComb[fs, mW], mkComb[fs, nInd]]];
    branchLt = compactMemFreshListSucFromDisj[sV, mW, nInd, disjLt];

    stepPoint = HOL`Bool`DISJCASES[caseTh, branchEq, branchLt];
    stepForM = HOL`Bool`GEN[mW, HOL`Bool`DISCH[hLtTm, stepPoint]];
    stepAll = HOL`Bool`GEN[nInd, HOL`Bool`DISCH[ihTm, stepForM]];

    indSpec = compactBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    hFinalTm = compactNatLt[mV, nV]; hFinal = ASSUME[hFinalTm];
    finalPoint = HOL`Bool`MP[HOL`Bool`SPEC[mV, HOL`Bool`SPEC[nV, indAll]], hFinal];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[mV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hFinalTm, finalPoint]]]]
  ];

freshSeqNeOfLtThm =
  Module[{sV, mV, nV, hInfTm, hInf, hLtTm, hLt, fs, fln, memM, notNAll,
          notN, hEqTm, hEq, memEq, memN, falseTh, notEq, point},
    sV = mkVar["S", compactSetTy]; mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    fs = freshSeqTm[sV]; fln = mkComb[freshListTm[sV], nV];
    hInfTm = listInfiniteTm[sV]; hInf = ASSUME[hInfTm];
    hLtTm = compactNatLt[mV, nV]; hLt = ASSUME[hLtTm];
    memM = HOL`Bool`MP[compactSpecAll[freshSeqMemFreshListOfLtThm, {sV, mV, nV}], hLt];
    notNAll = HOL`Bool`MP[HOL`Bool`SPEC[sV, freshSeqNotMemThm], hInf];
    notN = HOL`Bool`SPEC[nV, notNAll];
    hEqTm = mkEq[mkComb[fs, nV], mkComb[fs, mV]]; hEq = ASSUME[hEqTm];
    memEq = compactMemCong[HOL`Equal`SYM[hEq], REFL[fln]];
    memN = EQMP[memEq, memM];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notN], memN];
    notEq = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[hEqTm, falseTh]];
    point = HOL`Bool`DISCH[hLtTm, notEq];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hInfTm,
      HOL`Bool`GEN[mV, HOL`Bool`GEN[nV, point]]]]
  ];

freshSeqBoundedThm =
  Module[{sV, loW, hiW, nW, fs, hInfTm, hInf, hBoundTm, hBound, openBound,
          hAllTm, hAll, memAll, memN, boundsN, allN, cleanSeqBounded,
          outerEx, betaLo, innerEx, exHi, exLo, folded, chooseHi, chooseLo},
    sV = mkVar["S", compactSetTy]; loW = mkVar["loW", realTy];
    hiW = mkVar["hiW", realTy]; nW = mkVar["nW", numTy];
    fs = freshSeqTm[sV];
    hInfTm = listInfiniteTm[sV]; hInf = ASSUME[hInfTm];
    hBoundTm = setBoundedTm[sV]; hBound = ASSUME[hBoundTm];
    openBound = EQMP[unfoldSetBounded[sV], hBound];
    hAllTm = compactSetBoundedAll[sV, loW, hiW]; hAll = ASSUME[hAllTm];
    memAll = HOL`Bool`MP[HOL`Bool`SPEC[sV, freshSeqMemThm], hInf];
    memN = HOL`Bool`SPEC[nW, memAll];
    boundsN = HOL`Bool`MP[HOL`Bool`SPEC[mkComb[fs, nW], hAll], memN];
    allN = HOL`Bool`GEN[nW, boundsN];
    cleanSeqBounded = unfoldSeqBounded[fs];
    outerEx = concl[cleanSeqBounded][[2]];
    betaLo = HOL`Equal`BETACONV[mkComb[outerEx[[2]], loW]];
    innerEx = concl[betaLo][[2]];
    exHi = HOL`Bool`EXISTS[innerEx, hiW, allN];
    exLo = HOL`Bool`EXISTS[outerEx, loW, exHi];
    folded = EQMP[HOL`Equal`SYM[cleanSeqBounded], exLo];
    chooseHi = HOL`Bool`CHOOSE[hiW, ASSUME[existsTm[hiW, hAllTm]], folded];
    chooseLo = HOL`Bool`CHOOSE[loW, openBound, chooseHi];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hInfTm,
      HOL`Bool`DISCH[hBoundTm, chooseLo]]]
  ];

compactLimitAtom[aT_, lT_, epsT_, nT_] :=
  realLtTm[compactRealAbs[realAddTm[mkComb[aT, nT], realNegTm[lT]]], epsT];

compactLimitAll[aT_, lT_, epsT_, n0T_] :=
  Module[{nClose},
    nClose = mkVar["nClose", numTy];
    forallTm[nClose, impTm[compactNatLe[n0T, nClose],
      compactLimitAtom[aT, lT, epsT, nClose]]]
  ];

compactCloseAsDist[sT_, phiT_, lT_, epsT_, nT_, closeTh_] :=
  Module[{fs, subSeq, yT, subEq, argEq, absEq, closeFresh, distEq},
    fs = freshSeqTm[sT]; subSeq = subsequenceTm[fs, phiT];
    yT = mkComb[fs, mkComb[phiT, nT]];
    subEq = compactSubsequenceAppEq[fs, phiT, nT];
    argEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], subEq],
      REFL[realNegTm[lT]]];
    absEq = HOL`Equal`APTERM[realAbsConst[], argEq];
    closeFresh = EQMP[compactRealLtCong[absEq, REFL[epsT]], closeTh];
    distEq = unfoldDist[yT, lT];
    EQMP[compactRealLtCong[HOL`Equal`SYM[distEq], REFL[epsT]], closeFresh]
  ];

compactAccumulationExists[sT_, lT_, epsT_] :=
  Module[{yV},
    yV = mkVar["yAccum", realTy];
    existsTm[yV, conjTm[mkComb[sT, yV],
      conjTm[compactNotTm[mkEq[yV, lT]], realLtTm[distTm[yV, lT], epsT]]]]
  ];

freshLimitIsAccumThm =
  Module[{sV, phiV, lV, epsV, nW, fs, subSeq, hInfTm, hInf, hPhiTm, hPhi,
          hTendTm, hTend, openTend, hEpsTm, hEps, exN, hAllTm, hAll,
          phiN, phiSucN, y0, y1, memAll, hy0S, hy1S, close0Raw, close1Raw,
          close0, close1, hStepAll, hPhiLt, neAll, hDistinct, exGoal,
          y0EqTm, em, hY0Eq, hY1EqTm, hY1Eq, y1EqY0, falseY1, notY1,
          branchEq, hNotY0, branchNot, cases, chosenN, epsBody, allEps,
          folded},
    sV = mkVar["S", compactSetTy]; phiV = mkVar["phi", compactNumFunTy];
    lV = mkVar["l", realTy]; epsV = mkVar["eps", realTy];
    nW = mkVar["NAccum", numTy];
    fs = freshSeqTm[sV]; subSeq = subsequenceTm[fs, phiV];
    hInfTm = listInfiniteTm[sV]; hInf = ASSUME[hInfTm];
    hPhiTm = subseqIndexTm[phiV]; hPhi = ASSUME[hPhiTm];
    hTendTm = tendstoTm[subSeq, lV]; hTend = ASSUME[hTendTm];
    openTend = EQMP[unfoldTendsto[subSeq, lV], hTend];
    hEpsTm = realLtTm[zeroRealTm[], epsV]; hEps = ASSUME[hEpsTm];
    exN = HOL`Bool`MP[HOL`Bool`SPEC[epsV, openTend], hEps];
    hAllTm = compactLimitAll[subSeq, lV, epsV, nW]; hAll = ASSUME[hAllTm];

    phiN = mkComb[phiV, nW]; phiSucN = mkComb[phiV, sucT[nW]];
    y0 = mkComb[fs, phiN]; y1 = mkComb[fs, phiSucN];
    memAll = HOL`Bool`MP[HOL`Bool`SPEC[sV, freshSeqMemThm], hInf];
    hy0S = HOL`Bool`SPEC[phiN, memAll];
    hy1S = HOL`Bool`SPEC[phiSucN, memAll];
    close0Raw = HOL`Bool`MP[HOL`Bool`SPEC[nW, hAll],
      HOL`Bool`SPEC[nW, HOL`Stdlib`Num`leqReflThm]];
    close1Raw = HOL`Bool`MP[HOL`Bool`SPEC[sucT[nW], hAll],
      HOL`Bool`SPEC[nW, HOL`Stdlib`Num`leqSucThm]];
    close0 = compactCloseAsDist[sV, phiV, lV, epsV, nW, close0Raw];
    close1 = compactCloseAsDist[sV, phiV, lV, epsV, sucT[nW], close1Raw];
    hStepAll = EQMP[unfoldSubseqIndex[phiV], hPhi];
    hPhiLt = HOL`Bool`SPEC[nW, hStepAll];
    neAll = HOL`Bool`MP[HOL`Bool`SPEC[sV, freshSeqNeOfLtThm], hInf];
    hDistinct = HOL`Bool`MP[compactSpecAll[neAll, {phiN, phiSucN}], hPhiLt];

    exGoal = compactAccumulationExists[sV, lV, epsV];
    y0EqTm = mkEq[y0, lV];
    em = HOL`Bool`EXCLUDEDMIDDLE[y0EqTm];

    hY0Eq = ASSUME[y0EqTm];
    hY1EqTm = mkEq[y1, lV]; hY1Eq = ASSUME[hY1EqTm];
    y1EqY0 = TRANS[hY1Eq, HOL`Equal`SYM[hY0Eq]];
    falseY1 = HOL`Bool`MP[HOL`Bool`NOTELIM[hDistinct], y1EqY0];
    notY1 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[hY1EqTm, falseY1]];
    branchEq = HOL`Bool`EXISTS[exGoal, y1,
      HOL`Bool`CONJ[hy1S, HOL`Bool`CONJ[notY1, close1]]];

    hNotY0 = ASSUME[compactNotTm[y0EqTm]];
    branchNot = HOL`Bool`EXISTS[exGoal, y0,
      HOL`Bool`CONJ[hy0S, HOL`Bool`CONJ[hNotY0, close0]]];
    cases = HOL`Bool`DISJCASES[em, branchEq, branchNot];
    chosenN = HOL`Bool`CHOOSE[nW, exN, cases];
    epsBody = HOL`Bool`DISCH[hEpsTm, chosenN];
    allEps = HOL`Bool`GEN[epsV, epsBody];
    folded = EQMP[HOL`Equal`SYM[unfoldAccumulationPoint[sV, lV]], allEps];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[phiV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[hInfTm, HOL`Bool`DISCH[hPhiTm,
        HOL`Bool`DISCH[hTendTm, folded]]]]]]
  ];

seqBoundedSubseqAboveThm =
  Module[{uV, phiV, loW, hiW, nW, subSeq, hBoundTm, hBound, openBound,
          hAllTm, hAll, point, high, subEq, highSub, allN, cleanAbove,
          exAbove, chooseHi, chooseLo},
    uV = mkVar["u", compactSeqTy]; phiV = mkVar["phi", compactNumFunTy];
    loW = mkVar["loW", realTy]; hiW = mkVar["hiW", realTy];
    nW = mkVar["nW", numTy];
    subSeq = subsequenceTm[uV, phiV];
    hBoundTm = seqBoundedTm[uV]; hBound = ASSUME[hBoundTm];
    openBound = EQMP[unfoldSeqBounded[uV], hBound];
    hAllTm = compactSeqBoundedAll[uV, loW, hiW]; hAll = ASSUME[hAllTm];
    point = HOL`Bool`SPEC[mkComb[phiV, nW], hAll];
    high = HOL`Bool`CONJUNCT2[point];
    subEq = compactSubsequenceAppEq[uV, phiV, nW];
    highSub = EQMP[compactRealLeCong[HOL`Equal`SYM[subEq], REFL[hiW]], high];
    allN = HOL`Bool`GEN[nW, highSub];
    cleanAbove = unfoldSeqBddAbove[subSeq];
    exAbove = HOL`Bool`EXISTS[concl[cleanAbove][[2]], hiW, allN];
    chooseHi = HOL`Bool`CHOOSE[hiW,
      ASSUME[existsTm[hiW, hAllTm]], EQMP[HOL`Equal`SYM[cleanAbove], exAbove]];
    chooseLo = HOL`Bool`CHOOSE[loW, openBound, chooseHi];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[phiV, HOL`Bool`DISCH[hBoundTm, chooseLo]]]
  ];

seqBoundedSubseqBelowThm =
  Module[{uV, phiV, loW, hiW, nW, subSeq, hBoundTm, hBound, openBound,
          hAllTm, hAll, point, low, subEq, lowSub, allN, cleanBelow,
          exBelow, chooseHi, chooseLo},
    uV = mkVar["u", compactSeqTy]; phiV = mkVar["phi", compactNumFunTy];
    loW = mkVar["loW", realTy]; hiW = mkVar["hiW", realTy];
    nW = mkVar["nW", numTy];
    subSeq = subsequenceTm[uV, phiV];
    hBoundTm = seqBoundedTm[uV]; hBound = ASSUME[hBoundTm];
    openBound = EQMP[unfoldSeqBounded[uV], hBound];
    hAllTm = compactSeqBoundedAll[uV, loW, hiW]; hAll = ASSUME[hAllTm];
    point = HOL`Bool`SPEC[mkComb[phiV, nW], hAll];
    low = HOL`Bool`CONJUNCT1[point];
    subEq = compactSubsequenceAppEq[uV, phiV, nW];
    lowSub = EQMP[compactRealLeCong[REFL[loW], HOL`Equal`SYM[subEq]], low];
    allN = HOL`Bool`GEN[nW, lowSub];
    cleanBelow = unfoldSeqBddBelow[subSeq];
    exBelow = HOL`Bool`EXISTS[concl[cleanBelow][[2]], loW, allN];
    chooseHi = HOL`Bool`CHOOSE[hiW,
      ASSUME[existsTm[hiW, hAllTm]], EQMP[HOL`Equal`SYM[cleanBelow], exBelow]];
    chooseLo = HOL`Bool`CHOOSE[loW, openBound, chooseHi];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[phiV, HOL`Bool`DISCH[hBoundTm, chooseLo]]]
  ];

compactHasConvFromTendsto[uT_, phiT_, lT_, idxTh_, tendTh_] :=
  Module[{cleanHas, bodyEx, bodyConj},
    cleanHas = unfoldHasConvergentSubseq[uT, lT];
    bodyConj = HOL`Bool`CONJ[idxTh, tendTh];
    bodyEx = HOL`Bool`EXISTS[concl[cleanHas][[2]], phiT, bodyConj];
    EQMP[HOL`Equal`SYM[cleanHas], bodyEx]
  ];

compactBwIncBranch[uT_, phiT_, idxTh_, hBound_] :=
  Module[{subSeq, hIncTm, hInc, bddAbove, convEx, lW, hTend, hasConv, exL},
    subSeq = subsequenceTm[uT, phiT];
    hIncTm = monoIncTm[subSeq]; hInc = ASSUME[hIncTm];
    bddAbove = HOL`Bool`MP[compactSpecAll[seqBoundedSubseqAboveThm, {uT, phiT}], hBound];
    convEx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[subSeq, monoConvergesIncThm],
      hInc], bddAbove];
    lW = mkVar["lW", realTy];
    hTend = ASSUME[tendstoTm[subSeq, lW]];
    hasConv = compactHasConvFromTendsto[uT, phiT, lW, idxTh, hTend];
    exL = HOL`Bool`EXISTS[compactBwGoal[uT], lW, hasConv];
    HOL`Bool`CHOOSE[lW, convEx, exL]
  ];

compactBwDecBranch[uT_, phiT_, idxTh_, hBound_] :=
  Module[{subSeq, hDecTm, hDec, bddBelow, convEx, lW, hTend, hasConv, exL},
    subSeq = subsequenceTm[uT, phiT];
    hDecTm = monoDecTm[subSeq]; hDec = ASSUME[hDecTm];
    bddBelow = HOL`Bool`MP[compactSpecAll[seqBoundedSubseqBelowThm, {uT, phiT}], hBound];
    convEx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[subSeq, monoConvergesDecThm],
      hDec], bddBelow];
    lW = mkVar["lW", realTy];
    hTend = ASSUME[tendstoTm[subSeq, lW]];
    hasConv = compactHasConvFromTendsto[uT, phiT, lW, idxTh, hTend];
    exL = HOL`Bool`EXISTS[compactBwGoal[uT], lW, hasConv];
    HOL`Bool`CHOOSE[lW, convEx, exL]
  ];

bwSequentialThm =
  Module[{uV, phiW, subSeq, hBoundTm, hBound, monoEx, hMonoBodyTm, hMonoBody,
          idxTh, disjTh, incBranch, decBranch, cases, chosenPhi},
    uV = mkVar["u", compactSeqTy]; phiW = mkVar["phiW", compactNumFunTy];
    subSeq = subsequenceTm[uV, phiW];
    hBoundTm = seqBoundedTm[uV]; hBound = ASSUME[hBoundTm];
    monoEx = HOL`Bool`SPEC[uV, existsMonoSubseqThm];
    hMonoBodyTm = conjTm[subseqIndexTm[phiW],
      compactOrTm[monoIncTm[subSeq], monoDecTm[subSeq]]];
    hMonoBody = ASSUME[hMonoBodyTm];
    idxTh = HOL`Bool`CONJUNCT1[hMonoBody];
    disjTh = HOL`Bool`CONJUNCT2[hMonoBody];
    incBranch = compactBwIncBranch[uV, phiW, idxTh, hBound];
    decBranch = compactBwDecBranch[uV, phiW, idxTh, hBound];
    cases = HOL`Bool`DISJCASES[disjTh, incBranch, decBranch];
    chosenPhi = HOL`Bool`CHOOSE[phiW, monoEx, cases];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[hBoundTm, chosenPhi]]
  ];

accumulationPrincipleThm =
  Module[{sV, lW, phiW, xW, fs, hBoundTm, hBound, hInfTm, hInf, seqBdd,
          convEx, hHasTm, hHas, openHas, subSeq, hBodyTm, hBody, idxTh,
          tendTh, accumTh, exGoal, exX, choosePhi, chooseL},
    sV = mkVar["S", compactSetTy]; lW = mkVar["lW", realTy];
    phiW = mkVar["phiWAccum", compactNumFunTy]; xW = mkVar["x", realTy];
    fs = freshSeqTm[sV];
    hBoundTm = setBoundedTm[sV]; hBound = ASSUME[hBoundTm];
    hInfTm = listInfiniteTm[sV]; hInf = ASSUME[hInfTm];
    seqBdd = HOL`Bool`MP[
      HOL`Bool`MP[HOL`Bool`SPEC[sV, freshSeqBoundedThm], hInf], hBound];
    convEx = HOL`Bool`MP[HOL`Bool`SPEC[fs, bwSequentialThm], seqBdd];
    hHasTm = hasConvergentSubseqTm[fs, lW]; hHas = ASSUME[hHasTm];
    openHas = EQMP[unfoldHasConvergentSubseq[fs, lW], hHas];
    subSeq = subsequenceTm[fs, phiW];
    hBodyTm = conjTm[subseqIndexTm[phiW], tendstoTm[subSeq, lW]];
    hBody = ASSUME[hBodyTm];
    idxTh = HOL`Bool`CONJUNCT1[hBody];
    tendTh = HOL`Bool`CONJUNCT2[hBody];
    accumTh = HOL`Bool`MP[
      HOL`Bool`MP[
        HOL`Bool`MP[compactSpecAll[freshLimitIsAccumThm, {sV, phiW, lW}], hInf],
        idxTh], tendTh];
    exGoal = existsTm[xW, accumulationPointTm[sV, xW]];
    exX = HOL`Bool`EXISTS[exGoal, lW, accumTh];
    choosePhi = HOL`Bool`CHOOSE[phiW, openHas, exX];
    chooseL = HOL`Bool`CHOOSE[lW, convEx, choosePhi];
    HOL`Bool`GEN[sV, HOL`Bool`DISCH[hBoundTm,
      HOL`Bool`DISCH[hInfTm, chooseL]]]
  ];

compactTwoNat[] := sucT[sucT[zeroN[]]];
compactTwoReal[] := realOfRatTm[ratOfIntTm[intOfNumTm[compactTwoNat[]]]];
compactRealInv[xT_] := mkComb[realInvConst[], xT];
compactHalfScalar[] := compactRealInv[compactTwoReal[]];
compactMidpointBody[aT_, bT_] :=
  realMulTm[realAddTm[aT, bT], compactHalfScalar[]];
compactHalfLength[aT_, bT_] :=
  realMulTm[realAddTm[bT, realNegTm[aT]], compactHalfScalar[]];

midpointDefThm =
  Module[{aV, bV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    newDefinition[mkEq[mkVar["midpoint", tyFun[realTy, tyFun[realTy, realTy]]],
      mkAbs[aV, mkAbs[bV, compactMidpointBody[aV, bV]]]]]
  ];

midpointConst[] := mkConst["midpoint", tyFun[realTy, tyFun[realTy, realTy]]];
midpointTm[aT_, bT_] := mkComb[mkComb[midpointConst[], aT], bT];

unfoldMidpoint[aT_, bT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[midpointDefThm, aT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, bT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

compactFoldMidpoint[th_, aT_, bT_] :=
  compactBetaClean[HOL`Drule`SUBS[{HOL`Equal`SYM[unfoldMidpoint[aT, bT]]}, th]];

compactHalfNonnegThm =
  HOL`Auto`RealArith`realArithProve[realLeTm[zeroRealTm[], compactHalfScalar[]]];

compactHalfPosThm =
  HOL`Auto`RealArith`realArithProve[realLtTm[zeroRealTm[], compactHalfScalar[]]];

compactHalfDoubleThm =
  Module[{xV},
    xV = mkVar["xHalf", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, mkEq[
        realAddTm[realMulTm[xV, compactHalfScalar[]],
          realMulTm[xV, compactHalfScalar[]]], xV]]]
  ];

compactHalfTimesDoubleThm =
  Module[{xV},
    xV = mkVar["xHalfL", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, mkEq[realMulTm[compactHalfScalar[], realAddTm[xV, xV]], xV]]]
  ];

compactLeLeftDoubleSumThm =
  Module[{aV, bV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{aV, bV}, impTm[realLeTm[aV, bV],
        realLeTm[realAddTm[aV, aV], realAddTm[aV, bV]]]]]
  ];

compactLeSumRightDoubleThm =
  Module[{aV, bV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{aV, bV}, impTm[realLeTm[aV, bV],
        realLeTm[realAddTm[aV, bV], realAddTm[bV, bV]]]]]
  ];

compactLtLeftDoubleSumThm =
  Module[{aV, bV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{aV, bV}, impTm[realLtTm[aV, bV],
        realLtTm[realAddTm[aV, aV], realAddTm[aV, bV]]]]]
  ];

compactLtSumRightDoubleThm =
  Module[{aV, bV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{aV, bV}, impTm[realLtTm[aV, bV],
        realLtTm[realAddTm[aV, bV], realAddTm[bV, bV]]]]]
  ];

compactDoubleCancelThm =
  Module[{xV, yV},
    xV = mkVar["xDouble", realTy]; yV = mkVar["yDouble", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{xV, yV}, impTm[
        mkEq[realAddTm[xV, xV], realAddTm[yV, yV]], mkEq[xV, yV]]]]
  ];

compactMidpointSubLeftDoubleThm =
  Module[{mV, aV, bV},
    mV = mkVar["mDouble", realTy]; aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{mV, aV, bV}, impTm[
        mkEq[realAddTm[mV, mV], realAddTm[aV, bV]],
        mkEq[realAddTm[realAddTm[mV, realNegTm[aV]],
            realAddTm[mV, realNegTm[aV]]],
          realAddTm[bV, realNegTm[aV]]]]]]
  ];

compactMidpointSubRightDoubleThm =
  Module[{mV, aV, bV},
    mV = mkVar["mDouble", realTy]; aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{mV, aV, bV}, impTm[
        mkEq[realAddTm[mV, mV], realAddTm[aV, bV]],
        mkEq[realAddTm[realAddTm[bV, realNegTm[mV]],
            realAddTm[bV, realNegTm[mV]]],
          realAddTm[bV, realNegTm[aV]]]]]]
  ];

compactMidpointDouble[aT_, bT_] :=
  Module[{halfDouble},
    halfDouble = HOL`Bool`SPEC[realAddTm[aT, bT], compactHalfDoubleThm];
    compactFoldMidpoint[halfDouble, aT, bT]
  ];

compactHalfTimesDoubleEq[xT_] :=
  HOL`Bool`SPEC[xT, compactHalfTimesDoubleThm];

compactHalfTimesMidpointEq[aT_, bT_] :=
  Module[{sumT, comm},
    sumT = realAddTm[aT, bT];
    comm = HOL`Bool`SPEC[sumT, HOL`Bool`SPEC[compactHalfScalar[], realMulCommThm]];
    TRANS[comm, HOL`Equal`SYM[unfoldMidpoint[aT, bT]]]
  ];

leftLeMidpointThm =
  Module[{aV, bV, hTm, h, doubleLe, scaled, leftEq, rightEq, point},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    hTm = realLeTm[aV, bV]; h = ASSUME[hTm];
    doubleLe = HOL`Bool`MP[compactSpecAll[compactLeLeftDoubleSumThm, {aV, bV}], h];
    scaled = HOL`Bool`MP[
      HOL`Bool`MP[compactSpecAll[realLeMulMonoThm,
        {realAddTm[aV, aV], realAddTm[aV, bV], compactHalfScalar[]}],
        compactHalfNonnegThm], doubleLe];
    leftEq = compactHalfTimesDoubleEq[aV];
    rightEq = compactHalfTimesMidpointEq[aV, bV];
    point = EQMP[compactRealLeCong[leftEq, rightEq], scaled];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[hTm, point]]]
  ];

midpointLeRightThm =
  Module[{aV, bV, hTm, h, doubleLe, scaled, leftEq, rightEq, point},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    hTm = realLeTm[aV, bV]; h = ASSUME[hTm];
    doubleLe = HOL`Bool`MP[compactSpecAll[compactLeSumRightDoubleThm, {aV, bV}], h];
    scaled = HOL`Bool`MP[
      HOL`Bool`MP[compactSpecAll[realLeMulMonoThm,
        {realAddTm[aV, bV], realAddTm[bV, bV], compactHalfScalar[]}],
        compactHalfNonnegThm], doubleLe];
    leftEq = compactHalfTimesMidpointEq[aV, bV];
    rightEq = compactHalfTimesDoubleEq[bV];
    point = EQMP[compactRealLeCong[leftEq, rightEq], scaled];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[hTm, point]]]
  ];

leftLtMidpointThm =
  Module[{aV, bV, hTm, h, doubleLt, scaled, leftEq, rightEq, point},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    hTm = realLtTm[aV, bV]; h = ASSUME[hTm];
    doubleLt = HOL`Bool`MP[compactSpecAll[compactLtLeftDoubleSumThm, {aV, bV}], h];
    scaled = HOL`Bool`MP[
      HOL`Bool`MP[compactSpecAll[realLtMulMonoThm,
        {realAddTm[aV, aV], realAddTm[aV, bV], compactHalfScalar[]}],
        compactHalfPosThm], doubleLt];
    leftEq = compactHalfTimesDoubleEq[aV];
    rightEq = compactHalfTimesMidpointEq[aV, bV];
    point = EQMP[compactRealLtCong[leftEq, rightEq], scaled];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[hTm, point]]]
  ];

midpointLtRightThm =
  Module[{aV, bV, hTm, h, doubleLt, scaled, leftEq, rightEq, point},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    hTm = realLtTm[aV, bV]; h = ASSUME[hTm];
    doubleLt = HOL`Bool`MP[compactSpecAll[compactLtSumRightDoubleThm, {aV, bV}], h];
    scaled = HOL`Bool`MP[
      HOL`Bool`MP[compactSpecAll[realLtMulMonoThm,
        {realAddTm[aV, bV], realAddTm[bV, bV], compactHalfScalar[]}],
        compactHalfPosThm], doubleLt];
    leftEq = compactHalfTimesMidpointEq[aV, bV];
    rightEq = compactHalfTimesDoubleEq[bV];
    point = EQMP[compactRealLtCong[leftEq, rightEq], scaled];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[hTm, point]]]
  ];

midpointSubLeftThm =
  Module[{aV, bV, mid, lhs, rhs, midDouble, lhsDouble, rhsDouble, bothDouble,
          point},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    mid = midpointTm[aV, bV];
    lhs = realAddTm[mid, realNegTm[aV]]; rhs = compactHalfLength[aV, bV];
    midDouble = compactMidpointDouble[aV, bV];
    lhsDouble = HOL`Bool`MP[
      compactSpecAll[compactMidpointSubLeftDoubleThm, {mid, aV, bV}], midDouble];
    rhsDouble = HOL`Bool`SPEC[realAddTm[bV, realNegTm[aV]], compactHalfDoubleThm];
    bothDouble = TRANS[lhsDouble, HOL`Equal`SYM[rhsDouble]];
    point = HOL`Bool`MP[compactSpecAll[compactDoubleCancelThm, {lhs, rhs}], bothDouble];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, point]]
  ];

rightSubMidpointThm =
  Module[{aV, bV, mid, lhs, rhs, midDouble, lhsDouble, rhsDouble, bothDouble,
          point},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    mid = midpointTm[aV, bV];
    lhs = realAddTm[bV, realNegTm[mid]]; rhs = compactHalfLength[aV, bV];
    midDouble = compactMidpointDouble[aV, bV];
    lhsDouble = HOL`Bool`MP[
      compactSpecAll[compactMidpointSubRightDoubleThm, {mid, aV, bV}], midDouble];
    rhsDouble = HOL`Bool`SPEC[realAddTm[bV, realNegTm[aV]], compactHalfDoubleThm];
    bothDouble = TRANS[lhsDouble, HOL`Equal`SYM[rhsDouble]];
    point = HOL`Bool`MP[compactSpecAll[compactDoubleCancelThm, {lhs, rhs}], bothDouble];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, point]]
  ];

compactListInstAt[ty_, th_] := HOL`Kernel`INSTTYPE[{mkVarType["A"] -> ty}, th];
compactListTyAt[ty_] := HOL`Stdlib`List`listTy[ty];
compactNilAt[ty_] := mkConst["NIL", compactListTyAt[ty]];
compactConsConstAt[ty_] := mkConst["CONS",
  tyFun[ty, tyFun[compactListTyAt[ty], compactListTyAt[ty]]]];
compactConsTmAt[ty_, xT_, xsT_] := mkComb[mkComb[compactConsConstAt[ty], xT], xsT];
compactAppendConstAt[ty_] := mkConst["APPEND",
  tyFun[compactListTyAt[ty], tyFun[compactListTyAt[ty], compactListTyAt[ty]]]];
compactAppendTmAt[ty_, xsT_, ysT_] := mkComb[mkComb[compactAppendConstAt[ty], xsT], ysT];

compactAppendNilEqAt[ty_, ysT_] :=
  HOL`Bool`SPEC[ysT, compactListInstAt[ty, HOL`Stdlib`List`appendNilThm]];

compactAppendConsEqAt[ty_, xT_, xsT_, ysT_] :=
  compactSpecAll[compactListInstAt[ty, HOL`Stdlib`List`appendConsThm],
    {xT, xsT, ysT}];

compactMemNilEqAt[ty_, xT_] :=
  HOL`Bool`SPEC[xT, compactListInstAt[ty, HOL`Stdlib`List`memNilThm]];

compactMemConsEqAt[ty_, xT_, yT_, xsT_] :=
  compactSpecAll[compactListInstAt[ty, HOL`Stdlib`List`memConsThm],
    {xT, yT, xsT}];

compactMemAppendConsFromCons[ty_, iT_, xT_, xsT_, ysT_, consMemTh_] :=
  Module[{appEq, memEq},
    appEq = compactAppendConsEqAt[ty, xT, xsT, ysT];
    memEq = HOL`Equal`APTERM[mkComb[compactMemConstAt[ty], iT], appEq];
    EQMP[HOL`Equal`SYM[memEq], consMemTh]
  ];

memAppendLeftThm =
  Module[{iV, jsV, ksV, lV, xV, predLam, inductSpec, inductBeta,
          baseCase, stepCase, finalAll, point},
    iV = mkVar["i", iotaTy]; jsV = mkVar["js", compactIotaListTy];
    ksV = mkVar["ks", compactIotaListTy]; lV = mkVar["lMem", compactIotaListTy];
    xV = mkVar["xMem", iotaTy];
    predLam = mkAbs[lV, compactForallList[{iV, ksV},
      impTm[compactMemTmAt[iotaTy, iV, lV],
        compactMemTmAt[iotaTy, iV, compactAppendTmAt[iotaTy, lV, ksV]]]]];
    inductSpec = HOL`Bool`SPEC[predLam,
      compactListInstAt[iotaTy, HOL`Stdlib`List`listInductionThm]];
    inductBeta = compactBetaClean[inductSpec];
    baseCase = Module[{hTm, hMem, baseGoal, baseFalse, basePoint},
      hTm = compactMemTmAt[iotaTy, iV, compactNilAt[iotaTy]];
      hMem = ASSUME[hTm];
      baseGoal = compactMemTmAt[iotaTy, iV,
        compactAppendTmAt[iotaTy, compactNilAt[iotaTy], ksV]];
      baseFalse = EQMP[compactMemNilEqAt[iotaTy, iV], hMem];
      basePoint = HOL`Bool`CONTR[baseGoal, baseFalse];
      HOL`Bool`GEN[iV, HOL`Bool`GEN[ksV, HOL`Bool`DISCH[hTm, basePoint]]]
    ];
    stepCase = Module[{ihTm, ih, hTm, hMem, memConsOpen, tailAppend,
                       consTailList, target, branchEq, branchTail, stepPoint,
                       stepDisch, stepGen},
      ihTm = compactForallList[{iV, ksV},
        impTm[compactMemTmAt[iotaTy, iV, lV],
          compactMemTmAt[iotaTy, iV, compactAppendTmAt[iotaTy, lV, ksV]]]];
      ih = ASSUME[ihTm];
      hTm = compactMemTmAt[iotaTy, iV, compactConsTmAt[iotaTy, xV, lV]];
      hMem = ASSUME[hTm];
      memConsOpen = EQMP[compactMemConsEqAt[iotaTy, iV, xV, lV], hMem];
      tailAppend = compactAppendTmAt[iotaTy, lV, ksV];
      consTailList = compactConsTmAt[iotaTy, xV, tailAppend];
      target = compactMemTmAt[iotaTy, iV,
        compactAppendTmAt[iotaTy, compactConsTmAt[iotaTy, xV, lV], ksV]];
      branchEq = Module[{eqTm, hEq, disj, consMem},
        eqTm = mkEq[iV, xV]; hEq = ASSUME[eqTm];
        disj = HOL`Bool`DISJ1[hEq, compactMemTmAt[iotaTy, iV, tailAppend]];
        consMem = EQMP[HOL`Equal`SYM[compactMemConsEqAt[iotaTy, iV, xV, tailAppend]], disj];
        compactMemAppendConsFromCons[iotaTy, iV, xV, lV, ksV, consMem]
      ];
      branchTail = Module[{tailTm, hTail, ihAt, tailMem, disj, consMem},
        tailTm = compactMemTmAt[iotaTy, iV, lV]; hTail = ASSUME[tailTm];
        ihAt = compactSpecAll[ih, {iV, ksV}];
        tailMem = HOL`Bool`MP[ihAt, hTail];
        disj = HOL`Bool`DISJ2[tailMem, mkEq[iV, xV]];
        consMem = EQMP[HOL`Equal`SYM[compactMemConsEqAt[iotaTy, iV, xV, tailAppend]], disj];
        compactMemAppendConsFromCons[iotaTy, iV, xV, lV, ksV, consMem]
      ];
      stepPoint = HOL`Bool`DISJCASES[memConsOpen, branchEq, branchTail];
      stepDisch = HOL`Bool`DISCH[hTm, stepPoint];
      stepGen = HOL`Bool`GEN[iV, HOL`Bool`GEN[ksV, stepDisch]];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[lV, HOL`Bool`DISCH[ihTm, stepGen]]]
    ];
    finalAll = HOL`Bool`MP[inductBeta, HOL`Bool`CONJ[baseCase, stepCase]];
    point = compactSpecAll[finalAll, {jsV, iV, ksV}];
    HOL`Bool`GEN[iV, HOL`Bool`GEN[jsV, HOL`Bool`GEN[ksV, point]]]
  ];

memAppendRightThm =
  Module[{iV, jsV, ksV, lV, xV, predLam, inductSpec, inductBeta,
          baseCase, stepCase, finalAll, point},
    iV = mkVar["i", iotaTy]; jsV = mkVar["js", compactIotaListTy];
    ksV = mkVar["ks", compactIotaListTy]; lV = mkVar["lMemR", compactIotaListTy];
    xV = mkVar["xMemR", iotaTy];
    predLam = mkAbs[lV, compactForallList[{iV, ksV},
      impTm[compactMemTmAt[iotaTy, iV, ksV],
        compactMemTmAt[iotaTy, iV, compactAppendTmAt[iotaTy, lV, ksV]]]]];
    inductSpec = HOL`Bool`SPEC[predLam,
      compactListInstAt[iotaTy, HOL`Stdlib`List`listInductionThm]];
    inductBeta = compactBetaClean[inductSpec];
    baseCase = Module[{hTm, hMem, target, memEq, basePoint},
      hTm = compactMemTmAt[iotaTy, iV, ksV]; hMem = ASSUME[hTm];
      target = compactMemTmAt[iotaTy, iV,
        compactAppendTmAt[iotaTy, compactNilAt[iotaTy], ksV]];
      memEq = HOL`Equal`APTERM[mkComb[compactMemConstAt[iotaTy], iV],
        compactAppendNilEqAt[iotaTy, ksV]];
      basePoint = EQMP[HOL`Equal`SYM[memEq], hMem];
      HOL`Bool`GEN[iV, HOL`Bool`GEN[ksV, HOL`Bool`DISCH[hTm, basePoint]]]
    ];
    stepCase = Module[{ihTm, ih, hTm, hMem, ihAt, tailMem, tailAppend,
                       disj, consMem, stepPoint, stepDisch, stepGen},
      ihTm = compactForallList[{iV, ksV},
        impTm[compactMemTmAt[iotaTy, iV, ksV],
          compactMemTmAt[iotaTy, iV, compactAppendTmAt[iotaTy, lV, ksV]]]];
      ih = ASSUME[ihTm];
      hTm = compactMemTmAt[iotaTy, iV, ksV]; hMem = ASSUME[hTm];
      ihAt = compactSpecAll[ih, {iV, ksV}];
      tailMem = HOL`Bool`MP[ihAt, hMem];
      tailAppend = compactAppendTmAt[iotaTy, lV, ksV];
      disj = HOL`Bool`DISJ2[tailMem, mkEq[iV, xV]];
      consMem = EQMP[HOL`Equal`SYM[compactMemConsEqAt[iotaTy, iV, xV, tailAppend]], disj];
      stepPoint = compactMemAppendConsFromCons[iotaTy, iV, xV, lV, ksV, consMem];
      stepDisch = HOL`Bool`DISCH[hTm, stepPoint];
      stepGen = HOL`Bool`GEN[iV, HOL`Bool`GEN[ksV, stepDisch]];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[lV, HOL`Bool`DISCH[ihTm, stepGen]]]
    ];
    finalAll = HOL`Bool`MP[inductBeta, HOL`Bool`CONJ[baseCase, stepCase]];
    point = compactSpecAll[finalAll, {jsV, iV, ksV}];
    HOL`Bool`GEN[iV, HOL`Bool`GEN[jsV, HOL`Bool`GEN[ksV, point]]]
  ];

compactClosedIntervalSetTm[leftT_, rightT_] :=
  mkComb[mkComb[closedIntervalConst[], leftT], rightT];

compactNoFiniteSubcoverTyAt[ty_] :=
  tyFun[compactCoverTyAt[ty], tyFun[realTy, tyFun[realTy, boolTy]]];
noFiniteSubcoverTy = compactNoFiniteSubcoverTyAt[iotaTy];

compactNoFiniteSubcoverBody[uT_, aT_, bT_] :=
  compactNotTm[finiteSubcoverTm[uT, compactClosedIntervalSetTm[aT, bT]]];

noFiniteSubcoverDefThm =
  Module[{uV, aV, bV},
    uV = mkVar["U", compactCoverTy]; aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    newDefinition[mkEq[mkVar["noFiniteSubcover", noFiniteSubcoverTy],
      mkAbs[uV, mkAbs[aV, mkAbs[bV, compactNoFiniteSubcoverBody[uV, aV, bV]]]]]]
  ];

noFiniteSubcoverConst[] := mkConst["noFiniteSubcover", noFiniteSubcoverTy];
compactNoFiniteSubcoverConstAt[ty_] :=
  mkConst["noFiniteSubcover", compactNoFiniteSubcoverTyAt[ty]];
noFiniteSubcoverTm[uT_, aT_, bT_] :=
  mkComb[mkComb[mkComb[compactNoFiniteSubcoverConstAt[compactCoverIndexTy[uT]], uT],
    aT], bT];

unfoldNoFiniteSubcover[uT_, aT_, bT_] :=
  Module[{s1, s1b, s2, s2b, s3},
    s1 = HOL`Equal`APTHM[noFiniteSubcoverDefThm, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, aT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, bT];
    TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]]
  ];

compactSubcoverExistsTm[uT_, xT_, jsT_] :=
  Module[{ty, iV},
    ty = compactCoverIndexTy[uT]; iV = mkVar["iHalf", ty];
    existsTm[iV, conjTm[compactMemTmAt[ty, iV, jsT],
      compactCoverApp[uT, iV, xT]]]
  ];

compactChooseSubcoverWitness[uT_, xT_, sourceListT_, appendLeftT_, appendRightT_,
    exTh_, memRuleTh_] :=
  Module[{ty, iW, bodyTm, bodyHyp, memFrom, coverAt, memTo, goalEx},
    ty = compactCoverIndexTy[uT]; iW = mkVar["iHalfW", ty];
    bodyTm = conjTm[compactMemTmAt[ty, iW, sourceListT],
      compactCoverApp[uT, iW, xT]];
    bodyHyp = ASSUME[bodyTm];
    memFrom = HOL`Bool`CONJUNCT1[bodyHyp];
    coverAt = HOL`Bool`CONJUNCT2[bodyHyp];
    memTo = HOL`Bool`MP[compactSpecAll[memRuleTh, {iW, appendLeftT, appendRightT}],
      memFrom];
    goalEx = compactSubcoverExistsTm[uT, xT, compactAppendTmAt[ty, appendLeftT, appendRightT]];
    HOL`Bool`CHOOSE[iW, exTh,
      HOL`Bool`EXISTS[goalEx, iW, HOL`Bool`CONJ[memTo, coverAt]]]
  ];

combineHalfSubcoverThm =
  Module[{uV, aV, mV, bV, jsV, ksV, xV, leftSet, rightSet, wholeSet,
          appendList, hLeftTm, hRightTm, hLeft, hRight, openLeft, openRight,
          hXTm, hX, xBounds, hAx, hXb, split, leftBranch, rightBranch,
          point, allX, folded},
    uV = mkVar["U", compactCoverTy]; aV = mkVar["a", realTy];
    mV = mkVar["m", realTy]; bV = mkVar["b", realTy];
    jsV = mkVar["js", compactIotaListTy]; ksV = mkVar["ks", compactIotaListTy];
    xV = mkVar["x", realTy];
    leftSet = compactClosedIntervalSetTm[aV, mV];
    rightSet = compactClosedIntervalSetTm[mV, bV];
    wholeSet = compactClosedIntervalSetTm[aV, bV];
    appendList = compactAppendTmAt[iotaTy, jsV, ksV];
    hLeftTm = listSubcoverTm[uV, leftSet, jsV]; hLeft = ASSUME[hLeftTm];
    hRightTm = listSubcoverTm[uV, rightSet, ksV]; hRight = ASSUME[hRightTm];
    openLeft = EQMP[unfoldListSubcover[uV, leftSet, jsV], hLeft];
    openRight = EQMP[unfoldListSubcover[uV, rightSet, ksV], hRight];
    hXTm = closedIntervalTm[aV, bV, xV]; hX = ASSUME[hXTm];
    xBounds = EQMP[unfoldClosedInterval[aV, bV, xV], hX];
    hAx = HOL`Bool`CONJUNCT1[xBounds]; hXb = HOL`Bool`CONJUNCT2[xBounds];
    split = HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, mV]];
    leftBranch = Module[{hXmTm, hXm, closedAM, exLeft},
      hXmTm = realLeTm[xV, mV]; hXm = ASSUME[hXmTm];
      closedAM = EQMP[HOL`Equal`SYM[unfoldClosedInterval[aV, mV, xV]],
        HOL`Bool`CONJ[hAx, hXm]];
      exLeft = HOL`Bool`MP[HOL`Bool`SPEC[xV, openLeft], closedAM];
      compactChooseSubcoverWitness[uV, xV, jsV, jsV, ksV, exLeft, memAppendLeftThm]
    ];
    rightBranch = Module[{hNotXmTm, hNotXm, total, mLeX, closedMB, exRight},
      hNotXmTm = compactNotTm[realLeTm[xV, mV]]; hNotXm = ASSUME[hNotXmTm];
      total = HOL`Bool`SPEC[mV, HOL`Bool`SPEC[xV, realLeTotalThm]];
      mLeX = HOL`Bool`DISJCASES[total,
        HOL`Bool`CONTR[realLeTm[mV, xV],
          HOL`Bool`MP[HOL`Bool`NOTELIM[hNotXm], ASSUME[realLeTm[xV, mV]]]],
        ASSUME[realLeTm[mV, xV]]];
      closedMB = EQMP[HOL`Equal`SYM[unfoldClosedInterval[mV, bV, xV]],
        HOL`Bool`CONJ[mLeX, hXb]];
      exRight = HOL`Bool`MP[HOL`Bool`SPEC[xV, openRight], closedMB];
      compactChooseSubcoverWitness[uV, xV, ksV, jsV, ksV, exRight, memAppendRightThm]
    ];
    point = HOL`Bool`DISJCASES[split, leftBranch, rightBranch];
    allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hXTm, point]];
    folded = EQMP[HOL`Equal`SYM[unfoldListSubcover[uV, wholeSet, appendList]], allX];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[aV, HOL`Bool`GEN[mV, HOL`Bool`GEN[bV,
      HOL`Bool`GEN[jsV, HOL`Bool`GEN[ksV,
        HOL`Bool`DISCH[hLeftTm, HOL`Bool`DISCH[hRightTm, folded]]]]]]]]
  ];

finiteSubcoverOfHalvesThm =
  Module[{uV, aV, mV, bV, jsW, ksW, leftSet, rightSet, wholeSet,
          hLeftTm, hRightTm, hLeft, hRight, openLeft, openRight, hListLeftTm,
          hListRightTm, hListLeft, hListRight, combined, cleanWhole, exWhole,
          folded, chooseKs, chooseJs},
    uV = mkVar["U", compactCoverTy]; aV = mkVar["a", realTy];
    mV = mkVar["m", realTy]; bV = mkVar["b", realTy];
    jsW = mkVar["jsHalf", compactIotaListTy]; ksW = mkVar["ksHalf", compactIotaListTy];
    leftSet = compactClosedIntervalSetTm[aV, mV];
    rightSet = compactClosedIntervalSetTm[mV, bV];
    wholeSet = compactClosedIntervalSetTm[aV, bV];
    hLeftTm = finiteSubcoverTm[uV, leftSet]; hLeft = ASSUME[hLeftTm];
    hRightTm = finiteSubcoverTm[uV, rightSet]; hRight = ASSUME[hRightTm];
    openLeft = EQMP[unfoldFiniteSubcover[uV, leftSet], hLeft];
    openRight = EQMP[unfoldFiniteSubcover[uV, rightSet], hRight];
    hListLeftTm = listSubcoverTm[uV, leftSet, jsW]; hListLeft = ASSUME[hListLeftTm];
    hListRightTm = listSubcoverTm[uV, rightSet, ksW]; hListRight = ASSUME[hListRightTm];
    combined = HOL`Bool`MP[
      HOL`Bool`MP[compactSpecAll[combineHalfSubcoverThm, {uV, aV, mV, bV, jsW, ksW}],
        hListLeft], hListRight];
    cleanWhole = unfoldFiniteSubcover[uV, wholeSet];
    exWhole = HOL`Bool`EXISTS[concl[cleanWhole][[2]],
      compactAppendTmAt[iotaTy, jsW, ksW], combined];
    folded = EQMP[HOL`Equal`SYM[cleanWhole], exWhole];
    chooseKs = HOL`Bool`CHOOSE[ksW, openRight, folded];
    chooseJs = HOL`Bool`CHOOSE[jsW, openLeft, chooseKs];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[aV, HOL`Bool`GEN[mV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[hLeftTm, HOL`Bool`DISCH[hRightTm, chooseJs]]]]]]
  ];

rightHalfBadThm =
  Module[{uV, aV, bV, mV, leftSet, rightSet, wholeSet, hBadTm, hBad,
          hLeftTm, hLeft, notWhole, hRightTm, hRight, wholeFinite, falseTh,
          notRight, folded},
    uV = mkVar["U", compactCoverTy]; aV = mkVar["a", realTy];
    bV = mkVar["b", realTy]; mV = mkVar["m", realTy];
    leftSet = compactClosedIntervalSetTm[aV, mV];
    rightSet = compactClosedIntervalSetTm[mV, bV];
    wholeSet = compactClosedIntervalSetTm[aV, bV];
    hBadTm = noFiniteSubcoverTm[uV, aV, bV]; hBad = ASSUME[hBadTm];
    hLeftTm = finiteSubcoverTm[uV, leftSet]; hLeft = ASSUME[hLeftTm];
    notWhole = EQMP[unfoldNoFiniteSubcover[uV, aV, bV], hBad];
    hRightTm = finiteSubcoverTm[uV, rightSet]; hRight = ASSUME[hRightTm];
    wholeFinite = HOL`Bool`MP[
      HOL`Bool`MP[compactSpecAll[finiteSubcoverOfHalvesThm, {uV, aV, mV, bV}],
        hLeft], hRight];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notWhole], wholeFinite];
    notRight = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[hRightTm, falseTh]];
    folded = EQMP[HOL`Equal`SYM[unfoldNoFiniteSubcover[uV, mV, bV]], notRight];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[mV,
      HOL`Bool`DISCH[hBadTm, HOL`Bool`DISCH[hLeftTm, folded]]]]]]
  ];

compactRealPairTy = HOL`Stdlib`Pair`prodTy[realTy, realTy];
compactBisectFunTy = tyFun[numTy, compactRealPairTy];

compactPairConsConst[] :=
  mkConst[",", tyFun[realTy, tyFun[realTy, compactRealPairTy]]];
compactPairTm[aT_, bT_] := mkComb[mkComb[compactPairConsConst[], aT], bT];
compactFstConst[] := mkConst["FST", tyFun[compactRealPairTy, realTy]];
compactSndConst[] := mkConst["SND", tyFun[compactRealPairTy, realTy]];
compactFstTm[pT_] := mkComb[compactFstConst[], pT];
compactSndTm[pT_] := mkComb[compactSndConst[], pT];

compactPairInst[th_] := HOL`Kernel`INSTTYPE[
  {mkVarType["A"] -> realTy, mkVarType["B"] -> realTy}, th];
compactFstPairEq[aT_, bT_] := INST[
  {mkVar["a", realTy] -> aT, mkVar["b", realTy] -> bT},
  compactPairInst[HOL`Stdlib`Pair`fstPairEqThm]];
compactSndPairEq[aT_, bT_] := INST[
  {mkVar["a", realTy] -> aT, mkVar["b", realTy] -> bT},
  compactPairInst[HOL`Stdlib`Pair`sndPairEqThm]];

compactTransList[ths_List] := Fold[TRANS, First[ths], Rest[ths]];

compactPairCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[compactPairConsConst[], eqLeft], eqRight];
compactMidpointCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[midpointConst[], eqLeft], eqRight];
compactClosedIntervalSetCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[closedIntervalConst[], eqLeft], eqRight];
compactFiniteSubcoverSetCong[uT_, eqSet_] :=
  HOL`Equal`APTERM[mkComb[compactFiniteSubcoverConstAt[compactCoverIndexTy[uT]], uT],
    eqSet];
compactFiniteSubcoverCong[uT_, eqLeft_, eqRight_] :=
  Module[{midEq, setEq},
    midEq = compactMidpointCong[eqLeft, eqRight];
    setEq = compactClosedIntervalSetCong[eqLeft, midEq];
    compactFiniteSubcoverSetCong[uT, setEq]
  ];
compactNoFiniteSubcoverCong[uT_, eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[
    HOL`Equal`APTERM[mkComb[compactNoFiniteSubcoverConstAt[compactCoverIndexTy[uT]], uT],
      eqLeft], eqRight];
compactRealLeTrans[aT_, bT_, cT_, abTh_, bcTh_] :=
  HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[realLeTransThm, {aT, bT, cT}],
    abTh], bcTh];

compactFalseTm[] := mkConst["F", boolTy];
compactEqfIntro[thNotP_] :=
  Module[{pT, pToF, fToP},
    pT = concl[thNotP][[2]];
    pToF = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], ASSUME[pT]];
    fToP = HOL`Bool`CONTR[pT, ASSUME[compactFalseTm[]]];
    HOL`Kernel`DEDUCTANTISYM[fToP, pToF]
  ];
compactNotEqRight[eqTh_, notLeftTh_] :=
  Module[{rightT, hRight, leftTh, falseTh},
    rightT = concl[eqTh][[2]];
    hRight = ASSUME[rightT];
    leftTh = EQMP[HOL`Equal`SYM[eqTh], hRight];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeftTh], leftTh];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[rightT, falseTh]]
  ];
compactCondReduceT[ty_, condProof_, aT_, bT_] :=
  TRANS[HOL`Equal`APTHM[HOL`Equal`APTHM[
      HOL`Equal`APTERM[HOL`Bool`condConst[ty], HOL`Bool`EQTINTRO[condProof]],
      aT], bT],
    HOL`Bool`ISPEC[bT, HOL`Bool`ISPEC[aT, HOL`Bool`condTThm]]];
compactCondReduceF[ty_, notCondProof_, aT_, bT_] :=
  TRANS[HOL`Equal`APTHM[HOL`Equal`APTHM[
      HOL`Equal`APTERM[HOL`Bool`condConst[ty], compactEqfIntro[notCondProof]],
      aT], bT],
    HOL`Bool`ISPEC[bT, HOL`Bool`ISPEC[aT, HOL`Bool`condFThm]]];

compactBadIntervalTyAt[ty_] :=
  tyFun[compactCoverTyAt[ty], tyFun[realTy, tyFun[realTy, boolTy]]];
badIntervalTy = compactBadIntervalTyAt[iotaTy];

compactBadIntervalBody[uT_, aT_, bT_] :=
  conjTm[realLeTm[aT, bT], noFiniteSubcoverTm[uT, aT, bT]];

badIntervalDefThm =
  Module[{uV, aV, bV},
    uV = mkVar["U", compactCoverTy]; aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    newDefinition[mkEq[mkVar["badInterval", badIntervalTy],
      mkAbs[uV, mkAbs[aV, mkAbs[bV, compactBadIntervalBody[uV, aV, bV]]]]]]
  ];

badIntervalConst[] := mkConst["badInterval", badIntervalTy];
compactBadIntervalConstAt[ty_] := mkConst["badInterval", compactBadIntervalTyAt[ty]];
badIntervalTm[uT_, aT_, bT_] :=
  mkComb[mkComb[mkComb[compactBadIntervalConstAt[compactCoverIndexTy[uT]], uT],
    aT], bT];

unfoldBadInterval[uT_, aT_, bT_] :=
  Module[{def, s1, s1b, s2, s2b, s3},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, badIntervalDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, aT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, bT];
    TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]]
  ];

compactStepIntervalTyAt[ty_] :=
  tyFun[compactCoverTyAt[ty], tyFun[compactRealPairTy, compactRealPairTy]];
stepIntervalTy = compactStepIntervalTyAt[iotaTy];

compactStepIntervalCond[uT_, pT_] :=
  Module[{loT, hiT},
    loT = compactFstTm[pT]; hiT = compactSndTm[pT];
    finiteSubcoverTm[uT, compactClosedIntervalSetTm[loT, midpointTm[loT, hiT]]]
  ];
compactStepIntervalBody[uT_, pT_] :=
  Module[{loT, hiT, midT, rightPair, leftPair},
    loT = compactFstTm[pT]; hiT = compactSndTm[pT]; midT = midpointTm[loT, hiT];
    rightPair = compactPairTm[midT, hiT]; leftPair = compactPairTm[loT, midT];
    mkComb[mkComb[mkComb[HOL`Bool`condConst[compactRealPairTy],
      compactStepIntervalCond[uT, pT]], rightPair], leftPair]
  ];

stepIntervalDefThm =
  Module[{uV, pV},
    uV = mkVar["U", compactCoverTy]; pV = mkVar["p", compactRealPairTy];
    newDefinition[mkEq[mkVar["stepInterval", stepIntervalTy],
      mkAbs[uV, mkAbs[pV, compactStepIntervalBody[uV, pV]]]]]
  ];

stepIntervalConst[] := mkConst["stepInterval", stepIntervalTy];
compactStepIntervalConstAt[ty_] := mkConst["stepInterval", compactStepIntervalTyAt[ty]];
stepIntervalTm[uT_, pT_] :=
  mkComb[mkComb[compactStepIntervalConstAt[compactCoverIndexTy[uT]], uT], pT];

unfoldStepInterval[uT_, pT_] :=
  Module[{def, s1, s1b, s2},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, stepIntervalDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, pT];
    compactBetaClean[TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]]
  ];

compactBisectIntervalTyAt[ty_] :=
  tyFun[compactCoverTyAt[ty],
    tyFun[realTy, tyFun[realTy, compactBisectFunTy]]];
bisectIntervalTy = compactBisectIntervalTyAt[iotaTy];

compactBisectIntervalRecPred[uT_, leftT_, rightT_] :=
  Module[{gV, nV},
    gV = mkVar["gBisect", compactBisectFunTy]; nV = mkVar["nBisect", numTy];
    mkAbs[gV, conjTm[
      mkEq[mkComb[gV, zeroN[]], compactPairTm[leftT, rightT]],
      forallTm[nV, mkEq[mkComb[gV, sucT[nV]], stepIntervalTm[uT, mkComb[gV, nV]]]]]]
  ];

bisectIntervalDefThm =
  Module[{uV, leftV, rightV},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy];
    newDefinition[mkEq[mkVar["bisectInterval", bisectIntervalTy],
      mkAbs[uV, mkAbs[leftV, mkAbs[rightV,
        compactSelectTm[compactBisectFunTy,
          compactBisectIntervalRecPred[uV, leftV, rightV]]]]]]]
  ];

bisectIntervalConst[] := mkConst["bisectInterval", bisectIntervalTy];
compactBisectIntervalConstAt[ty_] :=
  mkConst["bisectInterval", compactBisectIntervalTyAt[ty]];
bisectIntervalTm[uT_, leftT_, rightT_] :=
  mkComb[mkComb[mkComb[compactBisectIntervalConstAt[compactCoverIndexTy[uT]], uT],
    leftT], rightT];
compactBisectAt[uT_, leftT_, rightT_, nT_] :=
  mkComb[bisectIntervalTm[uT, leftT, rightT], nT];

unfoldBisectInterval[uT_, leftT_, rightT_] :=
  Module[{def, s1, s1b, s2, s2b, s3},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]},
      bisectIntervalDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, leftT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, rightT];
    compactBetaClean[TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]]]
  ];

bisectRecSpecThm =
  Module[{uV, leftV, rightV, iter, exIter, sat, folded},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy];
    iter = HOL`Kernel`INSTTYPE[{tyVar["A"] -> compactRealPairTy},
      HOL`Stdlib`Num`numIterationThm];
    exIter = compactBetaClean[HOL`Bool`SPEC[mkAbs[mkVar["pStep", compactRealPairTy],
        stepIntervalTm[uV, mkVar["pStep", compactRealPairTy]]],
      HOL`Bool`SPEC[compactPairTm[leftV, rightV], iter]]];
    sat = HOL`Stdlib`Num`selectOfExists[
      compactBisectIntervalRecPred[uV, leftV, rightV], exIter];
    folded = compactBetaClean[
      HOL`Drule`SUBS[{HOL`Equal`SYM[unfoldBisectInterval[uV, leftV, rightV]]}, sat]];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, folded]]]
  ];

compactBisectRecAt[uT_, leftT_, rightT_] :=
  compactSpecAll[bisectRecSpecThm, {uT, leftT, rightT}];
compactBisectZeroEq[uT_, leftT_, rightT_] :=
  HOL`Bool`CONJUNCT1[compactBisectRecAt[uT, leftT, rightT]];
compactBisectSucEq[uT_, leftT_, rightT_, nT_] :=
  compactBetaClean[HOL`Bool`SPEC[nT,
    HOL`Bool`CONJUNCT2[compactBisectRecAt[uT, leftT, rightT]]]];

compactLowerTyAt[ty_] :=
  tyFun[compactCoverTyAt[ty], tyFun[realTy, tyFun[realTy, tyFun[numTy, realTy]]]];
compactUpperTyAt[ty_] := compactLowerTyAt[ty];
lowerTy = compactLowerTyAt[iotaTy];
upperTy = compactUpperTyAt[iotaTy];

lowerDefThm =
  Module[{uV, leftV, rightV, nV},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    newDefinition[mkEq[mkVar["lower", lowerTy],
      mkAbs[uV, mkAbs[leftV, mkAbs[rightV, mkAbs[nV,
        compactFstTm[compactBisectAt[uV, leftV, rightV, nV]]]]]]]]
  ];

upperDefThm =
  Module[{uV, leftV, rightV, nV},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    newDefinition[mkEq[mkVar["upper", upperTy],
      mkAbs[uV, mkAbs[leftV, mkAbs[rightV, mkAbs[nV,
        compactSndTm[compactBisectAt[uV, leftV, rightV, nV]]]]]]]]
  ];

lowerConst[] := mkConst["lower", lowerTy];
upperConst[] := mkConst["upper", upperTy];
compactLowerConstAt[ty_] := mkConst["lower", compactLowerTyAt[ty]];
compactUpperConstAt[ty_] := mkConst["upper", compactUpperTyAt[ty]];
lowerTm[uT_, leftT_, rightT_] :=
  mkComb[mkComb[mkComb[compactLowerConstAt[compactCoverIndexTy[uT]], uT],
    leftT], rightT];
upperTm[uT_, leftT_, rightT_] :=
  mkComb[mkComb[mkComb[compactUpperConstAt[compactCoverIndexTy[uT]], uT],
    leftT], rightT];
compactLowerAt[uT_, leftT_, rightT_, nT_] := mkComb[lowerTm[uT, leftT, rightT], nT];
compactUpperAt[uT_, leftT_, rightT_, nT_] := mkComb[upperTm[uT, leftT, rightT], nT];

unfoldLower[uT_, leftT_, rightT_, nT_] :=
  Module[{def, s1, s1b, s2, s2b, s3, s3b, s4},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, lowerDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, leftT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, rightT];
    s3b = TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]];
    s4 = HOL`Equal`APTHM[s3b, nT];
    compactBetaClean[TRANS[s4, HOL`Equal`BETACONV[concl[s4][[2]]]]]
  ];

unfoldUpper[uT_, leftT_, rightT_, nT_] :=
  Module[{def, s1, s1b, s2, s2b, s3, s3b, s4},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, upperDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, leftT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, rightT];
    s3b = TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]];
    s4 = HOL`Equal`APTHM[s3b, nT];
    compactBetaClean[TRANS[s4, HOL`Equal`BETACONV[concl[s4][[2]]]]]
  ];

compactStepCondition[uT_, leftT_, rightT_, nT_] :=
  finiteSubcoverTm[uT, compactClosedIntervalSetTm[
    compactLowerAt[uT, leftT, rightT, nT],
    midpointTm[compactLowerAt[uT, leftT, rightT, nT],
      compactUpperAt[uT, leftT, rightT, nT]]]];
compactStepData[uT_, leftT_, rightT_, nT_] :=
  Module[{bisN, loN, hiN, fstN, sndN, midN, midPair},
    bisN = compactBisectAt[uT, leftT, rightT, nT];
    loN = compactLowerAt[uT, leftT, rightT, nT];
    hiN = compactUpperAt[uT, leftT, rightT, nT];
    fstN = compactFstTm[bisN]; sndN = compactSndTm[bisN];
    midN = midpointTm[loN, hiN]; midPair = midpointTm[fstN, sndN];
    {bisN, loN, hiN, fstN, sndN, midN, midPair}
  ];
compactStepConditionEq[uT_, leftT_, rightT_, nT_] :=
  Module[{data, lowerEq, upperEq, midEq, setEq},
    data = compactStepData[uT, leftT, rightT, nT];
    lowerEq = unfoldLower[uT, leftT, rightT, nT];
    upperEq = unfoldUpper[uT, leftT, rightT, nT];
    midEq = compactMidpointCong[lowerEq, upperEq];
    setEq = compactClosedIntervalSetCong[lowerEq, midEq];
    compactFiniteSubcoverSetCong[uT, setEq]
  ];

lowerZeroThm =
  Module[{uV, leftV, rightV, bis0, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; bis0 = compactBisectAt[uV, leftV, rightV, zeroN[]];
    point = compactTransList[{
      unfoldLower[uV, leftV, rightV, zeroN[]],
      HOL`Equal`APTERM[compactFstConst[], compactBisectZeroEq[uV, leftV, rightV]],
      compactFstPairEq[leftV, rightV]}];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, point]]]
  ];

upperZeroThm =
  Module[{uV, leftV, rightV, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy];
    point = compactTransList[{
      unfoldUpper[uV, leftV, rightV, zeroN[]],
      HOL`Equal`APTERM[compactSndConst[], compactBisectZeroEq[uV, leftV, rightV]],
      compactSndPairEq[leftV, rightV]}];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, point]]]
  ];

compactLowerZeroEq[uT_, leftT_, rightT_] :=
  compactSpecAll[lowerZeroThm, {uT, leftT, rightT}];
compactUpperZeroEq[uT_, leftT_, rightT_] :=
  compactSpecAll[upperZeroThm, {uT, leftT, rightT}];

lowerSuccRightThm =
  Module[{uV, leftV, rightV, nV, data, bisN, sndN, midPair, midN, rightPair,
          leftPair, hTm, h, condEq, hPair, condRed, stepToPair, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    data = compactStepData[uV, leftV, rightV, nV];
    bisN = data[[1]]; sndN = data[[5]]; midN = data[[6]]; midPair = data[[7]];
    rightPair = compactPairTm[midPair, sndN];
    leftPair = compactPairTm[data[[4]], midPair];
    hTm = compactStepCondition[uV, leftV, rightV, nV]; h = ASSUME[hTm];
    condEq = compactStepConditionEq[uV, leftV, rightV, nV];
    hPair = EQMP[condEq, h];
    condRed = compactCondReduceT[compactRealPairTy, hPair, rightPair, leftPair];
    stepToPair = TRANS[unfoldStepInterval[uV, bisN], condRed];
    point = compactTransList[{
      unfoldLower[uV, leftV, rightV, sucT[nV]],
      HOL`Equal`APTERM[compactFstConst[], compactBisectSucEq[uV, leftV, rightV, nV]],
      HOL`Equal`APTERM[compactFstConst[], stepToPair],
      compactFstPairEq[midPair, sndN],
      HOL`Equal`SYM[compactMidpointCong[unfoldLower[uV, leftV, rightV, nV],
        unfoldUpper[uV, leftV, rightV, nV]]]}];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hTm, point]]]]]
  ];

upperSuccRightThm =
  Module[{uV, leftV, rightV, nV, data, bisN, sndN, midPair, rightPair,
          leftPair, hTm, h, condEq, hPair, condRed, stepToPair, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    data = compactStepData[uV, leftV, rightV, nV];
    bisN = data[[1]]; sndN = data[[5]]; midPair = data[[7]];
    rightPair = compactPairTm[midPair, sndN];
    leftPair = compactPairTm[data[[4]], midPair];
    hTm = compactStepCondition[uV, leftV, rightV, nV]; h = ASSUME[hTm];
    condEq = compactStepConditionEq[uV, leftV, rightV, nV];
    hPair = EQMP[condEq, h];
    condRed = compactCondReduceT[compactRealPairTy, hPair, rightPair, leftPair];
    stepToPair = TRANS[unfoldStepInterval[uV, bisN], condRed];
    point = compactTransList[{
      unfoldUpper[uV, leftV, rightV, sucT[nV]],
      HOL`Equal`APTERM[compactSndConst[], compactBisectSucEq[uV, leftV, rightV, nV]],
      HOL`Equal`APTERM[compactSndConst[], stepToPair],
      compactSndPairEq[midPair, sndN],
      HOL`Equal`SYM[unfoldUpper[uV, leftV, rightV, nV]]}];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hTm, point]]]]]
  ];

lowerSuccLeftThm =
  Module[{uV, leftV, rightV, nV, data, bisN, fstN, midPair, rightPair,
          leftPair, hTm, h, condEq, hPair, condRed, stepToPair, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    data = compactStepData[uV, leftV, rightV, nV];
    bisN = data[[1]]; fstN = data[[4]]; midPair = data[[7]];
    rightPair = compactPairTm[midPair, data[[5]]];
    leftPair = compactPairTm[fstN, midPair];
    hTm = compactNotTm[compactStepCondition[uV, leftV, rightV, nV]]; h = ASSUME[hTm];
    condEq = compactStepConditionEq[uV, leftV, rightV, nV];
    hPair = compactNotEqRight[condEq, h];
    condRed = compactCondReduceF[compactRealPairTy, hPair, rightPair, leftPair];
    stepToPair = TRANS[unfoldStepInterval[uV, bisN], condRed];
    point = compactTransList[{
      unfoldLower[uV, leftV, rightV, sucT[nV]],
      HOL`Equal`APTERM[compactFstConst[], compactBisectSucEq[uV, leftV, rightV, nV]],
      HOL`Equal`APTERM[compactFstConst[], stepToPair],
      compactFstPairEq[fstN, midPair],
      HOL`Equal`SYM[unfoldLower[uV, leftV, rightV, nV]]}];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hTm, point]]]]]
  ];

upperSuccLeftThm =
  Module[{uV, leftV, rightV, nV, data, bisN, fstN, midPair, midEq, rightPair,
          leftPair, hTm, h, condEq, hPair, condRed, stepToPair, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    data = compactStepData[uV, leftV, rightV, nV];
    bisN = data[[1]]; fstN = data[[4]]; midPair = data[[7]];
    midEq = compactMidpointCong[unfoldLower[uV, leftV, rightV, nV],
      unfoldUpper[uV, leftV, rightV, nV]];
    rightPair = compactPairTm[midPair, data[[5]]];
    leftPair = compactPairTm[fstN, midPair];
    hTm = compactNotTm[compactStepCondition[uV, leftV, rightV, nV]]; h = ASSUME[hTm];
    condEq = compactStepConditionEq[uV, leftV, rightV, nV];
    hPair = compactNotEqRight[condEq, h];
    condRed = compactCondReduceF[compactRealPairTy, hPair, rightPair, leftPair];
    stepToPair = TRANS[unfoldStepInterval[uV, bisN], condRed];
    point = compactTransList[{
      unfoldUpper[uV, leftV, rightV, sucT[nV]],
      HOL`Equal`APTERM[compactSndConst[], compactBisectSucEq[uV, leftV, rightV, nV]],
      HOL`Equal`APTERM[compactSndConst[], stepToPair],
      compactSndPairEq[fstN, midPair],
      HOL`Equal`SYM[midEq]}];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hTm, point]]]]]
  ];

compactBadFromParts[uT_, aT_, bT_, leTh_, noTh_] :=
  EQMP[HOL`Equal`SYM[unfoldBadInterval[uT, aT, bT]], HOL`Bool`CONJ[leTh, noTh]];
compactNoFiniteFromNot[uT_, aT_, bT_, notTh_] :=
  EQMP[HOL`Equal`SYM[unfoldNoFiniteSubcover[uT, aT, bT]], notTh];
compactLowerSuccRightEq[uT_, leftT_, rightT_, nT_, hTh_] :=
  HOL`Bool`MP[compactSpecAll[lowerSuccRightThm, {uT, leftT, rightT, nT}], hTh];
compactUpperSuccRightEq[uT_, leftT_, rightT_, nT_, hTh_] :=
  HOL`Bool`MP[compactSpecAll[upperSuccRightThm, {uT, leftT, rightT, nT}], hTh];
compactLowerSuccLeftEq[uT_, leftT_, rightT_, nT_, hTh_] :=
  HOL`Bool`MP[compactSpecAll[lowerSuccLeftThm, {uT, leftT, rightT, nT}], hTh];
compactUpperSuccLeftEq[uT_, leftT_, rightT_, nT_, hTh_] :=
  HOL`Bool`MP[compactSpecAll[upperSuccLeftThm, {uT, leftT, rightT, nT}], hTh];

badIntervalsThm =
  Module[{uV, leftV, rightV, nV, nInd, hLeTm, hLe, hBadTm, hBad, pLam,
          lo0, hi0, l0Eq, u0Eq, baseLe, baseNo, base, ihTm, ih, loN, hiN,
          midN, loS, hiS, ihOpen, ihLe, ihNo, condTm, em, hLeft, hNot,
          rightBad, lEq, uEq, midLe, branchRightLe, branchRightNo, branchRight,
          noLeft, leftMidLe, branchLeftLe, branchLeftNo, branchLeft, stepPoint,
          stepAll, indSpec, indAll},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    pLam = Module[{kP},
      kP = mkVar["kBad", numTy];
      mkAbs[kP, badIntervalTm[uV, compactLowerAt[uV, leftV, rightV, kP],
        compactUpperAt[uV, leftV, rightV, kP]]]
    ];

    lo0 = compactLowerAt[uV, leftV, rightV, zeroN[]];
    hi0 = compactUpperAt[uV, leftV, rightV, zeroN[]];
    l0Eq = compactLowerZeroEq[uV, leftV, rightV];
    u0Eq = compactUpperZeroEq[uV, leftV, rightV];
    baseLe = EQMP[compactRealLeCong[HOL`Equal`SYM[l0Eq], HOL`Equal`SYM[u0Eq]], hLe];
    baseNo = EQMP[compactNoFiniteSubcoverCong[uV, HOL`Equal`SYM[l0Eq],
      HOL`Equal`SYM[u0Eq]], hBad];
    base = compactBadFromParts[uV, lo0, hi0, baseLe, baseNo];

    nInd = mkVar["nBad", numTy];
    loN = compactLowerAt[uV, leftV, rightV, nInd];
    hiN = compactUpperAt[uV, leftV, rightV, nInd];
    midN = midpointTm[loN, hiN];
    loS = compactLowerAt[uV, leftV, rightV, sucT[nInd]];
    hiS = compactUpperAt[uV, leftV, rightV, sucT[nInd]];
    ihTm = badIntervalTm[uV, loN, hiN]; ih = ASSUME[ihTm];
    ihOpen = EQMP[unfoldBadInterval[uV, loN, hiN], ih];
    ihLe = HOL`Bool`CONJUNCT1[ihOpen]; ihNo = HOL`Bool`CONJUNCT2[ihOpen];
    condTm = compactStepCondition[uV, leftV, rightV, nInd];
    em = HOL`Bool`EXCLUDEDMIDDLE[condTm];

    hLeft = ASSUME[condTm];
    rightBad = HOL`Bool`MP[
      HOL`Bool`MP[compactSpecAll[rightHalfBadThm, {uV, loN, hiN, midN}], ihNo],
      hLeft];
    lEq = compactLowerSuccRightEq[uV, leftV, rightV, nInd, hLeft];
    uEq = compactUpperSuccRightEq[uV, leftV, rightV, nInd, hLeft];
    midLe = HOL`Bool`MP[compactSpecAll[midpointLeRightThm, {loN, hiN}], ihLe];
    branchRightLe = EQMP[compactRealLeCong[HOL`Equal`SYM[lEq], HOL`Equal`SYM[uEq]],
      midLe];
    branchRightNo = EQMP[compactNoFiniteSubcoverCong[uV, HOL`Equal`SYM[lEq],
      HOL`Equal`SYM[uEq]], rightBad];
    branchRight = compactBadFromParts[uV, loS, hiS, branchRightLe, branchRightNo];

    hNot = ASSUME[compactNotTm[condTm]];
    noLeft = compactNoFiniteFromNot[uV, loN, midN, hNot];
    lEq = compactLowerSuccLeftEq[uV, leftV, rightV, nInd, hNot];
    uEq = compactUpperSuccLeftEq[uV, leftV, rightV, nInd, hNot];
    leftMidLe = HOL`Bool`MP[compactSpecAll[leftLeMidpointThm, {loN, hiN}], ihLe];
    branchLeftLe = EQMP[compactRealLeCong[HOL`Equal`SYM[lEq], HOL`Equal`SYM[uEq]],
      leftMidLe];
    branchLeftNo = EQMP[compactNoFiniteSubcoverCong[uV, HOL`Equal`SYM[lEq],
      HOL`Equal`SYM[uEq]], noLeft];
    branchLeft = compactBadFromParts[uV, loS, hiS, branchLeftLe, branchLeftNo];

    stepPoint = HOL`Bool`DISJCASES[em, branchRight, branchLeft];
    stepAll = HOL`Bool`GEN[nInd, HOL`Bool`DISCH[ihTm, stepPoint]];
    indSpec = compactBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, indAll]]]]]
  ];

intervalOrderThm =
  Module[{uV, leftV, rightV, nV, hLeTm, hLe, hBadTm, hBad, badAll, badN,
          opened, point, allN},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    badAll = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[badIntervalsThm,
      {uV, leftV, rightV}], hLe], hBad];
    badN = HOL`Bool`SPEC[nV, badAll];
    opened = EQMP[unfoldBadInterval[uV, compactLowerAt[uV, leftV, rightV, nV],
      compactUpperAt[uV, leftV, rightV, nV]], badN];
    point = HOL`Bool`CONJUNCT1[opened];
    allN = HOL`Bool`GEN[nV, point];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, allN]]]]]
  ];

compactIntervalOrderAt[uT_, leftT_, rightT_, hLeTh_, hBadTh_, nT_] :=
  HOL`Bool`SPEC[nT, HOL`Bool`MP[HOL`Bool`MP[
    compactSpecAll[intervalOrderThm, {uT, leftT, rightT}], hLeTh], hBadTh]];

lowerStepLeThm =
  Module[{uV, leftV, rightV, nV, hLeTm, hLe, hBadTm, hBad, loN, hiN, loS,
          orderN, condTm, em, hLeft, hNot, lEq, leMid, branchT, refl, branchF,
          point, allN},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    loN = compactLowerAt[uV, leftV, rightV, nV];
    hiN = compactUpperAt[uV, leftV, rightV, nV];
    loS = compactLowerAt[uV, leftV, rightV, sucT[nV]];
    orderN = compactIntervalOrderAt[uV, leftV, rightV, hLe, hBad, nV];
    condTm = compactStepCondition[uV, leftV, rightV, nV];
    em = HOL`Bool`EXCLUDEDMIDDLE[condTm];

    hLeft = ASSUME[condTm];
    lEq = compactLowerSuccRightEq[uV, leftV, rightV, nV, hLeft];
    leMid = HOL`Bool`MP[compactSpecAll[leftLeMidpointThm, {loN, hiN}], orderN];
    branchT = EQMP[compactRealLeCong[REFL[loN], HOL`Equal`SYM[lEq]], leMid];

    hNot = ASSUME[compactNotTm[condTm]];
    lEq = compactLowerSuccLeftEq[uV, leftV, rightV, nV, hNot];
    refl = HOL`Bool`SPEC[loN, realLeReflThm];
    branchF = EQMP[compactRealLeCong[REFL[loN], HOL`Equal`SYM[lEq]], refl];

    point = HOL`Bool`DISJCASES[em, branchT, branchF];
    allN = HOL`Bool`GEN[nV, point];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, allN]]]]]
  ];

upperStepLeThm =
  Module[{uV, leftV, rightV, nV, hLeTm, hLe, hBadTm, hBad, loN, hiN, hiS,
          orderN, condTm, em, hLeft, hNot, uEq, refl, branchT, leMid, branchF,
          point, allN},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    loN = compactLowerAt[uV, leftV, rightV, nV];
    hiN = compactUpperAt[uV, leftV, rightV, nV];
    hiS = compactUpperAt[uV, leftV, rightV, sucT[nV]];
    orderN = compactIntervalOrderAt[uV, leftV, rightV, hLe, hBad, nV];
    condTm = compactStepCondition[uV, leftV, rightV, nV];
    em = HOL`Bool`EXCLUDEDMIDDLE[condTm];

    hLeft = ASSUME[condTm];
    uEq = compactUpperSuccRightEq[uV, leftV, rightV, nV, hLeft];
    refl = HOL`Bool`SPEC[hiN, realLeReflThm];
    branchT = EQMP[compactRealLeCong[HOL`Equal`SYM[uEq], REFL[hiN]], refl];

    hNot = ASSUME[compactNotTm[condTm]];
    uEq = compactUpperSuccLeftEq[uV, leftV, rightV, nV, hNot];
    leMid = HOL`Bool`MP[compactSpecAll[midpointLeRightThm, {loN, hiN}], orderN];
    branchF = EQMP[compactRealLeCong[HOL`Equal`SYM[uEq], REFL[hiN]], leMid];

    point = HOL`Bool`DISJCASES[em, branchT, branchF];
    allN = HOL`Bool`GEN[nV, point];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, allN]]]]]
  ];

compactNumLeZeroEqThm =
  Module[{nV},
    nV = mkVar["n", numTy];
    HOL`Auto`Arith`arithProve[forallTm[nV,
      impTm[compactNatLe[nV, zeroN[]], mkEq[nV, zeroN[]]]]]
  ];

compactLowerStepAt[uT_, leftT_, rightT_, hLeTh_, hBadTh_, nT_] :=
  HOL`Bool`SPEC[nT, HOL`Bool`MP[HOL`Bool`MP[
    compactSpecAll[lowerStepLeThm, {uT, leftT, rightT}], hLeTh], hBadTh]];
compactUpperStepAt[uT_, leftT_, rightT_, hLeTh_, hBadTh_, nT_] :=
  HOL`Bool`SPEC[nT, HOL`Bool`MP[HOL`Bool`MP[
    compactSpecAll[upperStepLeThm, {uT, leftT, rightT}], hLeTh], hBadTh]];

lowerMonoThm =
  Module[{uV, leftV, rightV, mInd, nV, hLeTm, hLe, hBadTm, hBad, lowerSeq,
          pLam, hLeBase, nEq0, appEq, baseRefl, base, ihTm, ih, hLeSuc,
          caseTh, hLeM, ihLe, stepLe, branchA, hEqSuc, appEqS, branchB,
          stepPoint, stepAll, indSpec, indAll, mV, hLeFinal, finalPoint},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    lowerSeq = lowerTm[uV, leftV, rightV];
    pLam = Module[{mP, nP},
      mP = mkVar["mLower", numTy]; nP = mkVar["nLower", numTy];
      mkAbs[mP, forallTm[nP, impTm[compactNatLe[nP, mP],
        realLeTm[mkComb[lowerSeq, nP], mkComb[lowerSeq, mP]]]]]
    ];

    hLeBase = ASSUME[compactNatLe[nV, zeroN[]]];
    nEq0 = HOL`Bool`MP[HOL`Bool`SPEC[nV, compactNumLeZeroEqThm], hLeBase];
    appEq = HOL`Equal`APTERM[lowerSeq, nEq0];
    baseRefl = HOL`Bool`SPEC[mkComb[lowerSeq, zeroN[]], realLeReflThm];
    base = HOL`Bool`GEN[nV, HOL`Bool`DISCH[compactNatLe[nV, zeroN[]],
      EQMP[compactRealLeCong[HOL`Equal`SYM[appEq],
        REFL[mkComb[lowerSeq, zeroN[]]]], baseRefl]]];

    mInd = mkVar["mLowerInd", numTy];
    ihTm = forallTm[nV, impTm[compactNatLe[nV, mInd],
      realLeTm[mkComb[lowerSeq, nV], mkComb[lowerSeq, mInd]]]];
    ih = ASSUME[ihTm];
    hLeSuc = ASSUME[compactNatLe[nV, sucT[mInd]]];
    caseTh = HOL`Bool`MP[
      HOL`Bool`SPEC[mInd, HOL`Bool`SPEC[nV, HOL`Stdlib`Num`leqSucCaseThm]],
      hLeSuc];
    hLeM = ASSUME[compactNatLe[nV, mInd]];
    ihLe = HOL`Bool`MP[HOL`Bool`SPEC[nV, ih], hLeM];
    stepLe = compactLowerStepAt[uV, leftV, rightV, hLe, hBad, mInd];
    branchA = compactRealLeTrans[mkComb[lowerSeq, nV], mkComb[lowerSeq, mInd],
      mkComb[lowerSeq, sucT[mInd]], ihLe, stepLe];
    hEqSuc = ASSUME[mkEq[nV, sucT[mInd]]];
    appEqS = HOL`Equal`APTERM[lowerSeq, hEqSuc];
    branchB = EQMP[compactRealLeCong[HOL`Equal`SYM[appEqS],
      REFL[mkComb[lowerSeq, sucT[mInd]]]],
      HOL`Bool`SPEC[mkComb[lowerSeq, sucT[mInd]], realLeReflThm]];
    stepPoint = HOL`Bool`DISJCASES[caseTh, branchA, branchB];
    stepAll = HOL`Bool`GEN[mInd, HOL`Bool`DISCH[ihTm,
      HOL`Bool`GEN[nV, HOL`Bool`DISCH[compactNatLe[nV, sucT[mInd]], stepPoint]]]];

    indSpec = compactBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    hLeFinal = ASSUME[compactNatLe[nV, mV]];
    finalPoint = HOL`Bool`MP[HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, indAll]], hLeFinal];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm,
        HOL`Bool`GEN[nV, HOL`Bool`GEN[mV,
          HOL`Bool`DISCH[compactNatLe[nV, mV], finalPoint]]]]]]]]
  ];

upperAntitoneThm =
  Module[{uV, leftV, rightV, mInd, nV, hLeTm, hLe, hBadTm, hBad, upperSeq,
          pLam, hLeBase, nEq0, appEq, baseRefl, base, ihTm, ih, hLeSuc,
          caseTh, hLeM, ihLe, stepLe, branchA, hEqSuc, appEqS, branchB,
          stepPoint, stepAll, indSpec, indAll, mV, hLeFinal, finalPoint},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    upperSeq = upperTm[uV, leftV, rightV];
    pLam = Module[{mP, nP},
      mP = mkVar["mUpper", numTy]; nP = mkVar["nUpper", numTy];
      mkAbs[mP, forallTm[nP, impTm[compactNatLe[nP, mP],
        realLeTm[mkComb[upperSeq, mP], mkComb[upperSeq, nP]]]]]
    ];

    hLeBase = ASSUME[compactNatLe[nV, zeroN[]]];
    nEq0 = HOL`Bool`MP[HOL`Bool`SPEC[nV, compactNumLeZeroEqThm], hLeBase];
    appEq = HOL`Equal`APTERM[upperSeq, nEq0];
    baseRefl = HOL`Bool`SPEC[mkComb[upperSeq, zeroN[]], realLeReflThm];
    base = HOL`Bool`GEN[nV, HOL`Bool`DISCH[compactNatLe[nV, zeroN[]],
      EQMP[compactRealLeCong[REFL[mkComb[upperSeq, zeroN[]]],
        HOL`Equal`SYM[appEq]], baseRefl]]];

    mInd = mkVar["mUpperInd", numTy];
    ihTm = forallTm[nV, impTm[compactNatLe[nV, mInd],
      realLeTm[mkComb[upperSeq, mInd], mkComb[upperSeq, nV]]]];
    ih = ASSUME[ihTm];
    hLeSuc = ASSUME[compactNatLe[nV, sucT[mInd]]];
    caseTh = HOL`Bool`MP[
      HOL`Bool`SPEC[mInd, HOL`Bool`SPEC[nV, HOL`Stdlib`Num`leqSucCaseThm]],
      hLeSuc];
    hLeM = ASSUME[compactNatLe[nV, mInd]];
    ihLe = HOL`Bool`MP[HOL`Bool`SPEC[nV, ih], hLeM];
    stepLe = compactUpperStepAt[uV, leftV, rightV, hLe, hBad, mInd];
    branchA = compactRealLeTrans[mkComb[upperSeq, sucT[mInd]],
      mkComb[upperSeq, mInd], mkComb[upperSeq, nV], stepLe, ihLe];
    hEqSuc = ASSUME[mkEq[nV, sucT[mInd]]];
    appEqS = HOL`Equal`APTERM[upperSeq, hEqSuc];
    branchB = EQMP[compactRealLeCong[REFL[mkComb[upperSeq, sucT[mInd]]],
      HOL`Equal`SYM[appEqS]],
      HOL`Bool`SPEC[mkComb[upperSeq, sucT[mInd]], realLeReflThm]];
    stepPoint = HOL`Bool`DISJCASES[caseTh, branchA, branchB];
    stepAll = HOL`Bool`GEN[mInd, HOL`Bool`DISCH[ihTm,
      HOL`Bool`GEN[nV, HOL`Bool`DISCH[compactNatLe[nV, sucT[mInd]], stepPoint]]]];

    indSpec = compactBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    hLeFinal = ASSUME[compactNatLe[nV, mV]];
    finalPoint = HOL`Bool`MP[HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, indAll]], hLeFinal];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm,
        HOL`Bool`GEN[nV, HOL`Bool`GEN[mV,
          HOL`Bool`DISCH[compactNatLe[nV, mV], finalPoint]]]]]]]]
  ];

nestedIntervalsThm =
  Module[{uV, leftV, rightV, hLeTm, hLe, hBadTm, hBad, lowerSeq, upperSeq,
          orderAll, lowerAll, upperAll, body, folded},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    lowerSeq = lowerTm[uV, leftV, rightV]; upperSeq = upperTm[uV, leftV, rightV];
    orderAll = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[intervalOrderThm,
      {uV, leftV, rightV}], hLe], hBad];
    lowerAll = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[lowerMonoThm,
      {uV, leftV, rightV}], hLe], hBad];
    upperAll = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[upperAntitoneThm,
      {uV, leftV, rightV}], hLe], hBad];
    body = HOL`Bool`CONJ[orderAll, HOL`Bool`CONJ[lowerAll, upperAll]];
    folded = EQMP[HOL`Equal`SYM[unfoldNestedIntervals[lowerSeq, upperSeq]], body];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, folded]]]]]
  ];

compactRealAddCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], eqLeft], eqRight];
compactRealNegCong[eq_] := HOL`Equal`APTERM[realNegConst[], eq];
compactRealMulCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realMulConst[], eqLeft], eqRight];
compactRealMulCongLeft[eqLeft_, rightT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realMulConst[], eqLeft], REFL[rightT]];
compactRealMulCongRight[leftT_, eqRight_] :=
  HOL`Equal`APTERM[mkComb[realMulConst[], leftT], eqRight];

compactOneReal[] := realOfRatTm[oneQ[]];

compactMulComm[xT_, yT_] :=
  HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMulCommThm]];
compactMulAssoc[xT_, yT_, zT_] :=
  HOL`Bool`SPEC[zT, HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMulAssocThm]]];
compactMulOneLeft[xT_] :=
  TRANS[compactMulComm[compactOneReal[], xT], HOL`Bool`SPEC[xT, realMulOneThm]];

compactMulFourShuffleThm =
  Module[{aV, bV, cV, dV, cd, bd, e1, e2, e3, e4, e5, point},
    aV = mkVar["aMulFour", realTy]; bV = mkVar["bMulFour", realTy];
    cV = mkVar["cMulFour", realTy]; dV = mkVar["dMulFour", realTy];
    cd = realMulTm[cV, dV]; bd = realMulTm[bV, dV];
    e1 = compactMulAssoc[aV, bV, cd];
    e2 = compactRealMulCongRight[aV, compactMulComm[bV, cd]];
    e3 = compactRealMulCongRight[aV, compactMulAssoc[cV, dV, bV]];
    e4 = compactRealMulCongRight[aV,
      compactRealMulCongRight[cV, compactMulComm[dV, bV]]];
    e5 = HOL`Equal`SYM[compactMulAssoc[aV, cV, bd]];
    point = compactTransList[{e1, e2, e3, e4, e5}];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV, point]]]]
  ];

compactSubNonnegThm =
  Module[{aV, bV},
    aV = mkVar["aSubNonneg", realTy]; bV = mkVar["bSubNonneg", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{aV, bV}, impTm[realLeTm[aV, bV],
        realLeTm[zeroRealTm[], realAddTm[bV, realNegTm[aV]]]]]]
  ];

compactSubLeSubThm =
  Module[{unV, uNV, lNV, lnV},
    unV = mkVar["uppernSubLe", realTy]; uNV = mkVar["upperNSubLe", realTy];
    lNV = mkVar["lowerNSubLe", realTy]; lnV = mkVar["lowernSubLe", realTy];
    HOL`Auto`RealArith`realArithProve[
      compactForallList[{unV, uNV, lNV, lnV},
        compactImpList[{realLeTm[unV, uNV], realLeTm[lNV, lnV]},
          realLeTm[realAddTm[unV, realNegTm[lnV]],
            realAddTm[uNV, realNegTm[lNV]]]]]]
  ];

compactDropZeroThm =
  Module[{zV},
    zV = mkVar["zDropZero", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[zV, mkEq[realAddTm[zV, realNegTm[zeroRealTm[]]], zV]]]
  ];

compactTwoNeZeroThm =
  Module[{twoPos},
    twoPos = HOL`Auto`RealArith`realArithProve[
      realLtTm[zeroRealTm[], compactTwoReal[]]];
    HOL`Bool`MP[HOL`Bool`SPEC[compactTwoReal[], seqArithPosNeZeroThm], twoPos]
  ];

compactLengthTyAt[ty_] := compactLowerTyAt[ty];
lengthTy = compactLengthTyAt[iotaTy];

compactLengthBody[uT_, leftT_, rightT_, nT_] :=
  realAddTm[compactUpperAt[uT, leftT, rightT, nT],
    realNegTm[compactLowerAt[uT, leftT, rightT, nT]]];

intervalLengthDefThm =
  Module[{uV, leftV, rightV, nV},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    newDefinition[mkEq[mkVar["length", lengthTy],
      mkAbs[uV, mkAbs[leftV, mkAbs[rightV, mkAbs[nV,
        compactLengthBody[uV, leftV, rightV, nV]]]]]]]
  ];

HOL`Stdlib`Real`intervalLengthConst[] := mkConst["length", lengthTy];
compactLengthConstAt[ty_] := mkConst["length", compactLengthTyAt[ty]];
intervalLengthTm[uT_, leftT_, rightT_] :=
  mkComb[mkComb[mkComb[compactLengthConstAt[compactCoverIndexTy[uT]], uT],
    leftT], rightT];
compactLengthAt[uT_, leftT_, rightT_, nT_] := mkComb[intervalLengthTm[uT, leftT, rightT], nT];

unfoldIntervalLengthFun[uT_, leftT_, rightT_] :=
  Module[{def, s1, s1b, s2, s2b, s3},
    def = HOL`Kernel`INSTTYPE[{iotaTy -> compactCoverIndexTy[uT]}, intervalLengthDefThm];
    s1 = HOL`Equal`APTHM[def, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, leftT];
    s2b = TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]];
    s3 = HOL`Equal`APTHM[s2b, rightT];
    compactBetaClean[TRANS[s3, HOL`Equal`BETACONV[concl[s3][[2]]]]]
  ];

unfoldIntervalLength[uT_, leftT_, rightT_, nT_] :=
  Module[{s1, s2},
    s1 = HOL`Equal`APTHM[unfoldIntervalLengthFun[uT, leftT, rightT], nT];
    s2 = HOL`Equal`BETACONV[concl[s1][[2]]];
    compactBetaClean[TRANS[s1, s2]]
  ];

lengthZeroThm =
  Module[{uV, leftV, rightV, lEq, uEq, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy];
    lEq = compactLowerZeroEq[uV, leftV, rightV];
    uEq = compactUpperZeroEq[uV, leftV, rightV];
    point = TRANS[unfoldIntervalLength[uV, leftV, rightV, zeroN[]],
      compactRealAddCong[uEq, compactRealNegCong[lEq]]];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, point]]]
  ];

lengthSuccThm =
  Module[{uV, leftV, rightV, nV, loN, hiN, lenN, lenS, rhs, condTm, em,
          hLeft, uEq, lEq, branchT, hNot, branchF},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    loN = compactLowerAt[uV, leftV, rightV, nV];
    hiN = compactUpperAt[uV, leftV, rightV, nV];
    lenN = compactLengthAt[uV, leftV, rightV, nV];
    lenS = compactLengthAt[uV, leftV, rightV, sucT[nV]];
    rhs = realMulTm[lenN, compactHalfScalar[]];
    condTm = compactStepCondition[uV, leftV, rightV, nV];
    em = HOL`Bool`EXCLUDEDMIDDLE[condTm];

    hLeft = ASSUME[condTm];
    uEq = compactUpperSuccRightEq[uV, leftV, rightV, nV, hLeft];
    lEq = compactLowerSuccRightEq[uV, leftV, rightV, nV, hLeft];
    branchT = compactTransList[{
      unfoldIntervalLength[uV, leftV, rightV, sucT[nV]],
      compactRealAddCong[uEq, compactRealNegCong[lEq]],
      compactSpecAll[rightSubMidpointThm, {loN, hiN}],
      compactRealMulCongLeft[HOL`Equal`SYM[unfoldIntervalLength[uV, leftV, rightV, nV]],
        compactHalfScalar[]]}];

    hNot = ASSUME[compactNotTm[condTm]];
    uEq = compactUpperSuccLeftEq[uV, leftV, rightV, nV, hNot];
    lEq = compactLowerSuccLeftEq[uV, leftV, rightV, nV, hNot];
    branchF = compactTransList[{
      unfoldIntervalLength[uV, leftV, rightV, sucT[nV]],
      compactRealAddCong[uEq, compactRealNegCong[lEq]],
      compactSpecAll[midpointSubLeftThm, {loN, hiN}],
      compactRealMulCongLeft[HOL`Equal`SYM[unfoldIntervalLength[uV, leftV, rightV, nV]],
        compactHalfScalar[]]}];

    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[nV,
      HOL`Bool`DISJCASES[em, branchT, branchF]]]]]
  ];

lengthInvariantThm =
  Module[{uV, leftV, rightV, nInd, pLam, lT, len0, baseStep, base, ihTm, ih,
          lenN, lenS, dN, dS, recEq, shuffle, invTwo, oneStep, stepPoint,
          stepAll, indSpec, indAll, nV, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    lT = realAddTm[rightV, realNegTm[leftV]];
    pLam = Module[{kInv},
      kInv = mkVar["kLengthInv", numTy];
      mkAbs[kInv, mkEq[
        realMulTm[dyadicTm[kInv], compactLengthAt[uV, leftV, rightV, kInv]],
        lT]]
    ];

    len0 = compactLengthAt[uV, leftV, rightV, zeroN[]];
    baseStep = compactRealMulCong[dyadicZeroThm,
      compactSpecAll[lengthZeroThm, {uV, leftV, rightV}]];
    base = TRANS[baseStep, compactMulOneLeft[lT]];

    nInd = mkVar["nLengthInv", numTy];
    lenN = compactLengthAt[uV, leftV, rightV, nInd];
    lenS = compactLengthAt[uV, leftV, rightV, sucT[nInd]];
    dN = dyadicTm[nInd]; dS = dyadicTm[sucT[nInd]];
    ihTm = mkEq[realMulTm[dN, lenN], lT]; ih = ASSUME[ihTm];
    recEq = compactRealMulCong[
      HOL`Bool`SPEC[nInd, dyadicSuccThm],
      compactSpecAll[lengthSuccThm, {uV, leftV, rightV, nInd}]];
    shuffle = compactSpecAll[compactMulFourShuffleThm,
      {dN, compactTwoReal[], lenN, compactHalfScalar[]}];
    invTwo = HOL`Bool`MP[HOL`Bool`SPEC[compactTwoReal[], realMulInvThm],
      compactTwoNeZeroThm];
    oneStep = compactRealMulCongRight[realMulTm[dN, lenN], invTwo];
    stepPoint = compactTransList[{recEq, shuffle, oneStep,
      HOL`Bool`SPEC[realMulTm[dN, lenN], realMulOneThm], ih}];
    stepAll = HOL`Bool`GEN[nInd, HOL`Bool`DISCH[ihTm, stepPoint]];

    indSpec = compactBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    point = HOL`Bool`SPEC[nV, indAll];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[nV, point]]]]
  ];

lengthFormulaThm =
  Module[{uV, leftV, rightV, nV, lenN, dN, invD, lT, invEq, dNe, invLaw,
          invLeft, leftCancel, scaled, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    lenN = compactLengthAt[uV, leftV, rightV, nV];
    dN = dyadicTm[nV]; invD = compactRealInv[dN];
    lT = realAddTm[rightV, realNegTm[leftV]];
    invEq = compactSpecAll[lengthInvariantThm, {uV, leftV, rightV, nV}];
    dNe = HOL`Bool`SPEC[nV, dyadicNeZeroThm];
    invLaw = HOL`Bool`MP[HOL`Bool`SPEC[dN, realMulInvThm], dNe];
    invLeft = TRANS[compactMulComm[invD, dN], invLaw];
    leftCancel = compactTransList[{
      HOL`Equal`SYM[compactMulAssoc[invD, dN, lenN]],
      compactRealMulCongLeft[invLeft, lenN],
      compactMulOneLeft[lenN]}];
    scaled = compactRealMulCongRight[invD, invEq];
    point = compactTransList[{HOL`Equal`SYM[leftCancel], scaled, compactMulComm[invD, lT]}];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV, HOL`Bool`GEN[nV, point]]]]
  ];

lengthNonnegThm =
  Module[{uV, leftV, rightV, nV, hLeTm, hLe, hBadTm, hBad, loN, hiN, order,
          raw, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; nV = mkVar["n", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    loN = compactLowerAt[uV, leftV, rightV, nV];
    hiN = compactUpperAt[uV, leftV, rightV, nV];
    order = compactIntervalOrderAt[uV, leftV, rightV, hLe, hBad, nV];
    raw = HOL`Bool`MP[compactSpecAll[compactSubNonnegThm, {loN, hiN}], order];
    point = EQMP[compactRealLeCong[REFL[zeroRealTm[]],
      HOL`Equal`SYM[unfoldIntervalLength[uV, leftV, rightV, nV]]], raw];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, HOL`Bool`GEN[nV, point]]]]]]
  ];

lengthDecreaseThm =
  Module[{uV, leftV, rightV, bigN, nV, hLeTm, hLe, hBadTm, hBad, hNatTm, hNat,
          lowerAll, upperAll, lowerLe, upperLe, raw, point},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; bigN = mkVar["N", numTy];
    nV = mkVar["n", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    hNatTm = compactNatLe[bigN, nV]; hNat = ASSUME[hNatTm];
    lowerAll = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[lowerMonoThm,
      {uV, leftV, rightV}], hLe], hBad];
    upperAll = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[upperAntitoneThm,
      {uV, leftV, rightV}], hLe], hBad];
    lowerLe = HOL`Bool`MP[compactSpecAll[lowerAll, {bigN, nV}], hNat];
    upperLe = HOL`Bool`MP[compactSpecAll[upperAll, {bigN, nV}], hNat];
    raw = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[compactSubLeSubThm,
      {compactUpperAt[uV, leftV, rightV, nV], compactUpperAt[uV, leftV, rightV, bigN],
        compactLowerAt[uV, leftV, rightV, bigN], compactLowerAt[uV, leftV, rightV, nV]}],
      upperLe], lowerLe];
    point = EQMP[compactRealLeCong[
      HOL`Equal`SYM[unfoldIntervalLength[uV, leftV, rightV, nV]],
      HOL`Equal`SYM[unfoldIntervalLength[uV, leftV, rightV, bigN]]], raw];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm,
        HOL`Bool`GEN[bigN, HOL`Bool`GEN[nV, HOL`Bool`DISCH[hNatTm, point]]]]]]]]
  ];

compactLengthTendstoZeroThm =
  Module[{uV, leftV, rightV, eV, bigN, nV, hLeTm, hLe, hBadTm, hBad, hETm,
          hE, lenSeq, lT, hLNonneg, arch, hSmallTm, hSmall, hNatTm, hNat,
          lenN, lenBig, formula, lenBigLt, dec, lenLt, nonneg, absPos,
          dropZero, absDrop, absEq, point, allN, exN, chosen, epsAll, folded},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy]; eV = mkVar["e", realTy];
    bigN = mkVar["bigNLength", numTy]; nV = mkVar["n", numTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    hETm = realLtTm[zeroRealTm[], eV]; hE = ASSUME[hETm];
    lenSeq = intervalLengthTm[uV, leftV, rightV];
    lT = realAddTm[rightV, realNegTm[leftV]];
    hLNonneg = HOL`Bool`MP[compactSpecAll[compactSubNonnegThm, {leftV, rightV}], hLe];
    arch = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[dyadicArchThm, {lT, eV}],
      hLNonneg], hE];

    hSmallTm = realLtTm[realMulTm[lT, compactRealInv[dyadicTm[bigN]]], eV];
    hSmall = ASSUME[hSmallTm];
    hNatTm = compactNatLe[bigN, nV]; hNat = ASSUME[hNatTm];
    lenN = compactLengthAt[uV, leftV, rightV, nV];
    lenBig = compactLengthAt[uV, leftV, rightV, bigN];
    formula = compactSpecAll[lengthFormulaThm, {uV, leftV, rightV, bigN}];
    lenBigLt = EQMP[compactRealLtCong[HOL`Equal`SYM[formula], REFL[eV]], hSmall];
    dec = HOL`Bool`MP[compactSpecAll[
      HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[lengthDecreaseThm,
        {uV, leftV, rightV}], hLe], hBad], {bigN, nV}], hNat];
    lenLt = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[realLeLtTransThm,
      {lenN, lenBig, eV}], dec], lenBigLt];
    nonneg = HOL`Bool`SPEC[nV, HOL`Bool`MP[HOL`Bool`MP[
      compactSpecAll[lengthNonnegThm, {uV, leftV, rightV}], hLe], hBad]];
    absPos = HOL`Bool`MP[HOL`Bool`SPEC[lenN, realAbsPosThm], nonneg];
    dropZero = HOL`Bool`SPEC[lenN, compactDropZeroThm];
    absDrop = HOL`Equal`APTERM[realAbsConst[], dropZero];
    absEq = TRANS[absDrop, absPos];
    point = EQMP[compactRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], lenLt];
    allN = HOL`Bool`GEN[nV, HOL`Bool`DISCH[hNatTm, point]];
    exN = HOL`Bool`EXISTS[existsTm[bigN, forallTm[nV,
      impTm[compactNatLe[bigN, nV],
        realLtTm[compactRealAbs[realAddTm[compactLengthAt[uV, leftV, rightV, nV],
          realNegTm[zeroRealTm[]]]], eV]]]], bigN, allN];
    chosen = HOL`Bool`CHOOSE[bigN, arch, exN];
    epsAll = HOL`Bool`GEN[eV, HOL`Bool`DISCH[hETm, chosen]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[lenSeq, zeroRealTm[]]], epsAll];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, folded]]]]]
  ];

lengthsToZeroThm =
  Module[{uV, leftV, rightV, hLeTm, hLe, hBadTm, hBad, lowerSeq, upperSeq,
          tendLen, lenFunEq, tendEq, tendBody, folded},
    uV = mkVar["U", compactCoverTy]; leftV = mkVar["left", realTy];
    rightV = mkVar["right", realTy];
    hLeTm = realLeTm[leftV, rightV]; hLe = ASSUME[hLeTm];
    hBadTm = noFiniteSubcoverTm[uV, leftV, rightV]; hBad = ASSUME[hBadTm];
    lowerSeq = lowerTm[uV, leftV, rightV];
    upperSeq = upperTm[uV, leftV, rightV];
    tendLen = HOL`Bool`MP[HOL`Bool`MP[compactSpecAll[compactLengthTendstoZeroThm,
      {uV, leftV, rightV}], hLe], hBad];
    lenFunEq = unfoldIntervalLengthFun[uV, leftV, rightV];
    tendEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[tendstoConst[], lenFunEq],
      REFL[zeroRealTm[]]];
    tendBody = EQMP[tendEq, tendLen];
    folded = EQMP[HOL`Equal`SYM[unfoldIntervalLengthsToZero[lowerSeq, upperSeq]], tendBody];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[leftV, HOL`Bool`GEN[rightV,
      HOL`Bool`DISCH[hLeTm, HOL`Bool`DISCH[hBadTm, folded]]]]]
  ];

End[];

EndPackage[];
