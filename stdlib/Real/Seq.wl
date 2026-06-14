(* M7-8 / stdlib/Real/Seq.wl - real sequences and epsilon-N limits. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`Arith`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

tendstoDefThm::usage = "tendstoDefThm - |- tendsto = (lambda a L. forall e. 0 < e ==> exists N. forall n. N <= n ==> realAbs (a n + realNeg L) < e).";
tendstoConst::usage = "tendstoConst[] - tendsto : (num -> real) -> real -> bool.";
tendstoTm::usage = "tendstoTm[a, L] - builds tendsto a L.";
unfoldTendsto::usage = "unfoldTendsto[a, L] - proves the beta-reduced tendsto definition at a and L.";

convergentDefThm::usage = "convergentDefThm - |- convergent = (lambda a. exists L. tendsto a L).";
convergentConst::usage = "convergentConst[] - convergent : (num -> real) -> bool.";
convergentTm::usage = "convergentTm[a] - builds convergent a.";

eventuallyDefThm::usage = "eventuallyDefThm - |- eventually = (lambda P. exists N. forall n. N <= n ==> P n).";
eventuallyConst::usage = "eventuallyConst[] - eventually : (num -> bool) -> bool.";
eventuallyTm::usage = "eventuallyTm[P] - builds eventually P.";
unfoldEventually::usage = "unfoldEventually[P] - proves the beta-reduced eventually definition at P.";

eventuallyBoundedDefThm::usage = "eventuallyBoundedDefThm - |- eventuallyBounded = (lambda u. exists B. 0 < B /\\ eventually (lambda n. realAbs (u n) < B)).";
eventuallyBoundedConst::usage = "eventuallyBoundedConst[] - eventuallyBounded : (num -> real) -> bool.";
eventuallyBoundedTm::usage = "eventuallyBoundedTm[u] - builds eventuallyBounded u.";
unfoldEventuallyBounded::usage = "unfoldEventuallyBounded[u] - proves the beta-reduced eventuallyBounded definition at u.";

eventuallyAwayFromZeroDefThm::usage = "eventuallyAwayFromZeroDefThm - |- eventuallyAwayFromZero = (lambda u. exists c. 0 < c /\\ eventually (lambda n. c < realAbs (u n))).";
eventuallyAwayFromZeroConst::usage = "eventuallyAwayFromZeroConst[] - eventuallyAwayFromZero : (num -> real) -> bool.";
eventuallyAwayFromZeroTm::usage = "eventuallyAwayFromZeroTm[u] - builds eventuallyAwayFromZero u.";
unfoldEventuallyAwayFromZero::usage = "unfoldEventuallyAwayFromZero[u] - proves the beta-reduced eventuallyAwayFromZero definition at u.";

tendstoConstThm::usage = "tendstoConstThm - |- forall c. tendsto (lambda n. c) c.";
realNeAbsPosThm::usage = "realNeAbsPosThm - |- forall x. ~(x = 0) ==> 0 < realAbs x.";
tendstoUniqueThm::usage = "tendstoUniqueThm - |- forall a L1 L2. tendsto a L1 ==> tendsto a L2 ==> L1 = L2.";
tendstoAddThm::usage = "tendstoAddThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. a n + b n) (A + B).";
tendstoNegThm::usage = "tendstoNegThm - |- forall a A. tendsto a A ==> tendsto (lambda n. realNeg (a n)) (realNeg A).";
tendstoSubThm::usage = "tendstoSubThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. a n + realNeg (b n)) (A + realNeg B).";
tendstoConvergentThm::usage = "tendstoConvergentThm - |- forall a L. tendsto a L ==> convergent a.";
eventuallyOfForallThm::usage = "eventuallyOfForallThm - |- forall P. (forall n. P n) ==> eventually P.";
eventuallyMonoThm::usage = "eventuallyMonoThm - |- forall P Q. (forall n. P n ==> Q n) ==> eventually P ==> eventually Q.";
eventuallyAndThm::usage = "eventuallyAndThm - |- forall P Q. eventually P ==> eventually Q ==> eventually (lambda n. P n /\\ Q n).";
tendstoEventuallyThm::usage = "tendstoEventuallyThm - |- forall a L e. tendsto a L ==> 0 < e ==> eventually (lambda n. realAbs (a n + realNeg L) < e).";
seqTendstoEventuallyBoundedThm::usage = "seqTendstoEventuallyBoundedThm - |- forall a L. tendsto a L ==> eventuallyBounded a.";
seqTendstoEventuallyAwayFromZeroThm::usage = "seqTendstoEventuallyAwayFromZeroThm - |- forall a L. tendsto a L ==> ~(L = 0) ==> eventuallyAwayFromZero a.";
realAbsMulThm::usage = "realAbsMulThm - |- forall x y. realAbs (realMul x y) = realMul (realAbs x) (realAbs y).";
seqTendstoMulThm::usage = "seqTendstoMulThm - |- forall a b A B. tendsto a A ==> tendsto b B ==> tendsto (lambda n. realMul (a n) (b n)) (realMul A B).";
seqTendstoScalarMulThm::usage = "seqTendstoScalarMulThm - |- forall a A c. tendsto a A ==> tendsto (lambda n. realMul c (a n)) (realMul c A).";

monoIncDefThm::usage = "monoIncDefThm - |- monoInc = (lambda u. forall n m. n <= m ==> realLe (u n) (u m)).";
monoIncConst::usage = "monoIncConst[] - monoInc : (num -> real) -> bool.";
monoIncTm::usage = "monoIncTm[u] - builds monoInc u.";
unfoldMonoInc::usage = "unfoldMonoInc[u] - proves the beta-reduced monoInc definition at u.";
monoDecDefThm::usage = "monoDecDefThm - |- monoDec = (lambda u. forall n m. n <= m ==> realLe (u m) (u n)).";
monoDecConst::usage = "monoDecConst[] - monoDec : (num -> real) -> bool.";
monoDecTm::usage = "monoDecTm[u] - builds monoDec u.";
unfoldMonoDec::usage = "unfoldMonoDec[u] - proves the beta-reduced monoDec definition at u.";
seqBddAboveDefThm::usage = "seqBddAboveDefThm - |- seqBddAbove = (lambda u. exists B. forall n. realLe (u n) B).";
seqBddAboveConst::usage = "seqBddAboveConst[] - seqBddAbove : (num -> real) -> bool.";
seqBddAboveTm::usage = "seqBddAboveTm[u] - builds seqBddAbove u.";
unfoldSeqBddAbove::usage = "unfoldSeqBddAbove[u] - proves the beta-reduced seqBddAbove definition at u.";
seqBddBelowDefThm::usage = "seqBddBelowDefThm - |- seqBddBelow = (lambda u. exists B. forall n. realLe B (u n)).";
seqBddBelowConst::usage = "seqBddBelowConst[] - seqBddBelow : (num -> real) -> bool.";
seqBddBelowTm::usage = "seqBddBelowTm[u] - builds seqBddBelow u.";
unfoldSeqBddBelow::usage = "unfoldSeqBddBelow[u] - proves the beta-reduced seqBddBelow definition at u.";
realAbsSubLtThm::usage = "realAbsSubLtThm - |- forall x a e. realLt (a + -e) x ==> realLt x (a + e) ==> realLt (realAbs (x + -a)) e.";
realSupLtMemThm::usage = "realSupLtMemThm - |- forall S t. (exists a. S a) ==> (exists u. forall a. S a ==> realLe a u) ==> realLt t (realSup S) ==> exists a. S a /\\ realLt t a.";
monoIncTendstoSupThm::usage = "monoIncTendstoSupThm - |- forall u. monoInc u ==> seqBddAbove u ==> tendsto u (realSup (lambda x. exists n. x = u n)).";
monoConvergesIncThm::usage = "monoConvergesIncThm - |- forall u. monoInc u ==> seqBddAbove u ==> exists L. tendsto u L.";
monoConvergesDecThm::usage = "monoConvergesDecThm - |- forall u. monoDec u ==> seqBddBelow u ==> exists L. tendsto u L.";

subseqIndexDefThm::usage = "subseqIndexDefThm - |- subseqIndex = (lambda phi. forall n. phi n < phi (SUC n)).";
subseqIndexConst::usage = "subseqIndexConst[] - subseqIndex : (num -> num) -> bool.";
subseqIndexTm::usage = "subseqIndexTm[phi] - builds subseqIndex phi.";
unfoldSubseqIndex::usage = "unfoldSubseqIndex[phi] - proves the beta-reduced subseqIndex definition at phi.";
subsequenceDefThm::usage = "subsequenceDefThm - |- subsequence = (lambda u phi n. u (phi n)).";
subsequenceConst::usage = "subsequenceConst[] - subsequence : (num -> real) -> (num -> num) -> num -> real.";
subsequenceTm::usage = "subsequenceTm[u, phi] - builds subsequence u phi.";
unfoldSubsequence::usage = "unfoldSubsequence[u, phi] - proves the beta-reduced subsequence definition at u and phi.";
peakDefThm::usage = "peakDefThm - |- peak = (lambda u n. forall m. n <= m ==> realLe (u m) (u n)).";
peakConst::usage = "peakConst[] - peak : (num -> real) -> num -> bool.";
peakTm::usage = "peakTm[u, n] - builds peak u n.";
unfoldPeak::usage = "unfoldPeak[u, n] - proves the beta-reduced peak definition at u and n.";
peakIndexDefThm::usage = "peakIndexDefThm - epsilon-selected ITER recursion for the infinitely-many-peaks branch.";
peakIndexConst::usage = "peakIndexConst[] - peakIndex : (num -> real) -> num -> num.";
peakIndexTm::usage = "peakIndexTm[u] - builds the index function peakIndex u.";
risingIndexDefThm::usage = "risingIndexDefThm - epsilon-selected ITER recursion for the eventually-no-peaks branch.";
risingIndexConst::usage = "risingIndexConst[] - risingIndex : (num -> real) -> num -> num -> num.";
risingIndexTm::usage = "risingIndexTm[u, N] - builds the index function risingIndex u N.";
subseqIndexMonoThm::usage = "subseqIndexMonoThm - |- forall phi. subseqIndex phi ==> forall n m. n <= m ==> phi n <= phi m.";
subseqIndexGeSelfThm::usage = "subseqIndexGeSelfThm - |- forall phi. subseqIndex phi ==> forall n. n <= phi n.";
notPeakExistsLaterThm::usage = "notPeakExistsLaterThm - |- forall u n. ~(peak u n) ==> exists m. n < m /\\ realLe (u n) (u m).";
eventuallyNotPeakThm::usage = "eventuallyNotPeakThm - |- forall u. ~(forall N. exists n. N <= n /\\ peak u n) ==> exists N. forall n. N <= n ==> ~(peak u n).";
peakIndexPeakThm::usage = "peakIndexPeakThm - infinitely-many-peaks branch: every peakIndex value is a peak.";
peakIndexStepThm::usage = "peakIndexStepThm - infinitely-many-peaks branch: peakIndex is strictly increasing.";
peakIndexSubseqThm::usage = "peakIndexSubseqThm - infinitely-many-peaks branch: peakIndex is a subsequence index.";
peakIndexDecreasingThm::usage = "peakIndexDecreasingThm - infinitely-many-peaks branch: the selected subsequence is decreasing.";
risingIndexGeThm::usage = "risingIndexGeThm - eventually-no-peaks branch invariant: N <= risingIndex u N k.";
risingIndexStepThm::usage = "risingIndexStepThm - eventually-no-peaks branch: risingIndex is strictly increasing.";
risingIndexStepLeThm::usage = "risingIndexStepLeThm - eventually-no-peaks branch: consecutive selected values are realLe-increasing.";
risingIndexSubseqThm::usage = "risingIndexSubseqThm - eventually-no-peaks branch: risingIndex is a subsequence index.";
risingIndexIncreasingThm::usage = "risingIndexIncreasingThm - eventually-no-peaks branch: the selected subsequence is increasing.";
existsMonoSubseqThm::usage = "existsMonoSubseqThm - |- forall u. exists phi. subseqIndex phi /\\ (monoInc (subsequence u phi) \\/ monoDec (subsequence u phi)).";

seqCauchyDefThm::usage = "seqCauchyDefThm - |- seqCauchy = (lambda u. forall e. realLt 0 e ==> exists N. forall n m. N <= n ==> N <= m ==> realAbs (u n + realNeg (u m)) < e).";
seqCauchyConst::usage = "seqCauchyConst[] - seqCauchy : (num -> real) -> bool.";
seqCauchyTm::usage = "seqCauchyTm[u] - builds seqCauchy u.";
unfoldSeqCauchy::usage = "unfoldSeqCauchy[u] - proves the beta-reduced seqCauchy definition at u.";
elbDefThm::usage = "elbDefThm - |- elb = (lambda u x. exists N. forall n. N <= n ==> realLe x (u n)).";
elbConst::usage = "elbConst[] - elb : (num -> real) -> real -> bool.";
elbTm::usage = "elbTm[u, x] - builds elb u x.";
unfoldElb::usage = "unfoldElb[u, x] - proves the beta-reduced elb definition at u and x.";
realAbsSubLtLeftThm::usage = "realAbsSubLtLeftThm - |- forall a b e. realLt (realAbs (realAdd a (realNeg b))) e ==> realLt (realAdd b (realNeg e)) a.";
realAbsSubLtRightThm::usage = "realAbsSubLtRightThm - |- forall a b e. realLt (realAbs (realAdd a (realNeg b))) e ==> realLt a (realAdd b e).";
cauchyTailLowerThm::usage = "cauchyTailLowerThm - Cauchy tail lower bound at the chosen center.";
cauchyTailUpperThm::usage = "cauchyTailUpperThm - Cauchy tail upper bound at the chosen center.";
elbNonemptyThm::usage = "elbNonemptyThm - |- forall u. seqCauchy u ==> exists x. elb u x.";
elbBddAboveThm::usage = "elbBddAboveThm - |- forall u. seqCauchy u ==> exists w. forall x. elb u x ==> realLe x w.";
tailLowerMemThm::usage = "tailLowerMemThm - Cauchy tail lower center is an eventual lower bound.";
tailUpperBoundThm::usage = "tailUpperBoundThm - Cauchy tail upper center is an upper bound for eventual lower bounds.";
cauchyConvergesThm::usage = "cauchyConvergesThm - |- forall u. seqCauchy u ==> exists L. tendsto u L.";

Begin["`Private`"];

seqTy = tyFun[numTy, realTy];
tendstoTy = tyFun[seqTy, tyFun[realTy, boolTy]];
convergentTy = tyFun[seqTy, boolTy];

seqNatAdd[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], aT], bT];
seqNatLe[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], aT], bT];
seqRealAbs[xT_] := mkComb[realAbsConst[], xT];
seqRealInv[xT_] := mkComb[realInvConst[], xT];

seqTwoNat[] := sucT[sucT[zeroN[]]];
seqTwoReal[] := realOfRatTm[ratOfIntTm[intOfNumTm[seqTwoNat[]]]];
seqHalf[eT_] := realMulTm[eT, seqRealInv[seqTwoReal[]]];

seqSpecAll[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

seqBetaClean[th_] := HOL`Drule`CONVRULE[
  HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

seqForallList[vs_List, body_] :=
  Fold[Function[{acc, v}, forallTm[v, acc]], body, Reverse[vs]];

seqImpList[hs_List, body_] :=
  Fold[Function[{acc, h}, impTm[h, acc]], body, Reverse[hs]];

seqRealLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqLeft], eqRight];

seqRealLtCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], eqLeft], eqRight];

seqNatLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Num`leqConst[], eqLeft], eqRight];

seqRealAddCongLeft[eq_, cT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], eq], REFL[cT]];

seqRealAddCongRight[cT_, eq_] :=
  HOL`Equal`APTERM[mkComb[realAddConst[], cT], eq];

seqRealAbsCong[eq_] := HOL`Equal`APTERM[realAbsConst[], eq];

seqLimitAtom[aT_, lT_, eT_, nT_] :=
  realLtTm[seqRealAbs[realAddTm[mkComb[aT, nT], realNegTm[lT]]], eT];

seqLimitAll[aT_, lT_, eT_, n0T_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    forallTm[nV, impTm[seqNatLe[n0T, nV], seqLimitAtom[aT, lT, eT, nV]]]
  ];

seqTendstoBody[aT_, lT_] :=
  Module[{eV, nV},
    eV = mkVar["e", realTy];
    nV = mkVar["N", numTy];
    forallTm[eV, impTm[realLtTm[zeroRealTm[], eV],
      existsTm[nV, seqLimitAll[aT, lT, eV, nV]]]]
  ];

tendstoDefThm =
  Module[{aV, lV, body},
    aV = mkVar["a", seqTy];
    lV = mkVar["L", realTy];
    body = mkAbs[aV, mkAbs[lV, seqTendstoBody[aV, lV]]];
    newDefinition[mkEq[mkVar["tendsto", tendstoTy], body]]
  ];

tendstoConst[] := mkConst["tendsto", tendstoTy];
tendstoTm[aT_, lT_] := mkComb[mkComb[tendstoConst[], aT], lT];

unfoldTendsto[aT_, lT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[tendstoDefThm, aT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, lT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

convergentDefThm =
  Module[{aV, lV, body},
    aV = mkVar["a", seqTy];
    lV = mkVar["L", realTy];
    body = mkAbs[aV, existsTm[lV, tendstoTm[aV, lV]]];
    newDefinition[mkEq[mkVar["convergent", convergentTy], body]]
  ];

convergentConst[] := mkConst["convergent", convergentTy];
convergentTm[aT_] := mkComb[convergentConst[], aT];

seqUnfoldConvergent[aT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[convergentDefThm, aT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqArithHalfPosThm =
  Module[{eV},
    eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[eV, impTm[realLtTm[zeroRealTm[], eV],
        realLtTm[zeroRealTm[], seqHalf[eV]]]]]
  ];

seqArithZeroDiffThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV},
        impTm[mkEq[realAddTm[xV, realNegTm[yV]], zeroRealTm[]], mkEq[xV, yV]]]]
  ];

seqArithDiffChainThm =
  Module[{xV, yV, zV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV, zV},
        mkEq[realAddTm[realAddTm[xV, realNegTm[yV]], realAddTm[yV, realNegTm[zV]]],
          realAddTm[xV, realNegTm[zV]]]]]
  ];

seqArithAddDiffThm =
  Module[{xV, yV, uV, vV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    uV = mkVar["u", realTy]; vV = mkVar["v", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV, uV, vV},
        mkEq[realAddTm[realAddTm[xV, yV], realNegTm[realAddTm[uV, vV]]],
          realAddTm[realAddTm[xV, realNegTm[uV]], realAddTm[yV, realNegTm[vV]]]]]]
  ];

seqArithNegDiffThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV},
        mkEq[realAddTm[realNegTm[xV], realNegTm[realNegTm[yV]]],
          realNegTm[realAddTm[xV, realNegTm[yV]]]]]]
  ];

seqArithTriangleLtThm =
  Module[{uV, vV, wV, eV},
    uV = mkVar["u", realTy]; vV = mkVar["v", realTy];
    wV = mkVar["w", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{uV, vV, wV, eV},
        seqImpList[{realLeTm[uV, realAddTm[vV, wV]],
          realLtTm[vV, seqHalf[eV]], realLtTm[wV, seqHalf[eV]]},
          realLtTm[uV, eV]]]]
  ];

seqArithUniqueContrThm =
  Module[{vV, wV, eV},
    vV = mkVar["v", realTy]; wV = mkVar["w", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{vV, wV, eV},
        seqImpList[{realLeTm[eV, realAddTm[vV, wV]],
          realLtTm[vV, seqHalf[eV]], realLtTm[wV, seqHalf[eV]]},
          realLtTm[eV, eV]]]]
  ];

seqUnfoldLeq[aT_, bT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, aT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, bT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

seqLeqAddSelf[mT_, kT_] :=
  Module[{jV, exTm, exThm},
    jV = mkVar["kLAS", numTy];
    exTm = existsTm[jV, mkEq[seqNatAdd[mT, jV], seqNatAdd[mT, kT]]];
    exThm = HOL`Bool`EXISTS[exTm, kT, REFL[seqNatAdd[mT, kT]]];
    EQMP[HOL`Equal`SYM[seqUnfoldLeq[mT, seqNatAdd[mT, kT]]], exThm]
  ];

seqLeqToSumLeft[mT_, kT_] := seqLeqAddSelf[mT, kT];

seqLeqToSumRight[mT_, kT_] :=
  Module[{raw, comm},
    raw = seqLeqAddSelf[kT, mT];
    comm = HOL`Bool`SPEC[mT, HOL`Bool`SPEC[kT, HOL`Stdlib`Num`addCommThm]];
    EQMP[seqNatLeCong[REFL[kT], comm], raw]
  ];

seqLeqTrans[abTh_, bcTh_] :=
  Module[{aT, bT, cT},
    aT = concl[abTh][[1, 2]]; bT = concl[abTh][[2]]; cT = concl[bcTh][[2]];
    HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[HOL`Stdlib`Num`leqTransThm, {aT, bT, cT}], abTh], bcTh]
  ];

tendstoConstThm =
  Module[{cV, nV, eV, constSeq, hE, appEq, sumEq, sumZero, absEq, ltGoal,
          impN, allN, exN, body, folded},
    cV = mkVar["c", realTy]; nV = mkVar["n", numTy]; eV = mkVar["e", realTy];
    constSeq = mkAbs[nV, cV];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    appEq = HOL`Equal`BETACONV[mkComb[constSeq, nV]];
    sumEq = seqRealAddCongLeft[appEq, realNegTm[cV]];
    sumZero = TRANS[sumEq, HOL`Bool`SPEC[cV, realAddNegThm]];
    absEq = TRANS[seqRealAbsCong[sumZero], realAbsZeroThm];
    ltGoal = EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], hE];
    impN = HOL`Bool`DISCH[seqNatLe[zeroN[], nV], ltGoal];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[constSeq, cV, eV, mkVar["N", numTy]]],
      zeroN[], allN];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], exN]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[constSeq, cV]], body];
    HOL`Bool`GEN[cV, folded]
  ];

realNeAbsPosThm =
  Module[{xV, hNe, hPos, hNeg, absPos, hNotLt, ltNotLe, notNotLe, dd, xLe0,
          xEq0, ff, lt0x, posBranch, absNeg, notLeLt, xLt0, negPos,
          negBranch, body},
    xV = mkVar["x", realTy];
    hNe = ASSUME[notTm[mkEq[xV, zeroRealTm[]]]];
    hPos = ASSUME[realLeTm[zeroRealTm[], xV]];
    absPos = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
    hNotLt = ASSUME[notTm[realLtTm[zeroRealTm[], xV]]];
    ltNotLe = HOL`Bool`SPEC[xV, HOL`Bool`SPEC[zeroRealTm[], realLtNotLeThm]];
    notNotLe = EQMP[HOL`Equal`APTERM[notC[], ltNotLe], hNotLt];
    dd = HOL`Auto`PropTaut`propTaut[
      impTm[notTm[notTm[realLeTm[xV, zeroRealTm[]]]], realLeTm[xV, zeroRealTm[]]]];
    xLe0 = HOL`Bool`MP[dd, notNotLe];
    xEq0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[zeroRealTm[], HOL`Bool`SPEC[xV, realLeAntisymThm]], xLe0], hPos];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[hNe], xEq0];
    lt0x = HOL`Bool`CCONTR[realLtTm[zeroRealTm[], xV], ff];
    posBranch = EQMP[seqRealLtCong[REFL[zeroRealTm[]], HOL`Equal`SYM[absPos]], lt0x];

    hNeg = ASSUME[notTm[realLeTm[zeroRealTm[], xV]]];
    absNeg = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg];
    notLeLt = HOL`Bool`SPEC[xV, HOL`Bool`SPEC[zeroRealTm[], HOL`Auto`RealArith`realNotLeLtThm]];
    xLt0 = EQMP[notLeLt, hNeg];
    negPos = HOL`Bool`MP[HOL`Bool`SPEC[xV, realNegPosThm], xLt0];
    negBranch = EQMP[seqRealLtCong[REFL[zeroRealTm[]], HOL`Equal`SYM[absNeg]], negPos];

    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], xV]],
      posBranch, negBranch];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[notTm[mkEq[xV, zeroRealTm[]]], body]]
  ];

tendstoUniqueThm =
  Module[{aV, l1V, l2V, h1, h2, hNe, diff, e0, half, hDiff0, diffImpEq,
          eqL1L2, ffDiff, notDiff0, ePos, halfPos, u1, u2, ex1, ex2, nW1,
          nW2, all1Tm, all2Tm, hAll1, hAll2, nSum, le1, le2, d1, d2, an,
          vAbs, wAbs, xTerm, yTerm, tri, chainEq, triLeftEq, negNegL1,
          leftComm, leftNegNeg, negEq, xNegEq, absXEq, rhsEq, triLe, eLtE,
          notELtE, ff, chosen2, chosen1, eqTh},
    aV = mkVar["a", seqTy]; l1V = mkVar["L1", realTy]; l2V = mkVar["L2", realTy];
    h1 = ASSUME[tendstoTm[aV, l1V]]; h2 = ASSUME[tendstoTm[aV, l2V]];
    hNe = ASSUME[notTm[mkEq[l1V, l2V]]];
    diff = realAddTm[l1V, realNegTm[l2V]];
    e0 = seqRealAbs[diff]; half = seqHalf[e0];

    hDiff0 = ASSUME[mkEq[diff, zeroRealTm[]]];
    diffImpEq = seqSpecAll[seqArithZeroDiffThm, {l1V, l2V}];
    eqL1L2 = HOL`Bool`MP[diffImpEq, hDiff0];
    ffDiff = HOL`Bool`MP[HOL`Bool`NOTELIM[hNe], eqL1L2];
    notDiff0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[diff, zeroRealTm[]], ffDiff]];
    ePos = HOL`Bool`MP[HOL`Bool`SPEC[diff, realNeAbsPosThm], notDiff0];
    halfPos = HOL`Bool`MP[HOL`Bool`SPEC[e0, seqArithHalfPosThm], ePos];
    u1 = EQMP[unfoldTendsto[aV, l1V], h1];
    u2 = EQMP[unfoldTendsto[aV, l2V], h2];
    ex1 = HOL`Bool`MP[HOL`Bool`SPEC[half, u1], halfPos];
    ex2 = HOL`Bool`MP[HOL`Bool`SPEC[half, u2], halfPos];

    nW1 = mkVar["nW1", numTy]; nW2 = mkVar["nW2", numTy];
    all1Tm = seqLimitAll[aV, l1V, half, nW1];
    all2Tm = seqLimitAll[aV, l2V, half, nW2];
    hAll1 = ASSUME[all1Tm]; hAll2 = ASSUME[all2Tm];
    nSum = seqNatAdd[nW1, nW2];
    le1 = seqLeqToSumLeft[nW1, nW2];
    le2 = seqLeqToSumRight[nW1, nW2];
    d1 = HOL`Bool`MP[HOL`Bool`SPEC[nSum, hAll1], le1];
    d2 = HOL`Bool`MP[HOL`Bool`SPEC[nSum, hAll2], le2];
    an = mkComb[aV, nSum];
    vAbs = seqRealAbs[realAddTm[an, realNegTm[l1V]]];
    wAbs = seqRealAbs[realAddTm[an, realNegTm[l2V]]];
    xTerm = realAddTm[l1V, realNegTm[an]];
    yTerm = realAddTm[an, realNegTm[l2V]];
    tri = seqSpecAll[realAbsTriangleThm, {xTerm, yTerm}];
    chainEq = seqSpecAll[seqArithDiffChainThm, {l1V, an, l2V}];
    triLeftEq = seqRealAbsCong[chainEq];
    leftComm = HOL`Bool`SPEC[realNegTm[an], HOL`Bool`SPEC[l1V, realAddCommThm]];
    negNegL1 = HOL`Bool`SPEC[l1V, realNegNegThm];
    leftNegNeg = seqRealAddCongRight[realNegTm[an], negNegL1];
    negEq = seqSpecAll[seqArithNegDiffThm, {an, l1V}];
    xNegEq = TRANS[leftComm, TRANS[HOL`Equal`SYM[leftNegNeg], negEq]];
    absXEq = TRANS[seqRealAbsCong[xNegEq],
      HOL`Bool`SPEC[realAddTm[an, realNegTm[l1V]], realAbsNegThm]];
    rhsEq = seqRealAddCongLeft[absXEq, wAbs];
    triLe = EQMP[seqRealLeCong[triLeftEq, rhsEq], tri];
    eLtE = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithUniqueContrThm, {vAbs, wAbs, e0}], triLe], d1], d2];
    notELtE = HOL`Bool`SPEC[e0, HOL`Auto`RealArith`realLtIrreflThm];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notELtE], eLtE];
    chosen2 = HOL`Bool`CHOOSE[nW2, ex2, ff];
    chosen1 = HOL`Bool`CHOOSE[nW1, ex1, chosen2];
    eqTh = HOL`Bool`CCONTR[mkEq[l1V, l2V], chosen1];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[l1V, HOL`Bool`GEN[l2V,
      HOL`Bool`DISCH[tendstoTm[aV, l1V], HOL`Bool`DISCH[tendstoTm[aV, l2V], eqTh]]]]]
  ];

tendstoAddThm =
  Module[{aV, bV, avV, bvV, eV, nV, hA, hB, hE, half, halfPos, uA, uB, exA,
          exB, nW1, nW2, allATm, allBTm, hAllA, hAllB, nSum, hN, leA0, leB0,
          leA, leB, dA, dB, an, bn, seqAdd, limit, appEq, betaEq, arithEq,
          argEq, absEq, xTerm, yTerm, vAbs, wAbs, tri, triOld, ltGoal, impN,
          allN, exN, body, folded, chosenB, chosenA},
    aV = mkVar["a", seqTy]; bV = mkVar["b", seqTy];
    avV = mkVar["A", realTy]; bvV = mkVar["B", realTy];
    eV = mkVar["e", realTy]; nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]]; hB = ASSUME[tendstoTm[bV, bvV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    half = seqHalf[eV];
    halfPos = HOL`Bool`MP[HOL`Bool`SPEC[eV, seqArithHalfPosThm], hE];
    uA = EQMP[unfoldTendsto[aV, avV], hA];
    uB = EQMP[unfoldTendsto[bV, bvV], hB];
    exA = HOL`Bool`MP[HOL`Bool`SPEC[half, uA], halfPos];
    exB = HOL`Bool`MP[HOL`Bool`SPEC[half, uB], halfPos];
    nW1 = mkVar["nW1", numTy]; nW2 = mkVar["nW2", numTy];
    allATm = seqLimitAll[aV, avV, half, nW1];
    allBTm = seqLimitAll[bV, bvV, half, nW2];
    hAllA = ASSUME[allATm]; hAllB = ASSUME[allBTm];
    nSum = seqNatAdd[nW1, nW2];
    hN = ASSUME[seqNatLe[nSum, nV]];
    leA0 = seqLeqToSumLeft[nW1, nW2];
    leB0 = seqLeqToSumRight[nW1, nW2];
    leA = seqLeqTrans[leA0, hN];
    leB = seqLeqTrans[leB0, hN];
    dA = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllA], leA];
    dB = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllB], leB];
    an = mkComb[aV, nV]; bn = mkComb[bV, nV];
    seqAdd = mkAbs[nV, realAddTm[mkComb[aV, nV], mkComb[bV, nV]]];
    limit = realAddTm[avV, bvV];
    appEq = HOL`Equal`BETACONV[mkComb[seqAdd, nV]];
    betaEq = seqRealAddCongLeft[appEq, realNegTm[limit]];
    arithEq = seqSpecAll[seqArithAddDiffThm, {an, bn, avV, bvV}];
    argEq = TRANS[betaEq, arithEq];
    absEq = seqRealAbsCong[argEq];
    xTerm = realAddTm[an, realNegTm[avV]];
    yTerm = realAddTm[bn, realNegTm[bvV]];
    vAbs = seqRealAbs[xTerm]; wAbs = seqRealAbs[yTerm];
    tri = seqSpecAll[realAbsTriangleThm, {xTerm, yTerm}];
    triOld = EQMP[seqRealLeCong[HOL`Equal`SYM[absEq], REFL[realAddTm[vAbs, wAbs]]], tri];
    ltGoal = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithTriangleLtThm,
        {seqRealAbs[realAddTm[mkComb[seqAdd, nV], realNegTm[limit]]], vAbs, wAbs, eV}],
      triOld], dA], dB];
    impN = HOL`Bool`DISCH[seqNatLe[nSum, nV], ltGoal];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[seqAdd, limit, eV, mkVar["N", numTy]]],
      nSum, allN];
    chosenB = HOL`Bool`CHOOSE[nW2, exB, exN];
    chosenA = HOL`Bool`CHOOSE[nW1, exA, chosenB];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosenA]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[seqAdd, limit]], body];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[avV, HOL`Bool`GEN[bvV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], HOL`Bool`DISCH[tendstoTm[bV, bvV], folded]]]]]]
  ];

tendstoNegThm =
  Module[{aV, avV, eV, nV, hA, hE, uA, exA, nW, allTm, hAll, hN, dA, an,
          seqNeg, limit, appEq, betaEq, arithEq, argEq, absEq, ltGoal, impN,
          allN, exN, body, folded, chosen},
    aV = mkVar["a", seqTy]; avV = mkVar["A", realTy];
    eV = mkVar["e", realTy]; nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    uA = EQMP[unfoldTendsto[aV, avV], hA];
    exA = HOL`Bool`MP[HOL`Bool`SPEC[eV, uA], hE];
    nW = mkVar["nW", numTy];
    allTm = seqLimitAll[aV, avV, eV, nW];
    hAll = ASSUME[allTm];
    hN = ASSUME[seqNatLe[nW, nV]];
    dA = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAll], hN];
    an = mkComb[aV, nV];
    seqNeg = mkAbs[nV, realNegTm[mkComb[aV, nV]]];
    limit = realNegTm[avV];
    appEq = HOL`Equal`BETACONV[mkComb[seqNeg, nV]];
    betaEq = seqRealAddCongLeft[appEq, realNegTm[limit]];
    arithEq = seqSpecAll[seqArithNegDiffThm, {an, avV}];
    argEq = TRANS[betaEq, arithEq];
    absEq = TRANS[seqRealAbsCong[argEq],
      HOL`Bool`SPEC[realAddTm[an, realNegTm[avV]], realAbsNegThm]];
    ltGoal = EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], dA];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], ltGoal];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[seqNeg, limit, eV, mkVar["N", numTy]]],
      nW, allN];
    chosen = HOL`Bool`CHOOSE[nW, exA, exN];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosen]];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[seqNeg, limit]], body];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[avV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], folded]]]
  ];

tendstoSubThm =
  Module[{aV, bV, avV, bvV, nV, hA, hB, negSeq, negTh, addInst, addRes, clean},
    aV = mkVar["a", seqTy]; bV = mkVar["b", seqTy];
    avV = mkVar["A", realTy]; bvV = mkVar["B", realTy];
    nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]]; hB = ASSUME[tendstoTm[bV, bvV]];
    negSeq = mkAbs[nV, realNegTm[mkComb[bV, nV]]];
    negTh = HOL`Bool`MP[seqSpecAll[tendstoNegThm, {bV, bvV}], hB];
    addInst = seqSpecAll[tendstoAddThm, {aV, negSeq, avV, realNegTm[bvV]}];
    addRes = HOL`Bool`MP[HOL`Bool`MP[addInst, hA], negTh];
    clean = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], addRes];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[avV, HOL`Bool`GEN[bvV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], HOL`Bool`DISCH[tendstoTm[bV, bvV], clean]]]]]]
  ];

tendstoConvergentThm =
  Module[{aV, lV, h, exThm, convThm},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy];
    h = ASSUME[tendstoTm[aV, lV]];
    exThm = HOL`Bool`EXISTS[existsTm[lV, tendstoTm[aV, lV]], lV, h];
    convThm = EQMP[HOL`Equal`SYM[seqUnfoldConvergent[aV]], exThm];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[tendstoTm[aV, lV], convThm]]]
  ];

eventuallyPredTy = tyFun[numTy, boolTy];
eventuallyTy = tyFun[eventuallyPredTy, boolTy];
eventuallyBoundedTy = tyFun[seqTy, boolTy];
eventuallyAwayFromZeroTy = tyFun[seqTy, boolTy];

seqOneNat[] := sucT[zeroN[]];
seqOneReal[] := realOfRatTm[ratOfIntTm[intOfNumTm[seqOneNat[]]]];

seqEventuallyAll[pT_, n0T_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    forallTm[nV, impTm[seqNatLe[n0T, nV], mkComb[pT, nV]]]
  ];

seqEventuallyBody[pT_] :=
  Module[{n0V},
    n0V = mkVar["N", numTy];
    existsTm[n0V, seqEventuallyAll[pT, n0V]]
  ];

seqBoundPred[uT_, bT_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    mkAbs[nV, realLtTm[seqRealAbs[mkComb[uT, nV]], bT]]
  ];

seqAwayPred[uT_, cT_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    mkAbs[nV, realLtTm[cT, seqRealAbs[mkComb[uT, nV]]]]
  ];

seqEventuallyBoundedBody[uT_] :=
  Module[{bV},
    bV = mkVar["B", realTy];
    existsTm[bV, conjTm[realLtTm[zeroRealTm[], bV],
      eventuallyTm[seqBoundPred[uT, bV]]]]
  ];

seqEventuallyAwayFromZeroBody[uT_] :=
  Module[{cV},
    cV = mkVar["c", realTy];
    existsTm[cV, conjTm[realLtTm[zeroRealTm[], cV],
      eventuallyTm[seqAwayPred[uT, cV]]]]
  ];

eventuallyDefThm =
  Module[{pV, body},
    pV = mkVar["P", eventuallyPredTy];
    body = mkAbs[pV, seqEventuallyBody[pV]];
    newDefinition[mkEq[mkVar["eventually", eventuallyTy], body]]
  ];

eventuallyConst[] := mkConst["eventually", eventuallyTy];
eventuallyTm[pT_] := mkComb[eventuallyConst[], pT];

unfoldEventually[pT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[eventuallyDefThm, pT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

eventuallyBoundedDefThm =
  Module[{uV, body},
    uV = mkVar["u", seqTy];
    body = mkAbs[uV, seqEventuallyBoundedBody[uV]];
    newDefinition[mkEq[mkVar["eventuallyBounded", eventuallyBoundedTy], body]]
  ];

eventuallyBoundedConst[] := mkConst["eventuallyBounded", eventuallyBoundedTy];
eventuallyBoundedTm[uT_] := mkComb[eventuallyBoundedConst[], uT];

unfoldEventuallyBounded[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[eventuallyBoundedDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

eventuallyAwayFromZeroDefThm =
  Module[{uV, body},
    uV = mkVar["u", seqTy];
    body = mkAbs[uV, seqEventuallyAwayFromZeroBody[uV]];
    newDefinition[mkEq[mkVar["eventuallyAwayFromZero", eventuallyAwayFromZeroTy], body]]
  ];

eventuallyAwayFromZeroConst[] := mkConst["eventuallyAwayFromZero", eventuallyAwayFromZeroTy];
eventuallyAwayFromZeroTm[uT_] := mkComb[eventuallyAwayFromZeroConst[], uT];

unfoldEventuallyAwayFromZero[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[eventuallyAwayFromZeroDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqArithSubAddCancelThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, yV},
        mkEq[realAddTm[realAddTm[xV, realNegTm[yV]], yV], xV]]]
  ];

seqArithAddOnePosThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, impTm[realLeTm[zeroRealTm[], xV],
        realLtTm[zeroRealTm[], realAddTm[xV, seqOneReal[]]]]]]
  ];

seqArithBoundSumThm =
  Module[{pV, qV},
    pV = mkVar["p", realTy]; qV = mkVar["q", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{pV, qV},
        impTm[realLtTm[pV, seqOneReal[]],
          realLtTm[realAddTm[pV, qV], realAddTm[qV, seqOneReal[]]]]]]
  ];

seqArithHalfDoubleThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, mkEq[realAddTm[seqHalf[xV], seqHalf[xV]], xV]]]
  ];

seqArithAwayThm =
  Module[{xV, dV, uV, cV},
    xV = mkVar["x", realTy]; dV = mkVar["d", realTy];
    uV = mkVar["u", realTy]; cV = mkVar["c", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, dV, uV, cV},
        seqImpList[{mkEq[realAddTm[cV, cV], xV],
          realLeTm[xV, realAddTm[dV, uV]], realLtTm[dV, cV]},
          realLtTm[cV, uV]]]]
  ];

eventuallyOfForallThm =
  Module[{pV, nV, hAll, pN, impN, allN, exThm, folded},
    pV = mkVar["P", eventuallyPredTy]; nV = mkVar["n", numTy];
    hAll = ASSUME[forallTm[nV, mkComb[pV, nV]]];
    pN = HOL`Bool`SPEC[nV, hAll];
    impN = HOL`Bool`DISCH[seqNatLe[zeroN[], nV], pN];
    allN = HOL`Bool`GEN[nV, impN];
    exThm = HOL`Bool`EXISTS[seqEventuallyBody[pV], zeroN[], allN];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[pV]], exThm];
    HOL`Bool`GEN[pV, HOL`Bool`DISCH[forallTm[nV, mkComb[pV, nV]], folded]]
  ];

eventuallyMonoThm =
  Module[{pV, qV, nV, nW, hPQ, hEvP, exP, allPTm, hAllP, hLe, pN, qImp,
          qN, impN, allQ, exQ, folded, chosen},
    pV = mkVar["P", eventuallyPredTy]; qV = mkVar["Q", eventuallyPredTy];
    nV = mkVar["n", numTy]; nW = mkVar["nW", numTy];
    hPQ = ASSUME[forallTm[nV, impTm[mkComb[pV, nV], mkComb[qV, nV]]]];
    hEvP = ASSUME[eventuallyTm[pV]];
    exP = EQMP[unfoldEventually[pV], hEvP];
    allPTm = seqEventuallyAll[pV, nW];
    hAllP = ASSUME[allPTm];
    hLe = ASSUME[seqNatLe[nW, nV]];
    pN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllP], hLe];
    qImp = HOL`Bool`SPEC[nV, hPQ];
    qN = HOL`Bool`MP[qImp, pN];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], qN];
    allQ = HOL`Bool`GEN[nV, impN];
    exQ = HOL`Bool`EXISTS[seqEventuallyBody[qV], nW, allQ];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[qV]], exQ];
    chosen = HOL`Bool`CHOOSE[nW, exP, folded];
    HOL`Bool`GEN[pV, HOL`Bool`GEN[qV,
      HOL`Bool`DISCH[forallTm[nV, impTm[mkComb[pV, nV], mkComb[qV, nV]]],
        HOL`Bool`DISCH[eventuallyTm[pV], chosen]]]]
  ];

eventuallyAndThm =
  Module[{pV, qV, nV, nW1, nW2, pred, hEvP, hEvQ, exP, exQ, allPTm, allQTm,
          hAllP, hAllQ, nSum, hLe, leP0, leQ0, leP, leQ, pN, qN, conjN,
          betaN, redexN, impN, allN, exN, folded, chosenQ, chosenP},
    pV = mkVar["P", eventuallyPredTy]; qV = mkVar["Q", eventuallyPredTy];
    nV = mkVar["n", numTy]; nW1 = mkVar["nW1", numTy]; nW2 = mkVar["nW2", numTy];
    pred = mkAbs[nV, conjTm[mkComb[pV, nV], mkComb[qV, nV]]];
    hEvP = ASSUME[eventuallyTm[pV]]; hEvQ = ASSUME[eventuallyTm[qV]];
    exP = EQMP[unfoldEventually[pV], hEvP];
    exQ = EQMP[unfoldEventually[qV], hEvQ];
    allPTm = seqEventuallyAll[pV, nW1];
    allQTm = seqEventuallyAll[qV, nW2];
    hAllP = ASSUME[allPTm]; hAllQ = ASSUME[allQTm];
    nSum = seqNatAdd[nW1, nW2];
    hLe = ASSUME[seqNatLe[nSum, nV]];
    leP0 = seqLeqToSumLeft[nW1, nW2];
    leQ0 = seqLeqToSumRight[nW1, nW2];
    leP = seqLeqTrans[leP0, hLe];
    leQ = seqLeqTrans[leQ0, hLe];
    pN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllP], leP];
    qN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAllQ], leQ];
    conjN = HOL`Bool`CONJ[pN, qN];
    betaN = HOL`Equal`BETACONV[mkComb[pred, nV]];
    redexN = EQMP[HOL`Equal`SYM[betaN], conjN];
    impN = HOL`Bool`DISCH[seqNatLe[nSum, nV], redexN];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[seqEventuallyBody[pred], nSum, allN];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[pred]], exN];
    chosenQ = HOL`Bool`CHOOSE[nW2, exQ, folded];
    chosenP = HOL`Bool`CHOOSE[nW1, exP, chosenQ];
    HOL`Bool`GEN[pV, HOL`Bool`GEN[qV,
      HOL`Bool`DISCH[eventuallyTm[pV], HOL`Bool`DISCH[eventuallyTm[qV], chosenP]]]]
  ];

tendstoEventuallyThm =
  Module[{aV, lV, eV, nV, nW, pred, hT, hE, unfolded, exRed, allTm, hAll,
          hLe, closeN, betaN, redexN, impN, allN, exN, folded, chosen},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy]; eV = mkVar["e", realTy];
    nV = mkVar["n", numTy]; nW = mkVar["nW", numTy];
    pred = mkAbs[nV, seqLimitAtom[aV, lV, eV, nV]];
    hT = ASSUME[tendstoTm[aV, lV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    unfolded = EQMP[unfoldTendsto[aV, lV], hT];
    exRed = HOL`Bool`MP[HOL`Bool`SPEC[eV, unfolded], hE];
    allTm = seqLimitAll[aV, lV, eV, nW];
    hAll = ASSUME[allTm];
    hLe = ASSUME[seqNatLe[nW, nV]];
    closeN = HOL`Bool`MP[HOL`Bool`SPEC[nV, hAll], hLe];
    betaN = HOL`Equal`BETACONV[mkComb[pred, nV]];
    redexN = EQMP[HOL`Equal`SYM[betaN], closeN];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], redexN];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[seqEventuallyBody[pred], nW, allN];
    folded = EQMP[HOL`Equal`SYM[unfoldEventually[pred]], exN];
    chosen = HOL`Bool`CHOOSE[nW, exRed, folded];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV, HOL`Bool`GEN[eV,
      HOL`Bool`DISCH[tendstoTm[aV, lV],
        HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosen]]]]]
  ];

seqTendstoEventuallyBoundedThm =
  Module[{aV, lV, nV, hT, oneR, bT, closePred, boundPred, absLNonneg, bPos,
          closeEv, monoInst, hClose, an, diff, appAbs, subAdd, absEq, triRaw,
          triLe, rhsLt, ltGoal, pointImp, pointAll, evBound, conjB, exB, folded},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy]; nV = mkVar["n", numTy];
    hT = ASSUME[tendstoTm[aV, lV]];
    oneR = seqOneReal[];
    bT = realAddTm[seqRealAbs[lV], oneR];
    closePred = mkAbs[nV, seqLimitAtom[aV, lV, oneR, nV]];
    boundPred = seqBoundPred[aV, bT];
    absLNonneg = HOL`Bool`SPEC[lV, realAbsNonnegThm];
    bPos = HOL`Bool`MP[HOL`Bool`SPEC[seqRealAbs[lV], seqArithAddOnePosThm], absLNonneg];
    closeEv = HOL`Bool`MP[
      HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm, {aV, lV, oneR}], hT],
      HOL`Auto`RealArith`rnumPos[1]];
    monoInst = seqBetaClean[seqSpecAll[eventuallyMonoThm, {closePred, boundPred}]];
    hClose = ASSUME[seqLimitAtom[aV, lV, oneR, nV]];
    an = mkComb[aV, nV];
    diff = realAddTm[an, realNegTm[lV]];
    appAbs = seqRealAbs[mkComb[aV, nV]];
    subAdd = seqSpecAll[seqArithSubAddCancelThm, {an, lV}];
    absEq = seqRealAbsCong[subAdd];
    triRaw = seqSpecAll[realAbsTriangleThm, {diff, lV}];
    triLe = EQMP[seqRealLeCong[absEq,
      REFL[realAddTm[seqRealAbs[diff], seqRealAbs[lV]]]], triRaw];
    rhsLt = HOL`Bool`MP[
      seqSpecAll[seqArithBoundSumThm, {seqRealAbs[diff], seqRealAbs[lV]}], hClose];
    ltGoal = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeLtTransThm,
        {appAbs, realAddTm[seqRealAbs[diff], seqRealAbs[lV]], bT}], triLe], rhsLt];
    pointImp = HOL`Bool`DISCH[seqLimitAtom[aV, lV, oneR, nV], ltGoal];
    pointAll = HOL`Bool`GEN[nV, pointImp];
    evBound = HOL`Bool`MP[HOL`Bool`MP[monoInst, pointAll], closeEv];
    conjB = HOL`Bool`CONJ[bPos, evBound];
    exB = HOL`Bool`EXISTS[seqEventuallyBoundedBody[aV], bT, conjB];
    folded = EQMP[HOL`Equal`SYM[unfoldEventuallyBounded[aV]], exB];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[tendstoTm[aV, lV], folded]]]
  ];

seqTendstoEventuallyAwayFromZeroThm =
  Module[{aV, lV, nV, hT, hNe, absL, cT, closePred, awayPred, absLPos, cPos,
          closeEv, monoInst, hClose, an, diffAL, diffLA, leftComm,
          negNegL, leftNegNeg, negEq, diffNegEq, absDiffEq, closeLA, subAdd,
          absEq, triRaw, triLe, halfDouble, awayLt, pointImp, pointAll, evAway,
          conjC, exC, folded},
    aV = mkVar["a", seqTy]; lV = mkVar["L", realTy]; nV = mkVar["n", numTy];
    hT = ASSUME[tendstoTm[aV, lV]];
    hNe = ASSUME[notTm[mkEq[lV, zeroRealTm[]]]];
    absL = seqRealAbs[lV];
    cT = seqHalf[absL];
    closePred = mkAbs[nV, seqLimitAtom[aV, lV, cT, nV]];
    awayPred = seqAwayPred[aV, cT];
    absLPos = HOL`Bool`MP[HOL`Bool`SPEC[lV, realNeAbsPosThm], hNe];
    cPos = HOL`Bool`MP[HOL`Bool`SPEC[absL, seqArithHalfPosThm], absLPos];
    closeEv = HOL`Bool`MP[
      HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm, {aV, lV, cT}], hT], cPos];
    monoInst = seqBetaClean[seqSpecAll[eventuallyMonoThm, {closePred, awayPred}]];
    hClose = ASSUME[seqLimitAtom[aV, lV, cT, nV]];
    an = mkComb[aV, nV];
    diffAL = realAddTm[an, realNegTm[lV]];
    diffLA = realAddTm[lV, realNegTm[an]];
    leftComm = HOL`Bool`SPEC[realNegTm[an], HOL`Bool`SPEC[lV, realAddCommThm]];
    negNegL = HOL`Bool`SPEC[lV, realNegNegThm];
    leftNegNeg = seqRealAddCongRight[realNegTm[an], negNegL];
    negEq = seqSpecAll[seqArithNegDiffThm, {an, lV}];
    diffNegEq = TRANS[leftComm, TRANS[HOL`Equal`SYM[leftNegNeg], negEq]];
    absDiffEq = TRANS[seqRealAbsCong[diffNegEq], HOL`Bool`SPEC[diffAL, realAbsNegThm]];
    closeLA = EQMP[HOL`Equal`SYM[seqRealLtCong[absDiffEq, REFL[cT]]], hClose];
    subAdd = seqSpecAll[seqArithSubAddCancelThm, {lV, an}];
    absEq = seqRealAbsCong[subAdd];
    triRaw = seqSpecAll[realAbsTriangleThm, {diffLA, an}];
    triLe = EQMP[seqRealLeCong[absEq,
      REFL[realAddTm[seqRealAbs[diffLA], seqRealAbs[an]]]], triRaw];
    halfDouble = HOL`Bool`SPEC[absL, seqArithHalfDoubleThm];
    awayLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithAwayThm, {absL, seqRealAbs[diffLA], seqRealAbs[an], cT}],
      halfDouble], triLe], closeLA];
    pointImp = HOL`Bool`DISCH[seqLimitAtom[aV, lV, cT, nV], awayLt];
    pointAll = HOL`Bool`GEN[nV, pointImp];
    evAway = HOL`Bool`MP[HOL`Bool`MP[monoInst, pointAll], closeEv];
    conjC = HOL`Bool`CONJ[cPos, evAway];
    exC = HOL`Bool`EXISTS[seqEventuallyAwayFromZeroBody[aV], cT, conjC];
    folded = EQMP[HOL`Equal`SYM[unfoldEventuallyAwayFromZero[aV]], exC];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[lV,
      HOL`Bool`DISCH[tendstoTm[aV, lV],
        HOL`Bool`DISCH[notTm[mkEq[lV, zeroRealTm[]]], folded]]]]
  ];

seqRealMulCongLeft[eq_, cT_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realMulConst[], eq], REFL[cT]];

seqRealMulCongRight[cT_, eq_] :=
  HOL`Equal`APTERM[mkComb[realMulConst[], cT], eq];

seqMulOneLeft[xT_] :=
  TRANS[HOL`Bool`SPEC[xT, HOL`Bool`SPEC[seqOneReal[], realMulCommThm]],
    HOL`Bool`SPEC[xT, realMulOneThm]];

seqMulDistribRight[xT_, yT_, zT_] :=
  Module[{commL, dist, commX, commY, rhs1, rhs2},
    commL = HOL`Bool`SPEC[zT, HOL`Bool`SPEC[realAddTm[xT, yT], realMulCommThm]];
    dist = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT,
      HOL`Bool`SPEC[zT, realMulDistribThm]]];
    commX = HOL`Bool`SPEC[xT, HOL`Bool`SPEC[zT, realMulCommThm]];
    commY = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[zT, realMulCommThm]];
    rhs1 = seqRealAddCongLeft[commX, realMulTm[zT, yT]];
    rhs2 = seqRealAddCongRight[realMulTm[xT, zT], commY];
    TRANS[commL, TRANS[dist, TRANS[rhs1, rhs2]]]
  ];

seqScaleCancelRight[xT_, yT_, yNe0_] :=
  Module[{iy, assoc, comm, inv, middle, one},
    iy = seqRealInv[yT];
    assoc = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[iy,
      HOL`Bool`SPEC[xT, realMulAssocThm]]];
    comm = HOL`Bool`SPEC[yT, HOL`Bool`SPEC[iy, realMulCommThm]];
    inv = HOL`Bool`MP[HOL`Bool`SPEC[yT, realMulInvThm], yNe0];
    middle = seqRealMulCongRight[xT, TRANS[comm, inv]];
    one = HOL`Bool`SPEC[xT, realMulOneThm];
    TRANS[assoc, TRANS[middle, one]]
  ];

seqScaleCancelLeft[xT_, yT_, yNe0_] :=
  Module[{iy, assoc, inv, middle, one},
    iy = seqRealInv[yT];
    assoc = HOL`Equal`SYM[HOL`Bool`SPEC[xT, HOL`Bool`SPEC[iy,
      HOL`Bool`SPEC[yT, realMulAssocThm]]]];
    inv = HOL`Bool`MP[HOL`Bool`SPEC[yT, realMulInvThm], yNe0];
    middle = seqRealMulCongLeft[inv, xT];
    one = seqMulOneLeft[xT];
    TRANS[assoc, TRANS[middle, one]]
  ];

seqArithPosNeZeroThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, impTm[realLtTm[zeroRealTm[], xV],
        notTm[mkEq[xV, zeroRealTm[]]]]]]
  ];

seqArithLtAddOneThm =
  Module[{xV},
    xV = mkVar["x", realTy];
    HOL`Auto`RealArith`realArithProve[
      forallTm[xV, realLtTm[xV, realAddTm[xV, seqOneReal[]]]]]
  ];

seqLtImpLeRule[ltTh_] :=
  Module[{aT, bT},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]];
    HOL`Bool`MP[seqSpecAll[realLtImpLeThm, {aT, bT}], ltTh]
  ];

seqLeLtTransRule[leTh_, ltTh_] :=
  Module[{aT, bT, cT},
    aT = concl[leTh][[1, 2]]; bT = concl[leTh][[2]]; cT = concl[ltTh][[2]];
    HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLeLtTransThm, {aT, bT, cT}],
      leTh], ltTh]
  ];

seqMulLeRightRule[leTh_, cNonneg_] :=
  Module[{aT, bT, cT, mono, leftComm, rightComm},
    aT = concl[leTh][[1, 2]]; bT = concl[leTh][[2]]; cT = concl[cNonneg][[2]];
    mono = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLeMulMonoThm, {aT, bT, cT}],
      cNonneg], leTh];
    leftComm = HOL`Bool`SPEC[aT, HOL`Bool`SPEC[cT, realMulCommThm]];
    rightComm = HOL`Bool`SPEC[bT, HOL`Bool`SPEC[cT, realMulCommThm]];
    EQMP[seqRealLeCong[leftComm, rightComm], mono]
  ];

seqMulLtRightRule[ltTh_, cPos_] :=
  Module[{aT, bT, cT, mono, leftComm, rightComm},
    aT = concl[ltTh][[1, 2]]; bT = concl[ltTh][[2]]; cT = concl[cPos][[2]];
    mono = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLtMulMonoThm, {aT, bT, cT}],
      cPos], ltTh];
    leftComm = HOL`Bool`SPEC[aT, HOL`Bool`SPEC[cT, realMulCommThm]];
    rightComm = HOL`Bool`SPEC[bT, HOL`Bool`SPEC[cT, realMulCommThm]];
    EQMP[seqRealLtCong[leftComm, rightComm], mono]
  ];

realAbsNonposThm =
  Module[{xV, hNonpos, body},
    xV = mkVar["x", realTy];
    hNonpos = ASSUME[realLeTm[xV, zeroRealTm[]]];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], xV]],
      Module[{hPos, xEq0, absTo0, negTo0},
        hPos = ASSUME[realLeTm[zeroRealTm[], xV]];
        xEq0 = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[zeroRealTm[], HOL`Bool`SPEC[xV, realLeAntisymThm]],
          hNonpos], hPos];
        absTo0 = TRANS[seqRealAbsCong[xEq0], realAbsZeroThm];
        negTo0 = TRANS[HOL`Equal`APTERM[realNegConst[], xEq0], realNegZeroThm];
        TRANS[absTo0, HOL`Equal`SYM[negTo0]]
      ],
      Module[{hNeg},
        hNeg = ASSUME[notTm[realLeTm[zeroRealTm[], xV]]];
        HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLeTm[xV, zeroRealTm[]], body]]
  ];

realAbsMulThm =
  Module[{xV, yV, xy, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; xy = realMulTm[xV, yV];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], xV]],
      Module[{hXpos},
        hXpos = ASSUME[realLeTm[zeroRealTm[], xV]];
        HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], yV]],
          Module[{hYpos, hXYpos, absX, absY, absXY, rhs1, rhs2},
            hYpos = ASSUME[realLeTm[zeroRealTm[], yV]];
            hXYpos = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNonnegThm]], hXpos], hYpos];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hXpos];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsPosThm], hYpos];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsPosThm], hXYpos];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[xV, absY];
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, rhs2]]]
          ],
          Module[{hYneg, yLe0, negYNonneg, hProd, mulNeg, hNegProd, negNegLe0,
                  xyLe0, absX, absY, absXY, rhs1, rhs2, rhs3},
            hYneg = ASSUME[notTm[realLeTm[zeroRealTm[], yV]]];
            yLe0 = HOL`Bool`MP[HOL`Bool`SPEC[yV, notNonnegToLeZeroThm], hYneg];
            negYNonneg = HOL`Bool`MP[HOL`Bool`SPEC[yV, realNegNonnegThm], yLe0];
            hProd = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[realNegTm[yV], HOL`Bool`SPEC[xV, realMulNonnegThm]],
              hXpos], negYNonneg];
            mulNeg = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNegRightThm]];
            hNegProd = EQMP[seqRealLeCong[REFL[zeroRealTm[]], mulNeg], hProd];
            negNegLe0 = HOL`Bool`MP[HOL`Bool`SPEC[realNegTm[xy], realNegNonposThm],
              hNegProd];
            xyLe0 = EQMP[seqRealLeCong[HOL`Bool`SPEC[xy, realNegNegThm],
              REFL[zeroRealTm[]]], negNegLe0];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hXpos];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsNonposThm], yLe0];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsNonposThm], xyLe0];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[xV, absY];
            rhs3 = mulNeg;
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, TRANS[rhs2, rhs3]]]]
          ]]
      ],
      Module[{hXneg, xLe0, negXNonneg},
        hXneg = ASSUME[notTm[realLeTm[zeroRealTm[], xV]]];
        xLe0 = HOL`Bool`MP[HOL`Bool`SPEC[xV, notNonnegToLeZeroThm], hXneg];
        negXNonneg = HOL`Bool`MP[HOL`Bool`SPEC[xV, realNegNonnegThm], xLe0];
        HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], yV]],
          Module[{hYpos, hProd, mulNeg, hNegProd, negNegLe0, xyLe0, absX, absY,
                  absXY, rhs1, rhs2, rhs3},
            hYpos = ASSUME[realLeTm[zeroRealTm[], yV]];
            hProd = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[yV, HOL`Bool`SPEC[realNegTm[xV], realMulNonnegThm]],
              negXNonneg], hYpos];
            mulNeg = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNegLeftThm]];
            hNegProd = EQMP[seqRealLeCong[REFL[zeroRealTm[]], mulNeg], hProd];
            negNegLe0 = HOL`Bool`MP[HOL`Bool`SPEC[realNegTm[xy], realNegNonposThm],
              hNegProd];
            xyLe0 = EQMP[seqRealLeCong[HOL`Bool`SPEC[xy, realNegNegThm],
              REFL[zeroRealTm[]]], negNegLe0];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNonposThm], xLe0];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsPosThm], hYpos];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsNonposThm], xyLe0];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[realNegTm[xV], absY];
            rhs3 = mulNeg;
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, TRANS[rhs2, rhs3]]]]
          ],
          Module[{hYneg, yLe0, negYNonneg, hProd, negLeft, negRight, negNeg,
                  prodEq, hXYpos, absX, absY, absXY, rhs1, rhs2, rhs3},
            hYneg = ASSUME[notTm[realLeTm[zeroRealTm[], yV]]];
            yLe0 = HOL`Bool`MP[HOL`Bool`SPEC[yV, notNonnegToLeZeroThm], hYneg];
            negYNonneg = HOL`Bool`MP[HOL`Bool`SPEC[yV, realNegNonnegThm], yLe0];
            hProd = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[realNegTm[yV],
                HOL`Bool`SPEC[realNegTm[xV], realMulNonnegThm]],
              negXNonneg], negYNonneg];
            negLeft = HOL`Bool`SPEC[realNegTm[yV],
              HOL`Bool`SPEC[xV, realMulNegLeftThm]];
            negRight = HOL`Equal`APTERM[realNegConst[],
              HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMulNegRightThm]]];
            negNeg = HOL`Bool`SPEC[xy, realNegNegThm];
            prodEq = TRANS[negLeft, TRANS[negRight, negNeg]];
            hXYpos = EQMP[seqRealLeCong[REFL[zeroRealTm[]], prodEq], hProd];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNonposThm], xLe0];
            absY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realAbsNonposThm], yLe0];
            absXY = HOL`Bool`MP[HOL`Bool`SPEC[xy, realAbsPosThm], hXYpos];
            rhs1 = seqRealMulCongLeft[absX, seqRealAbs[yV]];
            rhs2 = seqRealMulCongRight[realNegTm[xV], absY];
            rhs3 = prodEq;
            TRANS[absXY, HOL`Equal`SYM[TRANS[rhs1, TRANS[rhs2, rhs3]]]]
          ]]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

mulSubMulThm =
  Module[{xV, yV, aV, bV, lhs, rhs1, rhs2, rhs, ay, eq1, eq2, rhsA, rhsB,
          rhsExpand, cancel},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    lhs = realAddTm[realMulTm[xV, yV], realNegTm[realMulTm[aV, bV]]];
    rhs1 = realMulTm[realAddTm[xV, realNegTm[aV]], yV];
    rhs2 = realMulTm[aV, realAddTm[yV, realNegTm[bV]]];
    rhs = realAddTm[rhs1, rhs2];
    ay = realMulTm[aV, yV];
    eq1 = TRANS[seqMulDistribRight[xV, realNegTm[aV], yV],
      seqRealAddCongRight[realMulTm[xV, yV],
        HOL`Bool`SPEC[yV, HOL`Bool`SPEC[aV, realMulNegLeftThm]]]];
    eq2 = TRANS[HOL`Bool`SPEC[realNegTm[bV], HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[aV, realMulDistribThm]]],
      seqRealAddCongRight[ay,
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, realMulNegRightThm]]]];
    rhsA = realAddTm[realMulTm[xV, yV], realNegTm[ay]];
    rhsB = realAddTm[ay, realNegTm[realMulTm[aV, bV]]];
    rhsExpand = TRANS[seqRealAddCongLeft[eq1, rhs2],
      seqRealAddCongRight[rhsA, eq2]];
    cancel = seqSpecAll[seqArithDiffChainThm,
      {realMulTm[xV, yV], ay, realMulTm[aV, bV]}];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Equal`SYM[TRANS[rhsExpand, cancel]]]]]]
  ];

seqRealInvPositiveThm =
  Module[{xV, ix, hPos, hNeX, invEq, invNonnegRaw, invRewrite, invNonneg,
          hInvEq0, prodEq0, oneEq0, ffInvEq0, invNe0, hInvLe0, eq0Inv, ffLe,
          notLe, ltEq, body},
    xV = mkVar["x", realTy]; ix = seqRealInv[xV];
    hPos = ASSUME[realLtTm[zeroRealTm[], xV]];
    hNeX = HOL`Bool`MP[HOL`Bool`SPEC[xV, seqArithPosNeZeroThm], hPos];
    invEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realInvPosThm], hPos];
    invNonnegRaw = HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosNonnegThm], hPos];
    invRewrite = seqRealLeCong[REFL[zeroRealTm[]], HOL`Equal`SYM[invEq]];
    invNonneg = EQMP[invRewrite, invNonnegRaw];
    hInvEq0 = ASSUME[mkEq[ix, zeroRealTm[]]];
    prodEq0 = TRANS[seqRealMulCongRight[xV, hInvEq0],
      HOL`Bool`SPEC[xV, realMulZeroThm]];
    oneEq0 = TRANS[HOL`Equal`SYM[
      HOL`Bool`MP[HOL`Bool`SPEC[xV, realMulInvThm], hNeX]], prodEq0];
    ffInvEq0 = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Auto`RealArith`rnumNe[1, 0]],
      oneEq0];
    invNe0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[ix, zeroRealTm[]], ffInvEq0]];
    hInvLe0 = ASSUME[realLeTm[ix, zeroRealTm[]]];
    eq0Inv = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[ix, HOL`Bool`SPEC[zeroRealTm[], realLeAntisymThm]],
      invNonneg], hInvLe0];
    ffLe = HOL`Bool`MP[HOL`Bool`NOTELIM[invNe0], HOL`Equal`SYM[eq0Inv]];
    notLe = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[ix, zeroRealTm[]], ffLe]];
    ltEq = HOL`Bool`SPEC[zeroRealTm[], HOL`Bool`SPEC[ix,
      HOL`Auto`RealArith`realNotLeLtThm]];
    body = EQMP[ltEq, notLe];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], xV], body]]
  ];

seqTendstoMulThm =
  Module[{uV, vV, aV, bV, eV, nV, hU, hV, hE, e2, e2Pos, boundedV,
          exBound, boundW, boundPred, boundConjTm, hBoundConj, hBoundPos,
          hEvBound, absA, aBound, aBoundPos, boundNe0, aBoundNe0, invBound,
          invABound, invBoundPos, invABoundPos, deltaU, deltaV, deltaUPos,
          deltaVPos, scaleU, scaleV, closeUPred, closeVPred, evU, evV,
          evPairRaw, evPair, pairPred, evAllRaw, evAll, allPred, prodSeq,
          prodLim, goalPred, hPoint, allBeta, hAllConj, hPair, hBound,
          hCloseU, hCloseV, un, vn, uDiff, vDiff, t1, t2, prodDiff, absT1,
          absT2, absUDiff, absVn, absVDiff, absMul1, hBoundLe, absUDiffNonneg,
          le1Base, le1, lt1Base, lt1, term1, absMul2, absALtBound,
          absALeBound, absVDiffNonneg, le2Base, le2, lt2Base, lt2, term2,
          decompEq, triRaw, triLe, diffLt, appEq, argEq, absEq, ltGoal,
          goalBeta, pointGoal, pointImp, pointAll, monoInst, evGoal, exGoal,
          body, folded, chosenBound},
    uV = mkVar["a", seqTy]; vV = mkVar["b", seqTy];
    aV = mkVar["A", realTy]; bV = mkVar["B", realTy];
    eV = mkVar["e", realTy]; nV = mkVar["n", numTy];
    hU = ASSUME[tendstoTm[uV, aV]]; hV = ASSUME[tendstoTm[vV, bV]];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    e2 = seqHalf[eV];
    e2Pos = HOL`Bool`MP[HOL`Bool`SPEC[eV, seqArithHalfPosThm], hE];
    boundedV = HOL`Bool`MP[seqSpecAll[seqTendstoEventuallyBoundedThm, {vV, bV}], hV];
    exBound = EQMP[unfoldEventuallyBounded[vV], boundedV];
    boundW = mkVar["boundW", realTy];
    boundPred = seqBoundPred[vV, boundW];
    boundConjTm = conjTm[realLtTm[zeroRealTm[], boundW], eventuallyTm[boundPred]];
    hBoundConj = ASSUME[boundConjTm];
    hBoundPos = HOL`Bool`CONJUNCT1[hBoundConj];
    hEvBound = HOL`Bool`CONJUNCT2[hBoundConj];
    absA = seqRealAbs[aV];
    aBound = realAddTm[absA, seqOneReal[]];
    aBoundPos = HOL`Bool`MP[HOL`Bool`SPEC[absA, seqArithAddOnePosThm],
      HOL`Bool`SPEC[aV, realAbsNonnegThm]];
    boundNe0 = HOL`Bool`MP[HOL`Bool`SPEC[boundW, seqArithPosNeZeroThm], hBoundPos];
    aBoundNe0 = HOL`Bool`MP[HOL`Bool`SPEC[aBound, seqArithPosNeZeroThm], aBoundPos];
    invBound = seqRealInv[boundW];
    invABound = seqRealInv[aBound];
    invBoundPos = HOL`Bool`MP[HOL`Bool`SPEC[boundW, seqRealInvPositiveThm], hBoundPos];
    invABoundPos = HOL`Bool`MP[HOL`Bool`SPEC[aBound, seqRealInvPositiveThm], aBoundPos];
    deltaU = realMulTm[e2, invBound];
    deltaV = realMulTm[invABound, e2];
    deltaUPos = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[invBound, HOL`Bool`SPEC[e2, realLtMulPosThm]],
      e2Pos], invBoundPos];
    deltaVPos = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[e2, HOL`Bool`SPEC[invABound, realLtMulPosThm]],
      invABoundPos], e2Pos];
    scaleU = seqScaleCancelRight[e2, boundW, boundNe0];
    scaleV = seqScaleCancelLeft[e2, aBound, aBoundNe0];
    closeUPred = mkAbs[nV, seqLimitAtom[uV, aV, deltaU, nV]];
    closeVPred = mkAbs[nV, seqLimitAtom[vV, bV, deltaV, nV]];
    evU = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm,
      {uV, aV, deltaU}], hU], deltaUPos];
    evV = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[tendstoEventuallyThm,
      {vV, bV, deltaV}], hV], deltaVPos];
    evPairRaw = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[eventuallyAndThm,
      {closeUPred, closeVPred}], evU], evV];
    evPair = seqBetaClean[evPairRaw];
    pairPred = concl[evPair][[2]];
    evAllRaw = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[eventuallyAndThm,
      {pairPred, boundPred}], evPair], hEvBound];
    evAll = seqBetaClean[evAllRaw];
    allPred = concl[evAll][[2]];
    prodSeq = mkAbs[nV, realMulTm[mkComb[uV, nV], mkComb[vV, nV]]];
    prodLim = realMulTm[aV, bV];
    goalPred = mkAbs[nV, seqLimitAtom[prodSeq, prodLim, eV, nV]];

    hPoint = ASSUME[mkComb[allPred, nV]];
    allBeta = HOL`Equal`BETACONV[mkComb[allPred, nV]];
    hAllConj = EQMP[allBeta, hPoint];
    hPair = HOL`Bool`CONJUNCT1[hAllConj];
    hBound = HOL`Bool`CONJUNCT2[hAllConj];
    hCloseU = HOL`Bool`CONJUNCT1[hPair];
    hCloseV = HOL`Bool`CONJUNCT2[hPair];
    un = mkComb[uV, nV]; vn = mkComb[vV, nV];
    uDiff = realAddTm[un, realNegTm[aV]];
    vDiff = realAddTm[vn, realNegTm[bV]];
    t1 = realMulTm[uDiff, vn];
    t2 = realMulTm[aV, vDiff];
    prodDiff = realAddTm[realMulTm[un, vn], realNegTm[prodLim]];
    absT1 = seqRealAbs[t1]; absT2 = seqRealAbs[t2];
    absUDiff = seqRealAbs[uDiff]; absVn = seqRealAbs[vn]; absVDiff = seqRealAbs[vDiff];

    absMul1 = seqSpecAll[realAbsMulThm, {uDiff, vn}];
    hBoundLe = seqLtImpLeRule[hBound];
    absUDiffNonneg = HOL`Bool`SPEC[uDiff, realAbsNonnegThm];
    le1Base = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLeMulMonoThm,
      {absVn, boundW, absUDiff}], absUDiffNonneg], hBoundLe];
    le1 = EQMP[seqRealLeCong[HOL`Equal`SYM[absMul1],
      REFL[realMulTm[absUDiff, boundW]]], le1Base];
    lt1Base = seqMulLtRightRule[hCloseU, hBoundPos];
    lt1 = seqLeLtTransRule[le1, lt1Base];
    term1 = EQMP[seqRealLtCong[REFL[absT1], scaleU], lt1];

    absMul2 = seqSpecAll[realAbsMulThm, {aV, vDiff}];
    absALtBound = HOL`Bool`SPEC[absA, seqArithLtAddOneThm];
    absALeBound = seqLtImpLeRule[absALtBound];
    absVDiffNonneg = HOL`Bool`SPEC[vDiff, realAbsNonnegThm];
    le2Base = seqMulLeRightRule[absALeBound, absVDiffNonneg];
    le2 = EQMP[seqRealLeCong[HOL`Equal`SYM[absMul2],
      REFL[realMulTm[aBound, absVDiff]]], le2Base];
    lt2Base = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[realLtMulMonoThm,
      {absVDiff, deltaV, aBound}], aBoundPos], hCloseV];
    lt2 = seqLeLtTransRule[le2, lt2Base];
    term2 = EQMP[seqRealLtCong[REFL[absT2], scaleV], lt2];

    decompEq = seqSpecAll[mulSubMulThm, {un, vn, aV, bV}];
    triRaw = seqSpecAll[realAbsTriangleThm, {t1, t2}];
    triLe = EQMP[seqRealLeCong[HOL`Equal`SYM[seqRealAbsCong[decompEq]],
      REFL[realAddTm[absT1, absT2]]], triRaw];
    diffLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithTriangleLtThm, {seqRealAbs[prodDiff], absT1, absT2, eV}],
      triLe], term1], term2];
    appEq = HOL`Equal`BETACONV[mkComb[prodSeq, nV]];
    argEq = seqRealAddCongLeft[appEq, realNegTm[prodLim]];
    absEq = seqRealAbsCong[argEq];
    ltGoal = EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], diffLt];
    goalBeta = HOL`Equal`BETACONV[mkComb[goalPred, nV]];
    pointGoal = EQMP[HOL`Equal`SYM[goalBeta], ltGoal];
    pointImp = HOL`Bool`DISCH[mkComb[allPred, nV], pointGoal];
    pointAll = HOL`Bool`GEN[nV, pointImp];
    monoInst = seqSpecAll[eventuallyMonoThm, {allPred, goalPred}];
    evGoal = HOL`Bool`MP[HOL`Bool`MP[monoInst, pointAll], evAll];
    exGoal = seqBetaClean[EQMP[unfoldEventually[goalPred], evGoal]];
    body = HOL`Bool`GEN[eV, HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], exGoal]];
    folded = EQMP[HOL`Equal`SYM[seqBetaClean[unfoldTendsto[prodSeq, prodLim]]], body];
    chosenBound = HOL`Bool`CHOOSE[boundW, exBound, folded];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[vV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[tendstoTm[uV, aV], HOL`Bool`DISCH[tendstoTm[vV, bV],
        chosenBound]]]]]]
  ];

seqTendstoScalarMulThm =
  Module[{aV, avV, cV, nV, hA, constSeq, constTh, prodInst, prodTh, cleanProd,
          seqLeft, seqRight, betaL, betaR, bodyComm, pointEq, pointAll, seqEq,
          limitEq, tendstoEq, reshaped},
    aV = mkVar["a", seqTy]; avV = mkVar["A", realTy]; cV = mkVar["c", realTy];
    nV = mkVar["n", numTy];
    hA = ASSUME[tendstoTm[aV, avV]];
    constSeq = mkAbs[nV, cV];
    constTh = HOL`Bool`SPEC[cV, tendstoConstThm];
    prodInst = seqSpecAll[seqTendstoMulThm, {aV, constSeq, avV, cV}];
    prodTh = HOL`Bool`MP[HOL`Bool`MP[prodInst, hA], constTh];
    cleanProd = seqBetaClean[prodTh];
    seqLeft = mkAbs[nV, realMulTm[mkComb[aV, nV], cV]];
    seqRight = mkAbs[nV, realMulTm[cV, mkComb[aV, nV]]];
    betaL = HOL`Equal`BETACONV[mkComb[seqLeft, nV]];
    betaR = HOL`Equal`BETACONV[mkComb[seqRight, nV]];
    bodyComm = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[mkComb[aV, nV], realMulCommThm]];
    pointEq = TRANS[betaL, TRANS[bodyComm, HOL`Equal`SYM[betaR]]];
    pointAll = HOL`Bool`GEN[nV, pointEq];
    seqEq = HOL`Stdlib`List`funcExtThm[seqLeft, seqRight, pointAll];
    limitEq = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[avV, realMulCommThm]];
    tendstoEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[tendstoConst[], seqEq], limitEq];
    reshaped = EQMP[tendstoEq, cleanProd];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[avV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[tendstoTm[aV, avV], reshaped]]]]
  ];

monoPredTy = tyFun[seqTy, boolTy];
seqBddTy = tyFun[seqTy, boolTy];
seqSetTy = tyFun[realTy, boolTy];

seqRealSup[sT_] := mkComb[realSupConst[], sT];

seqRangeTm[uT_] :=
  Module[{xR, nR},
    xR = mkVar["xR", realTy]; nR = mkVar["nR", numTy];
    mkAbs[xR, existsTm[nR, mkEq[xR, mkComb[uT, nR]]]]
  ];

seqRangeMemThm[rangeT_, uT_, nT_] :=
  Module[{xT, beta, exThm},
    xT = mkComb[uT, nT];
    beta = HOL`Equal`BETACONV[mkComb[rangeT, xT]];
    exThm = HOL`Bool`EXISTS[concl[beta][[2]], nT, REFL[xT]];
    EQMP[HOL`Equal`SYM[beta], exThm]
  ];

seqRangeNonemptyThm[rangeT_, uT_] :=
  Module[{aR, mem0},
    aR = mkVar["aR", realTy];
    mem0 = seqRangeMemThm[rangeT, uT, zeroN[]];
    HOL`Bool`EXISTS[existsTm[aR, mkComb[rangeT, aR]], mkComb[uT, zeroN[]], mem0]
  ];

seqMonoIncBody[uT_] :=
  Module[{nV, mV},
    nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    forallTm[nV, forallTm[mV,
      impTm[seqNatLe[nV, mV], realLeTm[mkComb[uT, nV], mkComb[uT, mV]]]]]
  ];

seqMonoDecBody[uT_] :=
  Module[{nV, mV},
    nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    forallTm[nV, forallTm[mV,
      impTm[seqNatLe[nV, mV], realLeTm[mkComb[uT, mV], mkComb[uT, nV]]]]]
  ];

seqBddAboveBody[uT_] :=
  Module[{bV, nV},
    bV = mkVar["B", realTy]; nV = mkVar["n", numTy];
    existsTm[bV, forallTm[nV, realLeTm[mkComb[uT, nV], bV]]]
  ];

seqBddBelowBody[uT_] :=
  Module[{bV, nV},
    bV = mkVar["B", realTy]; nV = mkVar["n", numTy];
    existsTm[bV, forallTm[nV, realLeTm[bV, mkComb[uT, nV]]]]
  ];

monoIncDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["monoInc", monoPredTy],
      mkAbs[uV, seqMonoIncBody[uV]]]]
  ];

monoIncConst[] := mkConst["monoInc", monoPredTy];
monoIncTm[uT_] := mkComb[monoIncConst[], uT];

unfoldMonoInc[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[monoIncDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

monoDecDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["monoDec", monoPredTy],
      mkAbs[uV, seqMonoDecBody[uV]]]]
  ];

monoDecConst[] := mkConst["monoDec", monoPredTy];
monoDecTm[uT_] := mkComb[monoDecConst[], uT];

unfoldMonoDec[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[monoDecDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqBddAboveDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["seqBddAbove", seqBddTy],
      mkAbs[uV, seqBddAboveBody[uV]]]]
  ];

seqBddAboveConst[] := mkConst["seqBddAbove", seqBddTy];
seqBddAboveTm[uT_] := mkComb[seqBddAboveConst[], uT];

unfoldSeqBddAbove[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[seqBddAboveDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqBddBelowDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["seqBddBelow", seqBddTy],
      mkAbs[uV, seqBddBelowBody[uV]]]]
  ];

seqBddBelowConst[] := mkConst["seqBddBelow", seqBddTy];
seqBddBelowTm[uT_] := mkComb[seqBddBelowConst[], uT];

unfoldSeqBddBelow[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[seqBddBelowDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

seqArithAbsUpperThm =
  Module[{xV, aV, eV},
    xV = mkVar["x", realTy]; aV = mkVar["a", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, aV, eV},
        impTm[realLtTm[xV, realAddTm[aV, eV]],
          realLtTm[realAddTm[xV, realNegTm[aV]], eV]]]]
  ];

seqArithAbsLowerThm =
  Module[{xV, aV, eV},
    xV = mkVar["x", realTy]; aV = mkVar["a", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{xV, aV, eV},
        impTm[realLtTm[realAddTm[aV, realNegTm[eV]], xV],
          realLtTm[realNegTm[realAddTm[xV, realNegTm[aV]]], eV]]]]
  ];

seqArithSubSelfLtThm =
  Module[{sV, eV},
    sV = mkVar["s", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{sV, eV},
        impTm[realLtTm[zeroRealTm[], eV],
          realLtTm[realAddTm[sV, realNegTm[eV]], sV]]]]
  ];

seqArithSelfLtAddThm =
  Module[{sV, eV},
    sV = mkVar["s", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{sV, eV},
        impTm[realLtTm[zeroRealTm[], eV],
          realLtTm[sV, realAddTm[sV, eV]]]]]
  ];

seqArithLtLeContrThm =
  Module[{tV, sV},
    tV = mkVar["t", realTy]; sV = mkVar["s", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{tV, sV},
        seqImpList[{realLtTm[tV, sV], realLeTm[sV, tV]}, realLtTm[tV, tV]]]]
  ];

realAbsSubLtThm =
  Module[{xV, aV, eV, diff, hLeft, hRight, body},
    xV = mkVar["x", realTy]; aV = mkVar["a", realTy]; eV = mkVar["e", realTy];
    diff = realAddTm[xV, realNegTm[aV]];
    hLeft = ASSUME[realLtTm[realAddTm[aV, realNegTm[eV]], xV]];
    hRight = ASSUME[realLtTm[xV, realAddTm[aV, eV]]];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[zeroRealTm[], diff]],
      Module[{hNonneg, absEq, diffLt},
        hNonneg = ASSUME[realLeTm[zeroRealTm[], diff]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[diff, realAbsPosThm], hNonneg];
        diffLt = HOL`Bool`MP[seqSpecAll[seqArithAbsUpperThm, {xV, aV, eV}], hRight];
        EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], diffLt]
      ],
      Module[{hNotNonneg, notLeLt, diffLt0, diffLe0, absEq, negDiffLt},
        hNotNonneg = ASSUME[notTm[realLeTm[zeroRealTm[], diff]]];
        notLeLt = HOL`Bool`SPEC[diff,
          HOL`Bool`SPEC[zeroRealTm[], HOL`Auto`RealArith`realNotLeLtThm]];
        diffLt0 = EQMP[notLeLt, hNotNonneg];
        diffLe0 = seqLtImpLeRule[diffLt0];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[diff, realAbsNonposThm], diffLe0];
        negDiffLt = HOL`Bool`MP[seqSpecAll[seqArithAbsLowerThm, {xV, aV, eV}], hLeft];
        EQMP[seqRealLtCong[HOL`Equal`SYM[absEq], REFL[eV]], negDiffLt]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[aV, HOL`Bool`GEN[eV,
      HOL`Bool`DISCH[realLtTm[realAddTm[aV, realNegTm[eV]], xV],
        HOL`Bool`DISCH[realLtTm[xV, realAddTm[aV, eV]], body]]]]]
  ];

realSupLtMemThm =
  Module[{sV, tV, aV, uB, hneTm, hbndTm, goalTm, hne, hbnd, hLt, hNotGoal,
          aB, hSa, hNotLe, notLeLt, ltTa, conjA, exA, ffA, leAt, ubAll,
          least, badLt, ff, body},
    sV = mkVar["S", seqSetTy]; tV = mkVar["t", realTy];
    aV = mkVar["a", realTy]; uB = mkVar["u", realTy]; aB = mkVar["aB", realTy];
    hneTm = existsTm[aV, mkComb[sV, aV]];
    hbndTm = existsTm[uB,
      forallTm[aV, impTm[mkComb[sV, aV], realLeTm[aV, uB]]]];
    goalTm = existsTm[aV, conjTm[mkComb[sV, aV], realLtTm[tV, aV]]];
    hne = ASSUME[hneTm]; hbnd = ASSUME[hbndTm];
    hLt = ASSUME[realLtTm[tV, seqRealSup[sV]]];
    hNotGoal = ASSUME[notTm[goalTm]];
    hSa = ASSUME[mkComb[sV, aB]];
    hNotLe = ASSUME[notTm[realLeTm[aB, tV]]];
    notLeLt = HOL`Bool`SPEC[tV,
      HOL`Bool`SPEC[aB, HOL`Auto`RealArith`realNotLeLtThm]];
    ltTa = EQMP[notLeLt, hNotLe];
    conjA = HOL`Bool`CONJ[hSa, ltTa];
    exA = HOL`Bool`EXISTS[goalTm, aB, conjA];
    ffA = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotGoal], exA];
    leAt = HOL`Bool`CCONTR[realLeTm[aB, tV], ffA];
    ubAll = HOL`Bool`GEN[aB, HOL`Bool`DISCH[mkComb[sV, aB], leAt]];
    least = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realSupLeastThm, {sV, tV}], hne], hbnd], ubAll];
    badLt = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithLtLeContrThm, {tV, seqRealSup[sV]}], hLt], least];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[
      HOL`Bool`SPEC[tV, HOL`Auto`RealArith`realLtIrreflThm]], badLt];
    body = HOL`Bool`CCONTR[goalTm, ff];
    HOL`Bool`GEN[sV, HOL`Bool`GEN[tV,
      HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm,
        HOL`Bool`DISCH[realLtTm[tV, seqRealSup[sV]], body]]]]]
  ];

monoIncTendstoSupThm =
  Module[{uV, range, sup, hMono, hBdd, monoAll, bddEx, bW, hAllB,
          nBdd, nonempty, bounded, supUpper, eV, hE, below, belowLtSup, memEx,
          aW, hMemConj, hRangeA, hBelowA, betaRangeA, exRangeN, nW, hEqA,
          hBelowUN, nV, hLeNn, monoStep, leUN, hLeft, hUNleSup, supLtPlus,
          hRight, absClose, impN, allN, exN, chosenN, chosenA, epsBody,
          tendBody, folded, chosenB},
    uV = mkVar["u", seqTy];
    range = seqRangeTm[uV]; sup = seqRealSup[range];
    hMono = ASSUME[monoIncTm[uV]]; hBdd = ASSUME[seqBddAboveTm[uV]];
    monoAll = EQMP[unfoldMonoInc[uV], hMono];
    bddEx = EQMP[unfoldSeqBddAbove[uV], hBdd];
    bW = mkVar["bW", realTy]; nBdd = mkVar["n", numTy];
    hAllB = ASSUME[forallTm[nBdd, realLeTm[mkComb[uV, nBdd], bW]]];
    nonempty = seqRangeNonemptyThm[range, uV];
    bounded = Module[{aB, wB, hRange, exNRange, nB, hEq, boundN, leAB, impA, allA},
      aB = mkVar["aB", realTy]; nB = mkVar["nB", numTy];
      wB = mkVar["wB", realTy];
      hRange = ASSUME[mkComb[range, aB]];
      exNRange = EQMP[HOL`Equal`BETACONV[mkComb[range, aB]], hRange];
      hEq = ASSUME[mkEq[aB, mkComb[uV, nB]]];
      boundN = HOL`Bool`SPEC[nB, hAllB];
      leAB = EQMP[HOL`Equal`SYM[seqRealLeCong[hEq, REFL[bW]]], boundN];
      impA = HOL`Bool`DISCH[mkComb[range, aB], HOL`Bool`CHOOSE[nB, exNRange, leAB]];
      allA = HOL`Bool`GEN[aB, impA];
      HOL`Bool`EXISTS[existsTm[wB,
        forallTm[aB, impTm[mkComb[range, aB], realLeTm[aB, wB]]]],
        bW, allA]
    ];
    supUpper = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[range, realSupUpperThm],
      nonempty], bounded];
    eV = mkVar["e", realTy];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    below = realAddTm[sup, realNegTm[eV]];
    belowLtSup = HOL`Bool`MP[seqSpecAll[seqArithSubSelfLtThm, {sup, eV}], hE];
    memEx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realSupLtMemThm, {range, below}], nonempty], bounded], belowLtSup];
    aW = mkVar["aW", realTy]; nW = mkVar["nW", numTy]; nV = mkVar["n", numTy];
    hMemConj = ASSUME[conjTm[mkComb[range, aW], realLtTm[below, aW]]];
    hRangeA = HOL`Bool`CONJUNCT1[hMemConj];
    hBelowA = HOL`Bool`CONJUNCT2[hMemConj];
    betaRangeA = HOL`Equal`BETACONV[mkComb[range, aW]];
    exRangeN = EQMP[betaRangeA, hRangeA];
    hEqA = ASSUME[mkEq[aW, mkComb[uV, nW]]];
    hBelowUN = EQMP[seqRealLtCong[REFL[below], hEqA], hBelowA];
    hLeNn = ASSUME[seqNatLe[nW, nV]];
    monoStep = HOL`Bool`MP[seqSpecAll[monoAll, {nW, nV}], hLeNn];
    leUN = monoStep;
    hLeft = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLtLeTransThm, {below, mkComb[uV, nW], mkComb[uV, nV]}],
      hBelowUN], leUN];
    hUNleSup = HOL`Bool`MP[HOL`Bool`SPEC[mkComb[uV, nV], supUpper],
      seqRangeMemThm[range, uV, nV]];
    supLtPlus = HOL`Bool`MP[seqSpecAll[seqArithSelfLtAddThm, {sup, eV}], hE];
    hRight = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeLtTransThm, {mkComb[uV, nV], sup, realAddTm[sup, eV]}],
      hUNleSup], supLtPlus];
    absClose = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realAbsSubLtThm, {mkComb[uV, nV], sup, eV}], hLeft], hRight];
    impN = HOL`Bool`DISCH[seqNatLe[nW, nV], absClose];
    allN = HOL`Bool`GEN[nV, impN];
    exN = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy], seqLimitAll[uV, sup, eV, mkVar["N", numTy]]],
      nW, allN];
    chosenN = HOL`Bool`CHOOSE[nW, exRangeN, exN];
    chosenA = HOL`Bool`CHOOSE[aW, memEx, chosenN];
    epsBody = HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosenA];
    tendBody = HOL`Bool`GEN[eV, epsBody];
    folded = EQMP[HOL`Equal`SYM[unfoldTendsto[uV, sup]], tendBody];
    chosenB = HOL`Bool`CHOOSE[bW, bddEx, folded];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[monoIncTm[uV],
      HOL`Bool`DISCH[seqBddAboveTm[uV], chosenB]]]
  ];

monoConvergesIncThm =
  Module[{uV, hMono, hBdd, range, sup, tend, exThm},
    uV = mkVar["u", seqTy]; range = seqRangeTm[uV]; sup = seqRealSup[range];
    hMono = ASSUME[monoIncTm[uV]]; hBdd = ASSUME[seqBddAboveTm[uV]];
    tend = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uV, monoIncTendstoSupThm],
      hMono], hBdd];
    exThm = HOL`Bool`EXISTS[existsTm[mkVar["L", realTy], tendstoTm[uV, mkVar["L", realTy]]],
      sup, tend];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[monoIncTm[uV],
      HOL`Bool`DISCH[seqBddAboveTm[uV], exThm]]]
  ];

monoConvergesDecThm =
  Module[{uV, nV, vSeq, hDec, hBelow, decAll, monoV, belowEx, bW, hAllBelow,
          nBelow, bddAboveV, incEx, lW, hTendV, negTend, seqLeft, betaL, negNeg,
          pointEq, pointAll, seqEq, tendEq, tendU, exFinal, chosenL, chosenB},
    uV = mkVar["u", seqTy]; nV = mkVar["n", numTy];
    vSeq = mkAbs[nV, realNegTm[mkComb[uV, nV]]];
    hDec = ASSUME[monoDecTm[uV]]; hBelow = ASSUME[seqBddBelowTm[uV]];
    decAll = EQMP[unfoldMonoDec[uV], hDec];
    monoV = Module[{nA, mA, hLe, decLe, negLe, impNM, allM, allN},
      nA = mkVar["nA", numTy]; mA = mkVar["mA", numTy];
      hLe = ASSUME[seqNatLe[nA, mA]];
      decLe = HOL`Bool`MP[seqSpecAll[decAll, {nA, mA}], hLe];
      negLe = HOL`Bool`MP[
        seqSpecAll[realLeNegThm, {mkComb[uV, mA], mkComb[uV, nA]}], decLe];
      impNM = HOL`Bool`DISCH[seqNatLe[nA, mA], negLe];
      allM = HOL`Bool`GEN[mA, impNM];
      allN = HOL`Bool`GEN[nA, allM];
      EQMP[HOL`Equal`SYM[seqBetaClean[unfoldMonoInc[vSeq]]], allN]
    ];
    belowEx = EQMP[unfoldSeqBddBelow[uV], hBelow];
    bW = mkVar["bW", realTy]; nBelow = mkVar["n", numTy];
    hAllBelow = ASSUME[forallTm[nBelow, realLeTm[bW, mkComb[uV, nBelow]]]];
    bddAboveV = Module[{nA, lower, negLe, allN, cleanUnfold, exB},
      nA = mkVar["nA", numTy];
      lower = HOL`Bool`SPEC[nA, hAllBelow];
      negLe = HOL`Bool`MP[
        seqSpecAll[realLeNegThm, {bW, mkComb[uV, nA]}], lower];
      allN = HOL`Bool`GEN[nA, negLe];
      cleanUnfold = seqBetaClean[unfoldSeqBddAbove[vSeq]];
      exB = HOL`Bool`EXISTS[concl[cleanUnfold][[2]], realNegTm[bW], allN];
      EQMP[HOL`Equal`SYM[cleanUnfold], exB]
    ];
    incEx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[vSeq, monoConvergesIncThm],
      monoV], bddAboveV];
    lW = mkVar["lW", realTy];
    hTendV = ASSUME[tendstoTm[vSeq, lW]];
    negTend = seqBetaClean[HOL`Bool`MP[seqSpecAll[tendstoNegThm, {vSeq, lW}], hTendV]];
    seqLeft = concl[negTend][[1, 2]];
    betaL = HOL`Equal`BETACONV[mkComb[seqLeft, nV]];
    negNeg = HOL`Bool`SPEC[mkComb[uV, nV], realNegNegThm];
    pointEq = TRANS[betaL, negNeg];
    pointAll = HOL`Bool`GEN[nV, pointEq];
    seqEq = HOL`Stdlib`List`funcExtThm[seqLeft, uV, pointAll];
    tendEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[tendstoConst[], seqEq],
      REFL[realNegTm[lW]]];
    tendU = EQMP[tendEq, negTend];
    exFinal = HOL`Bool`EXISTS[existsTm[mkVar["L", realTy], tendstoTm[uV, mkVar["L", realTy]]],
      realNegTm[lW], tendU];
    chosenL = HOL`Bool`CHOOSE[lW, incEx, exFinal];
    chosenB = HOL`Bool`CHOOSE[bW, belowEx, chosenL];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[monoDecTm[uV],
      HOL`Bool`DISCH[seqBddBelowTm[uV], chosenB]]]
  ];

numFunTy = tyFun[numTy, numTy];
subseqIndexTy = tyFun[numFunTy, boolTy];
subsequenceTy = tyFun[seqTy, tyFun[numFunTy, seqTy]];
peakTy = tyFun[seqTy, tyFun[numTy, boolTy]];
peakIndexTy = tyFun[seqTy, numFunTy];
risingIndexTy = tyFun[seqTy, tyFun[numTy, numFunTy]];

seqNatLt[aT_, bT_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], aT], bT];

seqNatLtCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Num`ltConst[], eqLeft], eqRight];

seqSelectTm[ty_, predT_] := mkComb[mkConst["@", tyFun[tyFun[ty, boolTy], ty]], predT];

seqSubseqIndexBody[phiT_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    forallTm[nV, seqNatLt[mkComb[phiT, nV], mkComb[phiT, sucT[nV]]]]
  ];

seqSubsequenceBody[uT_, phiT_] :=
  Module[{nV},
    nV = mkVar["n", numTy];
    mkAbs[nV, mkComb[uT, mkComb[phiT, nV]]]
  ];

seqPeakBody[uT_, nT_] :=
  Module[{mV},
    mV = mkVar["m", numTy];
    forallTm[mV, impTm[seqNatLe[nT, mV], realLeTm[mkComb[uT, mV], mkComb[uT, nT]]]]
  ];

subseqIndexDefThm =
  Module[{phiV},
    phiV = mkVar["phi", numFunTy];
    newDefinition[mkEq[mkVar["subseqIndex", subseqIndexTy],
      mkAbs[phiV, seqSubseqIndexBody[phiV]]]]
  ];

subseqIndexConst[] := mkConst["subseqIndex", subseqIndexTy];
subseqIndexTm[phiT_] := mkComb[subseqIndexConst[], phiT];

unfoldSubseqIndex[phiT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[subseqIndexDefThm, phiT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

subsequenceDefThm =
  Module[{uV, phiV},
    uV = mkVar["u", seqTy]; phiV = mkVar["phi", numFunTy];
    newDefinition[mkEq[mkVar["subsequence", subsequenceTy],
      mkAbs[uV, mkAbs[phiV, seqSubsequenceBody[uV, phiV]]]]]
  ];

subsequenceConst[] := mkConst["subsequence", subsequenceTy];
subsequenceTm[uT_, phiT_] := mkComb[mkComb[subsequenceConst[], uT], phiT];

unfoldSubsequence[uT_, phiT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[subsequenceDefThm, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, phiT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

seqSubsequenceAppEq[uT_, phiT_, nT_] :=
  Module[{unf, app},
    unf = unfoldSubsequence[uT, phiT];
    app = HOL`Equal`APTHM[unf, nT];
    TRANS[app, HOL`Equal`BETACONV[concl[app][[2]]]]
  ];

peakDefThm =
  Module[{uV, nV},
    uV = mkVar["u", seqTy]; nV = mkVar["n", numTy];
    newDefinition[mkEq[mkVar["peak", peakTy],
      mkAbs[uV, mkAbs[nV, seqPeakBody[uV, nV]]]]]
  ];

peakConst[] := mkConst["peak", peakTy];
peakTm[uT_, nT_] := mkComb[mkComb[peakConst[], uT], nT];

unfoldPeak[uT_, nT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[peakDefThm, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, nT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

seqPeakSelectPred[uT_, lowerT_] :=
  Module[{nPk},
    nPk = mkVar["nPk", numTy];
    mkAbs[nPk, conjTm[seqNatLe[lowerT, nPk], peakTm[uT, nPk]]]
  ];

seqPeakChoice[uT_, lowerT_] := seqSelectTm[numTy, seqPeakSelectPred[uT, lowerT]];

seqPeakStepFun[uT_] :=
  Module[{jStep},
    jStep = mkVar["jStep", numTy];
    mkAbs[jStep, seqPeakChoice[uT, sucT[jStep]]]
  ];

seqPeakIndexRecPred[uT_] :=
  Module[{gRec, kPk, eT, fT},
    gRec = mkVar["gRec", numFunTy]; kPk = mkVar["kPk", numTy];
    eT = seqPeakChoice[uT, zeroN[]]; fT = seqPeakStepFun[uT];
    mkAbs[gRec, conjTm[mkEq[mkComb[gRec, zeroN[]], eT],
      forallTm[kPk, mkEq[mkComb[gRec, sucT[kPk]], mkComb[fT, mkComb[gRec, kPk]]]]]]
  ];

peakIndexDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["peakIndex", peakIndexTy],
      mkAbs[uV, seqSelectTm[numFunTy, seqPeakIndexRecPred[uV]]]]]
  ];

peakIndexConst[] := mkConst["peakIndex", peakIndexTy];
peakIndexTm[uT_] := mkComb[peakIndexConst[], uT];

unfoldPeakIndex[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[peakIndexDefThm, uT];
    (* deep beta: the recursion predicate carries an inner f-redex; selectOfExists
       reduces it, so unfold must too or the @-terms won't aconv-match for SUBS *)
    seqBetaClean[TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]]
  ];

seqRisingSelectPred[uT_, jT_] :=
  Module[{mRise},
    mRise = mkVar["mRise", numTy];
    mkAbs[mRise, conjTm[seqNatLt[jT, mRise],
      realLeTm[mkComb[uT, jT], mkComb[uT, mRise]]]]
  ];

seqRisingChoice[uT_, jT_] := seqSelectTm[numTy, seqRisingSelectPred[uT, jT]];

seqRisingStepFun[uT_] :=
  Module[{jStep},
    jStep = mkVar["jStep", numTy];
    mkAbs[jStep, seqRisingChoice[uT, jStep]]
  ];

seqRisingIndexRecPred[uT_, n0T_] :=
  Module[{gRec, kRise, fT},
    gRec = mkVar["gRec", numFunTy]; kRise = mkVar["kRise", numTy];
    fT = seqRisingStepFun[uT];
    mkAbs[gRec, conjTm[mkEq[mkComb[gRec, zeroN[]], n0T],
      forallTm[kRise, mkEq[mkComb[gRec, sucT[kRise]], mkComb[fT, mkComb[gRec, kRise]]]]]]
  ];

risingIndexDefThm =
  Module[{uV, n0V},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy];
    newDefinition[mkEq[mkVar["risingIndex", risingIndexTy],
      mkAbs[uV, mkAbs[n0V, seqSelectTm[numFunTy, seqRisingIndexRecPred[uV, n0V]]]]]]
  ];

risingIndexConst[] := mkConst["risingIndex", risingIndexTy];
risingIndexTm[uT_, n0T_] := mkComb[mkComb[risingIndexConst[], uT], n0T];

unfoldRisingIndex[uT_, n0T_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[risingIndexDefThm, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, n0T];
    seqBetaClean[TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]]
  ];

seqNumLeZeroEqThm =
  Module[{nV},
    nV = mkVar["n", numTy];
    HOL`Auto`Arith`arithProve[forallTm[nV,
      impTm[seqNatLe[nV, zeroN[]], mkEq[nV, zeroN[]]]]]
  ];

seqNumLeLtTransThm =
  Module[{aV, bV, cV},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    HOL`Auto`Arith`arithProve[seqForallList[{aV, bV, cV},
      seqImpList[{seqNatLe[aV, bV], seqNatLt[bV, cV]}, seqNatLe[aV, cV]]]]
  ];

seqNumStepLeLtTransThm =
  Module[{nV, aV, bV},
    nV = mkVar["n", numTy]; aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    HOL`Auto`Arith`arithProve[seqForallList[{nV, aV, bV},
      seqImpList[{seqNatLe[nV, aV], seqNatLt[aV, bV]}, seqNatLe[sucT[nV], bV]]]]
  ];

seqNumSucLeImpLtThm =
  Module[{aV, bV},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    HOL`Auto`Arith`arithProve[seqForallList[{aV, bV},
      impTm[seqNatLe[sucT[aV], bV], seqNatLt[aV, bV]]]]
  ];

seqNumLeNotLtEqThm =
  Module[{aV, bV, hLe, hNotLt, bLeA, aEqB, bEqA},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    hLe = ASSUME[seqNatLe[aV, bV]];
    hNotLt = ASSUME[notTm[seqNatLt[aV, bV]]];
    bLeA = EQMP[
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`notLtEqLeqThm]],
      hNotLt];
    aEqB = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`leqAntisymThm]],
      hLe], bLeA];
    bEqA = HOL`Equal`SYM[aEqB];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[seqNatLe[aV, bV],
        HOL`Bool`DISCH[notTm[seqNatLt[aV, bV]], bEqA]]]]
  ];

seqNumEqLeqReflLeft[eqTh_] :=
  Module[{aT, bT, refl},
    aT = concl[eqTh][[1, 2]]; bT = concl[eqTh][[2]];
    refl = HOL`Bool`SPEC[bT, HOL`Stdlib`Num`leqReflThm];
    EQMP[seqNatLeCong[HOL`Equal`SYM[eqTh], REFL[bT]], refl]
  ];

peakIndexRecSpecThm =
  Module[{uV, iter, exIter, sat, folded},
    uV = mkVar["u", seqTy];
    iter = HOL`Kernel`INSTTYPE[{tyVar["A"] -> numTy}, HOL`Stdlib`Num`numIterationThm];
    exIter = seqBetaClean[
      HOL`Bool`SPEC[seqPeakStepFun[uV], HOL`Bool`SPEC[seqPeakChoice[uV, zeroN[]], iter]]];
    sat = HOL`Stdlib`Num`selectOfExists[seqPeakIndexRecPred[uV], exIter];
    folded = seqBetaClean[HOL`Drule`SUBS[{HOL`Equal`SYM[unfoldPeakIndex[uV]]}, sat]];
    HOL`Bool`GEN[uV, folded]
  ];

seqPeakIndexZeroEq[uT_] := HOL`Bool`CONJUNCT1[HOL`Bool`SPEC[uT, peakIndexRecSpecThm]];

seqPeakIndexSucEq[uT_, kT_] :=
  seqBetaClean[HOL`Bool`SPEC[kT, HOL`Bool`CONJUNCT2[HOL`Bool`SPEC[uT, peakIndexRecSpecThm]]]];

risingIndexRecSpecThm =
  Module[{uV, n0V, iter, exIter, sat, folded},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy];
    iter = HOL`Kernel`INSTTYPE[{tyVar["A"] -> numTy}, HOL`Stdlib`Num`numIterationThm];
    exIter = seqBetaClean[
      HOL`Bool`SPEC[seqRisingStepFun[uV], HOL`Bool`SPEC[n0V, iter]]];
    sat = HOL`Stdlib`Num`selectOfExists[seqRisingIndexRecPred[uV, n0V], exIter];
    folded = seqBetaClean[HOL`Drule`SUBS[{HOL`Equal`SYM[unfoldRisingIndex[uV, n0V]]}, sat]];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[n0V, folded]]
  ];

seqRisingIndexZeroEq[uT_, n0T_] :=
  HOL`Bool`CONJUNCT1[HOL`Bool`SPEC[n0T, HOL`Bool`SPEC[uT, risingIndexRecSpecThm]]];

seqRisingIndexSucEq[uT_, n0T_, kT_] :=
  seqBetaClean[HOL`Bool`SPEC[kT,
    HOL`Bool`CONJUNCT2[HOL`Bool`SPEC[n0T, HOL`Bool`SPEC[uT, risingIndexRecSpecThm]]]]];

subseqIndexMonoThm =
  Module[{phiV, nV, mV, hSubTm, hSub, hStepAll, pLam, mInd, nBase, hLeBase,
          nEq0, baseGoal, base, ihTm, ih, nStep, hLeSuc, caseTh, hLeM,
          ihLe, hLtM, branchA, hEqSuc, phiEq, branchB, stepPoint, stepAll,
          indSpec, indAllM, hLe, finalPoint},
    phiV = mkVar["phi", numFunTy]; nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    hSubTm = subseqIndexTm[phiV]; hSub = ASSUME[hSubTm];
    hStepAll = EQMP[unfoldSubseqIndex[phiV], hSub];
    pLam = Module[{mP, nP},
      mP = mkVar["mP", numTy]; nP = mkVar["nP", numTy];
      mkAbs[mP, forallTm[nP,
        impTm[seqNatLe[nP, mP], seqNatLe[mkComb[phiV, nP], mkComb[phiV, mP]]]]]
    ];

    nBase = mkVar["nBase", numTy];
    hLeBase = ASSUME[seqNatLe[nBase, zeroN[]]];
    nEq0 = HOL`Bool`MP[HOL`Bool`SPEC[nBase, seqNumLeZeroEqThm], hLeBase];
    baseGoal = seqNumEqLeqReflLeft[HOL`Equal`APTERM[phiV, nEq0]];
    base = HOL`Bool`GEN[nBase, HOL`Bool`DISCH[seqNatLe[nBase, zeroN[]], baseGoal]];

    mInd = mkVar["mInd", numTy];
    ihTm = forallTm[nV, impTm[seqNatLe[nV, mInd],
      seqNatLe[mkComb[phiV, nV], mkComb[phiV, mInd]]]];
    ih = ASSUME[ihTm];
    nStep = mkVar["nStep", numTy];
    hLeSuc = ASSUME[seqNatLe[nStep, sucT[mInd]]];
    caseTh = HOL`Bool`MP[
      HOL`Bool`SPEC[mInd, HOL`Bool`SPEC[nStep, HOL`Stdlib`Num`leqSucCaseThm]],
      hLeSuc];
    hLeM = ASSUME[seqNatLe[nStep, mInd]];
    ihLe = HOL`Bool`MP[HOL`Bool`SPEC[nStep, ih], hLeM];
    hLtM = HOL`Bool`SPEC[mInd, hStepAll];
    branchA = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqNumLeLtTransThm,
        {mkComb[phiV, nStep], mkComb[phiV, mInd], mkComb[phiV, sucT[mInd]]}],
      ihLe], hLtM];
    hEqSuc = ASSUME[mkEq[nStep, sucT[mInd]]];
    phiEq = HOL`Equal`APTERM[phiV, hEqSuc];
    branchB = seqNumEqLeqReflLeft[phiEq];
    stepPoint = HOL`Bool`DISJCASES[caseTh, branchA, branchB];
    stepAll = HOL`Bool`GEN[mInd, HOL`Bool`DISCH[ihTm,
      HOL`Bool`GEN[nStep, HOL`Bool`DISCH[seqNatLe[nStep, sucT[mInd]], stepPoint]]]];
    indSpec = seqBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAllM = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];

    hLe = ASSUME[seqNatLe[nV, mV]];
    finalPoint = HOL`Bool`MP[HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, indAllM]], hLe];
    HOL`Bool`GEN[phiV, HOL`Bool`DISCH[hSubTm,
      HOL`Bool`GEN[nV, HOL`Bool`GEN[mV,
        HOL`Bool`DISCH[seqNatLe[nV, mV], finalPoint]]]]]
  ];

subseqIndexGeSelfThm =
  Module[{phiV, nV, hSubTm, hSub, hStepAll, pLam, base, nInd, ihTm, ih,
          hLt, stepGoal, stepAll, indSpec, indAll, finalPoint},
    phiV = mkVar["phi", numFunTy]; nV = mkVar["n", numTy];
    hSubTm = subseqIndexTm[phiV]; hSub = ASSUME[hSubTm];
    hStepAll = EQMP[unfoldSubseqIndex[phiV], hSub];
    pLam = Module[{nP},
      nP = mkVar["nP", numTy];
      mkAbs[nP, seqNatLe[nP, mkComb[phiV, nP]]]
    ];
    base = HOL`Bool`SPEC[mkComb[phiV, zeroN[]], HOL`Stdlib`Num`leqZeroThm];
    nInd = mkVar["nInd", numTy];
    ihTm = seqNatLe[nInd, mkComb[phiV, nInd]];
    ih = ASSUME[ihTm];
    hLt = HOL`Bool`SPEC[nInd, hStepAll];
    stepGoal = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqNumStepLeLtTransThm,
        {nInd, mkComb[phiV, nInd], mkComb[phiV, sucT[nInd]]}],
      ih], hLt];
    stepAll = HOL`Bool`GEN[nInd, HOL`Bool`DISCH[ihTm, stepGoal]];
    indSpec = seqBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    finalPoint = HOL`Bool`SPEC[nV, indAll];
    HOL`Bool`GEN[phiV, HOL`Bool`DISCH[hSubTm,
      HOL`Bool`GEN[nV, finalPoint]]]
  ];

notPeakExistsLaterThm =
  Module[{uV, nV, mW, exGoal, hNotPeakTm, hNotPeak, hNo, hLe, total,
          hBack, branchBack, hForward, hLt, conjW, exW, ffW, notLt, mEqN,
          uEq, refl, branchForward, peakAll, peakFolded, ffPeak, body},
    uV = mkVar["u", seqTy]; nV = mkVar["n", numTy]; mW = mkVar["mW", numTy];
    exGoal = existsTm[mW, conjTm[seqNatLt[nV, mW],
      realLeTm[mkComb[uV, nV], mkComb[uV, mW]]]];
    hNotPeakTm = notTm[peakTm[uV, nV]];
    hNotPeak = ASSUME[hNotPeakTm];
    hNo = ASSUME[notTm[exGoal]];

    hLe = ASSUME[seqNatLe[nV, mW]];
    total = HOL`Bool`SPEC[mkComb[uV, nV],
      HOL`Bool`SPEC[mkComb[uV, mW], realLeTotalThm]];
    hBack = ASSUME[realLeTm[mkComb[uV, mW], mkComb[uV, nV]]];
    branchBack = hBack;

    hForward = ASSUME[realLeTm[mkComb[uV, nV], mkComb[uV, mW]]];
    hLt = ASSUME[seqNatLt[nV, mW]];
    conjW = HOL`Bool`CONJ[hLt, hForward];
    exW = HOL`Bool`EXISTS[exGoal, mW, conjW];
    ffW = HOL`Bool`MP[HOL`Bool`NOTELIM[hNo], exW];
    notLt = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[seqNatLt[nV, mW], ffW]];
    mEqN = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[seqNumLeNotLtEqThm, {nV, mW}],
      hLe], notLt];
    uEq = HOL`Equal`APTERM[uV, mEqN];
    refl = HOL`Bool`SPEC[mkComb[uV, nV], realLeReflThm];
    branchForward = EQMP[seqRealLeCong[HOL`Equal`SYM[uEq], REFL[mkComb[uV, nV]]], refl];

    peakAll = HOL`Bool`GEN[mW, HOL`Bool`DISCH[seqNatLe[nV, mW],
      HOL`Bool`DISJCASES[total, branchBack, branchForward]]];
    peakFolded = EQMP[HOL`Equal`SYM[unfoldPeak[uV, nV]], peakAll];
    ffPeak = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotPeak], peakFolded];
    body = HOL`Bool`CCONTR[exGoal, ffPeak];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hNotPeakTm, body]]]
  ];

eventuallyNotPeakThm =
  Module[{uV, n0V, nW, infTm, goalTm, hNotInfTm, hNotInf, hNoGoal,
          exAtN, hNoEx, hLe, hPeak, conjN, exN, ffN, notPeakN, allNo,
          exGoalN, ffGoal, exNByContr, infAll, ffInf, body},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy]; nW = mkVar["nW", numTy];
    infTm = forallTm[n0V, existsTm[nW,
      conjTm[seqNatLe[n0V, nW], peakTm[uV, nW]]]];
    goalTm = existsTm[n0V, forallTm[nW,
      impTm[seqNatLe[n0V, nW], notTm[peakTm[uV, nW]]]]];
    hNotInfTm = notTm[infTm]; hNotInf = ASSUME[hNotInfTm];
    hNoGoal = ASSUME[notTm[goalTm]];
    exAtN = existsTm[nW, conjTm[seqNatLe[n0V, nW], peakTm[uV, nW]]];
    hNoEx = ASSUME[notTm[exAtN]];
    hLe = ASSUME[seqNatLe[n0V, nW]];
    hPeak = ASSUME[peakTm[uV, nW]];
    conjN = HOL`Bool`CONJ[hLe, hPeak];
    exN = HOL`Bool`EXISTS[exAtN, nW, conjN];
    ffN = HOL`Bool`MP[HOL`Bool`NOTELIM[hNoEx], exN];
    notPeakN = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[peakTm[uV, nW], ffN]];
    allNo = HOL`Bool`GEN[nW,
      HOL`Bool`DISCH[seqNatLe[n0V, nW], notPeakN]];
    exGoalN = HOL`Bool`EXISTS[goalTm, n0V, allNo];
    ffGoal = HOL`Bool`MP[HOL`Bool`NOTELIM[hNoGoal], exGoalN];
    exNByContr = HOL`Bool`CCONTR[exAtN, ffGoal];
    infAll = HOL`Bool`GEN[n0V, exNByContr];
    ffInf = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotInf], infAll];
    body = HOL`Bool`CCONTR[goalTm, ffInf];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[hNotInfTm, body]]
  ];

seqPeakSelectSpec[hInf_, uT_, lowerT_] :=
  HOL`Stdlib`Num`selectOfExists[seqPeakSelectPred[uT, lowerT], HOL`Bool`SPEC[lowerT, hInf]];

seqPeakIndexInfTm[uT_] :=
  Module[{n0V, nPk},
    n0V = mkVar["N", numTy]; nPk = mkVar["nPk", numTy];
    forallTm[n0V, existsTm[nPk,
      conjTm[seqNatLe[n0V, nPk], peakTm[uT, nPk]]]]
  ];

peakIndexPeakThm =
  Module[{uV, kV, hInfTm, hInf, phi, peakU, pLam, spec0, basePeak, eq0,
          base, kInd, ihTm, ih, lower, specSuc, stepPeak, eqSuc, stepGoal,
          stepAll, indSpec, indAll},
    uV = mkVar["u", seqTy]; kV = mkVar["k", numTy];
    hInfTm = seqPeakIndexInfTm[uV]; hInf = ASSUME[hInfTm];
    phi = peakIndexTm[uV]; peakU = mkComb[peakConst[], uV];
    pLam = Module[{kP}, kP = mkVar["kP", numTy];
      mkAbs[kP, peakTm[uV, mkComb[phi, kP]]]];

    spec0 = seqPeakSelectSpec[hInf, uV, zeroN[]];
    basePeak = HOL`Bool`CONJUNCT2[spec0];
    eq0 = seqPeakIndexZeroEq[uV];
    base = EQMP[HOL`Equal`APTERM[peakU, HOL`Equal`SYM[eq0]], basePeak];

    kInd = mkVar["kInd", numTy];
    ihTm = peakTm[uV, mkComb[phi, kInd]]; ih = ASSUME[ihTm];
    lower = sucT[mkComb[phi, kInd]];
    specSuc = seqPeakSelectSpec[hInf, uV, lower];
    stepPeak = HOL`Bool`CONJUNCT2[specSuc];
    eqSuc = seqPeakIndexSucEq[uV, kInd];
    stepGoal = EQMP[HOL`Equal`APTERM[peakU, HOL`Equal`SYM[eqSuc]], stepPeak];
    stepAll = HOL`Bool`GEN[kInd, HOL`Bool`DISCH[ihTm, stepGoal]];
    indSpec = seqBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[hInfTm, indAll]]
  ];

peakIndexStepThm =
  Module[{uV, kV, hInfTm, hInf, phi, lower, specK, leChoice, eqSuc, leIdx, ltIdx,
          allK},
    uV = mkVar["u", seqTy]; kV = mkVar["k", numTy];
    hInfTm = seqPeakIndexInfTm[uV]; hInf = ASSUME[hInfTm];
    phi = peakIndexTm[uV];
    lower = sucT[mkComb[phi, kV]];
    specK = seqPeakSelectSpec[hInf, uV, lower];
    leChoice = HOL`Bool`CONJUNCT1[specK];
    eqSuc = seqPeakIndexSucEq[uV, kV];
    leIdx = EQMP[seqNatLeCong[REFL[lower], HOL`Equal`SYM[eqSuc]], leChoice];
    ltIdx = HOL`Bool`MP[seqSpecAll[seqNumSucLeImpLtThm,
      {mkComb[phi, kV], mkComb[phi, sucT[kV]]}], leIdx];
    allK = HOL`Bool`GEN[kV, ltIdx];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[hInfTm, allK]]
  ];

peakIndexSubseqThm =
  Module[{uV, hInfTm, hInf, phi, stepAll, folded},
    uV = mkVar["u", seqTy]; hInfTm = seqPeakIndexInfTm[uV]; hInf = ASSUME[hInfTm];
    phi = peakIndexTm[uV];
    stepAll = HOL`Bool`MP[HOL`Bool`SPEC[uV, peakIndexStepThm], hInf];
    folded = EQMP[HOL`Equal`SYM[unfoldSubseqIndex[phi]], stepAll];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[hInfTm, folded]]
  ];

peakIndexDecreasingThm =
  Module[{uV, nV, mV, hInfTm, hInf, phi, subSeq, hLe, subIdx, monoPhi,
          idxLe, peakAll, peakN, peakUnfolded, baseLe, appM, appN, point,
          allM, allN, folded},
    uV = mkVar["u", seqTy]; nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    hInfTm = seqPeakIndexInfTm[uV]; hInf = ASSUME[hInfTm];
    phi = peakIndexTm[uV]; subSeq = subsequenceTm[uV, phi];
    hLe = ASSUME[seqNatLe[nV, mV]];
    subIdx = HOL`Bool`MP[HOL`Bool`SPEC[uV, peakIndexSubseqThm], hInf];
    monoPhi = HOL`Bool`MP[HOL`Bool`SPEC[phi, subseqIndexMonoThm], subIdx];
    idxLe = HOL`Bool`MP[seqSpecAll[monoPhi, {nV, mV}], hLe];
    peakAll = HOL`Bool`MP[HOL`Bool`SPEC[uV, peakIndexPeakThm], hInf];
    peakN = HOL`Bool`SPEC[nV, peakAll];
    peakUnfolded = EQMP[unfoldPeak[uV, mkComb[phi, nV]], peakN];
    baseLe = HOL`Bool`MP[HOL`Bool`SPEC[mkComb[phi, mV], peakUnfolded], idxLe];
    appM = seqSubsequenceAppEq[uV, phi, mV];
    appN = seqSubsequenceAppEq[uV, phi, nV];
    point = EQMP[seqRealLeCong[HOL`Equal`SYM[appM], HOL`Equal`SYM[appN]], baseLe];
    allM = HOL`Bool`GEN[mV, HOL`Bool`DISCH[seqNatLe[nV, mV], point]];
    allN = HOL`Bool`GEN[nV, allM];
    folded = EQMP[HOL`Equal`SYM[unfoldMonoDec[subSeq]], allN];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[hInfTm, folded]]
  ];

seqRisingSelectSpec[uT_, jT_, notPeakTh_] :=
  HOL`Stdlib`Num`selectOfExists[seqRisingSelectPred[uT, jT],
    HOL`Bool`MP[seqSpecAll[notPeakExistsLaterThm, {uT, jT}], notPeakTh]];

seqRisingNoPeakTm[uT_, n0T_] :=
  Module[{nNo},
    nNo = mkVar["nNo", numTy];
    forallTm[nNo, impTm[seqNatLe[n0T, nNo], notTm[peakTm[uT, nNo]]]]
  ];

risingIndexGeThm =
  Module[{uV, n0V, kV, hNoTm, hNo, phi, pLam, eq0, baseRefl, base,
          kInd, ihTm, ih, idxK, idxSuc, notPk, specK, hLtChoice, eqSuc,
          hLtIdx, stepGoal, stepAll, indSpec, indAll},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy]; kV = mkVar["k", numTy];
    hNoTm = seqRisingNoPeakTm[uV, n0V]; hNo = ASSUME[hNoTm];
    phi = risingIndexTm[uV, n0V];
    pLam = Module[{kP}, kP = mkVar["kP", numTy];
      mkAbs[kP, seqNatLe[n0V, mkComb[phi, kP]]]];

    eq0 = seqRisingIndexZeroEq[uV, n0V];
    baseRefl = HOL`Bool`SPEC[n0V, HOL`Stdlib`Num`leqReflThm];
    base = EQMP[seqNatLeCong[REFL[n0V], HOL`Equal`SYM[eq0]], baseRefl];

    kInd = mkVar["kInd", numTy];
    idxK = mkComb[phi, kInd]; idxSuc = mkComb[phi, sucT[kInd]];
    ihTm = seqNatLe[n0V, idxK]; ih = ASSUME[ihTm];
    notPk = HOL`Bool`MP[HOL`Bool`SPEC[idxK, hNo], ih];
    specK = seqRisingSelectSpec[uV, idxK, notPk];
    hLtChoice = HOL`Bool`CONJUNCT1[specK];
    eqSuc = seqRisingIndexSucEq[uV, n0V, kInd];
    hLtIdx = EQMP[seqNatLtCong[REFL[idxK], HOL`Equal`SYM[eqSuc]], hLtChoice];
    stepGoal = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqNumLeLtTransThm, {n0V, idxK, idxSuc}], ih], hLtIdx];
    stepAll = HOL`Bool`GEN[kInd, HOL`Bool`DISCH[ihTm, stepGoal]];
    indSpec = seqBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAll = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[n0V, HOL`Bool`DISCH[hNoTm, indAll]]]
  ];

risingIndexStepThm =
  Module[{uV, n0V, kV, hNoTm, hNo, phi, idxK, idxSuc, geAll, geK, notPk,
          specK, hLtChoice, eqSuc, hLtIdx, allK},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy]; kV = mkVar["k", numTy];
    hNoTm = seqRisingNoPeakTm[uV, n0V]; hNo = ASSUME[hNoTm];
    phi = risingIndexTm[uV, n0V]; idxK = mkComb[phi, kV]; idxSuc = mkComb[phi, sucT[kV]];
    geAll = HOL`Bool`MP[seqSpecAll[risingIndexGeThm, {uV, n0V}], hNo];
    geK = HOL`Bool`SPEC[kV, geAll];
    notPk = HOL`Bool`MP[HOL`Bool`SPEC[idxK, hNo], geK];
    specK = seqRisingSelectSpec[uV, idxK, notPk];
    hLtChoice = HOL`Bool`CONJUNCT1[specK];
    eqSuc = seqRisingIndexSucEq[uV, n0V, kV];
    hLtIdx = EQMP[seqNatLtCong[REFL[idxK], HOL`Equal`SYM[eqSuc]], hLtChoice];
    allK = HOL`Bool`GEN[kV, hLtIdx];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[n0V, HOL`Bool`DISCH[hNoTm, allK]]]
  ];

risingIndexStepLeThm =
  Module[{uV, n0V, kV, hNoTm, hNo, phi, idxK, idxSuc, geAll, geK, notPk,
          specK, hLeChoice, eqSuc, uEq, hLeIdx, allK},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy]; kV = mkVar["k", numTy];
    hNoTm = seqRisingNoPeakTm[uV, n0V]; hNo = ASSUME[hNoTm];
    phi = risingIndexTm[uV, n0V]; idxK = mkComb[phi, kV]; idxSuc = mkComb[phi, sucT[kV]];
    geAll = HOL`Bool`MP[seqSpecAll[risingIndexGeThm, {uV, n0V}], hNo];
    geK = HOL`Bool`SPEC[kV, geAll];
    notPk = HOL`Bool`MP[HOL`Bool`SPEC[idxK, hNo], geK];
    specK = seqRisingSelectSpec[uV, idxK, notPk];
    hLeChoice = HOL`Bool`CONJUNCT2[specK];
    eqSuc = seqRisingIndexSucEq[uV, n0V, kV];
    uEq = HOL`Equal`APTERM[uV, HOL`Equal`SYM[eqSuc]];
    hLeIdx = EQMP[seqRealLeCong[REFL[mkComb[uV, idxK]], uEq], hLeChoice];
    allK = HOL`Bool`GEN[kV, hLeIdx];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[n0V, HOL`Bool`DISCH[hNoTm, allK]]]
  ];

risingIndexSubseqThm =
  Module[{uV, n0V, hNoTm, hNo, phi, stepAll, folded},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy];
    hNoTm = seqRisingNoPeakTm[uV, n0V]; hNo = ASSUME[hNoTm];
    phi = risingIndexTm[uV, n0V];
    stepAll = HOL`Bool`MP[seqSpecAll[risingIndexStepThm, {uV, n0V}], hNo];
    folded = EQMP[HOL`Equal`SYM[unfoldSubseqIndex[phi]], stepAll];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[n0V, HOL`Bool`DISCH[hNoTm, folded]]]
  ];

risingIndexIncreasingThm =
  Module[{uV, n0V, nV, mV, hNoTm, hNo, phi, subSeq, pLam, nBase, hLeBase,
          nEq0, seqEq0, baseRefl, base, mInd, ihTm, ih, nStep, hLeSuc,
          caseTh, hLeM, ihLe, stepLeAll, stepLeMRaw, appM, appSuc, stepLeM,
          branchA, hEqSuc, seqEqSuc, branchB, pointStep, stepAll, indSpec,
          indAllM, hLe, finalPoint, allM, allN, folded},
    uV = mkVar["u", seqTy]; n0V = mkVar["N", numTy];
    nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    hNoTm = seqRisingNoPeakTm[uV, n0V]; hNo = ASSUME[hNoTm];
    phi = risingIndexTm[uV, n0V]; subSeq = subsequenceTm[uV, phi];
    pLam = Module[{mP, nP},
      mP = mkVar["mP", numTy]; nP = mkVar["nP", numTy];
      mkAbs[mP, forallTm[nP,
        impTm[seqNatLe[nP, mP], realLeTm[mkComb[subSeq, nP], mkComb[subSeq, mP]]]]]
    ];

    nBase = mkVar["nBase", numTy];
    hLeBase = ASSUME[seqNatLe[nBase, zeroN[]]];
    nEq0 = HOL`Bool`MP[HOL`Bool`SPEC[nBase, seqNumLeZeroEqThm], hLeBase];
    seqEq0 = HOL`Equal`APTERM[subSeq, nEq0];
    baseRefl = HOL`Bool`SPEC[mkComb[subSeq, zeroN[]], realLeReflThm];
    base = EQMP[seqRealLeCong[HOL`Equal`SYM[seqEq0], REFL[mkComb[subSeq, zeroN[]]]], baseRefl];
    base = HOL`Bool`GEN[nBase, HOL`Bool`DISCH[seqNatLe[nBase, zeroN[]], base]];

    mInd = mkVar["mInd", numTy];
    ihTm = forallTm[nV, impTm[seqNatLe[nV, mInd],
      realLeTm[mkComb[subSeq, nV], mkComb[subSeq, mInd]]]];
    ih = ASSUME[ihTm];
    nStep = mkVar["nStep", numTy];
    hLeSuc = ASSUME[seqNatLe[nStep, sucT[mInd]]];
    caseTh = HOL`Bool`MP[
      HOL`Bool`SPEC[mInd, HOL`Bool`SPEC[nStep, HOL`Stdlib`Num`leqSucCaseThm]],
      hLeSuc];
    hLeM = ASSUME[seqNatLe[nStep, mInd]];
    ihLe = HOL`Bool`MP[HOL`Bool`SPEC[nStep, ih], hLeM];
    stepLeAll = HOL`Bool`MP[seqSpecAll[risingIndexStepLeThm, {uV, n0V}], hNo];
    stepLeMRaw = HOL`Bool`SPEC[mInd, stepLeAll];
    appM = seqSubsequenceAppEq[uV, phi, mInd];
    appSuc = seqSubsequenceAppEq[uV, phi, sucT[mInd]];
    stepLeM = EQMP[seqRealLeCong[HOL`Equal`SYM[appM], HOL`Equal`SYM[appSuc]], stepLeMRaw];
    branchA = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeTransThm,
        {mkComb[subSeq, nStep], mkComb[subSeq, mInd], mkComb[subSeq, sucT[mInd]]}],
      ihLe], stepLeM];
    hEqSuc = ASSUME[mkEq[nStep, sucT[mInd]]];
    seqEqSuc = HOL`Equal`APTERM[subSeq, hEqSuc];
    branchB = EQMP[seqRealLeCong[HOL`Equal`SYM[seqEqSuc],
      REFL[mkComb[subSeq, sucT[mInd]]]],
      HOL`Bool`SPEC[mkComb[subSeq, sucT[mInd]], realLeReflThm]];
    pointStep = HOL`Bool`DISJCASES[caseTh, branchA, branchB];
    stepAll = HOL`Bool`GEN[mInd, HOL`Bool`DISCH[ihTm,
      HOL`Bool`GEN[nStep, HOL`Bool`DISCH[seqNatLe[nStep, sucT[mInd]], pointStep]]]];
    indSpec = seqBetaClean[HOL`Bool`SPEC[pLam, HOL`Stdlib`Num`numInductionThm]];
    indAllM = HOL`Bool`MP[indSpec, HOL`Bool`CONJ[base, stepAll]];

    hLe = ASSUME[seqNatLe[nV, mV]];
    finalPoint = HOL`Bool`MP[HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, indAllM]], hLe];
    allM = HOL`Bool`GEN[mV, HOL`Bool`DISCH[seqNatLe[nV, mV], finalPoint]];
    allN = HOL`Bool`GEN[nV, allM];
    folded = EQMP[HOL`Equal`SYM[unfoldMonoInc[subSeq]], allN];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[n0V, HOL`Bool`DISCH[hNoTm, folded]]]
  ];

seqOrTm[pT_, qT_] :=
  mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], pT], qT];

seqMonoSubseqBody[uT_, phiT_] :=
  Module[{subSeq},
    subSeq = subsequenceTm[uT, phiT];
    conjTm[subseqIndexTm[phiT], seqOrTm[monoIncTm[subSeq], monoDecTm[subSeq]]]
  ];

seqMonoSubseqGoal[uT_] :=
  Module[{phiW},
    phiW = mkVar["phi", numFunTy];
    existsTm[phiW, seqMonoSubseqBody[uT, phiW]]
  ];

existsMonoSubseqThm =
  Module[{uV, infTm, goalTm, em, hInf, phiPeak, subPeak, decPeak, disjPeak,
          conjPeak, exPeak, hNotInf, exNo, nW, hNoTm, hNo, phiRise, subRise,
          incRise, disjRise, conjRise, exRise, chosenRise, body},
    uV = mkVar["u", seqTy];
    infTm = seqPeakIndexInfTm[uV]; goalTm = seqMonoSubseqGoal[uV];
    em = HOL`Bool`EXCLUDEDMIDDLE[infTm];

    hInf = ASSUME[infTm];
    phiPeak = peakIndexTm[uV];
    subPeak = HOL`Bool`MP[HOL`Bool`SPEC[uV, peakIndexSubseqThm], hInf];
    decPeak = HOL`Bool`MP[HOL`Bool`SPEC[uV, peakIndexDecreasingThm], hInf];
    disjPeak = HOL`Bool`DISJ2[decPeak, monoIncTm[subsequenceTm[uV, phiPeak]]];
    conjPeak = HOL`Bool`CONJ[subPeak, disjPeak];
    exPeak = HOL`Bool`EXISTS[goalTm, phiPeak, conjPeak];

    hNotInf = ASSUME[notTm[infTm]];
    exNo = HOL`Bool`MP[HOL`Bool`SPEC[uV, eventuallyNotPeakThm], hNotInf];
    nW = mkVar["nW", numTy];
    hNoTm = seqRisingNoPeakTm[uV, nW]; hNo = ASSUME[hNoTm];
    phiRise = risingIndexTm[uV, nW];
    subRise = HOL`Bool`MP[seqSpecAll[risingIndexSubseqThm, {uV, nW}], hNo];
    incRise = HOL`Bool`MP[seqSpecAll[risingIndexIncreasingThm, {uV, nW}], hNo];
    disjRise = HOL`Bool`DISJ1[incRise, monoDecTm[subsequenceTm[uV, phiRise]]];
    conjRise = HOL`Bool`CONJ[subRise, disjRise];
    exRise = HOL`Bool`EXISTS[goalTm, phiRise, conjRise];
    chosenRise = HOL`Bool`CHOOSE[nW, exNo, exRise];

    body = HOL`Bool`DISJCASES[em, exPeak, chosenRise];
    HOL`Bool`GEN[uV, body]
  ];

seqCauchyTy = tyFun[seqTy, boolTy];
elbTy = tyFun[seqTy, tyFun[realTy, boolTy]];

seqCauchyCloseAtom[uT_, eT_, nT_, mT_] :=
  realLtTm[seqRealAbs[realAddTm[mkComb[uT, nT], realNegTm[mkComb[uT, mT]]]], eT];

seqCauchyTailAll[uT_, eT_, n0T_] :=
  Module[{nC, mC},
    nC = mkVar["nC", numTy]; mC = mkVar["mC", numTy];
    forallTm[nC, forallTm[mC,
      impTm[seqNatLe[n0T, nC],
        impTm[seqNatLe[n0T, mC], seqCauchyCloseAtom[uT, eT, nC, mC]]]]]
  ];

seqCauchyBody[uT_] :=
  Module[{eC, nC},
    eC = mkVar["e", realTy]; nC = mkVar["N", numTy];
    forallTm[eC, impTm[realLtTm[zeroRealTm[], eC],
      existsTm[nC, seqCauchyTailAll[uT, eC, nC]]]]
  ];

seqElbAll[uT_, xT_, n0T_] :=
  Module[{nE},
    nE = mkVar["nE", numTy];
    forallTm[nE, impTm[seqNatLe[n0T, nE], realLeTm[xT, mkComb[uT, nE]]]]
  ];

seqElbBody[uT_, xT_] :=
  Module[{nE},
    nE = mkVar["NE", numTy];
    existsTm[nE, seqElbAll[uT, xT, nE]]
  ];

seqCauchyDefThm =
  Module[{uV},
    uV = mkVar["u", seqTy];
    newDefinition[mkEq[mkVar["seqCauchy", seqCauchyTy],
      mkAbs[uV, seqCauchyBody[uV]]]]
  ];

seqCauchyConst[] := mkConst["seqCauchy", seqCauchyTy];
seqCauchyTm[uT_] := mkComb[seqCauchyConst[], uT];

unfoldSeqCauchy[uT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[seqCauchyDefThm, uT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

elbDefThm =
  Module[{uV, xV},
    uV = mkVar["u", seqTy]; xV = mkVar["x", realTy];
    newDefinition[mkEq[mkVar["elb", elbTy],
      mkAbs[uV, mkAbs[xV, seqElbBody[uV, xV]]]]]
  ];

elbConst[] := mkConst["elb", elbTy];
elbTm[uT_, xT_] := mkComb[mkComb[elbConst[], uT], xT];

unfoldElb[uT_, xT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[elbDefThm, uT];
    s1b = TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, xT];
    TRANS[s2, HOL`Equal`BETACONV[concl[s2][[2]]]]
  ];

seqArithAbsSubLeftConvThm =
  Module[{aV, bV, eV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{aV, bV, eV},
        impTm[realLtTm[realNegTm[realAddTm[aV, realNegTm[bV]]], eV],
          realLtTm[realAddTm[bV, realNegTm[eV]], aV]]]]
  ];

seqArithAbsSubRightConvThm =
  Module[{aV, bV, eV},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{aV, bV, eV},
        impTm[realLtTm[realAddTm[aV, realNegTm[bV]], eV],
          realLtTm[aV, realAddTm[bV, eV]]]]]
  ];

seqArithCauchyLeftBoundThm =
  Module[{sV, cV, xV, eV},
    sV = mkVar["s", realTy]; cV = mkVar["c", realTy];
    xV = mkVar["x", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{sV, cV, xV, eV},
        seqImpList[{realLeTm[sV, realAddTm[cV, seqHalf[eV]]],
          realLtTm[cV, realAddTm[xV, seqHalf[eV]]]},
          realLtTm[realAddTm[sV, realNegTm[eV]], xV]]]]
  ];

seqArithCauchyRightBoundThm =
  Module[{sV, cV, xV, eV},
    sV = mkVar["s", realTy]; cV = mkVar["c", realTy];
    xV = mkVar["x", realTy]; eV = mkVar["e", realTy];
    HOL`Auto`RealArith`realArithProve[
      seqForallList[{sV, cV, xV, eV},
        seqImpList[{realLtTm[xV, realAddTm[cV, seqHalf[eV]]],
          realLeTm[realAddTm[cV, realNegTm[seqHalf[eV]]], sV]},
          realLtTm[xV, realAddTm[sV, eV]]]]]
  ];

realAbsSubLtLeftThm =
  Module[{aV, bV, eV, diff, hAbsTm, hAbs, negLe, negLt, body},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; eV = mkVar["e", realTy];
    diff = realAddTm[aV, realNegTm[bV]];
    hAbsTm = realLtTm[seqRealAbs[diff], eV];
    hAbs = ASSUME[hAbsTm];
    negLe = HOL`Bool`SPEC[diff, realNegLeAbsThm];
    negLt = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeLtTransThm, {realNegTm[diff], seqRealAbs[diff], eV}],
      negLe], hAbs];
    body = HOL`Bool`MP[seqSpecAll[seqArithAbsSubLeftConvThm, {aV, bV, eV}], negLt];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[eV,
      HOL`Bool`DISCH[hAbsTm, body]]]]
  ];

realAbsSubLtRightThm =
  Module[{aV, bV, eV, diff, hAbsTm, hAbs, diffLe, diffLt, body},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; eV = mkVar["e", realTy];
    diff = realAddTm[aV, realNegTm[bV]];
    hAbsTm = realLtTm[seqRealAbs[diff], eV];
    hAbs = ASSUME[hAbsTm];
    diffLe = HOL`Bool`SPEC[diff, realLeAbsSelfThm];
    diffLt = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeLtTransThm, {diff, seqRealAbs[diff], eV}],
      diffLe], hAbs];
    body = HOL`Bool`MP[seqSpecAll[seqArithAbsSubRightConvThm, {aV, bV, eV}], diffLt];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[eV,
      HOL`Bool`DISCH[hAbsTm, body]]]]
  ];

cauchyTailLowerThm =
  Module[{uV, eV, n0V, nV, hTailTm, hTail, hLeTm, hLe, reflN, close, body},
    uV = mkVar["u", seqTy]; eV = mkVar["e", realTy];
    n0V = mkVar["N", numTy]; nV = mkVar["n", numTy];
    hTailTm = seqCauchyTailAll[uV, eV, n0V]; hTail = ASSUME[hTailTm];
    hLeTm = seqNatLe[n0V, nV]; hLe = ASSUME[hLeTm];
    reflN = HOL`Bool`SPEC[n0V, HOL`Stdlib`Num`leqReflThm];
    close = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[hTail, {nV, n0V}], hLe], reflN];
    body = HOL`Bool`MP[
      seqSpecAll[realAbsSubLtLeftThm, {mkComb[uV, nV], mkComb[uV, n0V], eV}],
      close];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[eV, HOL`Bool`GEN[n0V, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hTailTm, HOL`Bool`DISCH[hLeTm, body]]]]]]
  ];

cauchyTailUpperThm =
  Module[{uV, eV, n0V, nV, hTailTm, hTail, hLeTm, hLe, reflN, close, body},
    uV = mkVar["u", seqTy]; eV = mkVar["e", realTy];
    n0V = mkVar["N", numTy]; nV = mkVar["n", numTy];
    hTailTm = seqCauchyTailAll[uV, eV, n0V]; hTail = ASSUME[hTailTm];
    hLeTm = seqNatLe[n0V, nV]; hLe = ASSUME[hLeTm];
    reflN = HOL`Bool`SPEC[n0V, HOL`Stdlib`Num`leqReflThm];
    close = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[hTail, {nV, n0V}], hLe], reflN];
    body = HOL`Bool`MP[
      seqSpecAll[realAbsSubLtRightThm, {mkComb[uV, nV], mkComb[uV, n0V], eV}],
      close];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[eV, HOL`Bool`GEN[n0V, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[hTailTm, HOL`Bool`DISCH[hLeTm, body]]]]]]
  ];

tailLowerMemThm =
  Module[{uV, eV, n0V, nV, hTailTm, hTail, hLeTm, hLe, lower, ltN, leN,
          allN, exN, folded},
    uV = mkVar["u", seqTy]; eV = mkVar["e", realTy]; n0V = mkVar["N", numTy];
    nV = mkVar["nELB", numTy];
    hTailTm = seqCauchyTailAll[uV, eV, n0V]; hTail = ASSUME[hTailTm];
    lower = realAddTm[mkComb[uV, n0V], realNegTm[eV]];
    hLeTm = seqNatLe[n0V, nV]; hLe = ASSUME[hLeTm];
    ltN = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[cauchyTailLowerThm, {uV, eV, n0V, nV}], hTail], hLe];
    leN = seqLtImpLeRule[ltN];
    allN = HOL`Bool`GEN[nV, HOL`Bool`DISCH[hLeTm, leN]];
    exN = HOL`Bool`EXISTS[seqElbBody[uV, lower], n0V, allN];
    folded = EQMP[HOL`Equal`SYM[unfoldElb[uV, lower]], exN];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[eV, HOL`Bool`GEN[n0V,
      HOL`Bool`DISCH[hTailTm, folded]]]]
  ];

tailUpperBoundThm =
  Module[{uV, eV, n0V, xV, mW, hTailTm, hTail, hElbTm, hElb, exM, hAllM,
          kT, leN, leM, xLeK, kLtUpper, kLeUpper, xLeUpper, xImp, allX},
    uV = mkVar["u", seqTy]; eV = mkVar["e", realTy]; n0V = mkVar["N", numTy];
    xV = mkVar["xUB", realTy]; mW = mkVar["MW", numTy];
    hTailTm = seqCauchyTailAll[uV, eV, n0V]; hTail = ASSUME[hTailTm];
    hElbTm = elbTm[uV, xV]; hElb = ASSUME[hElbTm];
    exM = EQMP[unfoldElb[uV, xV], hElb];
    hAllM = ASSUME[seqElbAll[uV, xV, mW]];
    kT = seqNatAdd[n0V, mW];
    leN = seqLeqToSumLeft[n0V, mW];
    leM = seqLeqToSumRight[n0V, mW];
    xLeK = HOL`Bool`MP[HOL`Bool`SPEC[kT, hAllM], leM];
    kLtUpper = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[cauchyTailUpperThm, {uV, eV, n0V, kT}], hTail], leN];
    kLeUpper = seqLtImpLeRule[kLtUpper];
    xLeUpper = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeTransThm, {xV, mkComb[uV, kT],
        realAddTm[mkComb[uV, n0V], eV]}], xLeK], kLeUpper];
    xImp = HOL`Bool`DISCH[hElbTm, HOL`Bool`CHOOSE[mW, exM, xLeUpper]];
    allX = HOL`Bool`GEN[xV, xImp];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[eV, HOL`Bool`GEN[n0V,
      HOL`Bool`DISCH[hTailTm, allX]]]]
  ];

elbNonemptyThm =
  Module[{uV, nW, nV, xW, hC, cauchyUnfolded, exN, hTail, hLeTm, hLe,
          lower, ltN, leN, allN, elbProof, exX, chosen},
    uV = mkVar["u", seqTy]; nW = mkVar["NW", numTy]; nV = mkVar["nNE", numTy];
    xW = mkVar["xW", realTy];
    hC = ASSUME[seqCauchyTm[uV]];
    cauchyUnfolded = EQMP[unfoldSeqCauchy[uV], hC];
    exN = HOL`Bool`MP[HOL`Bool`SPEC[seqOneReal[], cauchyUnfolded],
      HOL`Auto`RealArith`rnumPos[1]];
    hTail = ASSUME[seqCauchyTailAll[uV, seqOneReal[], nW]];
    lower = realAddTm[mkComb[uV, nW], realNegTm[seqOneReal[]]];
    hLeTm = seqNatLe[nW, nV]; hLe = ASSUME[hLeTm];
    ltN = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[cauchyTailLowerThm, {uV, seqOneReal[], nW, nV}], hTail], hLe];
    leN = seqLtImpLeRule[ltN];
    allN = HOL`Bool`GEN[nV, HOL`Bool`DISCH[hLeTm, leN]];
    elbProof = EQMP[HOL`Equal`SYM[unfoldElb[uV, lower]],
      HOL`Bool`EXISTS[seqElbBody[uV, lower], nW, allN]];
    exX = HOL`Bool`EXISTS[existsTm[xW, elbTm[uV, xW]], lower, elbProof];
    chosen = HOL`Bool`CHOOSE[nW, exN, exX];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[seqCauchyTm[uV], chosen]]
  ];

elbBddAboveThm =
  Module[{uV, nW, xV, mW, wW, hC, cauchyUnfolded, exN, hTail, upper, hElbTm,
          hElb, exM, hAllM, kT, leN, leM, xLeK, kLtUpper, kLeUpper, xLeUpper,
          xImp, allX, exW, chosen},
    uV = mkVar["u", seqTy]; nW = mkVar["NW", numTy];
    xV = mkVar["xBA", realTy]; mW = mkVar["MW", numTy]; wW = mkVar["wW", realTy];
    hC = ASSUME[seqCauchyTm[uV]];
    cauchyUnfolded = EQMP[unfoldSeqCauchy[uV], hC];
    exN = HOL`Bool`MP[HOL`Bool`SPEC[seqOneReal[], cauchyUnfolded],
      HOL`Auto`RealArith`rnumPos[1]];
    hTail = ASSUME[seqCauchyTailAll[uV, seqOneReal[], nW]];
    upper = realAddTm[mkComb[uV, nW], seqOneReal[]];
    hElbTm = elbTm[uV, xV]; hElb = ASSUME[hElbTm];
    exM = EQMP[unfoldElb[uV, xV], hElb];
    hAllM = ASSUME[seqElbAll[uV, xV, mW]];
    kT = seqNatAdd[nW, mW];
    leN = seqLeqToSumLeft[nW, mW];
    leM = seqLeqToSumRight[nW, mW];
    xLeK = HOL`Bool`MP[HOL`Bool`SPEC[kT, hAllM], leM];
    kLtUpper = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[cauchyTailUpperThm, {uV, seqOneReal[], nW, kT}], hTail], leN];
    kLeUpper = seqLtImpLeRule[kLtUpper];
    xLeUpper = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realLeTransThm, {xV, mkComb[uV, kT], upper}], xLeK], kLeUpper];
    xImp = HOL`Bool`DISCH[hElbTm, HOL`Bool`CHOOSE[mW, exM, xLeUpper]];
    allX = HOL`Bool`GEN[xV, xImp];
    exW = HOL`Bool`EXISTS[existsTm[wW,
      forallTm[xV, impTm[elbTm[uV, xV], realLeTm[xV, wW]]]], upper, allX];
    chosen = HOL`Bool`CHOOSE[nW, exN, exW];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[seqCauchyTm[uV], chosen]]
  ];

cauchyConvergesThm =
  Module[{uV, eV, nV, nW, lW, hC, sSet, sT, nonempty, bounded, hE, dT,
          dPos, cauchyUnfolded, exN, hTail, hLeTm, hLe, lower, upper,
          lowerMem, supUpperAll, lowerLeS, upperBound, supLeUpper, reflN,
          closeCenter, centerLtNAdd, nLtUpper, hLeft, hRight, absClose, impN,
          allN, exNTend, chosenN, epsBody, tendBody, foldedTend, exL},
    uV = mkVar["u", seqTy]; eV = mkVar["e", realTy]; nV = mkVar["n", numTy];
    nW = mkVar["NW", numTy]; lW = mkVar["L", realTy];
    hC = ASSUME[seqCauchyTm[uV]];
    sSet = mkComb[elbConst[], uV];
    sT = seqRealSup[sSet];
    nonempty = HOL`Bool`MP[HOL`Bool`SPEC[uV, elbNonemptyThm], hC];
    bounded = HOL`Bool`MP[HOL`Bool`SPEC[uV, elbBddAboveThm], hC];
    hE = ASSUME[realLtTm[zeroRealTm[], eV]];
    dT = seqHalf[eV];
    dPos = HOL`Bool`MP[HOL`Bool`SPEC[eV, seqArithHalfPosThm], hE];
    cauchyUnfolded = EQMP[unfoldSeqCauchy[uV], hC];
    exN = HOL`Bool`MP[HOL`Bool`SPEC[dT, cauchyUnfolded], dPos];
    hTail = ASSUME[seqCauchyTailAll[uV, dT, nW]];
    hLeTm = seqNatLe[nW, nV]; hLe = ASSUME[hLeTm];
    lower = realAddTm[mkComb[uV, nW], realNegTm[dT]];
    upper = realAddTm[mkComb[uV, nW], dT];
    lowerMem = HOL`Bool`MP[seqSpecAll[tailLowerMemThm, {uV, dT, nW}], hTail];
    supUpperAll = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[sSet, realSupUpperThm],
      nonempty], bounded];
    lowerLeS = HOL`Bool`MP[HOL`Bool`SPEC[lower, supUpperAll], lowerMem];
    upperBound = HOL`Bool`MP[seqSpecAll[tailUpperBoundThm, {uV, dT, nW}], hTail];
    supLeUpper = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realSupLeastThm, {sSet, upper}], nonempty], bounded], upperBound];
    reflN = HOL`Bool`SPEC[nW, HOL`Stdlib`Num`leqReflThm];
    closeCenter = HOL`Bool`MP[HOL`Bool`MP[seqSpecAll[hTail, {nW, nV}],
      reflN], hLe];
    centerLtNAdd = HOL`Bool`MP[
      seqSpecAll[realAbsSubLtRightThm, {mkComb[uV, nW], mkComb[uV, nV], dT}],
      closeCenter];
    nLtUpper = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[cauchyTailUpperThm, {uV, dT, nW, nV}], hTail], hLe];
    hLeft = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithCauchyLeftBoundThm, {sT, mkComb[uV, nW], mkComb[uV, nV], eV}],
      supLeUpper], centerLtNAdd];
    hRight = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[seqArithCauchyRightBoundThm, {sT, mkComb[uV, nW], mkComb[uV, nV], eV}],
      nLtUpper], lowerLeS];
    absClose = HOL`Bool`MP[HOL`Bool`MP[
      seqSpecAll[realAbsSubLtThm, {mkComb[uV, nV], sT, eV}], hLeft], hRight];
    impN = HOL`Bool`DISCH[hLeTm, absClose];
    allN = HOL`Bool`GEN[nV, impN];
    exNTend = HOL`Bool`EXISTS[existsTm[mkVar["N", numTy],
      seqLimitAll[uV, sT, eV, mkVar["N", numTy]]], nW, allN];
    chosenN = HOL`Bool`CHOOSE[nW, exN, exNTend];
    epsBody = HOL`Bool`DISCH[realLtTm[zeroRealTm[], eV], chosenN];
    tendBody = HOL`Bool`GEN[eV, epsBody];
    foldedTend = EQMP[HOL`Equal`SYM[unfoldTendsto[uV, sT]], tendBody];
    exL = HOL`Bool`EXISTS[existsTm[lW, tendstoTm[uV, lW]], sT, foldedTend];
    HOL`Bool`GEN[uV, HOL`Bool`DISCH[seqCauchyTm[uV], exL]]
  ];

End[];
EndPackage[];
