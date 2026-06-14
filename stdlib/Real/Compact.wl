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

Begin["`Private`"];

compactSeqTy = tyFun[numTy, realTy];
compactNumFunTy = tyFun[numTy, numTy];
seqBoundedTy = tyFun[compactSeqTy, boolTy];
hasConvergentSubseqTy = tyFun[compactSeqTy, tyFun[realTy, boolTy]];

compactRealLeCong[eqLeft_, eqRight_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqLeft], eqRight];

compactOrTm[pT_, qT_] :=
  mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], pT], qT];

compactSpecAll[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

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

End[];

EndPackage[];
