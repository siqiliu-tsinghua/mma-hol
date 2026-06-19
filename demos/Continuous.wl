(* demos/Continuous.wl - DEMO (not stdlib): continuous functions on closed
   intervals, built on the graduated point-set topology.  Global topological
   definition: continuous f = forall U. isOpen U ==> isOpen (PREIMAGE f U).
   Capstones: continuous image of a compact set is compact, of a connected set
   is connected; hence on [a,b] (compact and connected) a continuous f is
   bounded, attains its bounds (EVT), and hits every intermediate value (IVT). *)

BeginPackage["HOL`Demos`Continuous`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`", "HOL`Auto`Arith`", "HOL`Auto`RealArith`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Set`", "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`",
  "HOL`Stdlib`Real`"
}];

continuousDefThm::usage = "continuousDefThm - |- continuous = (lambda f. forall U. isOpen U ==> isOpen (PREIMAGE f U)).";
continuousConst::usage = "continuousConst[] - continuous : (real -> real) -> bool.";
continuousTm::usage = "continuousTm[f] - builds continuous f.";
unfoldContinuous::usage = "unfoldContinuous[f] - proves the beta-reduced continuous definition at f.";
continuousImageCompactThm::usage = "continuousImageCompactThm - |- forall f S. continuous f ==> isCompact S ==> isCompact (IMAGE f S).";
continuousImageConnectedThm::usage = "continuousImageConnectedThm - |- forall f S. continuous f ==> isConnected S ==> isConnected (IMAGE f S).";
closedIntervalCompactThm::usage = "closedIntervalCompactThm - |- forall a b. isCompact (closedInterval a b).";
continuousImageBoundedThm::usage = "continuousImageBoundedThm - |- forall f a b. continuous f ==> setBounded (IMAGE f (closedInterval a b)).";
continuousIVTThm::usage = "continuousIVTThm - |- forall f a b y. continuous f ==> realLe a b ==> realLe (f a) y ==> realLe y (f b) ==> exists c. closedInterval a b c /\\ f c = y.";

Begin["`Private`"];

ctRealTy = mkType["real", {}];
ctFunTy = tyFun[ctRealTy, ctRealTy];
ctSetTy = tyFun[ctRealTy, boolTy];
continuousTy = tyFun[ctFunTy, boolTy];

ctImpConst[] := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
ctImpTm[pT_, qT_] := mkComb[mkComb[ctImpConst[], pT], qT];
ctForallTm[vT_, bodyT_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];

(* IMAGE / PREIMAGE instantiated at alpha = beta = real (Set.wl's builders use
   the polymorphic const, which mkComb won't match against a concrete f). *)
ctPreimageConst[] := mkConst["PREIMAGE", tyFun[ctFunTy, tyFun[ctSetTy, ctSetTy]]];
ctPreimageTm[fT_, uT_] := mkComb[mkComb[ctPreimageConst[], fT], uT];
ctImageConst[] := mkConst["IMAGE", tyFun[ctFunTy, tyFun[ctSetTy, ctSetTy]]];
ctImageTm[fT_, sT_] := mkComb[mkComb[ctImageConst[], fT], sT];

ctContinuousBody[fT_] :=
  Module[{uV},
    uV = mkVar["U", ctSetTy];
    ctForallTm[uV, ctImpTm[isOpenTm[uV], isOpenTm[ctPreimageTm[fT, uV]]]]
  ];

continuousDefThm =
  Module[{fV},
    fV = mkVar["f", ctFunTy];
    newDefinition[mkEq[mkVar["continuous", continuousTy],
      mkAbs[fV, ctContinuousBody[fV]]]]
  ];

continuousConst[] := mkConst["continuous", continuousTy];
continuousTm[fT_] := mkComb[continuousConst[], fT];
unfoldContinuous[fT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[continuousDefThm, fT];
    TRANS[s1, HOL`Equal`BETACONV[concl[s1][[2]]]]
  ];

(* ---- common builders ---- *)
ctAndConst[] := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
ctOrConst[] := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
ctNotConst[] := mkConst["¬", tyFun[boolTy, boolTy]];
ctConjTm[pT_, qT_] := mkComb[mkComb[ctAndConst[], pT], qT];
ctOrTm[pT_, qT_] := mkComb[mkComb[ctOrConst[], pT], qT];
ctNotTm[pT_] := mkComb[ctNotConst[], pT];
ctExistsTm[vT_, bodyT_] :=
  mkComb[mkConst["∃", tyFun[tyFun[typeOf[vT], boolTy], boolTy]], mkAbs[vT, bodyT]];
ctSelectConst[ty_] := mkConst["@", tyFun[tyFun[ty, boolTy], ty]];
ctApp[sT_, xT_] := mkComb[sT, xT];
ctSpecAll[th_, ts_List] :=
  Fold[Function[{accTh, tt}, HOL`Bool`SPEC[tt, accTh]], th, ts];
ctApplyDef[defTh_, args_List] :=
  Fold[Function[{accTh, argT}, Module[{stepTh},
    stepTh = HOL`Equal`APTHM[accTh, argT];
    TRANS[stepTh, HOL`Equal`BETACONV[concl[stepTh][[2]]]]
  ]], defTh, args];

(* IMAGE / PREIMAGE def instances at alpha = beta = real *)
ctRealInst[th_] :=
  HOL`Kernel`INSTTYPE[{mkVarType["A"] -> ctRealTy, mkVarType["B"] -> ctRealTy}, th];
ctPreimageDef[] := ctRealInst[HOL`Stdlib`Set`preimageDefThm];
ctImageDef[] := ctRealInst[HOL`Stdlib`Set`imageDefThm];
ctPreimageAt[fT_, uT_, xT_] := ctApplyDef[ctPreimageDef[], {fT, uT, xT}];
ctImageAt[fT_, sT_, yT_] := ctApplyDef[ctImageDef[], {fT, sT, yT}];

(* MAP / MEM / list consts at element type set (real->bool) *)
ctSetListTy = HOL`Stdlib`List`listTy[ctSetTy];
ctMapConstAt[] :=
  mkConst["MAP", tyFun[tyFun[ctSetTy, ctSetTy], tyFun[ctSetListTy, ctSetListTy]]];
ctMapTm[gT_, lT_] := mkComb[mkComb[ctMapConstAt[], gT], lT];
ctMemConstAt[] :=
  mkConst["MEM", tyFun[ctSetTy, tyFun[ctSetListTy, boolTy]]];
ctMemTm[xT_, lT_] := mkComb[mkComb[ctMemConstAt[], xT], lT];
ctNilAt[] := mkConst["NIL", ctSetListTy];
ctConsConstAt[] := mkConst["CONS", tyFun[ctSetTy, tyFun[ctSetListTy, ctSetListTy]]];
ctConsTm[hT_, tT_] := mkComb[mkComb[ctConsConstAt[], hT], tT];
ctListInduct[predLam_] :=
  HOL`Bool`ISPEC[predLam, HOL`Stdlib`List`listInductionThm];
ctMapCons[gT_, hT_, tT_] :=
  ctSpecAll[HOL`Bool`ISPEC[gT, HOL`Stdlib`List`mapConsThm], {hT, tT}];
ctMemCons[xT_, yT_, tT_] :=
  ctSpecAll[HOL`Bool`ISPEC[xT, HOL`Stdlib`List`memConsThm], {yT, tT}];

(* memMap forward: MEM x l ==> MEM (g x) (MAP g l) *)
memMapThm =
  Module[{gV, xV, lV, wV, mV, predLam, induction, base, step, allL},
    gV = mkVar["g", tyFun[ctSetTy, ctSetTy]]; xV = mkVar["xMM", ctSetTy];
    lV = mkVar["lMM", ctSetListTy]; wV = mkVar["wMM", ctSetTy];
    mV = mkVar["mMM", ctSetListTy];
    predLam = mkAbs[lV, ctImpTm[ctMemTm[xV, lV],
      ctMemTm[mkComb[gV, xV], ctMapTm[gV, lV]]]];
    induction = ctListInduct[predLam];
    base = EQMP[HOL`Equal`SYM[HOL`Equal`BETACONV[mkComb[predLam, ctNilAt[]]]],
      HOL`Bool`DISCH[ctMemTm[xV, ctNilAt[]],
        HOL`Bool`CONTR[ctMemTm[mkComb[gV, xV], ctMapTm[gV, ctNilAt[]]],
          EQMP[HOL`Bool`ISPEC[xV, HOL`Stdlib`List`memNilThm],
            ASSUME[ctMemTm[xV, ctNilAt[]]]]]]];
    step = Module[{ihTm, ih, hMemTm, hMem, memConsL, mapCons, memConsR,
                   gCong, branch, redexC},
      ihTm = mkComb[predLam, mV];
      ih = EQMP[HOL`Equal`BETACONV[ihTm], ASSUME[ihTm]];
      hMemTm = ctMemTm[xV, ctConsTm[wV, mV]]; hMem = ASSUME[hMemTm];
      memConsL = ctMemCons[xV, wV, mV];
      mapCons = ctMapCons[gV, wV, mV];
      memConsR = TRANS[
        HOL`Equal`APTERM[mkComb[ctMemConstAt[], mkComb[gV, xV]], mapCons],
        ctMemCons[mkComb[gV, xV], mkComb[gV, wV], ctMapTm[gV, mV]]];
      gCong = HOL`Equal`APTERM[gV, ASSUME[mkEq[xV, wV]]];
      branch = EQMP[HOL`Equal`SYM[memConsR],
        HOL`Bool`DISJCASES[EQMP[memConsL, hMem],
          HOL`Bool`DISJ1[gCong, ctMemTm[mkComb[gV, xV], ctMapTm[gV, mV]]],
          HOL`Bool`DISJ2[HOL`Bool`MP[ih, ASSUME[ctMemTm[xV, mV]]],
            mkEq[mkComb[gV, xV], mkComb[gV, wV]]]]];
      redexC = HOL`Equal`BETACONV[mkComb[predLam, ctConsTm[wV, mV]]];
      HOL`Bool`GEN[wV, HOL`Bool`GEN[mV, HOL`Bool`DISCH[ihTm,
        EQMP[HOL`Equal`SYM[redexC], HOL`Bool`DISCH[hMemTm, branch]]]]]
    ];
    allL = HOL`Bool`MP[induction, HOL`Bool`CONJ[base, step]];
    HOL`Bool`GEN[gV, HOL`Bool`GEN[xV, HOL`Bool`GEN[lV,
      EQMP[HOL`Equal`BETACONV[mkComb[predLam, lV]], HOL`Bool`SPEC[lV, allL]]]]]
  ];

(* memMap backward: MEM v (MAP g l) ==> exists x. MEM x l /\ v = g x *)
memMapExThm =
  Module[{gV, vV, lV, yV, tV, xExV, exBody, predLam, induction, base, step, allL},
    gV = mkVar["g", tyFun[ctSetTy, ctSetTy]]; vV = mkVar["vME", ctSetTy];
    lV = mkVar["lME", ctSetListTy]; yV = mkVar["yME", ctSetTy];
    tV = mkVar["tME", ctSetListTy]; xExV = mkVar["xME", ctSetTy];
    exBody[lT_] := ctExistsTm[xExV, ctConjTm[ctMemTm[xExV, lT],
      mkEq[vV, mkComb[gV, xExV]]]];
    predLam = mkAbs[lV, ctImpTm[ctMemTm[vV, ctMapTm[gV, lV]], exBody[lV]]];
    induction = ctListInduct[predLam];
    base = Module[{mapNilG, memEqF, falseTh},
      mapNilG = HOL`Bool`ISPEC[gV, HOL`Stdlib`List`mapNilThm];
      memEqF = TRANS[HOL`Equal`APTERM[mkComb[ctMemConstAt[], vV], mapNilG],
        HOL`Bool`ISPEC[vV, HOL`Stdlib`List`memNilThm]];
      falseTh = EQMP[memEqF, ASSUME[ctMemTm[vV, ctMapTm[gV, ctNilAt[]]]]];
      EQMP[HOL`Equal`SYM[HOL`Equal`BETACONV[mkComb[predLam, ctNilAt[]]]],
        HOL`Bool`DISCH[ctMemTm[vV, ctMapTm[gV, ctNilAt[]]],
          HOL`Bool`CONTR[exBody[ctNilAt[]], falseTh]]]];
    step = Module[{ihTm, ih, mapCons, memVMapCons, hAsmTm, hAsm, disj,
                   hVeq, memYCons, case1, hMemT, exT, wV, hWbodyTm, hWbody,
                   memWCons, case2inner, case2, branch, redexC},
      ihTm = mkComb[predLam, tV];
      ih = EQMP[HOL`Equal`BETACONV[ihTm], ASSUME[ihTm]];
      mapCons = ctMapCons[gV, yV, tV];
      memVMapCons = TRANS[
        HOL`Equal`APTERM[mkComb[ctMemConstAt[], vV], mapCons],
        ctMemCons[vV, mkComb[gV, yV], ctMapTm[gV, tV]]];
      hAsmTm = ctMemTm[vV, ctMapTm[gV, ctConsTm[yV, tV]]]; hAsm = ASSUME[hAsmTm];
      disj = EQMP[memVMapCons, hAsm];
      hVeq = ASSUME[mkEq[vV, mkComb[gV, yV]]];
      memYCons = EQMP[HOL`Equal`SYM[ctMemCons[yV, yV, tV]],
        HOL`Bool`DISJ1[REFL[yV], ctMemTm[yV, tV]]];
      case1 = HOL`Bool`EXISTS[exBody[ctConsTm[yV, tV]], yV,
        HOL`Bool`CONJ[memYCons, hVeq]];
      hMemT = ASSUME[ctMemTm[vV, ctMapTm[gV, tV]]];
      exT = HOL`Bool`MP[ih, hMemT];
      wV = mkVar["wME", ctSetTy];
      hWbodyTm = ctConjTm[ctMemTm[wV, tV], mkEq[vV, mkComb[gV, wV]]];
      hWbody = ASSUME[hWbodyTm];
      memWCons = EQMP[HOL`Equal`SYM[ctMemCons[wV, yV, tV]],
        HOL`Bool`DISJ2[HOL`Bool`CONJUNCT1[hWbody], mkEq[wV, yV]]];
      case2inner = HOL`Bool`EXISTS[exBody[ctConsTm[yV, tV]], wV,
        HOL`Bool`CONJ[memWCons, HOL`Bool`CONJUNCT2[hWbody]]];
      case2 = HOL`Bool`CHOOSE[wV, exT, case2inner];
      branch = HOL`Bool`DISJCASES[disj, case1, case2];
      redexC = HOL`Equal`BETACONV[mkComb[predLam, ctConsTm[yV, tV]]];
      HOL`Bool`GEN[yV, HOL`Bool`GEN[tV, HOL`Bool`DISCH[ihTm,
        EQMP[HOL`Equal`SYM[redexC], HOL`Bool`DISCH[hAsmTm, branch]]]]]
    ];
    allL = HOL`Bool`MP[induction, HOL`Bool`CONJ[base, step]];
    HOL`Bool`GEN[gV, HOL`Bool`GEN[vV, HOL`Bool`GEN[lV,
      EQMP[HOL`Equal`BETACONV[mkComb[predLam, lV]], HOL`Bool`SPEC[lV, allL]]]]]
  ];

ctSetOfSetsTy = tyFun[ctSetTy, boolTy];
ctBetaClean[th_] :=
  HOL`Drule`CONVRULE[HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[HOL`Equal`BETACONV]], th];

(* T1: continuous image of a compact set is compact. *)
continuousImageCompactThm =
  Module[{fV, sV, cV, vExV, vCpV, wV, xV, imgS, hContTm, hCont, hCompactTm,
          hCompact, contU, hCopenTm, hCopen, hCcovTm, hCcov, ccovU,
          cpBody, cpTm, cpAt, recPred, recTm, recAt, hCpOpen, hCpCov,
          finRaw, fin, wsV, hLsTm, hLs, lsU, hWsMem, hWsCov, vsTm, partI,
          partII, lsFolded, finFolded, finChosen, isCompactBody, result},
    fV = mkVar["f", ctFunTy]; sV = mkVar["S", ctSetTy];
    cV = mkVar["C", ctSetOfSetsTy]; vExV = mkVar["V", ctSetTy];
    vCpV = mkVar["Vcp", ctSetTy];
    wV = mkVar["W", ctSetTy]; xV = mkVar["x", ctRealTy];
    imgS = ctImageTm[fV, sV];
    hContTm = continuousTm[fV]; hCont = ASSUME[hContTm];
    hCompactTm = isCompactTm[sV]; hCompact = ASSUME[hCompactTm];
    contU = EQMP[unfoldContinuous[fV], hCont];
    hCopenTm = ctForallTm[vExV, ctImpTm[ctApp[cV, vExV], isOpenTm[vExV]]];
    hCopen = ASSUME[hCopenTm];
    hCcovTm = setCoversTm[cV, imgS]; hCcov = ASSUME[hCcovTm];
    ccovU = EQMP[unfoldSetCovers[cV, imgS], hCcov];

    cpBody[wT_] := ctExistsTm[vCpV,
      ctConjTm[ctApp[cV, vCpV], mkEq[wT, ctPreimageTm[fV, vCpV]]]];
    cpTm = mkAbs[wV, cpBody[wV]];
    cpAt[wT_] := HOL`Equal`BETACONV[mkComb[cpTm, wT]];
    recPred[wT_] := mkAbs[vCpV,
      ctConjTm[ctApp[cV, vCpV], mkEq[wT, ctPreimageTm[fV, vCpV]]]];
    recTm = mkAbs[wV, mkComb[ctSelectConst[ctSetTy], recPred[wV]]];
    recAt[wT_] := HOL`Equal`BETACONV[mkComb[recTm, wT]];

    hCpOpen = Module[{hCpwTm, hCpw, exV, hbodyTm, hbody, hcv, weq, openV,
                      openPre, openW},
      hCpwTm = mkComb[cpTm, wV]; hCpw = ASSUME[hCpwTm];
      exV = EQMP[cpAt[wV], hCpw];
      hbodyTm = ctConjTm[ctApp[cV, vExV], mkEq[wV, ctPreimageTm[fV, vExV]]];
      hbody = ASSUME[hbodyTm];
      hcv = HOL`Bool`CONJUNCT1[hbody]; weq = HOL`Bool`CONJUNCT2[hbody];
      openV = HOL`Bool`MP[HOL`Bool`SPEC[vExV, hCopen], hcv];
      openPre = HOL`Bool`MP[HOL`Bool`SPEC[vExV, contU], openV];
      openW = EQMP[HOL`Equal`APTERM[isOpenConst[], HOL`Equal`SYM[weq]], openPre];
      HOL`Bool`GEN[wV, HOL`Bool`DISCH[hCpwTm,
        HOL`Bool`CHOOSE[vExV, exV, openW]]]
    ];

    hCpCov = Module[{hSxTm, hSx, fx, imgAt, fxInImg, ccAtfx, hbody2Tm,
                     hbody2, hcv2, vfx, preTerm, cpW, wAtx, exW, allX},
      hSxTm = ctApp[sV, xV]; hSx = ASSUME[hSxTm];
      fx = mkComb[fV, xV];
      imgAt = ctImageAt[fV, sV, fx];
      fxInImg = EQMP[HOL`Equal`SYM[imgAt],
        HOL`Bool`EXISTS[concl[imgAt][[2]], xV, HOL`Bool`CONJ[hSx, REFL[fx]]]];
      ccAtfx = HOL`Bool`MP[HOL`Bool`SPEC[fx, ccovU], fxInImg];
      hbody2Tm = ctConjTm[ctApp[cV, vExV], ctApp[vExV, fx]];
      hbody2 = ASSUME[hbody2Tm];
      hcv2 = HOL`Bool`CONJUNCT1[hbody2]; vfx = HOL`Bool`CONJUNCT2[hbody2];
      preTerm = ctPreimageTm[fV, vExV];
      cpW = EQMP[HOL`Equal`SYM[cpAt[preTerm]],
        HOL`Bool`EXISTS[cpBody[preTerm], vExV, HOL`Bool`CONJ[hcv2, REFL[preTerm]]]];
      wAtx = EQMP[HOL`Equal`SYM[ctPreimageAt[fV, vExV, xV]], vfx];
      exW = HOL`Bool`EXISTS[
        ctExistsTm[wV, ctConjTm[mkComb[cpTm, wV], ctApp[wV, xV]]],
        preTerm, HOL`Bool`CONJ[cpW, wAtx]];
      allX = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hSxTm,
        HOL`Bool`CHOOSE[vExV, ccAtfx, exW]]];
      EQMP[HOL`Equal`SYM[unfoldSetCovers[cpTm, sV]], allX]
    ];

    finRaw = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[cpTm,
      EQMP[unfoldIsCompact[sV], hCompact]], hCpOpen], hCpCov];
    fin = EQMP[unfoldSetFiniteSubcover[cpTm, sV], finRaw];

    wsV = mkVar["Ws", ctSetListTy];
    hLsTm = setListSubcoverTm[cpTm, sV, wsV]; hLs = ASSUME[hLsTm];
    lsU = EQMP[unfoldSetListSubcover[cpTm, sV, wsV], hLs];
    hWsMem = HOL`Bool`CONJUNCT1[lsU]; hWsCov = HOL`Bool`CONJUNCT2[lsU];
    vsTm = ctMapTm[recTm, wsV];

    partI = Module[{hMemTm, hMem, exW, hWcsTm, hWcs, memW, vEqRec, cpW,
                    selSpec, cRec},
      hMemTm = ctMemTm[vExV, vsTm]; hMem = ASSUME[hMemTm];
      exW = HOL`Bool`MP[ctSpecAll[memMapExThm, {recTm, vExV, wsV}], hMem];
      hWcsTm = ctConjTm[ctMemTm[wV, wsV], mkEq[vExV, mkComb[recTm, wV]]];
      hWcs = ASSUME[hWcsTm];
      memW = HOL`Bool`CONJUNCT1[hWcs]; vEqRec = HOL`Bool`CONJUNCT2[hWcs];
      cpW = HOL`Bool`MP[HOL`Bool`SPEC[wV, hWsMem], memW];
      selSpec = ctBetaClean[HOL`Stdlib`Num`selectOfExists[recPred[wV],
        EQMP[cpAt[wV], cpW]]];
      cRec = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[cV, recAt[wV]]],
        HOL`Bool`CONJUNCT1[selSpec]];
      HOL`Bool`GEN[vExV, HOL`Bool`DISCH[hMemTm,
        HOL`Bool`CHOOSE[wV, exW,
          EQMP[HOL`Equal`APTERM[cV, HOL`Equal`SYM[vEqRec]], cRec]]]]
    ];

    partII = Module[{yV, zV, hImgTm, hImg, imgAt, hzTm, hz, szz, yEqfz,
                     wcovEx, hWbTm, hWb, memW, wAtz, cpW, selSpec, wEqPre,
                     weqRec, wzPre, recAtz, recAty, vRecY, memRec, exV2,
                     innerZ, innerW},
      yV = mkVar["y", ctRealTy]; zV = mkVar["zII", ctRealTy];
      hImgTm = ctApp[imgS, yV]; hImg = ASSUME[hImgTm];
      imgAt = ctImageAt[fV, sV, yV];
      hzTm = ctConjTm[ctApp[sV, zV], mkEq[yV, mkComb[fV, zV]]];
      hz = ASSUME[hzTm];
      szz = HOL`Bool`CONJUNCT1[hz]; yEqfz = HOL`Bool`CONJUNCT2[hz];
      wcovEx = HOL`Bool`MP[HOL`Bool`SPEC[zV, hWsCov], szz];
      hWbTm = ctConjTm[ctMemTm[wV, wsV], ctApp[wV, zV]]; hWb = ASSUME[hWbTm];
      memW = HOL`Bool`CONJUNCT1[hWb]; wAtz = HOL`Bool`CONJUNCT2[hWb];
      cpW = HOL`Bool`MP[HOL`Bool`SPEC[wV, hWsMem], memW];
      selSpec = ctBetaClean[HOL`Stdlib`Num`selectOfExists[recPred[wV],
        EQMP[cpAt[wV], cpW]]];
      wEqPre = HOL`Bool`CONJUNCT2[selSpec];   (* W = PREIMAGE f (@V) *)
      weqRec = TRANS[wEqPre,
        HOL`Equal`APTERM[mkComb[ctPreimageConst[], fV], HOL`Equal`SYM[recAt[wV]]]];
        (* W = PREIMAGE f (recover W) *)
      wzPre = EQMP[HOL`Equal`APTHM[weqRec, zV], wAtz];   (* (PREIMAGE f (recover W)) z *)
      recAtz = EQMP[ctPreimageAt[fV, mkComb[recTm, wV], zV], wzPre];
        (* (recover W) (f z) *)
      vRecY = EQMP[HOL`Equal`APTERM[mkComb[recTm, wV], HOL`Equal`SYM[yEqfz]], recAtz];
        (* (recover W) y *)
      memRec = HOL`Bool`MP[ctSpecAll[memMapThm, {recTm, wV, wsV}], memW];
        (* MEM (recover W) (MAP recover Ws) *)
      exV2 = HOL`Bool`EXISTS[
        ctExistsTm[vExV, ctConjTm[ctMemTm[vExV, vsTm], ctApp[vExV, yV]]],
        mkComb[recTm, wV], HOL`Bool`CONJ[memRec, vRecY]];
      innerW = HOL`Bool`CHOOSE[wV, wcovEx, exV2];
      innerZ = HOL`Bool`CHOOSE[zV, EQMP[imgAt, hImg], innerW];
      HOL`Bool`GEN[yV, HOL`Bool`DISCH[hImgTm, innerZ]]
    ];

    lsFolded = EQMP[HOL`Equal`SYM[unfoldSetListSubcover[cV, imgS, vsTm]],
      HOL`Bool`CONJ[partI, partII]];
    finFolded = EQMP[HOL`Equal`SYM[unfoldSetFiniteSubcover[cV, imgS]],
      HOL`Bool`EXISTS[concl[unfoldSetFiniteSubcover[cV, imgS]][[2]], vsTm, lsFolded]];
    finChosen = HOL`Bool`CHOOSE[wsV, fin, finFolded];
    isCompactBody = HOL`Bool`GEN[cV, HOL`Bool`DISCH[hCopenTm,
      HOL`Bool`DISCH[hCcovTm, finChosen]]];
    result = EQMP[HOL`Equal`SYM[unfoldIsCompact[imgS]], isCompactBody];
    HOL`Bool`GEN[fV, HOL`Bool`GEN[sV,
      HOL`Bool`DISCH[hContTm, HOL`Bool`DISCH[hCompactTm, result]]]]
  ];

ctTraceAt[sT_, vT_, xT_] :=
  Module[{u},
    u = unfoldTrace[sT, vT];
    TRANS[HOL`Equal`APTHM[u, xT], HOL`Equal`BETACONV[mkComb[concl[u][[2]], xT]]]
  ];
(* eq of two bools from the two implications, via a propositional tautology *)
ctEqFromImps[pqTh_, qpTh_] :=
  Module[{pT, qT},
    pT = concl[pqTh][[1, 2]]; qT = concl[pqTh][[2]];
    HOL`Bool`MP[HOL`Bool`MP[HOL`Auto`PropTaut`propTaut[
      ctImpTm[ctImpTm[pT, qT], ctImpTm[ctImpTm[qT, pT], mkEq[pT, qT]]]],
      pqTh], qpTh]
  ];

(* T2: continuous image of a connected set is connected. *)
continuousImageConnectedThm =
  Module[{fV, sV, aV, bV, imgS, hContTm, hCont, contU, hConnTm, hConn, connU,
          hSepTm, hSep, sepU, hOpA, r1, hOpB, r2, hNeA, r3, hNeB, r4, hCov,
          hDisj, waV, wbV, openExA, openExB, memEqABodyA, memEqABodyB,
          hWAbodyTm, hWBbodyTm, preA, preB, aPrime, bPrime, mkBodyEq,
          prove6, isSepSAB, notSepInner, chooseWB, chooseWA, notSep,
          xV, yV, zV, aPrimeAt, bPrimeAt},
    fV = mkVar["f", ctFunTy]; sV = mkVar["S", ctSetTy];
    aV = mkVar["A", ctSetTy]; bV = mkVar["B", ctSetTy];
    waV = mkVar["WA", ctSetTy]; wbV = mkVar["WB", ctSetTy];
    xV = mkVar["x", ctRealTy]; yV = mkVar["yC", ctRealTy]; zV = mkVar["zC", ctRealTy];
    imgS = ctImageTm[fV, sV];
    hContTm = continuousTm[fV]; hCont = ASSUME[hContTm];
    contU = EQMP[unfoldContinuous[fV], hCont];
    hConnTm = isConnectedTm[sV]; hConn = ASSUME[hConnTm];
    connU = EQMP[unfoldIsConnected[sV], hConn];   (* forall U V. ~ isSeparation S U V *)
    hSepTm = isSeparationTm[imgS, aV, bV]; hSep = ASSUME[hSepTm];
    sepU = EQMP[unfoldIsSeparation[imgS, aV, bV], hSep];
    hOpA = HOL`Bool`CONJUNCT1[sepU]; r1 = HOL`Bool`CONJUNCT2[sepU];
    hOpB = HOL`Bool`CONJUNCT1[r1]; r2 = HOL`Bool`CONJUNCT2[r1];
    hNeA = HOL`Bool`CONJUNCT1[r2]; r3 = HOL`Bool`CONJUNCT2[r2];
    hNeB = HOL`Bool`CONJUNCT1[r3]; r4 = HOL`Bool`CONJUNCT2[r3];
    hCov = HOL`Bool`CONJUNCT1[r4]; hDisj = HOL`Bool`CONJUNCT2[r4];
    openExA = EQMP[unfoldOpenIn[imgS, aV], hOpA];   (* exists W. isOpen W /\ forall y. A y = (imgS y /\ W y) *)
    openExB = EQMP[unfoldOpenIn[imgS, bV], hOpB];
    memEqABodyA[wT_] := ctForallTm[yV, mkEq[ctApp[aV, yV],
      ctConjTm[ctApp[imgS, yV], ctApp[wT, yV]]]];
    memEqABodyB[wT_] := ctForallTm[yV, mkEq[ctApp[bV, yV],
      ctConjTm[ctApp[imgS, yV], ctApp[wT, yV]]]];
    hWAbodyTm = ctConjTm[isOpenTm[waV], memEqABodyA[waV]];
    hWBbodyTm = ctConjTm[isOpenTm[wbV], memEqABodyB[wbV]];
    preA = ctPreimageTm[fV, waV]; preB = ctPreimageTm[fV, wbV];
    aPrime = traceTm[sV, preA]; bPrime = traceTm[sV, preB];
    aPrimeAt[xT_] := ctTraceAt[sV, preA, xT];   (* A' x = S x /\ (PREIMAGE f WA) x *)
    bPrimeAt[xT_] := ctTraceAt[sV, preB, xT];

    (* the whole inner proof of F, assuming hWAbody and hWBbody *)
    notSepInner = Module[{hWA, hWB, openWA, openWB, memEqA, memEqB, c1, c2,
                          c3, c4, c5, c6, conj6, isSepSAB2, notSepS, falseTh},
      hWA = ASSUME[hWAbodyTm]; hWB = ASSUME[hWBbodyTm];
      openWA = HOL`Bool`CONJUNCT1[hWA]; memEqA = HOL`Bool`CONJUNCT2[hWA];
      openWB = HOL`Bool`CONJUNCT1[hWB]; memEqB = HOL`Bool`CONJUNCT2[hWB];
      (* C1, C2: openIn S A', B' *)
      c1 = HOL`Bool`MP[ctSpecAll[openInTraceThm, {sV, preA}],
        HOL`Bool`MP[HOL`Bool`SPEC[waV, contU], openWA]];
      c2 = HOL`Bool`MP[ctSpecAll[openInTraceThm, {sV, preB}],
        HOL`Bool`MP[HOL`Bool`SPEC[wbV, contU], openWB]];
      (* C3: nonempty A'  (exists x. A' x) *)
      c3 = Module[{neEx, y0, hAy0, conj0, imgY0, waY0, imgEx, z0, hz0, sz0,
                   y0eqfz0, wafz0, preAz0, aPz0, exA},
        neEx = EQMP[unfoldSetNonempty[aV], hNeA];   (* exists y. A y *)
        hAy0 = ASSUME[ctApp[aV, yV]];
        conj0 = EQMP[HOL`Bool`SPEC[yV, memEqA], hAy0];   (* imgS y /\ WA y *)
        imgY0 = HOL`Bool`CONJUNCT1[conj0]; waY0 = HOL`Bool`CONJUNCT2[conj0];
        imgEx = EQMP[ctImageAt[fV, sV, yV], imgY0];   (* exists z. S z /\ y = f z *)
        hz0 = ASSUME[ctConjTm[ctApp[sV, zV], mkEq[yV, mkComb[fV, zV]]]];
        sz0 = HOL`Bool`CONJUNCT1[hz0]; y0eqfz0 = HOL`Bool`CONJUNCT2[hz0];
        wafz0 = EQMP[HOL`Equal`APTERM[waV, y0eqfz0], waY0];   (* WA (f z) *)
        preAz0 = EQMP[HOL`Equal`SYM[ctPreimageAt[fV, waV, zV]], wafz0];  (* (PREIMAGE f WA) z *)
        aPz0 = EQMP[HOL`Equal`SYM[aPrimeAt[zV]], HOL`Bool`CONJ[sz0, preAz0]];  (* A' z *)
        exA = HOL`Bool`EXISTS[ctExistsTm[xV, ctApp[aPrime, xV]], zV, aPz0];
        EQMP[HOL`Equal`SYM[unfoldSetNonempty[aPrime]],
          HOL`Bool`CHOOSE[yV, neEx, HOL`Bool`CHOOSE[zV, imgEx, exA]]]
      ];
      (* C4: nonempty B' *)
      c4 = Module[{neEx, hBy0, conj0, imgY0, wbY0, imgEx, hz0, sz0, y0eqfz0,
                   wbfz0, preBz0, bPz0, exB},
        neEx = EQMP[unfoldSetNonempty[bV], hNeB];
        hBy0 = ASSUME[ctApp[bV, yV]];
        conj0 = EQMP[HOL`Bool`SPEC[yV, memEqB], hBy0];
        imgY0 = HOL`Bool`CONJUNCT1[conj0]; wbY0 = HOL`Bool`CONJUNCT2[conj0];
        imgEx = EQMP[ctImageAt[fV, sV, yV], imgY0];
        hz0 = ASSUME[ctConjTm[ctApp[sV, zV], mkEq[yV, mkComb[fV, zV]]]];
        sz0 = HOL`Bool`CONJUNCT1[hz0]; y0eqfz0 = HOL`Bool`CONJUNCT2[hz0];
        wbfz0 = EQMP[HOL`Equal`APTERM[wbV, y0eqfz0], wbY0];
        preBz0 = EQMP[HOL`Equal`SYM[ctPreimageAt[fV, wbV, zV]], wbfz0];
        bPz0 = EQMP[HOL`Equal`SYM[bPrimeAt[zV]], HOL`Bool`CONJ[sz0, preBz0]];
        exB = HOL`Bool`EXISTS[ctExistsTm[xV, ctApp[bPrime, xV]], zV, bPz0];
        EQMP[HOL`Equal`SYM[unfoldSetNonempty[bPrime]],
          HOL`Bool`CHOOSE[yV, neEx, HOL`Bool`CHOOSE[zV, imgEx, exB]]]
      ];
      (* C5: coversByTwo S A' B'  =  forall x. S x = (A' x \/ B' x) *)
      c5 = Module[{covU, fx, fwd, bwd, eqAt},
        covU = EQMP[unfoldCoversByTwo[imgS, aV, bV], hCov];  (* forall y. imgS y = (A y \/ B y) *)
        fx = mkComb[fV, xV];
        (* fwd: S x ==> A' x \/ B' x *)
        fwd = Module[{hSx, fxImg, covfx, disjAB, caseA, caseB},
          hSx = ASSUME[ctApp[sV, xV]];
          fxImg = EQMP[HOL`Equal`SYM[ctImageAt[fV, sV, fx]],
            HOL`Bool`EXISTS[concl[ctImageAt[fV, sV, fx]][[2]], xV,
              HOL`Bool`CONJ[hSx, REFL[fx]]]];   (* imgS (f x) *)
          disjAB = EQMP[HOL`Bool`SPEC[fx, covU], fxImg];   (* A (f x) \/ B (f x) *)
          caseA = Module[{hAfx, waFx, aPx},
            hAfx = ASSUME[ctApp[aV, fx]];
            waFx = HOL`Bool`CONJUNCT2[EQMP[HOL`Bool`SPEC[fx, memEqA], hAfx]];  (* WA (f x) *)
            aPx = EQMP[HOL`Equal`SYM[aPrimeAt[xV]],
              HOL`Bool`CONJ[hSx, EQMP[HOL`Equal`SYM[ctPreimageAt[fV, waV, xV]], waFx]]];
            HOL`Bool`DISJ1[aPx, ctApp[bPrime, xV]]];
          caseB = Module[{hBfx, wbFx, bPx},
            hBfx = ASSUME[ctApp[bV, fx]];
            wbFx = HOL`Bool`CONJUNCT2[EQMP[HOL`Bool`SPEC[fx, memEqB], hBfx]];
            bPx = EQMP[HOL`Equal`SYM[bPrimeAt[xV]],
              HOL`Bool`CONJ[hSx, EQMP[HOL`Equal`SYM[ctPreimageAt[fV, wbV, xV]], wbFx]]];
            HOL`Bool`DISJ2[bPx, ctApp[aPrime, xV]]];
          HOL`Bool`DISCH[ctApp[sV, xV],
            HOL`Bool`DISJCASES[disjAB, caseA, caseB]]];
        (* bwd: A' x \/ B' x ==> S x *)
        bwd = Module[{hDisjP, sFromA, sFromB},
          hDisjP = ASSUME[ctOrTm[ctApp[aPrime, xV], ctApp[bPrime, xV]]];
          sFromA = HOL`Bool`CONJUNCT1[EQMP[aPrimeAt[xV], ASSUME[ctApp[aPrime, xV]]]];
          sFromB = HOL`Bool`CONJUNCT1[EQMP[bPrimeAt[xV], ASSUME[ctApp[bPrime, xV]]]];
          HOL`Bool`DISCH[ctOrTm[ctApp[aPrime, xV], ctApp[bPrime, xV]],
            HOL`Bool`DISJCASES[hDisjP, sFromA, sFromB]]];
        eqAt = ctEqFromImps[fwd, bwd];   (* S x = (A' x \/ B' x) *)
        EQMP[HOL`Equal`SYM[unfoldCoversByTwo[sV, aPrime, bPrime]],
          HOL`Bool`GEN[xV, eqAt]]
      ];
      (* C6: setDisjoint A' B'  =  forall x. ~ (A' x /\ B' x) *)
      c6 = Module[{disjU, fx, hboth, aPx, bPx, sx, waFx, wbFx, fxImg, afx,
                   bfx, falseB},
        disjU = EQMP[unfoldSetDisjoint[aV, bV], hDisj];   (* forall y. ~ (A y /\ B y) *)
        fx = mkComb[fV, xV];
        hboth = ASSUME[ctConjTm[ctApp[aPrime, xV], ctApp[bPrime, xV]]];
        aPx = EQMP[aPrimeAt[xV], HOL`Bool`CONJUNCT1[hboth]];  (* S x /\ (PREIMAGE f WA) x *)
        bPx = EQMP[bPrimeAt[xV], HOL`Bool`CONJUNCT2[hboth]];
        sx = HOL`Bool`CONJUNCT1[aPx];
        waFx = EQMP[ctPreimageAt[fV, waV, xV], HOL`Bool`CONJUNCT2[aPx]];  (* WA (f x) *)
        wbFx = EQMP[ctPreimageAt[fV, wbV, xV], HOL`Bool`CONJUNCT2[bPx]];
        fxImg = EQMP[HOL`Equal`SYM[ctImageAt[fV, sV, fx]],
          HOL`Bool`EXISTS[concl[ctImageAt[fV, sV, fx]][[2]], xV,
            HOL`Bool`CONJ[sx, REFL[fx]]]];
        afx = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[fx, memEqA]],
          HOL`Bool`CONJ[fxImg, waFx]];   (* A (f x) *)
        bfx = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[fx, memEqB]],
          HOL`Bool`CONJ[fxImg, wbFx]];
        falseB = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[fx, disjU]],
          HOL`Bool`CONJ[afx, bfx]];
        EQMP[HOL`Equal`SYM[unfoldSetDisjoint[aPrime, bPrime]],
          HOL`Bool`GEN[xV, HOL`Bool`NOTINTRO[HOL`Bool`DISCH[
            ctConjTm[ctApp[aPrime, xV], ctApp[bPrime, xV]], falseB]]]]
      ];
      conj6 = HOL`Bool`CONJ[c1, HOL`Bool`CONJ[c2, HOL`Bool`CONJ[c3,
        HOL`Bool`CONJ[c4, HOL`Bool`CONJ[c5, c6]]]]];
      isSepSAB2 = EQMP[HOL`Equal`SYM[unfoldIsSeparation[sV, aPrime, bPrime]], conj6];
      notSepS = HOL`Bool`SPEC[bPrime, HOL`Bool`SPEC[aPrime, connU]];
      HOL`Bool`MP[HOL`Bool`NOTELIM[notSepS], isSepSAB2]
    ];
    chooseWB = HOL`Bool`CHOOSE[wbV, openExB, notSepInner];
    chooseWA = HOL`Bool`CHOOSE[waV, openExA, chooseWB];
    notSep = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[hSepTm, chooseWA]];
    EQMP[HOL`Equal`SYM[unfoldIsConnected[imgS]],
      HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, notSep]]] // (HOL`Bool`GEN[fV,
        HOL`Bool`GEN[sV, HOL`Bool`DISCH[hContTm, HOL`Bool`DISCH[hConnTm, #]]]] &)
  ];

ctRealLe[xT_, yT_] := mkComb[mkComb[realLeConst[], xT], yT];
ctClosedInterval[aT_, bT_] := mkComb[mkComb[closedIntervalConst[], aT], bT];
ctReflLe[xT_] := HOL`Bool`SPEC[xT,
  HOL`Auto`RealArith`realArithProve[ctForallTm[mkVar["zRefl", ctRealTy],
    ctRealLe[mkVar["zRefl", ctRealTy], mkVar["zRefl", ctRealTy]]]]];

(* T3 prerequisite: a closed interval is bounded, hence compact. *)
closedIntervalSetBoundedThm =
  Module[{aV, bV, xV, loV, hiV, ci, hCiTm, mem, body, innerExTm, outerExTm,
          innerEx, outerEx},
    aV = mkVar["a", ctRealTy]; bV = mkVar["b", ctRealTy]; xV = mkVar["x", ctRealTy];
    loV = mkVar["lo", ctRealTy]; hiV = mkVar["hi", ctRealTy];
    ci = ctClosedInterval[aV, bV];
    hCiTm = ctApp[ci, xV];
    mem = ctSpecAll[closedIntervalMemThm, {aV, bV, xV}];
    body = HOL`Bool`GEN[xV, HOL`Bool`DISCH[hCiTm, EQMP[mem, ASSUME[hCiTm]]]];
    innerExTm = ctExistsTm[hiV, ctForallTm[xV, ctImpTm[ctApp[ci, xV],
      ctConjTm[ctRealLe[aV, xV], ctRealLe[xV, hiV]]]]];
    outerExTm = ctExistsTm[loV, ctExistsTm[hiV, ctForallTm[xV,
      ctImpTm[ctApp[ci, xV], ctConjTm[ctRealLe[loV, xV], ctRealLe[xV, hiV]]]]]];
    innerEx = HOL`Bool`EXISTS[innerExTm, bV, body];
    outerEx = HOL`Bool`EXISTS[outerExTm, aV, innerEx];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      EQMP[HOL`Equal`SYM[unfoldSetBounded[ci]], outerEx]]]
  ];

closedIntervalCompactThm =
  Module[{aV, bV, ci},
    aV = mkVar["a", ctRealTy]; bV = mkVar["b", ctRealTy];
    ci = ctClosedInterval[aV, bV];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ci, compactOfClosedBoundedThm],
        ctSpecAll[closedIntervalIsClosedThm, {aV, bV}]],
        ctSpecAll[closedIntervalSetBoundedThm, {aV, bV}]]]]
  ];

(* corollary: a continuous image of a closed interval is bounded *)
continuousImageBoundedThm =
  Module[{fV, aV, bV, ci, img, hContTm, hCont, imgCompact, ccb},
    fV = mkVar["f", ctFunTy]; aV = mkVar["a", ctRealTy]; bV = mkVar["b", ctRealTy];
    ci = ctClosedInterval[aV, bV]; img = ctImageTm[fV, ci];
    hContTm = continuousTm[fV]; hCont = ASSUME[hContTm];
    imgCompact = HOL`Bool`MP[HOL`Bool`MP[
      ctSpecAll[continuousImageCompactThm, {fV, ci}], hCont],
      ctSpecAll[closedIntervalCompactThm, {aV, bV}]];
    ccb = EQMP[HOL`Bool`SPEC[img, compactIffClosedBoundedThm], imgCompact];
    HOL`Bool`GEN[fV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[hContTm, HOL`Bool`CONJUNCT2[ccb]]]]]
  ];

(* corollary: intermediate value theorem (function form) *)
continuousIVTThm =
  Module[{fV, aV, bV, yV, cV, fa, fb, ci, img, hContTm, hCont, hAbTm, hAb,
          hLoTm, hLo, hHiTm, hHi, imgConn, imgIv, ivU, ciA, ciB, faImg,
          fbImg, betweenThm, imgY, hcTm, hc, ciC, yEqfc, fcEqy, goalEx,
          chosen},
    fV = mkVar["f", ctFunTy]; aV = mkVar["a", ctRealTy]; bV = mkVar["b", ctRealTy];
    yV = mkVar["y", ctRealTy]; cV = mkVar["c", ctRealTy];
    fa = mkComb[fV, aV]; fb = mkComb[fV, bV];
    ci = ctClosedInterval[aV, bV]; img = ctImageTm[fV, ci];
    hContTm = continuousTm[fV]; hCont = ASSUME[hContTm];
    hAbTm = ctRealLe[aV, bV]; hAb = ASSUME[hAbTm];
    hLoTm = ctRealLe[fa, yV]; hLo = ASSUME[hLoTm];
    hHiTm = ctRealLe[yV, fb]; hHi = ASSUME[hHiTm];
    imgConn = HOL`Bool`MP[HOL`Bool`MP[
      ctSpecAll[continuousImageConnectedThm, {fV, ci}], hCont],
      ctSpecAll[connectedClosedIntervalThm, {aV, bV}]];
    imgIv = EQMP[HOL`Bool`SPEC[img, connectedIffIntervalSetThm], imgConn];
    ivU = EQMP[HOL`Bool`SPEC[img, isIntervalSetMemThm], imgIv];
    (* a, b in [a,b] *)
    ciA = EQMP[HOL`Equal`SYM[ctSpecAll[closedIntervalMemThm, {aV, bV, aV}]],
      HOL`Bool`CONJ[ctReflLe[aV], hAb]];
    ciB = EQMP[HOL`Equal`SYM[ctSpecAll[closedIntervalMemThm, {aV, bV, bV}]],
      HOL`Bool`CONJ[hAb, ctReflLe[bV]]];
    faImg = EQMP[HOL`Equal`SYM[ctImageAt[fV, ci, fa]],
      HOL`Bool`EXISTS[concl[ctImageAt[fV, ci, fa]][[2]], aV,
        HOL`Bool`CONJ[ciA, REFL[fa]]]];
    fbImg = EQMP[HOL`Equal`SYM[ctImageAt[fV, ci, fb]],
      HOL`Bool`EXISTS[concl[ctImageAt[fV, ci, fb]][[2]], bV,
        HOL`Bool`CONJ[ciB, REFL[fb]]]];
    betweenThm = EQMP[HOL`Equal`SYM[ctApplyDef[betweenDefThm, {fa, yV, fb}]],
      HOL`Bool`CONJ[hLo, hHi]];   (* between (f a) y (f b) *)
    imgY = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      ctSpecAll[ivU, {fa, yV, fb}], faImg], fbImg], betweenThm];  (* img y *)
    (* img y = exists c. ci c /\ y = f c ; turn into f c = y *)
    hcTm = ctConjTm[ctApp[ci, cV], mkEq[yV, mkComb[fV, cV]]]; hc = ASSUME[hcTm];
    ciC = HOL`Bool`CONJUNCT1[hc]; yEqfc = HOL`Bool`CONJUNCT2[hc];
    fcEqy = HOL`Equal`SYM[yEqfc];
    goalEx = ctExistsTm[cV, ctConjTm[ctApp[ci, cV], mkEq[mkComb[fV, cV], yV]]];
    chosen = HOL`Bool`CHOOSE[cV, EQMP[ctImageAt[fV, ci, yV], imgY],
      HOL`Bool`EXISTS[goalEx, cV, HOL`Bool`CONJ[ciC, fcEqy]]];
    HOL`Bool`GEN[fV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[hContTm, HOL`Bool`DISCH[hAbTm, HOL`Bool`DISCH[hLoTm,
        HOL`Bool`DISCH[hHiTm, chosen]]]]]]]]
  ];

End[];
EndPackage[];
