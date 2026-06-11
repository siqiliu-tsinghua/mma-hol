(* M7-7 / stdlib/Real/MinMax.wl - binary maximum and minimum on real. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

realMaxDefThm::usage = "realMaxDefThm - |- realMax = (lambda x y. COND (realLe x y) y x).";
realMaxConst::usage = "realMaxConst[] - realMax : real -> real -> real.";
realMinDefThm::usage = "realMinDefThm - |- realMin = (lambda x y. COND (realLe x y) x y).";
realMinConst::usage = "realMinConst[] - realMin : real -> real -> real.";
realMaxLeCaseThm::usage = "realMaxLeCaseThm - |- forall x y. realLe x y ==> realMax x y = y.";
realMaxGtCaseThm::usage = "realMaxGtCaseThm - |- forall x y. ~(realLe x y) ==> realMax x y = x.";
realMinLeCaseThm::usage = "realMinLeCaseThm - |- forall x y. realLe x y ==> realMin x y = x.";
realMinGtCaseThm::usage = "realMinGtCaseThm - |- forall x y. ~(realLe x y) ==> realMin x y = y.";
realLeMaxLeftThm::usage = "realLeMaxLeftThm - |- forall x y. realLe x (realMax x y).";
realLeMaxRightThm::usage = "realLeMaxRightThm - |- forall x y. realLe y (realMax x y).";
realMinLeLeftThm::usage = "realMinLeLeftThm - |- forall x y. realLe (realMin x y) x.";
realMinLeRightThm::usage = "realMinLeRightThm - |- forall x y. realLe (realMin x y) y.";
realMaxLubThm::usage = "realMaxLubThm - |- forall x y z. realLe x z ==> realLe y z ==> realLe (realMax x y) z.";
realMinGlbThm::usage = "realMinGlbThm - |- forall x y z. realLe z x ==> realLe z y ==> realLe z (realMin x y).";
realMaxCommThm::usage = "realMaxCommThm - |- forall x y. realMax x y = realMax y x.";
realMinCommThm::usage = "realMinCommThm - |- forall x y. realMin x y = realMin y x.";
realAbsMaxThm::usage = "realAbsMaxThm - |- forall x. realAbs x = realMax x (realNeg x).";

Begin["`Private`"];

realMaxTy = tyFun[realTy, tyFun[realTy, realTy]];
realMinTy = tyFun[realTy, tyFun[realTy, realTy]];

realMaxDefThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = mkAbs[xV, mkAbs[yV, condTm[realLeTm[xV, yV], yV, xV]]];
    newDefinition[mkEq[mkVar["realMax", realMaxTy], body]]
  ];

realMaxConst[] := mkConst["realMax", realMaxTy];
realMaxTm[xT_, yT_] := mkComb[mkComb[realMaxConst[], xT], yT];

unfoldRealMax[xT_, yT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[realMaxDefThm, xT];
    s1b = TRANS[s1, BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, yT];
    TRANS[s2, BETACONV[concl[s2][[2]]]]
  ];

realMinDefThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = mkAbs[xV, mkAbs[yV, condTm[realLeTm[xV, yV], xV, yV]]];
    newDefinition[mkEq[mkVar["realMin", realMinTy], body]]
  ];

realMinConst[] := mkConst["realMin", realMinTy];
realMinTm[xT_, yT_] := mkComb[mkComb[realMinConst[], xT], yT];

unfoldRealMin[xT_, yT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[realMinDefThm, xT];
    s1b = TRANS[s1, BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, yT];
    TRANS[s2, BETACONV[concl[s2][[2]]]]
  ];

minMaxLeCong[eqL_, eqR_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqL], eqR];

notLeFlip[aT_, bT_, hNotLe_] :=
  Module[{total},
    total = HOL`Bool`SPEC[bT, HOL`Bool`SPEC[aT, realLeTotalThm]];
    HOL`Bool`DISJCASES[total,
      HOL`Bool`CONTR[realLeTm[bT, aT],
        HOL`Bool`MP[HOL`Bool`NOTELIM[hNotLe], ASSUME[realLeTm[aT, bT]]]],
      ASSUME[realLeTm[bT, aT]]]
  ];

realMaxLeCaseThm =
  Module[{xV, yV, hLe},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hLe = ASSUME[realLeTm[xV, yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[realLeTm[xV, yV],
      TRANS[unfoldRealMax[xV, yV], condReduceT[hLe, yV, xV]]]]]
  ];

realMaxGtCaseThm =
  Module[{xV, yV, hNotLe},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[notTm[realLeTm[xV, yV]],
      TRANS[unfoldRealMax[xV, yV], condReduceF[hNotLe, yV, xV]]]]]
  ];

realMinLeCaseThm =
  Module[{xV, yV, hLe},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hLe = ASSUME[realLeTm[xV, yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[realLeTm[xV, yV],
      TRANS[unfoldRealMin[xV, yV], condReduceT[hLe, xV, yV]]]]]
  ];

realMinGtCaseThm =
  Module[{xV, yV, hNotLe},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[notTm[realLeTm[xV, yV]],
      TRANS[unfoldRealMin[xV, yV], condReduceF[hNotLe, xV, yV]]]]]
  ];

maxLeCase[xT_, yT_, hLe_] :=
  HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMaxLeCaseThm]], hLe];
maxGtCase[xT_, yT_, hNotLe_] :=
  HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMaxGtCaseThm]], hNotLe];
minLeCase[xT_, yT_, hLe_] :=
  HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMinLeCaseThm]], hLe];
minGtCase[xT_, yT_, hNotLe_] :=
  HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMinGtCaseThm]], hNotLe];

realLeMaxLeftThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, yV]],
      Module[{hLe, maxEq},
        hLe = ASSUME[realLeTm[xV, yV]];
        maxEq = maxLeCase[xV, yV, hLe];
        EQMP[minMaxLeCong[REFL[xV], HOL`Equal`SYM[maxEq]], hLe]
      ],
      Module[{hNotLe, maxEq, reflX},
        hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
        maxEq = maxGtCase[xV, yV, hNotLe];
        reflX = HOL`Bool`SPEC[xV, realLeReflThm];
        EQMP[minMaxLeCong[REFL[xV], HOL`Equal`SYM[maxEq]], reflX]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

realLeMaxRightThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, yV]],
      Module[{hLe, maxEq, reflY},
        hLe = ASSUME[realLeTm[xV, yV]];
        maxEq = maxLeCase[xV, yV, hLe];
        reflY = HOL`Bool`SPEC[yV, realLeReflThm];
        EQMP[minMaxLeCong[REFL[yV], HOL`Equal`SYM[maxEq]], reflY]
      ],
      Module[{hNotLe, maxEq, yLeX},
        hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
        maxEq = maxGtCase[xV, yV, hNotLe];
        yLeX = notLeFlip[xV, yV, hNotLe];
        EQMP[minMaxLeCong[REFL[yV], HOL`Equal`SYM[maxEq]], yLeX]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

realMinLeLeftThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, yV]],
      Module[{hLe, minEq, reflX},
        hLe = ASSUME[realLeTm[xV, yV]];
        minEq = minLeCase[xV, yV, hLe];
        reflX = HOL`Bool`SPEC[xV, realLeReflThm];
        EQMP[minMaxLeCong[HOL`Equal`SYM[minEq], REFL[xV]], reflX]
      ],
      Module[{hNotLe, minEq, yLeX},
        hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
        minEq = minGtCase[xV, yV, hNotLe];
        yLeX = notLeFlip[xV, yV, hNotLe];
        EQMP[minMaxLeCong[HOL`Equal`SYM[minEq], REFL[xV]], yLeX]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

realMinLeRightThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, yV]],
      Module[{hLe, minEq},
        hLe = ASSUME[realLeTm[xV, yV]];
        minEq = minLeCase[xV, yV, hLe];
        EQMP[minMaxLeCong[HOL`Equal`SYM[minEq], REFL[yV]], hLe]
      ],
      Module[{hNotLe, minEq, reflY},
        hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
        minEq = minGtCase[xV, yV, hNotLe];
        reflY = HOL`Bool`SPEC[yV, realLeReflThm];
        EQMP[minMaxLeCong[HOL`Equal`SYM[minEq], REFL[yV]], reflY]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

realMaxLubThm =
  Module[{xV, yV, zV, hXZ, hYZ, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hXZ = ASSUME[realLeTm[xV, zV]]; hYZ = ASSUME[realLeTm[yV, zV]];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, yV]],
      Module[{hLe, maxEq},
        hLe = ASSUME[realLeTm[xV, yV]];
        maxEq = maxLeCase[xV, yV, hLe];
        EQMP[minMaxLeCong[HOL`Equal`SYM[maxEq], REFL[zV]], hYZ]
      ],
      Module[{hNotLe, maxEq},
        hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
        maxEq = maxGtCase[xV, yV, hNotLe];
        EQMP[minMaxLeCong[HOL`Equal`SYM[maxEq], REFL[zV]], hXZ]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[realLeTm[xV, zV], HOL`Bool`DISCH[realLeTm[yV, zV], body]]]]]
  ];

realMinGlbThm =
  Module[{xV, yV, zV, hZX, hZY, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hZX = ASSUME[realLeTm[zV, xV]]; hZY = ASSUME[realLeTm[zV, yV]];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, yV]],
      Module[{hLe, minEq},
        hLe = ASSUME[realLeTm[xV, yV]];
        minEq = minLeCase[xV, yV, hLe];
        EQMP[minMaxLeCong[REFL[zV], HOL`Equal`SYM[minEq]], hZX]
      ],
      Module[{hNotLe, minEq},
        hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
        minEq = minGtCase[xV, yV, hNotLe];
        EQMP[minMaxLeCong[REFL[zV], HOL`Equal`SYM[minEq]], hZY]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[realLeTm[zV, xV], HOL`Bool`DISCH[realLeTm[zV, yV], body]]]]]
  ];

realMaxCommThm =
  Module[{xV, yV, maxXY, maxYX, leXYtoYX, leYXtoXY, antisym},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    maxXY = realMaxTm[xV, yV]; maxYX = realMaxTm[yV, xV];
    leXYtoYX = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[maxYX, HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMaxLubThm]]],
      HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realLeMaxRightThm]]],
      HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realLeMaxLeftThm]]];
    leYXtoXY = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[maxXY, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realMaxLubThm]]],
      HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realLeMaxRightThm]]],
      HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realLeMaxLeftThm]]];
    antisym = HOL`Bool`SPEC[maxYX, HOL`Bool`SPEC[maxXY, realLeAntisymThm]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`MP[HOL`Bool`MP[antisym, leXYtoYX], leYXtoXY]]]
  ];

realMinCommThm =
  Module[{xV, yV, minXY, minYX, leXYtoYX, leYXtoXY, antisym},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    minXY = realMinTm[xV, yV]; minYX = realMinTm[yV, xV];
    leXYtoYX = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[minXY, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realMinGlbThm]]],
      HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMinLeRightThm]]],
      HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMinLeLeftThm]]];
    leYXtoXY = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[minYX, HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realMinGlbThm]]],
      HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realMinLeRightThm]]],
      HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realMinLeLeftThm]]];
    antisym = HOL`Bool`SPEC[minYX, HOL`Bool`SPEC[minXY, realLeAntisymThm]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`MP[HOL`Bool`MP[antisym, leXYtoYX], leYXtoXY]]]
  ];

realAbsMaxThm =
  Module[{xV, negX, absX, maxT, leAbsMax, leMaxAbs, antisym},
    xV = mkVar["x", realTy]; negX = mkComb[realNegConst[], xV];
    absX = mkComb[realAbsConst[], xV]; maxT = realMaxTm[xV, negX];
    leAbsMax = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[rZ[], xV]],
      Module[{hPos, absEq, leXMax},
        hPos = ASSUME[realLeTm[rZ[], xV]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
        leXMax = HOL`Bool`SPEC[negX, HOL`Bool`SPEC[xV, realLeMaxLeftThm]];
        EQMP[minMaxLeCong[HOL`Equal`SYM[absEq], REFL[maxT]], leXMax]
      ],
      Module[{hNeg, absEq, leNegXMax},
        hNeg = ASSUME[notTm[realLeTm[rZ[], xV]]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg];
        leNegXMax = HOL`Bool`SPEC[negX, HOL`Bool`SPEC[xV, realLeMaxRightThm]];
        EQMP[minMaxLeCong[HOL`Equal`SYM[absEq], REFL[maxT]], leNegXMax]
      ]];
    leMaxAbs = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[absX, HOL`Bool`SPEC[negX, HOL`Bool`SPEC[xV, realMaxLubThm]]],
      HOL`Bool`SPEC[xV, realLeAbsSelfThm]],
      HOL`Bool`SPEC[xV, realNegLeAbsThm]];
    antisym = HOL`Bool`SPEC[maxT, HOL`Bool`SPEC[absX, realLeAntisymThm]];
    HOL`Bool`GEN[xV, HOL`Bool`MP[HOL`Bool`MP[antisym, leAbsMax], leMaxAbs]]
  ];

End[];
EndPackage[];
