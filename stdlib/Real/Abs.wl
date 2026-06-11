(* M7-7 / stdlib/Real/Abs.wl - absolute value on the completed ordered field. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

realAbsDefThm::usage = "realAbsDefThm - |- realAbs = (lambda x. COND (realLe 0 x) x (realNeg x)).";
realAbsConst::usage = "realAbsConst[] - realAbs : real -> real.";
realAbsPosThm::usage = "realAbsPosThm - |- forall x. realLe 0 x ==> realAbs x = x.";
realAbsNegCaseThm::usage = "realAbsNegCaseThm - |- forall x. ~(realLe 0 x) ==> realAbs x = realNeg x.";
realAbsZeroThm::usage = "realAbsZeroThm - |- realAbs 0 = 0.";
realAbsNonnegThm::usage = "realAbsNonnegThm - |- forall x. realLe 0 (realAbs x).";
realLeAbsSelfThm::usage = "realLeAbsSelfThm - |- forall x. realLe x (realAbs x).";
realNegLeAbsThm::usage = "realNegLeAbsThm - |- forall x. realLe (realNeg x) (realAbs x).";
realAbsNegThm::usage = "realAbsNegThm - |- forall x. realAbs (realNeg x) = realAbs x.";
realAbsTriangleThm::usage = "realAbsTriangleThm - |- forall x y. realLe (realAbs (realAdd x y)) (realAdd (realAbs x) (realAbs y)).";

Begin["`Private`"];

realAbsTy = tyFun[realTy, realTy];

realAbsDefThm =
  Module[{xV, body},
    xV = mkVar["x", realTy];
    body = mkAbs[xV, condTm[realLeTm[rZ[], xV], xV, realNegTm[xV]]];
    newDefinition[mkEq[mkVar["realAbs", realAbsTy], body]]
  ];

realAbsConst[] := mkConst["realAbs", realAbsTy];
realAbsTm[xT_] := mkComb[realAbsConst[], xT];

unfoldRealAbs[xT_] :=
  Module[{s1},
    s1 = HOL`Equal`APTHM[realAbsDefThm, xT];
    TRANS[s1, BETACONV[concl[s1][[2]]]]
  ];

leCong[eqL_, eqR_] := HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], eqL], eqR];

realAbsPosThm =
  Module[{xV, hPos},
    xV = mkVar["x", realTy]; hPos = ASSUME[realLeTm[rZ[], xV]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLeTm[rZ[], xV],
      TRANS[unfoldRealAbs[xV], condReduceT[hPos, xV, realNegTm[xV]]]]]
  ];

realAbsNegCaseThm =
  Module[{xV, hNeg},
    xV = mkVar["x", realTy]; hNeg = ASSUME[notTm[realLeTm[rZ[], xV]]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[notTm[realLeTm[rZ[], xV]],
      TRANS[unfoldRealAbs[xV], condReduceF[hNeg, xV, realNegTm[xV]]]]]
  ];

realAbsZeroThm =
  Module[{le00},
    le00 = HOL`Bool`SPEC[rZ[], realLeReflThm];
    HOL`Bool`MP[HOL`Bool`SPEC[rZ[], realAbsPosThm], le00]
  ];

realAbsNonnegThm =
  Module[{xV, body},
    xV = mkVar["x", realTy];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[rZ[], xV]],
      Module[{hPos, absEq},
        hPos = ASSUME[realLeTm[rZ[], xV]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
        EQMP[leCong[REFL[rZ[]], HOL`Equal`SYM[absEq]], hPos]
      ],
      Module[{hNeg, absEq, negNonneg},
        hNeg = ASSUME[notTm[realLeTm[rZ[], xV]]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg];
        negNonneg = HOL`Bool`MP[HOL`Bool`SPEC[xV, notNonnegNegThm], hNeg];
        EQMP[leCong[REFL[rZ[]], HOL`Equal`SYM[absEq]], negNonneg]
      ]];
    HOL`Bool`GEN[xV, body]
  ];

realLeAbsSelfThm =
  Module[{xV, body},
    xV = mkVar["x", realTy];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[rZ[], xV]],
      Module[{hPos, absEq, reflX},
        hPos = ASSUME[realLeTm[rZ[], xV]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
        reflX = HOL`Bool`SPEC[xV, realLeReflThm];
        EQMP[leCong[REFL[xV], HOL`Equal`SYM[absEq]], reflX]
      ],
      Module[{hNeg, absEq, xLe0, le0neg, xLeNeg},
        hNeg = ASSUME[notTm[realLeTm[rZ[], xV]]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg];
        xLe0 = HOL`Bool`MP[HOL`Bool`SPEC[xV, notNonnegToLeZeroThm], hNeg];
        le0neg = HOL`Bool`MP[HOL`Bool`SPEC[xV, notNonnegNegThm], hNeg];
        xLeNeg = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[realNegTm[xV], HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[xV, realLeTransThm]]],
          xLe0], le0neg];
        EQMP[leCong[REFL[xV], HOL`Equal`SYM[absEq]], xLeNeg]
      ]];
    HOL`Bool`GEN[xV, body]
  ];

realNegLeAbsThm =
  Module[{xV, body},
    xV = mkVar["x", realTy];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[rZ[], xV]],
      Module[{hPos, absEq, negLe0, negLeX},
        hPos = ASSUME[realLeTm[rZ[], xV]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
        negLe0 = HOL`Bool`MP[HOL`Bool`SPEC[xV, realNegNonposThm], hPos];
        negLeX = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[xV, HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[realNegTm[xV], realLeTransThm]]],
          negLe0], hPos];
        EQMP[leCong[REFL[realNegTm[xV]], HOL`Equal`SYM[absEq]], negLeX]
      ],
      Module[{hNeg, absEq, reflNeg},
        hNeg = ASSUME[notTm[realLeTm[rZ[], xV]]];
        absEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg];
        reflNeg = HOL`Bool`SPEC[realNegTm[xV], realLeReflThm];
        EQMP[leCong[REFL[realNegTm[xV]], HOL`Equal`SYM[absEq]], reflNeg]
      ]];
    HOL`Bool`GEN[xV, body]
  ];

realAbsNegThm =
  Module[{xV, nx, body},
    xV = mkVar["x", realTy]; nx = realNegTm[xV];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[rZ[], xV]],
      Module[{hPos, subBody},
        hPos = ASSUME[realLeTm[rZ[], xV]];
        subBody = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[rZ[], nx]],
          Module[{hPosNeg, absNegX, absX, negNeg, negNegLe0, xLe0, zeroEqX, negXEq0},
            hPosNeg = ASSUME[realLeTm[rZ[], nx]];
            absNegX = HOL`Bool`MP[HOL`Bool`SPEC[nx, realAbsPosThm], hPosNeg];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
            negNeg = HOL`Bool`SPEC[xV, realNegNegThm];
            negNegLe0 = HOL`Bool`MP[HOL`Bool`SPEC[nx, realNegNonposThm], hPosNeg];
            xLe0 = EQMP[leCong[negNeg, REFL[rZ[]]], negNegLe0];
            zeroEqX = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[xV, HOL`Bool`SPEC[rZ[], realLeAntisymThm]], hPos], xLe0];
            negXEq0 = TRANS[HOL`Equal`SYM[rNegCong[zeroEqX]], realNegZeroThm];
            TRANS[absNegX, TRANS[negXEq0, TRANS[zeroEqX, HOL`Equal`SYM[absX]]]]
          ],
          Module[{hNegNeg, absNegX, absX, negNeg},
            hNegNeg = ASSUME[notTm[realLeTm[rZ[], nx]]];
            absNegX = HOL`Bool`MP[HOL`Bool`SPEC[nx, realAbsNegCaseThm], hNegNeg];
            absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsPosThm], hPos];
            negNeg = HOL`Bool`SPEC[xV, realNegNegThm];
            TRANS[absNegX, TRANS[negNeg, HOL`Equal`SYM[absX]]]
          ]];
        subBody
      ],
      Module[{hNeg, absNegX, absX, negNonneg},
        hNeg = ASSUME[notTm[realLeTm[rZ[], xV]]];
        negNonneg = HOL`Bool`MP[HOL`Bool`SPEC[xV, notNonnegNegThm], hNeg];
        absNegX = HOL`Bool`MP[HOL`Bool`SPEC[nx, realAbsPosThm], negNonneg];
        absX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realAbsNegCaseThm], hNeg];
        TRANS[absNegX, HOL`Equal`SYM[absX]]
      ]];
    HOL`Bool`GEN[xV, body]
  ];

leAddMono2[abLe_, cdLe_] :=
  Module[{a, b, c, d, step1, step2Raw, step2, target},
    a = concl[abLe][[1, 2]]; b = concl[abLe][[2]];
    c = concl[cdLe][[1, 2]]; d = concl[cdLe][[2]];
    step1 = leAddMono[abLe, c];
    step2Raw = leAddMono[cdLe, b];
    step2 = EQMP[leCong[rComm[c, b], rComm[d, b]], step2Raw];
    target = HOL`Bool`SPEC[realAddTm[b, d],
      HOL`Bool`SPEC[realAddTm[b, c],
        HOL`Bool`SPEC[realAddTm[a, c], realLeTransThm]]];
    HOL`Bool`MP[HOL`Bool`MP[target, step1], step2]
  ];

realAbsTriangleThm =
  Module[{xV, yV, sum, rhs, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    sum = realAddTm[xV, yV]; rhs = realAddTm[realAbsTm[xV], realAbsTm[yV]];
    body = HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[realLeTm[rZ[], sum]],
      Module[{hPos, absSum, leX, leY, addLe},
        hPos = ASSUME[realLeTm[rZ[], sum]];
        absSum = HOL`Bool`MP[HOL`Bool`SPEC[sum, realAbsPosThm], hPos];
        leX = HOL`Bool`SPEC[xV, realLeAbsSelfThm];
        leY = HOL`Bool`SPEC[yV, realLeAbsSelfThm];
        addLe = leAddMono2[leX, leY];
        EQMP[leCong[HOL`Equal`SYM[absSum], REFL[rhs]], addLe]
      ],
      Module[{hNeg, absSum, negAdd, leX, leY, addLe, absSumNeg},
        hNeg = ASSUME[notTm[realLeTm[rZ[], sum]]];
        absSum = HOL`Bool`MP[HOL`Bool`SPEC[sum, realAbsNegCaseThm], hNeg];
        negAdd = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realNegAddThm]];
        leX = HOL`Bool`SPEC[xV, realNegLeAbsThm];
        leY = HOL`Bool`SPEC[yV, realNegLeAbsThm];
        addLe = leAddMono2[leX, leY];
        absSumNeg = TRANS[absSum, negAdd];
        EQMP[leCong[HOL`Equal`SYM[absSumNeg], REFL[rhs]], addLe]
      ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

End[];
EndPackage[];
