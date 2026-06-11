(* ::Package:: *)

BeginPackage["HOL`Auto`RealArith`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Num`", "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`",
  "HOL`Stdlib`Real`"
}];

rnumAdd::usage =
  "rnumAdd[m, n] — proves ground real-literal addition: " <>
  "⊢ realAdd (&ℝ(&ℚ(&ℤ m))) (&ℝ(&ℚ(&ℤ n))) = &ℝ(&ℚ(&ℤ(m+n))).";
rnumMul::usage =
  "rnumMul[m, n] — proves ground real-literal multiplication.";
rnumLe::usage =
  "rnumLe[m, n] — for m <= n, proves the corresponding ground real <= fact.";
rnumLt::usage =
  "rnumLt[m, n] — for m < n, proves the corresponding ground real < fact.";
rnumNotLe::usage =
  "rnumNotLe[m, n] — for n < m, proves not(realLe (rnum m) (rnum n)).";
rnumPos::usage =
  "rnumPos[n] — for n >= 1, proves realLt (rnum 0) (rnum n).";
rnumNonneg::usage =
  "rnumNonneg[n] — for n >= 0, proves realLe (rnum 0) (rnum n).";

realLeAddMonoRThm::usage =
  "realLeAddMonoRThm — ⊢ ∀a c d. realLe c d ⇒ realLe (realAdd a c) (realAdd a d).";
realLeAddMono2Thm::usage =
  "realLeAddMono2Thm — ⊢ ∀a b c d. realLe a b ⇒ realLe c d ⇒ realLe (realAdd a c) (realAdd b d).";
realLtAddMonoRThm::usage =
  "realLtAddMonoRThm — ⊢ ∀a c d. realLt c d ⇒ realLt (realAdd a c) (realAdd a d).";
realLtLeAddMonoThm::usage =
  "realLtLeAddMonoThm — ⊢ ∀a b c d. realLt a b ⇒ realLe c d ⇒ realLt (realAdd a c) (realAdd b d).";
realLeLtAddMonoThm::usage =
  "realLeLtAddMonoThm — ⊢ ∀a b c d. realLe a b ⇒ realLt c d ⇒ realLt (realAdd a c) (realAdd b d).";
realLtAddMono2Thm::usage =
  "realLtAddMono2Thm — ⊢ ∀a b c d. realLt a b ⇒ realLt c d ⇒ realLt (realAdd a c) (realAdd b d).";
realLtIrreflThm::usage =
  "realLtIrreflThm — ⊢ ∀x. ¬(realLt x x).";
realNotLeLtThm::usage =
  "realNotLeLtThm — ⊢ ∀x y. ¬(realLe x y) = realLt y x.";
realLeMulCancelThm::usage =
  "realLeMulCancelThm — ⊢ ∀c a b. realLt 0 c ⇒ (realLe (realMul c a) (realMul c b) = realLe a b).";
realLtMulCancelThm::usage =
  "realLtMulCancelThm — ⊢ ∀c a b. realLt 0 c ⇒ (realLt (realMul c a) (realMul c b) = realLt a b).";
realEqIffLeLeThm::usage =
  "realEqIffLeLeThm — ⊢ ∀a b. (a = b) = (realLe a b ∧ realLe b a).";

Begin["`Private`"];

numTy = mkType["num", {}];
intTy = mkType["int", {}];
ratTy = mkType["rat", {}];
realTy = mkType["real", {}];

natTm[n_Integer] /; n >= 0 :=
  Nest[mkComb[HOL`Stdlib`Num`sucConst[], #] &,
    HOL`Stdlib`Num`zeroConst[], n];
natTm[n_] :=
  HOL`Error`holError["realarith-ground", "natTm: expected nonnegative integer",
    <|"n" -> n|>];

intOfNumTm[nT_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], nT];
ratOfIntTm[zT_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], zT];
realOfRatTm[qT_] := mkComb[HOL`Stdlib`Real`realOfRatConst[], qT];
rnumTm[n_Integer] /; n >= 0 := realOfRatTm[ratOfIntTm[intOfNumTm[natTm[n]]]];

intAdd[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
intMul[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
intLe[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intLeConst[], a], b];
intLt[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intLtConst[], a], b];
ratAdd[a_, b_] := mkComb[mkComb[HOL`Stdlib`Rat`ratAddConst[], a], b];
ratMul[a_, b_] := mkComb[mkComb[HOL`Stdlib`Rat`ratMulConst[], a], b];
ratLe[a_, b_] := mkComb[mkComb[HOL`Stdlib`Rat`ratLeConst[], a], b];
ratLt[a_, b_] := mkComb[mkComb[HOL`Stdlib`Rat`ratLtConst[], a], b];

rAdd[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], a], b];
rMul[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realMulConst[], a], b];
rLe[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLeConst[], a], b];
rLt[a_, b_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], a], b];
rNeg[a_] := mkComb[HOL`Stdlib`Real`realNegConst[], a];

forallTm[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
existsTm[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
impTm[p_, q_] := mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
conjTm[p_, q_] := mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
notTm[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];

natAdd[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], a], b];
natMul[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`timesConst[], a], b];
natLe[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
natLt[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], a], b];

unfoldLeq[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, a];
    e1 = TRANS[ap1, HOL`Equal`BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, HOL`Equal`BETACONV[concl[ap2][[2]]]]
  ];

unfoldLt[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, a];
    e1 = TRANS[ap1, HOL`Equal`BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, HOL`Equal`BETACONV[concl[ap2][[2]]]]
  ];

groundNatAdd[m_Integer, 0] /; m >= 0 :=
  groundNatAdd[m, 0] = HOL`Bool`SPEC[natTm[m], HOL`Stdlib`Num`plusZeroEqThm];
groundNatAdd[m_Integer, n_Integer] /; m >= 0 && n > 0 :=
  groundNatAdd[m, n] =
    Module[{k, mLit, kLit, sucEq, recEq, sucRec},
      k = n - 1; mLit = natTm[m]; kLit = natTm[k];
      sucEq = HOL`Bool`SPEC[kLit,
        HOL`Bool`SPEC[mLit, HOL`Stdlib`Num`plusSucEqThm]];
      recEq = groundNatAdd[m, k];
      sucRec = HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], recEq];
      TRANS[sucEq, sucRec]
    ];

groundNatMul[m_Integer, 0] /; m >= 0 :=
  groundNatMul[m, 0] = HOL`Bool`SPEC[natTm[m], HOL`Stdlib`Num`timesZeroEqThm];
groundNatMul[m_Integer, n_Integer] /; m >= 0 && n > 0 :=
  groundNatMul[m, n] =
    Module[{k, mLit, kLit, sucEq, recEq, addArgEq, addEq},
      k = n - 1; mLit = natTm[m]; kLit = natTm[k];
      sucEq = HOL`Bool`SPEC[kLit,
        HOL`Bool`SPEC[mLit, HOL`Stdlib`Num`timesSucEqThm]];
      recEq = groundNatMul[m, k];
      addArgEq = HOL`Equal`APTHM[
        HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], recEq], mLit];
      addEq = groundNatAdd[m*k, m];
      TRANS[sucEq, TRANS[addArgEq, addEq]]
    ];

groundNatLe[m_Integer, n_Integer] /; 0 <= m && m <= n :=
  groundNatLe[m, n] =
    Module[{mLit, nLit, k, kLit, kV, addEq, exBody, exTm, exThm, leEq},
      mLit = natTm[m]; nLit = natTm[n]; k = n - m; kLit = natTm[k];
      kV = mkVar["kRGL", numTy];
      addEq = groundNatAdd[m, k];
      exBody = mkEq[natAdd[mLit, kV], nLit];
      exTm = existsTm[kV, exBody];
      exThm = HOL`Bool`EXISTS[exTm, kLit, addEq];
      leEq = unfoldLeq[mLit, nLit];
      EQMP[HOL`Equal`SYM[leEq], exThm]
    ];

groundNatLt[m_Integer, n_Integer] /; 0 <= m && m < n :=
  groundNatLt[m, n] =
    Module[{mLit, nLit, leThm, ltEq},
      mLit = natTm[m]; nLit = natTm[n];
      leThm = groundNatLe[m + 1, n];
      ltEq = unfoldLt[mLit, nLit];
      EQMP[HOL`Equal`SYM[ltEq], leThm]
    ];

(* holError is HoldRest: msg/extra must be a literal String/Association at
   the call site, else no DownValue matches and nothing is thrown. *)
groundError[name_String, payload_Association] :=
  HOL`Error`holError["realarith-ground", "arguments out of domain",
    <|"fn" -> name, "args" -> payload|>];

specAll[th_, ts_List] :=
  Fold[Function[{acc, t}, HOL`Bool`SPEC[t, acc]], th, ts];

rAddComm[x_, y_] := specAll[HOL`Stdlib`Real`realAddCommThm, {x, y}];

leCong[eqLeft_, eqRight_, th_] :=
  EQMP[HOL`Kernel`MKCOMB[
    HOL`Equal`APTERM[HOL`Stdlib`Real`realLeConst[], eqLeft], eqRight], th];
ltCong[eqLeft_, eqRight_, th_] :=
  EQMP[HOL`Kernel`MKCOMB[
    HOL`Equal`APTERM[HOL`Stdlib`Real`realLtConst[], eqLeft], eqRight], th];

realLeSides[th_] := {concl[th][[1, 2]], concl[th][[2]]};
realLtSides[th_] := {concl[th][[1, 2]], concl[th][[2]]};

leAddMono[abLe_, cT_] :=
  Module[{s},
    s = realLeSides[abLe];
    HOL`Bool`MP[specAll[HOL`Stdlib`Real`realLeAddMonoThm,
      {s[[1]], s[[2]], cT}], abLe]
  ];
ltAddMono[abLt_, cT_] :=
  Module[{s},
    s = realLtSides[abLt];
    HOL`Bool`MP[specAll[HOL`Stdlib`Real`realLtAddMonoThm,
      {s[[1]], s[[2]], cT}], abLt]
  ];
leAddMonoR[cdLe_, aT_] :=
  Module[{s, raw},
    s = realLeSides[cdLe];
    raw = leAddMono[cdLe, aT];
    leCong[rAddComm[s[[1]], aT], rAddComm[s[[2]], aT], raw]
  ];
ltAddMonoR[cdLt_, aT_] :=
  Module[{s, raw},
    s = realLtSides[cdLt];
    raw = ltAddMono[cdLt, aT];
    ltCong[rAddComm[s[[1]], aT], rAddComm[s[[2]], aT], raw]
  ];
leTrans[xyLe_, yzLe_] :=
  Module[{x, y, z},
    x = concl[xyLe][[1, 2]]; y = concl[xyLe][[2]]; z = concl[yzLe][[2]];
    HOL`Bool`MP[HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLeTransThm, {x, y, z}], xyLe], yzLe]
  ];
ltLeTrans[xyLt_, yzLe_] :=
  Module[{x, y, z},
    x = concl[xyLt][[1, 2]]; y = concl[xyLt][[2]]; z = concl[yzLe][[2]];
    HOL`Bool`MP[HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLtLeTransThm, {x, y, z}], xyLt], yzLe]
  ];
leLtTrans[xyLe_, yzLt_] :=
  Module[{x, y, z},
    x = concl[xyLe][[1, 2]]; y = concl[xyLe][[2]]; z = concl[yzLt][[2]];
    HOL`Bool`MP[HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLeLtTransThm, {x, y, z}], xyLe], yzLt]
  ];
ltTrans[xyLt_, yzLt_] :=
  Module[{x, y, z},
    x = concl[xyLt][[1, 2]]; y = concl[xyLt][[2]]; z = concl[yzLt][[2]];
    HOL`Bool`MP[HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLtTransThm, {x, y, z}], xyLt], yzLt]
  ];
ltImpLe[xyLt_] :=
  Module[{s},
    s = realLtSides[xyLt];
    HOL`Bool`MP[specAll[HOL`Stdlib`Real`realLtImpLeThm, s], xyLt]
  ];
leMulMono[posLt_, abLe_] :=
  Module[{s, cT, nonneg},
    s = realLeSides[abLe]; cT = concl[posLt][[2]];
    nonneg = ltImpLe[posLt];
    HOL`Bool`MP[HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLeMulMonoThm, {s[[1]], s[[2]], cT}],
      nonneg], abLe]
  ];
ltMulMono[posLt_, abLt_] :=
  Module[{s, cT},
    s = realLtSides[abLt]; cT = concl[posLt][[2]];
    HOL`Bool`MP[HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLtMulMonoThm, {s[[1]], s[[2]], cT}],
      posLt], abLt]
  ];
ltNotLeAt[x_, y_] := specAll[HOL`Stdlib`Real`realLtNotLeThm, {x, y}];

HOL`Auto`RealArith`rnumAdd[m_Integer, n_Integer] /; m >= 0 && n >= 0 :=
  HOL`Auto`RealArith`rnumAdd[m, n] =
    Module[{mN, nN, mnN, mZ, nZ, mQ, nQ, natEq, intLift, intHom, intEq,
            ratLift, ratHom, ratEq, realLift, realHom},
      mN = natTm[m]; nN = natTm[n]; mnN = natTm[m + n];
      mZ = intOfNumTm[mN]; nZ = intOfNumTm[nN];
      mQ = ratOfIntTm[mZ]; nQ = ratOfIntTm[nZ];
      natEq = groundNatAdd[m, n];
      intLift = HOL`Equal`APTERM[HOL`Stdlib`Int`intOfNumConst[], natEq];
      intHom = specAll[HOL`Stdlib`Int`intOfNumAddThm, {mN, nN}];
      intEq = TRANS[HOL`Equal`SYM[intHom], intLift];
      ratLift = HOL`Equal`APTERM[HOL`Stdlib`Rat`ratOfIntConst[], intEq];
      ratHom = specAll[HOL`Stdlib`Rat`ratOfIntAddThm, {mZ, nZ}];
      ratEq = TRANS[HOL`Equal`SYM[ratHom], ratLift];
      realLift = HOL`Equal`APTERM[HOL`Stdlib`Real`realOfRatConst[], ratEq];
      realHom = specAll[HOL`Stdlib`Real`realOfRatAddThm, {mQ, nQ}];
      TRANS[HOL`Equal`SYM[realHom], realLift]
    ];
HOL`Auto`RealArith`rnumAdd[m_, n_] :=
  groundError["rnumAdd", <|"m" -> m, "n" -> n|>];

HOL`Auto`RealArith`rnumMul[m_Integer, n_Integer] /; m >= 0 && n >= 0 :=
  HOL`Auto`RealArith`rnumMul[m, n] =
    Module[{mN, nN, mnN, mZ, nZ, mQ, nQ, natEq, intLift, intHom, intEq,
            ratLift, ratHom, ratEq, realLift, realHom},
      mN = natTm[m]; nN = natTm[n]; mnN = natTm[m*n];
      mZ = intOfNumTm[mN]; nZ = intOfNumTm[nN];
      mQ = ratOfIntTm[mZ]; nQ = ratOfIntTm[nZ];
      natEq = groundNatMul[m, n];
      intLift = HOL`Equal`APTERM[HOL`Stdlib`Int`intOfNumConst[], natEq];
      intHom = specAll[HOL`Stdlib`Int`intOfNumMulThm, {mN, nN}];
      intEq = TRANS[HOL`Equal`SYM[intHom], intLift];
      ratLift = HOL`Equal`APTERM[HOL`Stdlib`Rat`ratOfIntConst[], intEq];
      ratHom = specAll[HOL`Stdlib`Rat`ratOfIntMulThm, {mZ, nZ}];
      ratEq = TRANS[HOL`Equal`SYM[ratHom], ratLift];
      realLift = HOL`Equal`APTERM[HOL`Stdlib`Real`realOfRatConst[], ratEq];
      realHom = specAll[HOL`Stdlib`Real`realOfRatMulThm, {mQ, nQ}];
      TRANS[HOL`Equal`SYM[realHom], realLift]
    ];
HOL`Auto`RealArith`rnumMul[m_, n_] :=
  groundError["rnumMul", <|"m" -> m, "n" -> n|>];

HOL`Auto`RealArith`rnumLe[m_Integer, n_Integer] /; m >= 0 && n >= 0 && m <= n :=
  HOL`Auto`RealArith`rnumLe[m, n] =
    Module[{mN, nN, mZ, nZ, mQ, nQ, natTh, intEq, intTh, ratEq, ratTh, realEq},
      mN = natTm[m]; nN = natTm[n]; mZ = intOfNumTm[mN]; nZ = intOfNumTm[nN];
      mQ = ratOfIntTm[mZ]; nQ = ratOfIntTm[nZ];
      natTh = groundNatLe[m, n];
      intEq = specAll[HOL`Stdlib`Int`intOfNumLeThm, {mN, nN}];
      intTh = EQMP[HOL`Equal`SYM[intEq], natTh];
      ratEq = specAll[HOL`Stdlib`Rat`ratOfIntLeThm, {mZ, nZ}];
      ratTh = EQMP[HOL`Equal`SYM[ratEq], intTh];
      realEq = specAll[HOL`Stdlib`Real`realOfRatLeThm, {mQ, nQ}];
      EQMP[HOL`Equal`SYM[realEq], ratTh]
    ];
HOL`Auto`RealArith`rnumLe[m_, n_] :=
  groundError["rnumLe", <|"m" -> m, "n" -> n|>];

HOL`Auto`RealArith`rnumLt[m_Integer, n_Integer] /; m >= 0 && n >= 0 && m < n :=
  HOL`Auto`RealArith`rnumLt[m, n] =
    Module[{mN, nN, mZ, nZ, mQ, nQ, natTh, intEq, intTh, ratEq, ratTh, realEq},
      mN = natTm[m]; nN = natTm[n]; mZ = intOfNumTm[mN]; nZ = intOfNumTm[nN];
      mQ = ratOfIntTm[mZ]; nQ = ratOfIntTm[nZ];
      natTh = groundNatLt[m, n];
      intEq = specAll[HOL`Stdlib`Real`intOfNumLtThm, {mN, nN}];
      intTh = EQMP[HOL`Equal`SYM[intEq], natTh];
      ratEq = specAll[HOL`Stdlib`Real`ratOfIntLtThm, {mZ, nZ}];
      ratTh = EQMP[HOL`Equal`SYM[ratEq], intTh];
      realEq = specAll[HOL`Stdlib`Real`realOfRatLtThm, {mQ, nQ}];
      EQMP[HOL`Equal`SYM[realEq], ratTh]
    ];
HOL`Auto`RealArith`rnumLt[m_, n_] :=
  groundError["rnumLt", <|"m" -> m, "n" -> n|>];

HOL`Auto`RealArith`rnumNotLe[m_Integer, n_Integer] /; m >= 0 && n >= 0 && n < m :=
  HOL`Auto`RealArith`rnumNotLe[m, n] =
    Module[{ltTh, eqTh},
      ltTh = HOL`Auto`RealArith`rnumLt[n, m];
      eqTh = ltNotLeAt[rnumTm[n], rnumTm[m]];
      EQMP[eqTh, ltTh]
    ];
HOL`Auto`RealArith`rnumNotLe[m_, n_] :=
  groundError["rnumNotLe", <|"m" -> m, "n" -> n|>];

HOL`Auto`RealArith`rnumPos[n_Integer] /; n >= 1 :=
  HOL`Auto`RealArith`rnumPos[n] = HOL`Auto`RealArith`rnumLt[0, n];
HOL`Auto`RealArith`rnumPos[n_] :=
  groundError["rnumPos", <|"n" -> n|>];

HOL`Auto`RealArith`rnumNonneg[n_Integer] /; n >= 0 :=
  HOL`Auto`RealArith`rnumNonneg[n] = HOL`Auto`RealArith`rnumLe[0, n];
HOL`Auto`RealArith`rnumNonneg[n_] :=
  groundError["rnumNonneg", <|"n" -> n|>];

realLeAddMonoRThm =
  Module[{aV, cV, dV, h, res},
    aV = mkVar["a", realTy]; cV = mkVar["c", realTy]; dV = mkVar["d", realTy];
    h = ASSUME[rLe[cV, dV]];
    res = leAddMonoR[h, aV];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV,
      HOL`Bool`DISCH[rLe[cV, dV], res]]]]
  ];

realLeAddMono2Thm =
  Module[{aV, bV, cV, dV, hAB, hCD, step1, step2, res},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    cV = mkVar["c", realTy]; dV = mkVar["d", realTy];
    hAB = ASSUME[rLe[aV, bV]]; hCD = ASSUME[rLe[cV, dV]];
    step1 = leAddMono[hAB, cV];
    step2 = leAddMonoR[hCD, bV];
    res = leTrans[step1, step2];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV,
      HOL`Bool`DISCH[rLe[aV, bV], HOL`Bool`DISCH[rLe[cV, dV], res]]]]]]
  ];

realLtAddMonoRThm =
  Module[{aV, cV, dV, h, res},
    aV = mkVar["a", realTy]; cV = mkVar["c", realTy]; dV = mkVar["d", realTy];
    h = ASSUME[rLt[cV, dV]];
    res = ltAddMonoR[h, aV];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV,
      HOL`Bool`DISCH[rLt[cV, dV], res]]]]
  ];

realLtLeAddMonoThm =
  Module[{aV, bV, cV, dV, hAB, hCD, step1, step2, res},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    cV = mkVar["c", realTy]; dV = mkVar["d", realTy];
    hAB = ASSUME[rLt[aV, bV]]; hCD = ASSUME[rLe[cV, dV]];
    step1 = ltAddMono[hAB, cV];
    step2 = leAddMonoR[hCD, bV];
    res = ltLeTrans[step1, step2];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV,
      HOL`Bool`DISCH[rLt[aV, bV], HOL`Bool`DISCH[rLe[cV, dV], res]]]]]]
  ];

realLeLtAddMonoThm =
  Module[{aV, bV, cV, dV, hAB, hCD, step1, step2, res},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    cV = mkVar["c", realTy]; dV = mkVar["d", realTy];
    hAB = ASSUME[rLe[aV, bV]]; hCD = ASSUME[rLt[cV, dV]];
    step1 = leAddMono[hAB, cV];
    step2 = ltAddMonoR[hCD, bV];
    res = leLtTrans[step1, step2];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV,
      HOL`Bool`DISCH[rLe[aV, bV], HOL`Bool`DISCH[rLt[cV, dV], res]]]]]]
  ];

realLtAddMono2Thm =
  Module[{aV, bV, cV, dV, hAB, hCD, step1, step2, res},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    cV = mkVar["c", realTy]; dV = mkVar["d", realTy];
    hAB = ASSUME[rLt[aV, bV]]; hCD = ASSUME[rLt[cV, dV]];
    step1 = ltAddMono[hAB, cV];
    step2 = ltAddMonoR[hCD, bV];
    res = ltTrans[step1, step2];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV,
      HOL`Bool`DISCH[rLt[aV, bV], HOL`Bool`DISCH[rLt[cV, dV], res]]]]]]
  ];

realLtIrreflThm =
  Module[{xV, h, eqTh, notLe, leRefl, ff, notLt},
    xV = mkVar["x", realTy];
    h = ASSUME[rLt[xV, xV]];
    eqTh = ltNotLeAt[xV, xV];
    notLe = EQMP[eqTh, h];
    leRefl = HOL`Bool`SPEC[xV, HOL`Stdlib`Real`realLeReflThm];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notLe], leRefl];
    notLt = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[rLt[xV, xV], ff]];
    HOL`Bool`GEN[xV, notLt]
  ];

realNotLeLtThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Equal`SYM[ltNotLeAt[yV, xV]]]]
  ];

notLeLtAt[x_, y_] := specAll[realNotLeLtThm, {x, y}];

realLeMulCancelThm =
  Module[{cV, aV, bV, hPos, hAB, hProd, bwd, notAB, ltBA, ltProd, notProd,
          ff, fwd, iffTh},
    cV = mkVar["c", realTy]; aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    hPos = ASSUME[rLt[rnumTm[0], cV]];
    hAB = ASSUME[rLe[aV, bV]];
    bwd = leMulMono[hPos, hAB];
    hProd = ASSUME[rLe[rMul[cV, aV], rMul[cV, bV]]];
    notAB = ASSUME[notTm[rLe[aV, bV]]];
    ltBA = EQMP[notLeLtAt[aV, bV], notAB];
    ltProd = ltMulMono[hPos, ltBA];
    notProd = EQMP[ltNotLeAt[rMul[cV, bV], rMul[cV, aV]], ltProd];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notProd], hProd];
    fwd = HOL`Bool`CCONTR[rLe[aV, bV], ff];
    iffTh = HOL`Kernel`DEDUCTANTISYM[bwd, fwd];
    HOL`Bool`GEN[cV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[rLt[rnumTm[0], cV], iffTh]]]]
  ];

realLtMulCancelThm =
  Module[{cV, aV, bV, hPos, hAB, hProd, bwd, notAB, notLeBA, ltAB, ff1,
          leBA, leProd, notLeProd, ff, fwd, iffTh},
    cV = mkVar["c", realTy]; aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    hPos = ASSUME[rLt[rnumTm[0], cV]];
    hAB = ASSUME[rLt[aV, bV]];
    bwd = ltMulMono[hPos, hAB];
    hProd = ASSUME[rLt[rMul[cV, aV], rMul[cV, bV]]];
    notAB = ASSUME[notTm[rLt[aV, bV]]];
    notLeBA = ASSUME[notTm[rLe[bV, aV]]];
    ltAB = EQMP[notLeLtAt[bV, aV], notLeBA];
    ff1 = HOL`Bool`MP[HOL`Bool`NOTELIM[notAB], ltAB];
    leBA = HOL`Bool`CCONTR[rLe[bV, aV], ff1];
    leProd = leMulMono[hPos, leBA];
    notLeProd = EQMP[ltNotLeAt[rMul[cV, aV], rMul[cV, bV]], hProd];
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeProd], leProd];
    fwd = HOL`Bool`CCONTR[rLt[aV, bV], ff];
    iffTh = HOL`Kernel`DEDUCTANTISYM[bwd, fwd];
    HOL`Bool`GEN[cV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[rLt[rnumTm[0], cV], iffTh]]]]
  ];

realEqIffLeLeThm =
  Module[{aV, bV, eqTmAB, leABTm, leBATm, conj, hEq, leAA, leftEq, rightEq,
          leAB, leBA, dirEqToLe, hConj, antisym, dirLeToEq},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    eqTmAB = mkEq[aV, bV]; leABTm = rLe[aV, bV]; leBATm = rLe[bV, aV];
    conj = conjTm[leABTm, leBATm];
    hEq = ASSUME[eqTmAB];
    leAA = HOL`Bool`SPEC[aV, HOL`Stdlib`Real`realLeReflThm];
    leftEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realLeConst[], REFL[aV]], hEq];
    leAB = EQMP[leftEq, leAA];
    rightEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realLeConst[], HOL`Equal`SYM[hEq]],
      REFL[aV]];
    leBA = EQMP[HOL`Equal`SYM[rightEq], leAA];
    dirEqToLe = HOL`Bool`CONJ[leAB, leBA];
    hConj = ASSUME[conj];
    antisym = HOL`Bool`MP[HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLeAntisymThm, {aV, bV}],
      HOL`Bool`CONJUNCT1[hConj]], HOL`Bool`CONJUNCT2[hConj]];
    dirLeToEq = antisym;
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Kernel`DEDUCTANTISYM[dirLeToEq, dirEqToLe]]]
  ];

End[];
EndPackage[];
