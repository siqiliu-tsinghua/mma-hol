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
rnumNe::usage =
  "rnumNe[m, n] — for distinct nonnegative literals, proves " <>
  "¬(rnumTm m = rnumTm n).";

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
realLeAddCancelThm::usage =
  "realLeAddCancelThm — ⊢ ∀a b c. realLe (realAdd a c) (realAdd b c) = realLe a b.";
realLtAddCancelThm::usage =
  "realLtAddCancelThm — ⊢ ∀a b c. realLt (realAdd a c) (realAdd b c) = realLt a b.";
realLinNormConv::usage =
  "realLinNormConv[t] — proof-producing linear normalizer over reals: " <>
  "returns ⊢ t = signed canonical linear form.";
realAtomNormConv::usage =
  "realAtomNormConv[atom] — normalizes a realLe/realLt linear atom to " <>
  "an equivalent atom with nonnegative canonical linear sides.";

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

rInv[a_] := mkComb[HOL`Stdlib`Real`realInvConst[], a];

rMulComm[x_, y_] := specAll[HOL`Stdlib`Real`realMulCommThm, {x, y}];
rAddAssoc[x_, y_, z_] := specAll[HOL`Stdlib`Real`realAddAssocThm, {x, y, z}];
rMulAssoc[x_, y_, z_] := specAll[HOL`Stdlib`Real`realMulAssocThm, {x, y, z}];
rMulDistrib[x_, y_, z_] := specAll[HOL`Stdlib`Real`realMulDistribThm, {x, y, z}];

rAddLeftCong[eq_, rest_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], eq],
    REFL[rest]];
rAddRightCong[left_, eq_] :=
  HOL`Equal`APTERM[mkComb[HOL`Stdlib`Real`realAddConst[], left], eq];
rMulLeftCong[eq_, rest_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Real`realMulConst[], eq],
    REFL[rest]];
rMulRightCong[left_, eq_] :=
  HOL`Equal`APTERM[mkComb[HOL`Stdlib`Real`realMulConst[], left], eq];
rNegCong[eq_] := HOL`Equal`APTERM[HOL`Stdlib`Real`realNegConst[], eq];

zeroAddEq[x_] :=
  TRANS[rAddComm[rnumTm[0], x],
    HOL`Bool`SPEC[x, HOL`Stdlib`Real`realAddZeroThm]];

oneMulEq[x_] :=
  TRANS[rMulComm[rnumTm[1], x],
    HOL`Bool`SPEC[x, HOL`Stdlib`Real`realMulOneThm]];

addLeftCommEq[a_, b_, c_] :=
  Module[{s1, s2, s3},
    s1 = HOL`Equal`SYM[rAddAssoc[a, b, c]];
    s2 = HOL`Equal`APTHM[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], rAddComm[a, b]], c];
    s3 = rAddAssoc[b, a, c];
    TRANS[s1, TRANS[s2, s3]]
  ];

addNegCancelEq[x_, c_] :=
  Module[{assoc, neg, cong, zero},
    assoc = rAddAssoc[x, c, rNeg[c]];
    neg = HOL`Bool`SPEC[c, HOL`Stdlib`Real`realAddNegThm];
    cong = rAddRightCong[x, neg];
    zero = HOL`Bool`SPEC[x, HOL`Stdlib`Real`realAddZeroThm];
    TRANS[assoc, TRANS[cong, zero]]
  ];

realLeAddCancelThm =
  Module[{aV, bV, cV, hAB, hAdd, bwd, fwdRaw, eqL, eqR, fwd, iffTh},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; cV = mkVar["c", realTy];
    hAB = ASSUME[rLe[aV, bV]];
    bwd = HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLeAddMonoThm, {aV, bV, cV}], hAB];
    hAdd = ASSUME[rLe[rAdd[aV, cV], rAdd[bV, cV]]];
    fwdRaw = leAddMono[hAdd, rNeg[cV]];
    eqL = addNegCancelEq[aV, cV];
    eqR = addNegCancelEq[bV, cV];
    fwd = leCong[eqL, eqR, fwdRaw];
    iffTh = HOL`Kernel`DEDUCTANTISYM[bwd, fwd];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, iffTh]]]
  ];

realLtAddCancelThm =
  Module[{aV, bV, cV, hAB, hAdd, bwd, fwdRaw, eqL, eqR, fwd, iffTh},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; cV = mkVar["c", realTy];
    hAB = ASSUME[rLt[aV, bV]];
    bwd = HOL`Bool`MP[
      specAll[HOL`Stdlib`Real`realLtAddMonoThm, {aV, bV, cV}], hAB];
    hAdd = ASSUME[rLt[rAdd[aV, cV], rAdd[bV, cV]]];
    fwdRaw = ltAddMono[hAdd, rNeg[cV]];
    eqL = addNegCancelEq[aV, cV];
    eqR = addNegCancelEq[bV, cV];
    fwd = ltCong[eqL, eqR, fwdRaw];
    iffTh = HOL`Kernel`DEDUCTANTISYM[bwd, fwd];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, iffTh]]]
  ];

HOL`Auto`RealArith`rnumNe[m_Integer, n_Integer] /; m >= 0 && n >= 0 && m =!= n :=
  HOL`Auto`RealArith`rnumNe[m, n] =
    Module[{mT, nT, lo, hi, loT, hiT, hEq, iff, leBoth, hiLeLo, ltLoHi,
            notHiLeLo, ff},
      mT = rnumTm[m]; nT = rnumTm[n];
      lo = Min[m, n]; hi = Max[m, n]; loT = rnumTm[lo]; hiT = rnumTm[hi];
      hEq = ASSUME[mkEq[mT, nT]];
      iff = specAll[realEqIffLeLeThm, {mT, nT}];
      leBoth = EQMP[iff, hEq];
      hiLeLo = If[m > n, HOL`Bool`CONJUNCT1[leBoth],
        HOL`Bool`CONJUNCT2[leBoth]];
      ltLoHi = HOL`Auto`RealArith`rnumLt[lo, hi];
      notHiLeLo = EQMP[ltNotLeAt[loT, hiT], ltLoHi];
      ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notHiLeLo], hiLeLo];
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[mT, nT], ff]]
    ];
HOL`Auto`RealArith`rnumNe[m_, n_] :=
  groundError["rnumNe", <|"m" -> m, "n" -> n|>];

rnumDivFold[m_Integer, d_Integer] /; m >= 0 && d >= 1 && Mod[m, d] === 0 :=
  rnumDivFold[m, d] =
    Module[{q, qT, dT, mT, invD, mulEq, step1, assoc, invLaw, step3, one},
      q = Quotient[m, d];
      qT = rnumTm[q]; dT = rnumTm[d]; mT = rnumTm[m]; invD = rInv[dT];
      mulEq = HOL`Auto`RealArith`rnumMul[q, d];
      step1 = HOL`Equal`APTHM[
        HOL`Equal`APTERM[HOL`Stdlib`Real`realMulConst[],
          HOL`Equal`SYM[mulEq]], invD];
      assoc = rMulAssoc[qT, dT, invD];
      invLaw = HOL`Bool`MP[HOL`Bool`SPEC[dT, HOL`Stdlib`Real`realMulInvThm],
        HOL`Auto`RealArith`rnumNe[d, 0]];
      step3 = rMulRightCong[qT, invLaw];
      one = HOL`Bool`SPEC[qT, HOL`Stdlib`Real`realMulOneThm];
      TRANS[step1, TRANS[assoc, TRANS[step3, one]]]
    ];
rnumDivFold[m_, d_] :=
  HOL`Error`holError["realarith-ground", "arguments out of domain",
    <|"fn" -> "rnumDivFold", "m" -> m, "d" -> d|>];

natLitQ[const["0", _]] := True;
natLitQ[comb[const["SUC", _], n_]] := natLitQ[n];
natLitQ[_] := False;

natLitValue[const["0", _]] := 0;
natLitValue[comb[const["SUC", _], n_]] := 1 + natLitValue[n];

rnumLitQ[comb[const["&ℝ", _], comb[const["&ℚ", _],
    comb[const["&ℤ", _], n_]]]] := natLitQ[n];
rnumLitQ[_] := False;

rnumLitValue[comb[const["&ℝ", _], comb[const["&ℚ", _],
    comb[const["&ℤ", _], n_]]]] := natLitValue[n];

realAddTermQ[comb[comb[const["realAdd", _], _], _]] := True;
realAddTermQ[_] := False;
realMulTermQ[comb[comb[const["realMul", _], _], _]] := True;
realMulTermQ[_] := False;
realNegTermQ[comb[const["realNeg", _], _]] := True;
realNegTermQ[_] := False;
realInvTermQ[comb[const["realInv", _], _]] := True;
realInvTermQ[_] := False;
realLeTermQ[comb[comb[const["realLe", _], _], _]] := True;
realLeTermQ[_] := False;
realLtTermQ[comb[comb[const["realLt", _], _], _]] := True;
realLtTermQ[_] := False;

rFilterZeros[a_Association] := KeySelect[a, a[#] =!= 0 &];

rLinZero[] := rLin[0, <||>, <||>];
rLinConst[c_] := rLin[c, <||>, <||>];
rLinAtom[t_] := Module[{k = stripOrigin[t]}, rLin[0, <|k -> 1|>, <|k -> t|>]];

rLinAdd[rLin[c1_, v1_Association, e1_Association],
        rLin[c2_, v2_Association, e2_Association]] :=
  rLin[c1 + c2, rFilterZeros[Merge[{v1, v2}, Total]], Join[e1, e2]];

rLinScale[k_, rLin[c_, vs_Association, env_Association]] :=
  If[k === 0, rLinZero[],
    rLin[k*c, rFilterZeros[Association[KeyValueMap[#1 -> k*#2 &, vs]]], env]];

rLinIsConst[rLin[_, vs_Association, _Association]] := Length[vs] === 0;
rLinConstValue[rLin[c_, _Association, _Association]] := c;
rLinIsZero[rLin[c_, vs_Association, _Association]] := c === 0 && Length[vs] === 0;

rLinEnvTerm[rLin[_, _Association, env_Association], k_] := env[k];

rLinRecordData[rLin[c_, vs_Association, env_Association]] := {c, vs, env};

parseLinR[t_] := parseLinRAux[t];

parseLinRAux[t_ /; rnumLitQ[t]] := rLinConst[rnumLitValue[t]];

parseLinRAux[t_ /; realAddTermQ[t]] :=
  rLinAdd[parseLinRAux[t[[1, 2]]], parseLinRAux[t[[2]]]];

parseLinRAux[t_ /; realNegTermQ[t]] :=
  rLinScale[-1, parseLinRAux[t[[2]]]];

parseLinRAux[t_ /; realMulTermQ[t]] :=
  Module[{a, b, ar, br},
    a = t[[1, 2]]; b = t[[2]];
    ar = parseLinRAux[a]; br = parseLinRAux[b];
    Which[
      rLinIsConst[ar], rLinScale[rLinConstValue[ar], br],
      rLinIsConst[br], rLinScale[rLinConstValue[br], ar],
      True, rLinAtom[t]
    ]
  ];

parseLinRAux[t_ /; realInvTermQ[t]] :=
  Module[{r, c},
    r = parseLinRAux[t[[2]]];
    If[rLinIsConst[r] && rLinConstValue[r] =!= 0,
      c = rLinConstValue[r];
      rLinConst[1/c],
      rLinAtom[t]]
  ];

parseLinRAux[t_] :=
  If[HOL`Terms`typeOf[t] === realTy,
    rLinAtom[t],
    HOL`Error`holError["realarith-norm",
      "term is not a real linear expression", <|"got" -> t|>]];

positiveScalarTerm[r_] :=
  Module[{p, q},
    Which[
      r === 0, rnumTm[0],
      IntegerQ[r], rnumTm[r],
      True,
        p = Numerator[r]; q = Denominator[r];
        rMul[rnumTm[p], rInv[rnumTm[q]]]
    ]
  ];

scalarTerm[r_] :=
  Which[
    r >= 0, positiveScalarTerm[r],
    True, rNeg[positiveScalarTerm[-r]]
  ];

summandTerm[c_, x_] :=
  Which[
    c > 0, rMul[positiveScalarTerm[c], x],
    c < 0, rNeg[rMul[positiveScalarTerm[-c], x]],
    True, rnumTm[0]
  ];

varKeysSorted[vs_Association] := Sort[Keys[vs], Order[#1, #2] === 1 &];

varListTerm[{}, _Association, _Association] := rnumTm[0];
varListTerm[keys_List, vs_Association, env_Association] :=
  Module[{terms},
    terms = (summandTerm[vs[#], env[#]] &) /@ keys;
    Fold[rAdd[#2, #1] &, Last[terms], Reverse[Most[terms]]]
  ];

buildItems[items_List] :=
  If[Length[items] === 1, First[items],
    Fold[rAdd[#2, #1] &, Last[items], Reverse[Most[items]]]];

integerLinQ[rLin[c_, vs_Association, _Association]] :=
  IntegerQ[c] && And @@ (IntegerQ /@ Values[vs]);

buildLinRAny[rLin[c_, vs_Association, env_Association]] :=
  Module[{keys, terms},
    keys = varKeysSorted[vs];
    If[keys === {}, Return[scalarTerm[c]]];
    terms = Prepend[(summandTerm[vs[#], env[#]] &) /@ keys, scalarTerm[c]];
    buildItems[terms]
  ];

buildLinR[rLin[c_, vs_Association, env_Association]] :=
  Module[{keys, terms},
    If[! integerLinQ[rLin[c, vs, env]],
      HOL`Error`holError["realarith-norm",
        "linear form has non-integer totals", <|"record" -> rLin[c, vs, env]|>]];
    keys = varKeysSorted[vs];
    If[keys === {}, Return[scalarTerm[c]]];
    terms = Prepend[(summandTerm[vs[#], env[#]] &) /@ keys, scalarTerm[c]];
    buildItems[terms]
  ];

scalarNegEq[r_] :=
  scalarNegEq[r] =
    Which[
      r === 0, HOL`Stdlib`Real`realNegZeroThm,
      r > 0, REFL[rNeg[positiveScalarTerm[r]]],
      True, HOL`Bool`SPEC[positiveScalarTerm[-r], HOL`Stdlib`Real`realNegNegThm]
    ];

scalarAddPositiveSameDenEq[r_, s_] :=
  Module[{p, q, n, invQ, pT, nT, sumT, e1, e2, dist, addEq, e4, e5, div},
    p = Numerator[r]; n = Numerator[s]; q = Denominator[r];
    invQ = rInv[rnumTm[q]]; pT = rnumTm[p]; nT = rnumTm[n]; sumT = rnumTm[p + n];
    e1 = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], rMulComm[pT, invQ]],
      rMulComm[nT, invQ]];
    dist = HOL`Equal`SYM[rMulDistrib[invQ, pT, nT]];
    addEq = HOL`Auto`RealArith`rnumAdd[p, n];
    e4 = rMulRightCong[invQ, addEq];
    e5 = rMulComm[invQ, sumT];
    If[Mod[p + n, q] === 0,
      div = rnumDivFold[p + n, q],
      If[Denominator[r + s] =!= q || Numerator[r + s] =!= p + n,
        HOL`Error`holError["realarith-norm",
          "unsupported scalar addition", <|"left" -> r, "right" -> s|>]];
      div = REFL[rMul[sumT, invQ]]
    ];
    TRANS[e1, TRANS[dist, TRANS[e4, TRANS[e5, div]]]]
  ];

scalarAddIntPosNegEq[a_Integer, b_Integer] /; a >= 0 && b >= 0 :=
  Module[{k, addEq, e1, assoc, neg, e4, zero},
    Which[
      a === 0, zeroAddEq[rNeg[rnumTm[b]]],
      b === 0, HOL`Bool`SPEC[rnumTm[a], HOL`Stdlib`Real`realAddZeroThm],
      a === b, HOL`Bool`SPEC[rnumTm[a], HOL`Stdlib`Real`realAddNegThm],
      a > b,
        k = a - b;
        addEq = HOL`Auto`RealArith`rnumAdd[k, b];
        e1 = rAddLeftCong[HOL`Equal`SYM[addEq], rNeg[rnumTm[b]]];
        assoc = rAddAssoc[rnumTm[k], rnumTm[b], rNeg[rnumTm[b]]];
        neg = HOL`Bool`SPEC[rnumTm[b], HOL`Stdlib`Real`realAddNegThm];
        e4 = rAddRightCong[rnumTm[k], neg];
        zero = HOL`Bool`SPEC[rnumTm[k], HOL`Stdlib`Real`realAddZeroThm];
        TRANS[e1, TRANS[assoc, TRANS[e4, zero]]],
      True,
        HOL`Error`holError["realarith-norm",
          "unsupported scalar subtraction", <|"left" -> a, "right" -> b|>]
    ]
  ];

scalarAddEq[r_, s_] :=
  scalarAddEq[r, s] =
    Which[
      r === 0, zeroAddEq[scalarTerm[s]],
      s === 0, HOL`Bool`SPEC[scalarTerm[r], HOL`Stdlib`Real`realAddZeroThm],
      r > 0 && s > 0 && IntegerQ[r] && IntegerQ[s],
        HOL`Auto`RealArith`rnumAdd[r, s],
      r < 0 && s < 0 && IntegerQ[-r] && IntegerQ[-s],
        Module[{a = -r, b = -s, negAdd, addEq},
          negAdd = HOL`Equal`SYM[specAll[HOL`Stdlib`Real`realNegAddThm,
            {rnumTm[a], rnumTm[b]}]];
          addEq = HOL`Auto`RealArith`rnumAdd[a, b];
          TRANS[negAdd, rNegCong[addEq]]
        ],
      r >= 0 && s < 0 && IntegerQ[r] && IntegerQ[-s],
        scalarAddIntPosNegEq[r, -s],
      r < 0 && s >= 0 && IntegerQ[-r] && IntegerQ[s],
        TRANS[rAddComm[scalarTerm[r], scalarTerm[s]], scalarAddEq[s, r]],
      r > 0 && s > 0 && ! IntegerQ[r] && ! IntegerQ[s] &&
          Denominator[r] === Denominator[s],
        scalarAddPositiveSameDenEq[r, s],
      True,
        HOL`Error`holError["realarith-norm",
          "unsupported scalar addition", <|"left" -> r, "right" -> s|>]
    ];

positiveScalarMulEq[r_, s_] :=
  Module[{p, q, prod, assoc, mulEq, rw, div},
    Which[
      IntegerQ[r] && IntegerQ[s],
        HOL`Auto`RealArith`rnumMul[r, s],
      IntegerQ[r] && ! IntegerQ[s],
        p = Numerator[s]; q = Denominator[s]; prod = r*p;
        assoc = HOL`Equal`SYM[rMulAssoc[rnumTm[r], rnumTm[p], rInv[rnumTm[q]]]];
        mulEq = HOL`Auto`RealArith`rnumMul[r, p];
        rw = rMulLeftCong[mulEq, rInv[rnumTm[q]]];
        div = Which[
          Mod[prod, q] === 0, rnumDivFold[prod, q],
          Denominator[r*s] === q && Numerator[r*s] === prod,
            REFL[rMul[rnumTm[prod], rInv[rnumTm[q]]]],
          True,
            HOL`Error`holError["realarith-norm",
              "unsupported scalar multiplication", <|"left" -> r, "right" -> s|>]
        ];
        TRANS[assoc, TRANS[rw, div]],
      ! IntegerQ[r] && IntegerQ[s],
        TRANS[rMulComm[scalarTerm[r], scalarTerm[s]], positiveScalarMulEq[s, r]],
      True,
        HOL`Error`holError["realarith-norm",
          "unsupported scalar multiplication", <|"left" -> r, "right" -> s|>]
    ]
  ];

scalarMulEq[r_, s_] :=
  scalarMulEq[r, s] =
    Which[
      r === 0,
        TRANS[rMulComm[rnumTm[0], scalarTerm[s]],
          HOL`Bool`SPEC[scalarTerm[s], HOL`Stdlib`Real`realMulZeroThm]],
      s === 0,
        HOL`Bool`SPEC[scalarTerm[r], HOL`Stdlib`Real`realMulZeroThm],
      r > 0 && s > 0, positiveScalarMulEq[r, s],
      r < 0 && s > 0,
        Module[{pos = positiveScalarMulEq[-r, s], negStep},
          negStep = specAll[HOL`Stdlib`Real`realMulNegLeftThm,
            {positiveScalarTerm[-r], scalarTerm[s]}];
          TRANS[negStep, rNegCong[pos]]
        ],
      r > 0 && s < 0,
        Module[{pos = positiveScalarMulEq[r, -s], negStep},
          negStep = specAll[HOL`Stdlib`Real`realMulNegRightThm,
            {scalarTerm[r], positiveScalarTerm[-s]}];
          TRANS[negStep, rNegCong[pos]]
        ],
      r < 0 && s < 0,
        Module[{a = positiveScalarTerm[-r], b = positiveScalarTerm[-s],
                n1, n2, pos, nn},
          n1 = specAll[HOL`Stdlib`Real`realMulNegLeftThm, {a, rNeg[b]}];
          n2 = rNegCong[specAll[HOL`Stdlib`Real`realMulNegRightThm, {a, b}]];
          nn = HOL`Bool`SPEC[rMul[a, b], HOL`Stdlib`Real`realNegNegThm];
          pos = positiveScalarMulEq[-r, -s];
          TRANS[n1, TRANS[n2, TRANS[nn, pos]]]
        ]
    ];

scalarInvEq[r_] :=
  scalarInvEq[r] =
    Which[
      IntegerQ[r] && r > 1,
        HOL`Equal`SYM[oneMulEq[rInv[rnumTm[r]]]],
      r === 1,
        Module[{invLaw, oneMul},
          invLaw = HOL`Bool`MP[HOL`Bool`SPEC[rnumTm[1],
            HOL`Stdlib`Real`realMulInvThm], HOL`Auto`RealArith`rnumNe[1, 0]];
          oneMul = oneMulEq[rInv[rnumTm[1]]];
          TRANS[HOL`Equal`SYM[oneMul], invLaw]
        ],
      True,
        HOL`Error`holError["realarith-norm",
          "unsupported scalar inverse", <|"scalar" -> r|>]
    ];

summandToMulEq[c_, x_] :=
  Which[
    c > 0, REFL[summandTerm[c, x]],
    c < 0, HOL`Equal`SYM[specAll[HOL`Stdlib`Real`realMulNegLeftThm,
      {positiveScalarTerm[-c], x}]],
    True, HOL`Equal`SYM[
      TRANS[rMulComm[scalarTerm[0], x],
        HOL`Bool`SPEC[x, HOL`Stdlib`Real`realMulZeroThm]]]
  ];

mulToSummandEq[c_, x_] :=
  Which[
    c > 0, REFL[rMul[scalarTerm[c], x]],
    c < 0, specAll[HOL`Stdlib`Real`realMulNegLeftThm,
      {positiveScalarTerm[-c], x}],
    True, TRANS[rMulComm[scalarTerm[0], x],
      HOL`Bool`SPEC[x, HOL`Stdlib`Real`realMulZeroThm]]
  ];

mergeSummandEq[c_, d_, x_] :=
  Module[{sc, sd, e1, e2, dist, addEq, e5, commBack, toSum},
    sc = scalarTerm[c]; sd = scalarTerm[d];
    e1 = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], summandToMulEq[c, x]],
      summandToMulEq[d, x]];
    e2 = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], rMulComm[sc, x]],
      rMulComm[sd, x]];
    dist = HOL`Equal`SYM[rMulDistrib[x, sc, sd]];
    addEq = scalarAddEq[c, d];
    e5 = rMulRightCong[x, addEq];
    commBack = rMulComm[x, scalarTerm[c + d]];
    toSum = mulToSummandEq[c + d, x];
    TRANS[e1, TRANS[e2, TRANS[dist, TRANS[e5, TRANS[commBack, toSum]]]]]
  ];

monoBeforeQ[k1_, k2_] := Order[k1, k2] === 1;

insertVarIntoEq[key_, coef_, x_, keys_List, vs_Association, env_Association] :=
  Module[{mono, head, rest, restTerm, headTerm, hcoef, hx, merge, assoc, sub,
          lc, cong, newRestVs, newKeys, sumCoef, target},
    mono = summandTerm[coef, x];
    If[keys === {},
      Return[HOL`Bool`SPEC[mono, HOL`Stdlib`Real`realAddZeroThm]]];
    head = First[keys]; rest = Rest[keys];
    headTerm = summandTerm[vs[head], env[head]];
    hcoef = vs[head]; hx = env[head];
    If[rest === {},
      Which[
        key === head,
          mergeSummandEq[coef, hcoef, x],
        monoBeforeQ[key, head],
          REFL[rAdd[mono, headTerm]],
        True,
          rAddComm[mono, headTerm]
      ],
      restTerm = varListTerm[rest, vs, env];
      Which[
        key === head,
          merge = mergeSummandEq[coef, hcoef, x];
          assoc = HOL`Equal`SYM[rAddAssoc[mono, headTerm, restTerm]];
          sumCoef = coef + hcoef;
          If[sumCoef === 0,
            TRANS[assoc, TRANS[rAddLeftCong[merge, restTerm], zeroAddEq[restTerm]]],
            TRANS[assoc, rAddLeftCong[merge, restTerm]]
          ],
        monoBeforeQ[key, head],
          REFL[rAdd[mono, varListTerm[keys, vs, env]]],
        True,
          lc = addLeftCommEq[mono, headTerm, restTerm];
          sub = insertVarIntoEq[key, coef, x, rest, vs, env];
          cong = rAddRightCong[headTerm, sub];
          newRestVs = rFilterZeros[Merge[{KeyTake[vs, rest], <|key -> coef|>}, Total]];
          newKeys = varKeysSorted[newRestVs];
          target = If[newKeys === {}, rnumTm[0], varListTerm[newKeys, newRestVs, Join[env, <|key -> x|>]]];
          If[target === rnumTm[0],
            TRANS[lc, TRANS[cong, HOL`Bool`SPEC[headTerm, HOL`Stdlib`Real`realAddZeroThm]]],
            TRANS[lc, cong]
          ]
      ]
    ]
  ];

insertConstEq[c_, rec : rLin[mc_, vs_Association, env_Association]] :=
  Module[{buildM, keys, rest, assoc, addEq},
    buildM = buildLinRAny[rec];
    If[c === 0, Return[zeroAddEq[buildM]]];
    keys = varKeysSorted[vs];
    If[keys === {}, Return[scalarAddEq[c, mc]]];
    rest = varListTerm[keys, vs, env];
    assoc = HOL`Equal`SYM[rAddAssoc[scalarTerm[c], scalarTerm[mc], rest]];
    addEq = scalarAddEq[c, mc];
    TRANS[assoc, rAddLeftCong[addEq, rest]]
  ];

insertVarEq[key_, coef_, x_, rec : rLin[mc_, vs_Association, env_Association]] :=
  Module[{mono, keys, buildM, leftComm, sub, cong, newVs, newKeys, newEnv,
          rest, target},
    mono = summandTerm[coef, x];
    buildM = buildLinRAny[rec]; keys = varKeysSorted[vs];
    If[keys === {},
      Return[TRANS[rAddComm[mono, buildM],
        If[coef === 0, HOL`Equal`SYM[zeroAddEq[buildM]], REFL[rAdd[buildM, mono]]]]]];
    rest = varListTerm[keys, vs, env];
    leftComm = addLeftCommEq[mono, scalarTerm[mc], rest];
    sub = insertVarIntoEq[key, coef, x, keys, vs, env];
    cong = rAddRightCong[scalarTerm[mc], sub];
    newVs = rFilterZeros[Merge[{vs, <|key -> coef|>}, Total]];
    newKeys = varKeysSorted[newVs]; newEnv = Join[env, <|key -> x|>];
    target = If[newKeys === {}, scalarTerm[mc],
      rAdd[scalarTerm[mc], varListTerm[newKeys, newVs, newEnv]]];
    If[newKeys === {},
      TRANS[leftComm, TRANS[cong,
        HOL`Bool`SPEC[scalarTerm[mc], HOL`Stdlib`Real`realAddZeroThm]]],
      TRANS[leftComm, cong]
    ]
  ];

linFromItem["const", c_, _] := rLinConst[c];
linFromItem["var", {k_, c_, x_}, _] := rLin[0, <|k -> c|>, <|k -> x|>];

recordItems[rLin[c_, vs_Association, env_Association]] :=
  Join[{{"const", c, scalarTerm[c]}},
    ({"var", {#, vs[#], env[#]}, summandTerm[vs[#], env[#]]} &) /@
      varKeysSorted[vs]];

itemsRecord[items_List] :=
  Fold[rLinAdd[#1, #2] &, rLinZero[],
    (If[#[[1]] === "const", rLinConst[#[[2]]],
       rLin[0, <|#[[2, 1]] -> #[[2, 2]]|>, <|#[[2, 1]] -> #[[2, 3]]|>]] &) /@ items];

caAddItems[items_List, mrec_] :=
  Module[{first, rest, fs, restRec, step1, step2, step3, insert, afterRest},
    first = First[items]; fs = first[[3]]; rest = Rest[items];
    insert[target_] := If[first[[1]] === "const",
      insertConstEq[first[[2]], target],
      insertVarEq[first[[2, 1]], first[[2, 2]], first[[2, 3]], target]];
    If[rest === {},
      insert[mrec],
      restRec = itemsRecord[rest];
      step1 = rAddAssoc[fs, buildItems[rest[[All, 3]]], buildLinRAny[mrec]];
      step2 = caAddItems[rest, mrec];
      step3 = rAddRightCong[fs, step2];
      afterRest = rLinAdd[restRec, mrec];
      TRANS[step1, TRANS[step3, insert[afterRest]]]
    ]
  ];

caAdd[r1_, r2_] :=
  Which[
    rLinIsZero[r1], zeroAddEq[buildLinRAny[r2]],
    rLinIsZero[r2], HOL`Bool`SPEC[buildLinRAny[r1], HOL`Stdlib`Real`realAddZeroThm],
    True, caAddItems[recordItems[r1], r2]
  ];

scaleSummandEq[w_, coef_, x_] :=
  Module[{summEq, assoc, mulEq, toSum},
    summEq = rMulRightCong[scalarTerm[w], summandToMulEq[coef, x]];
    assoc = HOL`Equal`SYM[rMulAssoc[scalarTerm[w], scalarTerm[coef], x]];
    mulEq = scalarMulEq[w, coef];
    toSum = mulToSummandEq[w*coef, x];
    TRANS[summEq, TRANS[assoc, TRANS[rMulLeftCong[mulEq, x], toSum]]]
  ];

scaleVarListEq[w_, keys_List, vs_Association, env_Association] :=
  Module[{head, rest, headTerm, restTerm, dist, hEq, rEq, cong},
    If[keys === {},
      Return[HOL`Bool`SPEC[scalarTerm[w], HOL`Stdlib`Real`realMulZeroThm]]];
    head = First[keys]; rest = Rest[keys]; headTerm = summandTerm[vs[head], env[head]];
    If[rest === {}, Return[scaleSummandEq[w, vs[head], env[head]]]];
    restTerm = varListTerm[rest, vs, env];
    dist = rMulDistrib[scalarTerm[w], headTerm, restTerm];
    hEq = scaleSummandEq[w, vs[head], env[head]];
    rEq = scaleVarListEq[w, rest, vs, env];
    cong = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], hEq], rEq];
    TRANS[dist, cong]
  ];

scaleCanonicalEq[w_, rec : rLin[c_, vs_Association, env_Association]] :=
  Module[{build, keys, rest, dist, cEq, vEq, cong, scaled, scaledKeys},
    build = buildLinRAny[rec];
    If[w === 0,
      Return[TRANS[rMulComm[rnumTm[0], build],
        HOL`Bool`SPEC[build, HOL`Stdlib`Real`realMulZeroThm]]]];
    keys = varKeysSorted[vs];
    If[keys === {}, Return[scalarMulEq[w, c]]];
    rest = varListTerm[keys, vs, env];
    dist = rMulDistrib[scalarTerm[w], scalarTerm[c], rest];
    cEq = scalarMulEq[w, c];
    vEq = scaleVarListEq[w, keys, vs, env];
    cong = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], cEq], vEq];
    scaled = rLinScale[w, rec];
    scaledKeys = varKeysSorted[scaled[[2]]];
    If[scaledKeys === {},
      TRANS[dist, TRANS[cong,
        HOL`Bool`SPEC[scalarTerm[w*c], HOL`Stdlib`Real`realAddZeroThm]]],
      TRANS[dist, cong]
    ]
  ];

negAsMulNegOneEq[x_] :=
  Module[{mulNeg, oneMul},
    mulNeg = specAll[HOL`Stdlib`Real`realMulNegLeftThm, {rnumTm[1], x}];
    oneMul = oneMulEq[x];
    HOL`Equal`SYM[TRANS[mulNeg, rNegCong[oneMul]]]
  ];

atomNormEq[t_] :=
  Module[{oneMul, zeroAdd},
    oneMul = HOL`Equal`SYM[oneMulEq[t]];
    zeroAdd = HOL`Equal`SYM[zeroAddEq[rMul[rnumTm[1], t]]];
    TRANS[oneMul, zeroAdd]
  ];

normLinRAux[t_ /; rnumLitQ[t]] := {rLinConst[rnumLitValue[t]], REFL[t]};

normLinRAux[t_ /; realAddTermQ[t]] :=
  Module[{a, b, ar, br, thA, thB, cong, addEq, rec},
    a = t[[1, 2]]; b = t[[2]];
    {ar, thA} = normLinRAux[a]; {br, thB} = normLinRAux[b];
    cong = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realAddConst[], thA], thB];
    addEq = caAdd[ar, br]; rec = rLinAdd[ar, br];
    {rec, TRANS[cong, addEq]}
  ];

normLinRAux[t_ /; realNegTermQ[t]] :=
  Module[{r, th, build, cong, negMul, scale, rec},
    {r, th} = normLinRAux[t[[2]]];
    build = buildLinRAny[r];
    cong = rNegCong[th];
    negMul = negAsMulNegOneEq[build];
    scale = scaleCanonicalEq[-1, r];
    rec = rLinScale[-1, r];
    {rec, TRANS[cong, TRANS[negMul, scale]]}
  ];

normLinRAux[t_ /; realInvTermQ[t]] :=
  Module[{r, th, c, cong, invEq, rec},
    {r, th} = normLinRAux[t[[2]]];
    If[! rLinIsConst[r] || rLinConstValue[r] === 0,
      Return[{rLinAtom[t], atomNormEq[t]}]];
    c = rLinConstValue[r];
    cong = HOL`Equal`APTERM[HOL`Stdlib`Real`realInvConst[], th];
    invEq = scalarInvEq[c];
    rec = rLinConst[1/c];
    {rec, TRANS[cong, invEq]}
  ];

normLinRAux[t_ /; realMulTermQ[t]] :=
  Module[{a, b, arRaw, brRaw, ar, br, thA, thB, cong, comm, scale, rec},
    a = t[[1, 2]]; b = t[[2]];
    arRaw = parseLinR[a]; brRaw = parseLinR[b];
    If[! rLinIsConst[arRaw] && ! rLinIsConst[brRaw],
      Return[{rLinAtom[t], atomNormEq[t]}]];
    {ar, thA} = normLinRAux[a]; {br, thB} = normLinRAux[b];
    cong = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Real`realMulConst[], thA], thB];
    If[rLinIsConst[ar],
      rec = rLinScale[rLinConstValue[ar], br];
      scale = scaleCanonicalEq[rLinConstValue[ar], br];
      {rec, TRANS[cong, scale]},
      rec = rLinScale[rLinConstValue[br], ar];
      comm = rMulComm[buildLinRAny[ar], buildLinRAny[br]];
      scale = scaleCanonicalEq[rLinConstValue[br], ar];
      {rec, TRANS[cong, TRANS[comm, scale]]}
    ]
  ];

normLinRAux[t_] :=
  If[HOL`Terms`typeOf[t] === realTy,
    {rLinAtom[t], atomNormEq[t]},
    HOL`Error`holError["realarith-norm",
      "term is not a real linear expression", <|"got" -> t|>]];

HOL`Auto`RealArith`realLinNormConv[t_] :=
  Module[{rec, target, got, th},
    rec = parseLinR[t];
    target = buildLinR[rec];
    {got, th} = normLinRAux[t];
    If[buildLinRAny[got] =!= target,
      HOL`Error`holError["realarith-norm",
        "internal normalizer target mismatch", <|"term" -> t|>]];
    th
  ];

denominatorsOf[rLin[c_, vs_Association, _Association]] :=
  Denominator /@ Join[{c}, Values[vs]];

clearDenominatorFactor[rs_List] := Apply[LCM, Join[{1}, Flatten[denominatorsOf /@ rs]]];

negativePart[rLin[c_, vs_Association, env_Association]] :=
  Module[{nc, nvs},
    nc = If[c < 0, -c, 0];
    nvs = Association[KeyValueMap[If[#2 < 0, #1 -> -#2, Nothing] &, vs]];
    rLin[nc, nvs, env]
  ];

hasRealNegQ[comb[const["realNeg", _], _]] := True;
hasRealNegQ[comb[f_, x_]] := hasRealNegQ[f] || hasRealNegQ[x];
hasRealNegQ[abs[_, b_, _]] := hasRealNegQ[b];
hasRealNegQ[_] := False;

relCongEq[rel_, eqL_, eqR_] :=
  HOL`Kernel`MKCOMB[HOL`Equal`APTERM[rel, eqL], eqR];

HOL`Auto`RealArith`realAtomNormConv[atom_] :=
  Module[{isLe, rel, cancelThm, mulCancelThm, s, t, rs, rt, m, mT, th1,
          curS, curT, scaledS, scaledT, negRec, bTerm, th2, leftTerm,
          rightTerm, eqL, eqR, th3, outL, outR},
    isLe = realLeTermQ[atom];
    If[! isLe && ! realLtTermQ[atom],
      HOL`Error`holError["realarith-norm",
        "expected realLe or realLt atom", <|"got" -> atom|>]];
    rel = If[isLe, HOL`Stdlib`Real`realLeConst[], HOL`Stdlib`Real`realLtConst[]];
    cancelThm = If[isLe, realLeAddCancelThm, realLtAddCancelThm];
    mulCancelThm = If[isLe, realLeMulCancelThm, realLtMulCancelThm];
    s = atom[[1, 2]]; t = atom[[2]];
    rs = parseLinR[s]; rt = parseLinR[t];
    m = clearDenominatorFactor[{rs, rt}]; mT = rnumTm[m];
    If[m > 1,
      th1 = HOL`Equal`SYM[HOL`Bool`MP[
        specAll[mulCancelThm, {mT, s, t}], HOL`Auto`RealArith`rnumPos[m]]];
      curS = rMul[mT, s]; curT = rMul[mT, t],
      th1 = REFL[atom]; curS = s; curT = t
    ];
    scaledS = rLinScale[m, rs]; scaledT = rLinScale[m, rt];
    negRec = rLinAdd[negativePart[scaledS], negativePart[scaledT]];
    If[rLinIsZero[negRec],
      th2 = REFL[mkComb[mkComb[rel, curS], curT]];
      leftTerm = curS; rightTerm = curT,
      bTerm = buildLinR[negRec];
      th2 = HOL`Equal`SYM[specAll[cancelThm, {curS, curT, bTerm}]];
      leftTerm = rAdd[curS, bTerm]; rightTerm = rAdd[curT, bTerm]
    ];
    eqL = HOL`Auto`RealArith`realLinNormConv[leftTerm];
    eqR = HOL`Auto`RealArith`realLinNormConv[rightTerm];
    outL = concl[eqL][[2]]; outR = concl[eqR][[2]];
    If[hasRealNegQ[outL] || hasRealNegQ[outR],
      HOL`Error`holError["realarith-norm",
        "atom normalization produced a signed side", <|"atom" -> atom|>]];
    th3 = relCongEq[rel, eqL, eqR];
    TRANS[th1, TRANS[th2, th3]]
  ];

End[];
EndPackage[];
