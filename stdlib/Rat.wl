(* M7-6 / stdlib/Rat.wl — ℚ via canonical reduced fractions.

   rat is carved from int × num (numerator : int, denominator : num,
   the denominator a *positive* natural) by the predicate

       RAT_REP = λp. ¬(SND p = 0) ∧ gcd (intNatAbs (FST p)) (SND p) = SUC 0,

   i.e. canonical reduced fractions: positive denominator, numerator and
   denominator coprime (gcd of |numerator| and denominator is 1). Because
   the carve keeps only canonical representatives, kernel `=` on rat IS
   rational equality — no setoid. Mirrors the Int.wl playbook
   (canonEquiv / canonInj / canonRespects) one tower up.

   Stage a (this file, so far): the helper number-theory lemmas, the
   magnitude map intNatAbs : int → num, RAT_REP, the carve, and the
   witness RAT_REP (&ℤ 0, SUC 0) (= the rational 0 = 0/1).

   NB: dividesZeroImpZeroThm / dividesOneThm / gcdOneRightThm are pure ℕ
   facts whose proper home is Num.wl; kept here during construction to
   avoid snapshot churn, migrate when stabilizing. *)

BeginPackage["HOL`Stdlib`Rat`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`Int`", "HOL`Auto`Arith`"
}];

dividesZeroImpZeroThm::usage = "dividesZeroImpZeroThm — ⊢ ∀n. divides 0 n ⇒ n = 0.";
dividesOneThm::usage         = "dividesOneThm — ⊢ ∀d. divides d (SUC 0) ⇒ d = SUC 0.";
gcdOneRightThm::usage        = "gcdOneRightThm — ⊢ ∀a. gcd a (SUC 0) = SUC 0.";

intNatAbsConst::usage  = "intNatAbsConst[] — intNatAbs : int → num, |z| as a natural = FST(REP_int z) + SND(REP_int z).";
intNatAbsDefThm::usage = "intNatAbsDefThm — ⊢ intNatAbs = (λz. FST (REP_int z) + SND (REP_int z)).";
intNatAbsZeroThm::usage = "intNatAbsZeroThm — ⊢ intNatAbs (&ℤ 0) = 0.";

ratRepConst::usage     = "ratRepConst[] — RAT_REP : int × num → bool, the carving predicate.";
ratRepDefThm::usage    = "ratRepDefThm — ⊢ RAT_REP = (λp. ¬(SND p = 0) ∧ gcd (intNatAbs (FST p)) (SND p) = SUC 0).";
ratRepWitnessThm::usage = "ratRepWitnessThm — ⊢ RAT_REP (&ℤ 0, SUC 0). Witness for the type definition (the rational 0/1).";

absRatConst::usage = "absRatConst[] — ABS_rat : int × num → rat.";
repRatConst::usage = "repRatConst[] — REP_rat : rat → int × num.";
absRepRatThm::usage = "absRepRatThm — ⊢ ABS_rat (REP_rat q) = q.";
repAbsRatThm::usage = "repAbsRatThm — ⊢ RAT_REP r = (REP_rat (ABS_rat r) = r).";

ratRepOneDenomThm::usage = "ratRepOneDenomThm — ⊢ RAT_REP (q, SUC 0) (q free): every q/1 is canonical.";
ratOfIntConst::usage  = "ratOfIntConst[] — &ℚ : int → rat, the embedding q ↦ ABS_rat (q, SUC 0).";
ratOfIntDefThm::usage = "ratOfIntDefThm — ⊢ &ℚ = (λq. ABS_rat (q, SUC 0)).";
repRatOfIntThm::usage = "repRatOfIntThm — ⊢ REP_rat (&ℚ q) = (q, SUC 0) (q free).";
ratOfIntInjThm::usage = "ratOfIntInjThm — ⊢ ∀a b. &ℚ a = &ℚ b ⇒ a = b.";

Begin["`Private`"];

numTy = mkType["num", {}];
intTy = mkType["int", {}];
boolT = mkType["bool", {}];

zeroN[] := HOL`Stdlib`Num`zeroConst[];
sucC[]  := HOL`Stdlib`Num`sucConst[];
oneN[]  := mkComb[sucC[], zeroN[]];           (* SUC 0 *)

plusTm[a_, b_]  := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], a], b];
timesTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`timesConst[], a], b];
dividesTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], a], b];
gcdTm[a_, b_]   := mkComb[mkComb[HOL`Stdlib`Num`gcdConst[], a], b];

andC[] := mkConst["∧", tyFun[boolT, tyFun[boolT, boolT]]];
andTm[a_, b_] := mkComb[mkComb[andC[], a], b];
implC[] := mkConst["⇒", tyFun[boolT, tyFun[boolT, boolT]]];
implTm[a_, b_] := mkComb[mkComb[implC[], a], b];
notC[] := mkConst["¬", tyFun[boolT, boolT]];
notTm[a_] := mkComb[notC[], a];
forallTm[v_, body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[typeOf[v], boolT], boolT]], mkAbs[v, body]];

leqTmL[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];

numPairTy = HOL`Stdlib`Pair`prodTy[numTy, numTy];
fstNN[] := mkConst["FST", tyFun[numPairTy, numTy]];
sndNN[] := mkConst["SND", tyFun[numPairTy, numTy]];

ratPairTy = HOL`Stdlib`Pair`prodTy[intTy, numTy];
ratRepTy  = tyFun[ratPairTy, boolT];
fstIN[] := mkConst["FST", tyFun[ratPairTy, intTy]];
sndIN[] := mkConst["SND", tyFun[ratPairTy, numTy]];
ratPairCons[a_, b_] :=
  mkComb[mkComb[mkConst[",", tyFun[intTy, tyFun[numTy, ratPairTy]]], a], b];

intOfNum[n_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], n];
repInt[z_]   := mkComb[HOL`Stdlib`Int`repIntConst[], z];

(* local copy of FTA/Num's Private unfoldDivides:                     *)
(* ⊢ divides a b = (∃c. b = a * c) *)
unfoldDivides[aT_, bT_] :=
  Module[{ap1, beta1, ap2, beta2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`dividesDefThm, aT];
    beta1 = BETACONV[concl[ap1][[2]]];
    ap2 = HOL`Equal`APTHM[TRANS[ap1, beta1], bT];
    beta2 = BETACONV[concl[ap2][[2]]];
    TRANS[ap2, beta2]
  ];

(* ⊢ a < b = (SUC a ≤ b) *)
unfoldLt[aT_, bT_] :=
  Module[{ap1, beta1, ap2, beta2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, aT];
    beta1 = BETACONV[concl[ap1][[2]]];
    ap2 = HOL`Equal`APTHM[TRANS[ap1, beta1], bT];
    beta2 = BETACONV[concl[ap2][[2]]];
    TRANS[ap2, beta2]
  ];

(* FST/SND on num × num and int × num, by instantiating the Pair lemmas *)
fstNumAt[aT_, bT_] :=
  HOL`Kernel`INST[{mkVar["a", numTy] -> aT, mkVar["b", numTy] -> bT},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`fstPairEqThm]];
sndNumAt[aT_, bT_] :=
  HOL`Kernel`INST[{mkVar["a", numTy] -> aT, mkVar["b", numTy] -> bT},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`sndPairEqThm]];
fstINatAt[aT_, bT_] :=
  HOL`Kernel`INST[{mkVar["a", intTy] -> aT, mkVar["b", numTy] -> bT},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`fstPairEqThm]];
sndINatAt[aT_, bT_] :=
  HOL`Kernel`INST[{mkVar["a", intTy] -> aT, mkVar["b", numTy] -> bT},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`sndPairEqThm]];

(* ============================================================ *)
(* ℕ helper lemmas (proper home Num.wl — migrate later)         *)
(* ============================================================ *)

(* ⊢ ∀n. divides 0 n ⇒ n = 0 *)
dividesZeroImpZeroThm =
  Module[{nV, cV, hyp, exThm, bodyAssume, zc, nEq0, chosen},
    nV = mkVar["n", numTy]; cV = mkVar["c", numTy];
    hyp = ASSUME[dividesTm[zeroN[], nV]];
    exThm = EQMP[unfoldDivides[zeroN[], nV], hyp];             (* ∃c. n = 0 * c *)
    bodyAssume = ASSUME[mkEq[nV, timesTm[zeroN[], cV]]];       (* n = 0 * c *)
    zc = HOL`Bool`SPEC[cV, HOL`Stdlib`Num`timesLeftZeroThm];   (* 0 * c = 0 *)
    nEq0 = TRANS[bodyAssume, zc];                              (* n = 0 *)
    chosen = HOL`Bool`CHOOSE[cV, exThm, nEq0];                 (* ⊢ n = 0 (hyp divides 0 n) *)
    HOL`Bool`GEN[nV, HOL`Bool`DISCH[dividesTm[zeroN[], nV], chosen]]
  ];

oneNotZeroThm = HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`sucNotZeroThm];  (* ¬(SUC 0 = 0) *)

(* ⊢ ∀d. divides d (SUC 0) ⇒ d = SUC 0 *)
(* d ≤ SUC 0 (dividesLeq) and SUC 0 ≤ d (d ≠ 0, since 0 ∤ SUC 0) → leqAntisym. *)
dividesOneThm =
  Module[{dV, hyp, leqStep, dEq0, hSubst, divZeroSuc, falseThm, dischFalse,
          notDEq0, posD, sucLeqD, dd},
    dV = mkVar["d", numTy];
    hyp = ASSUME[dividesTm[dV, oneN[]]];                       (* divides d (SUC 0) *)
    leqStep = HOL`Bool`MP[
      HOL`Bool`MP[
        HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[dV, HOL`Stdlib`Num`dividesLeqThm]],
        oneNotZeroThm],
      hyp];                                                    (* d ≤ SUC 0 *)
    dEq0 = ASSUME[mkEq[dV, zeroN[]]];                          (* d = 0 *)
    hSubst = HOL`Drule`SUBS[{dEq0}, hyp];                      (* divides 0 (SUC 0) *)
    divZeroSuc = HOL`Bool`MP[
      HOL`Bool`SPEC[oneN[], dividesZeroImpZeroThm], hSubst];   (* SUC 0 = 0 *)
    falseThm = HOL`Bool`MP[HOL`Bool`NOTELIM[oneNotZeroThm], divZeroSuc];  (* F *)
    dischFalse = HOL`Bool`DISCH[mkEq[dV, zeroN[]], falseThm];  (* (d=0) ⇒ F *)
    notDEq0 = HOL`Bool`NOTINTRO[dischFalse];                   (* ¬(d = 0) *)
    posD = HOL`Bool`MP[HOL`Bool`SPEC[dV, HOL`Stdlib`Num`ltZeroNotZeroThm], notDEq0]; (* 0 < d *)
    sucLeqD = EQMP[unfoldLt[zeroN[], dV], posD];               (* SUC 0 ≤ d *)
    dd = HOL`Bool`MP[
      HOL`Bool`MP[HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[dV, HOL`Stdlib`Num`leqAntisymThm]],
        leqStep],
      sucLeqD];                                                (* d = SUC 0 *)
    HOL`Bool`GEN[dV, HOL`Bool`DISCH[dividesTm[dV, oneN[]], dd]]
  ];

(* ⊢ ∀a. gcd a (SUC 0) = SUC 0 *)
gcdOneRightThm =
  Module[{aV, gdiv, eq},
    aV = mkVar["a", numTy];
    gdiv = HOL`Bool`SPEC[oneN[],
      HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesRightThm]];  (* divides (gcd a 1) 1 *)
    eq = HOL`Bool`MP[HOL`Bool`SPEC[gcdTm[aV, oneN[]], dividesOneThm], gdiv];
    HOL`Bool`GEN[aV, eq]                                      (* gcd a 1 = 1 *)
  ];

(* ============================================================ *)
(* intNatAbs : int → num                                        *)
(* ============================================================ *)

intNatAbsTy = tyFun[intTy, numTy];

intNatAbsDefThm = newDefinition[mkEq[
  mkVar["intNatAbs", intNatAbsTy],
  Module[{zV}, zV = mkVar["z", intTy];
    mkAbs[zV, plusTm[mkComb[fstNN[], repInt[zV]], mkComb[sndNN[], repInt[zV]]]]]
]];

intNatAbsConst[] := mkConst["intNatAbs", intNatAbsTy];

(* ⊢ intNatAbs z = FST (REP_int z) + SND (REP_int z) *)
unfoldIntNatAbs[zT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intNatAbsDefThm, zT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ intNatAbs (&ℤ 0) = 0 *)
intNatAbsZeroThm =
  Module[{z0, repZ, fstRep, fstZ, sndRep, sndZ, sumEq, addZ},
    z0 = intOfNum[zeroN[]];                                   (* &ℤ 0 *)
    repZ = HOL`Kernel`INST[{mkVar["n", numTy] -> zeroN[]},
      HOL`Stdlib`Int`repIntOfNumThm];                        (* REP_int (&ℤ 0) = (0, 0) *)
    fstRep = HOL`Equal`APTERM[fstNN[], repZ];                 (* FST(REP(&ℤ0)) = FST(0,0) *)
    fstZ = TRANS[fstRep, fstNumAt[zeroN[], zeroN[]]];         (* FST(REP(&ℤ0)) = 0 *)
    sndRep = HOL`Equal`APTERM[sndNN[], repZ];
    sndZ = TRANS[sndRep, sndNumAt[zeroN[], zeroN[]]];         (* SND(REP(&ℤ0)) = 0 *)
    sumEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], fstZ], sndZ]; (* .. + .. = 0 + 0 *)
    addZ = HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`addLeftZeroThm]; (* 0 + 0 = 0 *)
    TRANS[unfoldIntNatAbs[z0], TRANS[sumEq, addZ]]
  ];

(* ============================================================ *)
(* RAT_REP + carve                                              *)
(* ============================================================ *)

ratRepBody[] :=
  Module[{pV},
    pV = mkVar["p", ratPairTy];
    mkAbs[pV, andTm[
      notTm[mkEq[mkComb[sndIN[], pV], zeroN[]]],
      mkEq[gcdTm[mkComb[intNatAbsConst[], mkComb[fstIN[], pV]],
                 mkComb[sndIN[], pV]], oneN[]]]]
  ];

ratRepDefThm = newDefinition[mkEq[mkVar["RAT_REP", ratRepTy], ratRepBody[]]];
ratRepConst[] := mkConst["RAT_REP", ratRepTy];

(* ⊢ RAT_REP p = (¬(SND p = 0) ∧ gcd (intNatAbs (FST p)) (SND p) = SUC 0) *)
unfoldRatRep[pT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[ratRepDefThm, pT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ RAT_REP (&ℤ 0, SUC 0) *)
ratRepWitnessThm =
  Module[{p0, sndEq, fstEq, c1, naFst, gcdArgs, gcd01, c2, conj},
    p0 = ratPairCons[intOfNum[zeroN[]], oneN[]];
    sndEq = sndINatAt[intOfNum[zeroN[]], oneN[]];             (* SND p0 = SUC 0 *)
    c1 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndEq]}, oneNotZeroThm]; (* ¬(SND p0 = 0) *)
    fstEq = fstINatAt[intOfNum[zeroN[]], oneN[]];             (* FST p0 = &ℤ 0 *)
    naFst = TRANS[HOL`Equal`APTERM[intNatAbsConst[], fstEq], intNatAbsZeroThm]; (* intNatAbs(FST p0) = 0 *)
    gcdArgs = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Num`gcdConst[], naFst], sndEq]; (* gcd(intNatAbs(FST p0))(SND p0) = gcd 0 (SUC 0) *)
    gcd01 = HOL`Bool`SPEC[zeroN[], gcdOneRightThm];           (* gcd 0 (SUC 0) = SUC 0 *)
    c2 = TRANS[gcdArgs, gcd01];                               (* gcd(..)(..) = SUC 0 *)
    conj = HOL`Bool`CONJ[c1, c2];
    EQMP[HOL`Equal`SYM[unfoldRatRep[p0]], conj]
  ];

{absRepRatThm, repAbsRatThm} =
  newBasicTypeDefinition["rat", "ABS_rat", "REP_rat", ratRepWitnessThm];

ratTy = mkType["rat", {}];
absRatConst[] := mkConst["ABS_rat", tyFun[ratPairTy, ratTy]];
repRatConst[] := mkConst["REP_rat", tyFun[ratTy, ratPairTy]];

(* ============================================================ *)
(* &ℚ : int → rat — the embedding q ↦ q/1 = ABS_rat (q, SUC 0). *)
(* ============================================================ *)

(* ⊢ RAT_REP (q, SUC 0)  (q : int free): every q/1 is canonical. *)
ratRepOneDenomThm =
  Module[{qV, p, sndEq, fstEq, c1, naFst, gcdArgs, gcd1, c2, conj},
    qV = mkVar["q", intTy];
    p = ratPairCons[qV, oneN[]];
    sndEq = sndINatAt[qV, oneN[]];                      (* SND (q, 1) = SUC 0 *)
    fstEq = fstINatAt[qV, oneN[]];                      (* FST (q, 1) = q *)
    c1 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndEq]}, oneNotZeroThm];   (* ¬(SND (q,1) = 0) *)
    naFst = HOL`Equal`APTERM[intNatAbsConst[], fstEq];  (* intNatAbs (FST (q,1)) = intNatAbs q *)
    gcdArgs = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Num`gcdConst[], naFst], sndEq]; (* gcd .. = gcd (intNatAbs q) (SUC 0) *)
    gcd1 = HOL`Bool`SPEC[mkComb[intNatAbsConst[], qV], gcdOneRightThm]; (* gcd (intNatAbs q) (SUC 0) = SUC 0 *)
    c2 = TRANS[gcdArgs, gcd1];
    conj = HOL`Bool`CONJ[c1, c2];
    EQMP[HOL`Equal`SYM[unfoldRatRep[p]], conj]
  ];

ratOfIntTy = tyFun[intTy, ratTy];

ratOfIntDefThm = newDefinition[mkEq[
  mkVar["&ℚ", ratOfIntTy],
  Module[{qV}, qV = mkVar["q", intTy];
    mkAbs[qV, mkComb[absRatConst[], ratPairCons[qV, oneN[]]]]]
]];

ratOfIntConst[] := mkConst["&ℚ", ratOfIntTy];
ratOfIntTm[qT_] := mkComb[ratOfIntConst[], qT];

(* ⊢ &ℚ q = ABS_rat (q, SUC 0) *)
unfoldRatOfInt[qT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[ratOfIntDefThm, qT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ REP_rat (&ℚ q) = (q, SUC 0)  (q free) *)
repRatOfIntThm =
  Module[{qV, p, unfDef, rVar, repAbsInst, repEq, apRep},
    qV = mkVar["q", intTy];
    p = ratPairCons[qV, oneN[]];
    unfDef = unfoldRatOfInt[qV];                        (* &ℚ q = ABS_rat (q, 1) *)
    rVar = concl[repAbsRatThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> p}, repAbsRatThm];
    repEq = EQMP[repAbsInst, ratRepOneDenomThm];        (* REP_rat (ABS_rat (q,1)) = (q,1) *)
    apRep = HOL`Equal`APTERM[repRatConst[], unfDef];    (* REP_rat (&ℚ q) = REP_rat (ABS_rat (q,1)) *)
    TRANS[apRep, repEq]
  ];

(* ⊢ ∀a b. &ℚ a = &ℚ b ⇒ a = b *)
ratOfIntInjThm =
  Module[{aV, bV, qV, hyp, apRep, repA, repB, pairEq, injInst, mpInj, conj1, dischd},
    aV = mkVar["a", intTy]; bV = mkVar["b", intTy]; qV = mkVar["q", intTy];
    hyp = ASSUME[mkEq[ratOfIntTm[aV], ratOfIntTm[bV]]];
    apRep = HOL`Equal`APTERM[repRatConst[], hyp];       (* REP_rat (&ℚ a) = REP_rat (&ℚ b) *)
    repA = HOL`Kernel`INST[{qV -> aV}, repRatOfIntThm]; (* REP_rat (&ℚ a) = (a, 1) *)
    repB = HOL`Kernel`INST[{qV -> bV}, repRatOfIntThm]; (* REP_rat (&ℚ b) = (b, 1) *)
    pairEq = TRANS[TRANS[HOL`Equal`SYM[repA], apRep], repB]; (* (a,1) = (b,1) *)
    injInst = HOL`Kernel`INST[
      {mkVar["x", intTy] -> aV, mkVar["y", numTy] -> oneN[],
       mkVar["xP", intTy] -> bV, mkVar["yP", numTy] -> oneN[]},
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairInjThm]];                   (* ((a,1)=(b,1)) ⇒ (a=b ∧ 1=1) *)
    mpInj = HOL`Bool`MP[injInst, pairEq];
    conj1 = HOL`Bool`CONJUNCT1[mpInj];                  (* a = b *)
    dischd = HOL`Bool`DISCH[concl[hyp], conj1];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, dischd]]
  ];

End[];
EndPackage[];
