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
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`FTA`", "HOL`Stdlib`Int`",
  "HOL`Auto`Arith`"
}];

dividesZeroImpZeroThm::usage = "dividesZeroImpZeroThm — ⊢ ∀n. divides 0 n ⇒ n = 0.";
dividesOneThm::usage         = "dividesOneThm — ⊢ ∀d. divides d (SUC 0) ⇒ d = SUC 0.";
gcdOneRightThm::usage        = "gcdOneRightThm — ⊢ ∀a. gcd a (SUC 0) = SUC 0.";

exDivConst::usage   = "exDivConst[] — exDiv : num → num → num, exact quotient exDiv n g = ε c. n = g * c. Well-behaved only when g divides n; chosen over DIV so divides g n ⇒ n = g*(exDiv n g) follows from selectAx with no division-uniqueness lemma.";
exDivDefThm::usage  = "exDivDefThm — ⊢ exDiv = (λn g. ε c. n = g * c).";
exDivThm::usage     = "exDivThm — ⊢ ∀g n. divides g n ⇒ n = g * exDiv n g. Exact division via the Hilbert-ε witness.";
exDivOneThm::usage  = "exDivOneThm — ⊢ ∀n. exDiv n (SUC 0) = n.";
exDivZeroThm::usage = "exDivZeroThm — ⊢ ∀g. ¬ (g = 0) ⇒ exDiv 0 g = 0.";

dividesMultBothLeftThm::usage = "dividesMultBothLeftThm — ⊢ ∀g h x. divides h x ⇒ divides (g * h) (g * x).";
gcdNonzeroFromRightThm::usage = "gcdNonzeroFromRightThm — ⊢ ∀a b. ¬ (b = 0) ⇒ ¬ (gcd a b = 0).";
coprimeReducedThm::usage = "coprimeReducedThm — ⊢ ∀a b. ¬ (gcd a b = 0) ⇒ gcd (exDiv a (gcd a b)) (exDiv b (gcd a b)) = SUC 0. Dividing both arguments by their gcd makes them coprime.";

dividesAntisymThm::usage = "dividesAntisymThm — ⊢ ∀a b. divides a b ⇒ divides b a ⇒ a = b. (proper home Num.wl)";
gcdZeroRightThm::usage   = "gcdZeroRightThm — ⊢ ∀a. gcd a 0 = a. (proper home Num.wl)";
gcdRecThm::usage         = "gcdRecThm — ⊢ ∀a b. ¬ (b = 0) ⇒ gcd a b = gcd b (a MOD b). Euclidean recurrence. (proper home Num.wl)";
bezoutNatThm::usage      = "bezoutNatThm — ⊢ ∀a b. ∃x y. a * x = b * y + gcd a b ∨ b * y = a * x + gcd a b. ℕ Bezout (disjunctive, subtraction-free). (proper home Num.wl)";
coprimeDividesProductThm::usage = "coprimeDividesProductThm — ⊢ ∀a b c. gcd a b = SUC 0 ⇒ divides a (b * c) ⇒ divides a c. ℕ Gauss / Euclid coprime-product lemma. (proper home Num.wl)";

intDivNatConst::usage  = "intDivNatConst[] — intDivNat : int → num → int, exact division of an integer by a natural, componentwise on the canonical rep: intDivNat z g = ABS_int (exDiv (FST (REP_int z)) g, exDiv (SND (REP_int z)) g).";
intDivNatDefThm::usage = "intDivNatDefThm — ⊢ intDivNat = (λz g. ABS_int (exDiv (FST (REP_int z)) g, exDiv (SND (REP_int z)) g)).";
repIntDivNatThm::usage = "repIntDivNatThm — ⊢ ∀z g. ¬ (g = 0) ⇒ REP_int (intDivNat z g) = (exDiv (FST (REP_int z)) g, exDiv (SND (REP_int z)) g).";
intDivNatOneThm::usage = "intDivNatOneThm — ⊢ ∀z. intDivNat z (SUC 0) = z.";
intNatAbsIntDivNatThm::usage = "intNatAbsIntDivNatThm — ⊢ ∀z g. ¬ (g = 0) ⇒ intNatAbs (intDivNat z g) = exDiv (intNatAbs z) g.";

ratCanonConst::usage  = "ratCanonConst[] — ratCanon : int × num → int × num, reduces a fraction to lowest terms: ratCanon p = (intDivNat (FST p) g, exDiv (SND p) g) with g = gcd (intNatAbs (FST p)) (SND p).";
ratCanonDefThm::usage = "ratCanonDefThm — ⊢ ratCanon = (λp. (intDivNat (FST p) g, exDiv (SND p) g)) where g = gcd (intNatAbs (FST p)) (SND p).";
ratCanonLandsThm::usage = "ratCanonLandsThm — ⊢ ∀p. ¬ (SND p = 0) ⇒ RAT_REP (ratCanon p). gcd-reduction of a positive-denominator fraction is canonical.";
ratCanonIdThm::usage = "ratCanonIdThm — ⊢ ∀p. RAT_REP p ⇒ ratCanon p = p. ratCanon is the identity on already-canonical reps.";

ratRepRepThm::usage = "ratRepRepThm — ⊢ RAT_REP (REP_rat q) (q free): REP_rat lands in the carve. Mirror of Int's intRepRepThm.";
multNonzeroThm::usage = "multNonzeroThm — ⊢ ∀m n. ¬ (m = 0) ⇒ ¬ (n = 0) ⇒ ¬ (m * n = 0). (proper home Num.wl)";

ratAddConst::usage  = "ratAddConst[] — ratAdd : rat → rat → rat. (a,b)+(c,d) = ratCanon (a·d + c·b, b·d) over the int×num reps.";
ratAddDefThm::usage = "ratAddDefThm — ⊢ ratAdd = (λq r. ABS_rat (ratCanon (intAdd (intMul (FST(REP q)) (&ℤ(SND(REP r)))) (intMul (FST(REP r)) (&ℤ(SND(REP q)))), SND(REP q) * SND(REP r)))).";
repRatAddThm::usage = "repRatAddThm — ⊢ ∀q r. REP_rat (ratAdd q r) = ratCanon (intAdd (intMul (FST(REP q)) (&ℤ(SND(REP r)))) (intMul (FST(REP r)) (&ℤ(SND(REP q)))), SND(REP q) * SND(REP r)). REP of a sum is the reduced sum-pair (lands via ratCanonLandsThm).";
ratAddCommThm::usage = "ratAddCommThm — ⊢ ∀q r. ratAdd q r = ratAdd r q (additive commutativity).";
ratAddZeroThm::usage = "ratAddZeroThm — ⊢ ∀q. ratAdd q (&ℚ (&ℤ 0)) = q (right additive identity, the rational 0 = 0/1).";

intNatAbsNegThm::usage = "intNatAbsNegThm — ⊢ ∀z. intNatAbs (intNeg z) = intNatAbs z. (proper home Int.wl)";
ratNegConst::usage  = "ratNegConst[] — ratNeg : rat → rat, negation. ratNeg q = ABS_rat (intNeg (FST(REP q)), SND(REP q)) — negate the numerator; stays canonical (|−a|=|a|).";
ratNegDefThm::usage = "ratNegDefThm — ⊢ ratNeg = (λq. ABS_rat (intNeg (FST(REP q)), SND(REP q))).";
repRatNegThm::usage = "repRatNegThm — ⊢ ∀q. REP_rat (ratNeg q) = (intNeg (FST(REP q)), SND(REP q)). Negation lands in the carve with no reduction.";

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

(* ℕ term constructors for the Bezout chain *)
ltTmR[a_, b_]  := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], a], b];
divTmR[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`divConst[], a], b];
modTmR[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`modConst[], a], b];
orCR[]         := mkConst["∨", tyFun[boolT, tyFun[boolT, boolT]]];
orTmR[a_, b_]  := mkComb[mkComb[orCR[], a], b];
existsCR[ty_]  := mkConst["∃", tyFun[tyFun[ty, boolT], boolT]];
existsTmR[v_, body_] := mkComb[existsCR[typeOf[v]], mkAbs[v, body]];
dividesHead[d_] := mkComb[HOL`Stdlib`Num`dividesConst[], d];

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
(* exDiv — exact quotient via Hilbert ε (proper home Num.wl)    *)
(* exDiv n g = ε c. n = g * c. When g divides n this is the     *)
(* unique quotient, and exDivThm falls straight out of selectAx *)
(* with no need for a DIV/MOD-uniqueness lemma.                 *)
(* ============================================================ *)

selectC[ty_] := mkConst["@", tyFun[tyFun[ty, boolT], ty]];

exDivTy = tyFun[numTy, tyFun[numTy, numTy]];

exDivDefThm = newDefinition[mkEq[
  mkVar["exDiv", exDivTy],
  Module[{nV, gV, cV},
    nV = mkVar["n", numTy]; gV = mkVar["g", numTy]; cV = mkVar["c", numTy];
    mkAbs[nV, mkAbs[gV,
      mkComb[selectC[numTy], mkAbs[cV, mkEq[nV, timesTm[gV, cV]]]]]]]
]];

exDivConst[] := mkConst["exDiv", exDivTy];
exDivTm[nT_, gT_] := mkComb[mkComb[exDivConst[], nT], gT];

(* ⊢ exDiv n g = (@ c. n = g * c) *)
unfoldExDiv[nT_, gT_] :=
  Module[{ap1, beta1, ap2, beta2},
    ap1 = HOL`Equal`APTHM[exDivDefThm, nT];
    beta1 = BETACONV[concl[ap1][[2]]];
    ap2 = HOL`Equal`APTHM[TRANS[ap1, beta1], gT];
    beta2 = BETACONV[concl[ap2][[2]]];
    TRANS[ap2, beta2]
  ];

(* ⊢ ∀g n. divides g n ⇒ n = g * exDiv n g *)
exDivThm =
  Module[{gV, nV, hyp, exTh, pred, selTh, unf, apTerm, result},
    gV = mkVar["g", numTy]; nV = mkVar["n", numTy];
    hyp = ASSUME[dividesTm[gV, nV]];                    (* divides g n *)
    exTh = EQMP[unfoldDivides[gV, nV], hyp];            (* ∃c. n = g * c *)
    pred = concl[exTh][[2]];                            (* λc. n = g * c *)
    selTh = HOL`Stdlib`Num`selectOfExists[pred, exTh];  (* n = g * (@pred) *)
    unf = unfoldExDiv[nV, gV];                          (* exDiv n g = @(λc. n=g*c) *)
    apTerm = HOL`Equal`APTERM[
      mkComb[HOL`Stdlib`Num`timesConst[], gV], HOL`Equal`SYM[unf]]; (* g*@pred = g*exDiv n g *)
    result = TRANS[selTh, apTerm];                      (* n = g * exDiv n g *)
    HOL`Bool`GEN[gV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[dividesTm[gV, nV], result]]]
  ];

(* ⊢ ∀n. exDiv n (SUC 0) = n *)
exDivOneThm =
  Module[{nV, oneT, oneTimesN, nEqOneTimesN, existsBody, exTh, divThm,
          eqStep, oneTimesEx, result},
    nV = mkVar["n", numTy]; oneT = oneN[];
    oneTimesN = HOL`Bool`SPEC[nV, HOL`Stdlib`Num`oneTimesEqThm];  (* SUC 0 * n = n *)
    nEqOneTimesN = HOL`Equal`SYM[oneTimesN];            (* n = SUC 0 * n *)
    existsBody = concl[unfoldDivides[oneT, nV]][[2]];   (* ∃c. n = SUC 0 * c *)
    exTh = HOL`Bool`EXISTS[existsBody, nV, nEqOneTimesN];
    divThm = EQMP[HOL`Equal`SYM[unfoldDivides[oneT, nV]], exTh];  (* divides (SUC 0) n *)
    eqStep = HOL`Bool`MP[
      HOL`Bool`SPEC[nV, HOL`Bool`SPEC[oneT, exDivThm]], divThm];  (* n = SUC 0 * exDiv n (SUC 0) *)
    oneTimesEx = HOL`Bool`SPEC[exDivTm[nV, oneT], HOL`Stdlib`Num`oneTimesEqThm];
    result = HOL`Equal`SYM[TRANS[eqStep, oneTimesEx]];  (* exDiv n (SUC 0) = n *)
    HOL`Bool`GEN[nV, result]
  ];

(* ⊢ ∀g. ¬ (g = 0) ⇒ exDiv 0 g = 0 *)
exDivZeroThm =
  Module[{gV, zeroT, divisG0, eqStep, prodEq0, disj, notGEq0,
          falseTh, case1, case2, elim, gEq0Tm, exDiv0gEq0Tm},
    gV = mkVar["g", numTy]; zeroT = zeroN[];
    divisG0 = HOL`Bool`SPEC[gV, HOL`Stdlib`Num`dividesZeroThm];   (* divides g 0 *)
    eqStep = HOL`Bool`MP[
      HOL`Bool`SPEC[zeroT, HOL`Bool`SPEC[gV, exDivThm]], divisG0]; (* 0 = g * exDiv 0 g *)
    prodEq0 = HOL`Equal`SYM[eqStep];                    (* g * exDiv 0 g = 0 *)
    disj = HOL`Bool`MP[
      HOL`Bool`SPEC[exDivTm[zeroT, gV],
        HOL`Bool`SPEC[gV, HOL`Stdlib`Num`multEqZeroThm]],
      prodEq0];                                         (* g = 0 ∨ exDiv 0 g = 0 *)
    gEq0Tm = mkEq[gV, zeroT];
    exDiv0gEq0Tm = mkEq[exDivTm[zeroT, gV], zeroT];
    notGEq0 = ASSUME[notTm[gEq0Tm]];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notGEq0], ASSUME[gEq0Tm]];  (* F *)
    case1 = HOL`Bool`CONTR[exDiv0gEq0Tm, falseTh];
    case2 = ASSUME[exDiv0gEq0Tm];
    elim = HOL`Bool`DISJCASES[disj, case1, case2];      (* ¬(g=0) ⊢ exDiv 0 g = 0 *)
    HOL`Bool`GEN[gV, HOL`Bool`DISCH[notTm[gEq0Tm], elim]]
  ];

(* ============================================================ *)
(* gcd-reduction number theory (proper home Num.wl)            *)
(* ============================================================ *)

(* ⊢ ∀g h x. divides h x ⇒ divides (g * h) (g * x) *)
dividesMultBothLeftThm =
  Module[{gV, hV, xV, cV, hyp, exTh, cBody, apG, assocSym, gxEq,
          existsTm, exC, chosen, folded},
    gV = mkVar["g", numTy]; hV = mkVar["h", numTy]; xV = mkVar["x", numTy];
    cV = mkVar["c", numTy];
    hyp = ASSUME[dividesTm[hV, xV]];                    (* divides h x *)
    exTh = EQMP[unfoldDivides[hV, xV], hyp];            (* ∃c. x = h * c *)
    cBody = ASSUME[mkEq[xV, timesTm[hV, cV]]];          (* x = h * c *)
    apG = HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], gV], cBody]; (* g*x = g*(h*c) *)
    assocSym = HOL`Equal`SYM[
      HOL`Bool`SPEC[cV, HOL`Bool`SPEC[hV, HOL`Bool`SPEC[gV,
        HOL`Stdlib`Num`timesAssocThm]]]];               (* g*(h*c) = (g*h)*c *)
    gxEq = TRANS[apG, assocSym];                        (* g*x = (g*h)*c *)
    existsTm = concl[unfoldDivides[timesTm[gV, hV], timesTm[gV, xV]]][[2]]; (* ∃c. g*x = (g*h)*c *)
    exC = HOL`Bool`EXISTS[existsTm, cV, gxEq];
    chosen = HOL`Bool`CHOOSE[cV, exTh, exC];            (* divides h x ⊢ ∃c. g*x=(g*h)*c *)
    folded = EQMP[
      HOL`Equal`SYM[unfoldDivides[timesTm[gV, hV], timesTm[gV, xV]]], chosen];
    HOL`Bool`GEN[gV, HOL`Bool`GEN[hV, HOL`Bool`GEN[xV,
      HOL`Bool`DISCH[dividesTm[hV, xV], folded]]]]
  ];

(* ⊢ ∀a b. ¬ (b = 0) ⇒ ¬ (gcd a b = 0) *)
gcdNonzeroFromRightThm =
  Module[{aV, bV, gTm, notB0, gB, posInst, notG0},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    gTm = gcdTm[aV, bV];
    notB0 = ASSUME[notTm[mkEq[bV, zeroN[]]]];           (* ¬(b = 0) *)
    gB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesRightThm]]; (* divides (gcd a b) b *)
    posInst = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[gTm, HOL`Stdlib`FTA`dividesPosThm]];
                                                        (* ¬(b=0) ⇒ divides (gcd a b) b ⇒ ¬(gcd a b=0) *)
    notG0 = HOL`Bool`MP[HOL`Bool`MP[posInst, notB0], gB];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[notTm[mkEq[bV, zeroN[]]], notG0]]]
  ];

(* ⊢ ∀a b. ¬ (gcd a b = 0) ⇒ gcd (exDiv a (gcd a b)) (exDiv b (gcd a b)) = SUC 0 *)
coprimeReducedThm =
  Module[{aV, bV, gTm, notG0, gA, gB, aEq, bEq, qaTm, qbTm, hTm,
          hA, hB, ghDivA0, ghDivA, ghDivB0, ghDivB, ghDivG, exK, kV,
          kBody, assocHK, gEqGhk, gTimesOne, gOneEqGhk, cancelInst,
          suc0EqHk, existsH1, divH1, hEqOne, chosen},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    gTm = gcdTm[aV, bV];
    notG0 = ASSUME[notTm[mkEq[gTm, zeroN[]]]];          (* ¬(gcd a b = 0) *)
    gA = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesLeftThm]];  (* divides (gcd a b) a *)
    gB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesRightThm]]; (* divides (gcd a b) b *)
    aEq = HOL`Bool`MP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[gTm, exDivThm]], gA];  (* a = gcd a b * exDiv a (gcd a b) *)
    bEq = HOL`Bool`MP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[gTm, exDivThm]], gB];
    qaTm = exDivTm[aV, gTm]; qbTm = exDivTm[bV, gTm];
    hTm = gcdTm[qaTm, qbTm];
    hA = HOL`Bool`SPEC[qbTm, HOL`Bool`SPEC[qaTm, HOL`Stdlib`Num`gcdDividesLeftThm]];  (* divides h qa *)
    hB = HOL`Bool`SPEC[qbTm, HOL`Bool`SPEC[qaTm, HOL`Stdlib`Num`gcdDividesRightThm]]; (* divides h qb *)
    ghDivA0 = HOL`Bool`MP[
      HOL`Bool`SPEC[qaTm, HOL`Bool`SPEC[hTm, HOL`Bool`SPEC[gTm, dividesMultBothLeftThm]]], hA];
                                                        (* divides (gcd a b * h) (gcd a b * qa) *)
    ghDivA = HOL`Drule`SUBS[{HOL`Equal`SYM[aEq]}, ghDivA0];   (* divides (gcd a b * h) a *)
    ghDivB0 = HOL`Bool`MP[
      HOL`Bool`SPEC[qbTm, HOL`Bool`SPEC[hTm, HOL`Bool`SPEC[gTm, dividesMultBothLeftThm]]], hB];
    ghDivB = HOL`Drule`SUBS[{HOL`Equal`SYM[bEq]}, ghDivB0];   (* divides (gcd a b * h) b *)
    ghDivG = HOL`Bool`MP[
      HOL`Bool`SPEC[timesTm[gTm, hTm],
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdUniversalThm]]],
      HOL`Bool`CONJ[ghDivA, ghDivB]];                   (* divides (gcd a b * h) (gcd a b) *)
    exK = EQMP[unfoldDivides[timesTm[gTm, hTm], gTm], ghDivG];  (* ∃k. gcd a b = (gcd a b * h) * k *)
    kV = mkVar["k", numTy];
    kBody = ASSUME[mkEq[gTm, timesTm[timesTm[gTm, hTm], kV]]];  (* gcd a b = (gcd a b * h) * k *)
    assocHK = HOL`Bool`SPEC[kV, HOL`Bool`SPEC[hTm, HOL`Bool`SPEC[gTm,
      HOL`Stdlib`Num`timesAssocThm]]];                  (* (gcd a b * h) * k = gcd a b * (h * k) *)
    gEqGhk = TRANS[kBody, assocHK];                     (* gcd a b = gcd a b * (h * k) *)
    gTimesOne = TRANS[
      HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[gTm, HOL`Stdlib`Num`timesCommThm]],
      HOL`Bool`SPEC[gTm, HOL`Stdlib`Num`oneTimesEqThm]];  (* gcd a b * SUC 0 = gcd a b *)
    gOneEqGhk = TRANS[gTimesOne, gEqGhk];               (* gcd a b * SUC 0 = gcd a b * (h * k) *)
    cancelInst = HOL`Bool`SPEC[timesTm[hTm, kV], HOL`Bool`SPEC[oneN[],
      HOL`Bool`MP[HOL`Bool`SPEC[gTm, HOL`Stdlib`FTA`multLeftCancelThm], notG0]]];
                                                        (* gcd a b * SUC 0 = gcd a b * (h*k) ⇒ SUC 0 = h*k *)
    suc0EqHk = HOL`Bool`MP[cancelInst, gOneEqGhk];      (* SUC 0 = h * k *)
    existsH1 = concl[unfoldDivides[hTm, oneN[]]][[2]];  (* ∃k. SUC 0 = h * k *)
    divH1 = EQMP[HOL`Equal`SYM[unfoldDivides[hTm, oneN[]]],
      HOL`Bool`EXISTS[existsH1, kV, suc0EqHk]];         (* divides h (SUC 0) *)
    hEqOne = HOL`Bool`MP[HOL`Bool`SPEC[hTm, dividesOneThm], divH1];  (* h = SUC 0 *)
    chosen = HOL`Bool`CHOOSE[kV, exK, hEqOne];          (* ¬(gcd a b=0) ⊢ h = SUC 0 *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[notTm[mkEq[gTm, zeroN[]]], chosen]]]
  ];

(* ============================================================ *)
(* Bezout chain (proper home Num.wl — migrate later)            *)
(*   dividesAntisym → gcdZeroRight → gcdRec → bezoutNat → Gauss  *)
(* ============================================================ *)

(* ⊢ ∀a b. divides a b ⇒ divides b a ⇒ a = b *)
dividesAntisymThm =
  Module[{aV, bV, hAB, hBA, em, caseB0, caseBnz, result},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    hAB = ASSUME[dividesTm[aV, bV]];
    hBA = ASSUME[dividesTm[bV, aV]];
    em = HOL`Bool`EXCLUDEDMIDDLE[mkEq[bV, zeroN[]]];
    caseB0 = Module[{hB0, div0a, aEq0},
      hB0 = ASSUME[mkEq[bV, zeroN[]]];
      div0a = HOL`Drule`SUBS[{hB0}, hBA];                 (* divides 0 a *)
      aEq0 = HOL`Bool`MP[HOL`Bool`SPEC[aV, dividesZeroImpZeroThm], div0a];  (* a = 0 *)
      TRANS[aEq0, HOL`Equal`SYM[hB0]]];                   (* a = b *)
    caseBnz = Module[{hBnz, aLeqB, notA0, bLeqA},
      hBnz = ASSUME[notTm[mkEq[bV, zeroN[]]]];
      aLeqB = HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesLeqThm]], hBnz], hAB]; (* a ≤ b *)
      notA0 = Module[{hA0, div0b, bEq0, falseTh},
        hA0 = ASSUME[mkEq[aV, zeroN[]]];
        div0b = HOL`Drule`SUBS[{hA0}, hAB];               (* divides 0 b *)
        bEq0 = HOL`Bool`MP[HOL`Bool`SPEC[bV, dividesZeroImpZeroThm], div0b];  (* b = 0 *)
        falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[hBnz], bEq0];
        HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[aV, zeroN[]], falseTh]]];      (* ¬(a = 0) *)
      bLeqA = HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`dividesLeqThm]], notA0], hBA]; (* b ≤ a *)
      HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`leqAntisymThm]], aLeqB], bLeqA]]; (* a = b *)
    result = HOL`Bool`DISJCASES[em, caseB0, caseBnz];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[dividesTm[aV, bV], HOL`Bool`DISCH[dividesTm[bV, aV], result]]]]
  ];

(* ⊢ ∀a. gcd a 0 = a *)
gcdZeroRightThm =
  Module[{aV, gTm, gDivA, aDivA, aDiv0, aDivG, eq},
    aV = mkVar["a", numTy];
    gTm = gcdTm[aV, zeroN[]];
    gDivA = HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesLeftThm]];  (* divides (gcd a 0) a *)
    aDivA = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesReflThm];   (* divides a a *)
    aDiv0 = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesZeroThm];   (* divides a 0 *)
    aDivG = HOL`Bool`MP[
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdUniversalThm]]],
      HOL`Bool`CONJ[aDivA, aDiv0]];                            (* divides a (gcd a 0) *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[gTm, dividesAntisymThm]], gDivA], aDivG];  (* gcd a 0 = a *)
    HOL`Bool`GEN[aV, eq]
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
(* intDivNat : int → num → int — exact division by a natural,   *)
(* componentwise on the canonical rep.                          *)
(* ============================================================ *)

absIntC[] := HOL`Stdlib`Int`absIntConst[];
plusC[]   := HOL`Stdlib`Num`plusConst[];
numPairConsC[] := mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]];
numPairCons[a_, b_] := mkComb[mkComb[numPairConsC[], a], b];

(* ⊢ INT_REP p = (FST p = 0 ∨ SND p = 0) *)
unfoldIntRep[pT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[HOL`Stdlib`Int`intRepDefThm, pT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ m + 0 = m  (no addRightZeroThm in Num; via addComm + addLeftZero) *)
addZeroRightAt[mT_] :=
  TRANS[HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[mT, HOL`Stdlib`Num`addCommThm]],
        HOL`Bool`SPEC[mT, HOL`Stdlib`Num`addLeftZeroThm]];

intDivNatTy = tyFun[intTy, tyFun[numTy, intTy]];

intDivNatDefThm = newDefinition[mkEq[
  mkVar["intDivNat", intDivNatTy],
  Module[{zV, gV},
    zV = mkVar["z", intTy]; gV = mkVar["g", numTy];
    mkAbs[zV, mkAbs[gV,
      mkComb[absIntC[],
        numPairCons[
          exDivTm[mkComb[fstNN[], repInt[zV]], gV],
          exDivTm[mkComb[sndNN[], repInt[zV]], gV]]]]]]
]];

intDivNatConst[] := mkConst["intDivNat", intDivNatTy];
intDivNatTm[zT_, gT_] := mkComb[mkComb[intDivNatConst[], zT], gT];

(* ⊢ intDivNat z g = ABS_int (exDiv (FST (REP_int z)) g, exDiv (SND (REP_int z)) g) *)
unfoldIntDivNat[zT_, gT_] :=
  Module[{ap1, beta1, ap2, beta2},
    ap1 = HOL`Equal`APTHM[intDivNatDefThm, zT];
    beta1 = BETACONV[concl[ap1][[2]]];
    ap2 = HOL`Equal`APTHM[TRANS[ap1, beta1], gT];
    beta2 = BETACONV[concl[ap2][[2]]];
    TRANS[ap2, beta2]
  ];

(* ⊢ ∀z g. ¬ (g = 0) ⇒ REP_int (intDivNat z g) =
       (exDiv (FST (REP_int z)) g, exDiv (SND (REP_int z)) g) *)
repIntDivNatThm =
  Module[{zV, gV, notG0, repZ, fstRepZ, sndRepZ, qF, qS, pairTm,
          exDivZeroG, intRepDisj, fstPairEq, sndPairEq, fstPairTm0,
          sndPairTm0, caseFst, caseSnd, repPairDisj, intRepPair, rVar,
          repAbsInst, repEqPair, unfDiv, apRep, repBody},
    zV = mkVar["z", intTy]; gV = mkVar["g", numTy];
    notG0 = ASSUME[notTm[mkEq[gV, zeroN[]]]];
    repZ = repInt[zV];
    fstRepZ = mkComb[fstNN[], repZ]; sndRepZ = mkComb[sndNN[], repZ];
    qF = exDivTm[fstRepZ, gV]; qS = exDivTm[sndRepZ, gV];
    pairTm = numPairCons[qF, qS];
    exDivZeroG = HOL`Bool`MP[HOL`Bool`SPEC[gV, exDivZeroThm], notG0];  (* exDiv 0 g = 0 *)
    intRepDisj = EQMP[unfoldIntRep[repZ], HOL`Stdlib`Int`intRepRepThm]; (* FST(REP z)=0 ∨ SND(REP z)=0 *)
    fstPairEq = fstNumAt[qF, qS];                       (* FST pair = qF *)
    sndPairEq = sndNumAt[qF, qS];                       (* SND pair = qS *)
    fstPairTm0 = mkEq[mkComb[fstNN[], pairTm], zeroN[]];
    sndPairTm0 = mkEq[mkComb[sndNN[], pairTm], zeroN[]];
    caseFst = Module[{h, exF, qFeq0, fstPair0},
      h = ASSUME[mkEq[fstRepZ, zeroN[]]];               (* FST(REP z)=0 *)
      exF = HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], h], gV];  (* qF = exDiv 0 g *)
      qFeq0 = TRANS[exF, exDivZeroG];                   (* qF = 0 *)
      fstPair0 = TRANS[fstPairEq, qFeq0];               (* FST pair = 0 *)
      HOL`Bool`DISJ1[fstPair0, sndPairTm0]];
    caseSnd = Module[{h, exS, qSeq0, sndPair0},
      h = ASSUME[mkEq[sndRepZ, zeroN[]]];               (* SND(REP z)=0 *)
      exS = HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], h], gV];  (* qS = exDiv 0 g *)
      qSeq0 = TRANS[exS, exDivZeroG];                   (* qS = 0 *)
      sndPair0 = TRANS[sndPairEq, qSeq0];               (* SND pair = 0 *)
      HOL`Bool`DISJ2[sndPair0, fstPairTm0]];
    repPairDisj = HOL`Bool`DISJCASES[intRepDisj, caseFst, caseSnd]; (* FST pair=0 ∨ SND pair=0 *)
    intRepPair = EQMP[HOL`Equal`SYM[unfoldIntRep[pairTm]], repPairDisj];  (* INT_REP pair *)
    rVar = concl[HOL`Stdlib`Int`repAbsIntThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> pairTm}, HOL`Stdlib`Int`repAbsIntThm];
    repEqPair = EQMP[repAbsInst, intRepPair];           (* REP (ABS pair) = pair *)
    unfDiv = unfoldIntDivNat[zV, gV];                   (* intDivNat z g = ABS pair *)
    apRep = HOL`Equal`APTERM[HOL`Stdlib`Int`repIntConst[], unfDiv];
    repBody = TRANS[apRep, repEqPair];                  (* REP (intDivNat z g) = pair *)
    HOL`Bool`GEN[zV, HOL`Bool`GEN[gV,
      HOL`Bool`DISCH[notTm[mkEq[gV, zeroN[]]], repBody]]]
  ];

(* ⊢ ∀z. intDivNat z (SUC 0) = z *)
intDivNatOneThm =
  Module[{zV, repZ, fstRepZ, sndRepZ, repAt1, exF, exS, pairEqProj,
          surjAtRepZ, repEqRepZ, apAbs, aVar, absRepZ, absRepAtDiv, result},
    zV = mkVar["z", intTy];
    repZ = repInt[zV]; fstRepZ = mkComb[fstNN[], repZ]; sndRepZ = mkComb[sndNN[], repZ];
    repAt1 = HOL`Bool`MP[
      HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[zV, repIntDivNatThm]], oneNotZeroThm];
    exF = HOL`Bool`SPEC[fstRepZ, exDivOneThm];          (* exDiv(FST(REP z))(SUC 0) = FST(REP z) *)
    exS = HOL`Bool`SPEC[sndRepZ, exDivOneThm];          (* exDiv(SND(REP z))(SUC 0) = SND(REP z) *)
    pairEqProj = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[numPairConsC[], exF], exS];      (* (..,..) = (FST(REP z), SND(REP z)) *)
    surjAtRepZ = HOL`Bool`SPEC[repZ,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                  (* (FST(REP z), SND(REP z)) = REP z *)
    repEqRepZ = TRANS[TRANS[repAt1, pairEqProj], surjAtRepZ];  (* REP(intDivNat z 1) = REP z *)
    apAbs = HOL`Equal`APTERM[absIntC[], repEqRepZ];     (* ABS(REP(intDivNat z 1)) = ABS(REP z) *)
    aVar = concl[HOL`Stdlib`Int`absRepIntThm][[2]];
    absRepZ = HOL`Kernel`INST[{aVar -> zV}, HOL`Stdlib`Int`absRepIntThm];  (* ABS(REP z) = z *)
    absRepAtDiv = HOL`Kernel`INST[{aVar -> intDivNatTm[zV, oneN[]]},
      HOL`Stdlib`Int`absRepIntThm];                     (* ABS(REP(intDivNat z 1)) = intDivNat z 1 *)
    result = TRANS[HOL`Equal`SYM[absRepAtDiv], TRANS[apAbs, absRepZ]];
    HOL`Bool`GEN[zV, result]
  ];

(* ⊢ ∀z g. ¬ (g = 0) ⇒ intNatAbs (intDivNat z g) = exDiv (intNatAbs z) g *)
intNatAbsIntDivNatThm =
  Module[{zV, gV, notG0, repZ, fstRepZ, sndRepZ, qF, qS, exDivZeroG,
          unfNAdiv, repAt, fstRepDiv, sndRepDiv, sumEq, lhsEq,
          intRepDisj, sumArgTm, caseFst, caseSnd, elim, unfNAz,
          rhsArgEq, result},
    zV = mkVar["z", intTy]; gV = mkVar["g", numTy];
    notG0 = ASSUME[notTm[mkEq[gV, zeroN[]]]];
    repZ = repInt[zV];
    fstRepZ = mkComb[fstNN[], repZ]; sndRepZ = mkComb[sndNN[], repZ];
    qF = exDivTm[fstRepZ, gV]; qS = exDivTm[sndRepZ, gV];
    sumArgTm = plusTm[fstRepZ, sndRepZ];                (* FST(REP z) + SND(REP z) *)
    exDivZeroG = HOL`Bool`MP[HOL`Bool`SPEC[gV, exDivZeroThm], notG0];
    (* LHS: intNatAbs(intDivNat z g) = qF + qS *)
    unfNAdiv = unfoldIntNatAbs[intDivNatTm[zV, gV]];
    repAt = HOL`Bool`MP[
      HOL`Bool`SPEC[gV, HOL`Bool`SPEC[zV, repIntDivNatThm]], notG0]; (* REP(intDivNat z g) = pair *)
    fstRepDiv = TRANS[HOL`Equal`APTERM[fstNN[], repAt], fstNumAt[qF, qS]];
    sndRepDiv = TRANS[HOL`Equal`APTERM[sndNN[], repAt], sndNumAt[qF, qS]];
    sumEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], fstRepDiv], sndRepDiv];
    lhsEq = TRANS[unfNAdiv, sumEq];                     (* intNatAbs(intDivNat z g) = qF + qS *)
    intRepDisj = EQMP[unfoldIntRep[repZ], HOL`Stdlib`Int`intRepRepThm];
    (* goal of the case-split: qF + qS = exDiv (FST(REP z)+SND(REP z)) g *)
    caseFst = Module[{h, qFeq0, lhsToQs, sumArgEq, rhsEqQs},
      h = ASSUME[mkEq[fstRepZ, zeroN[]]];               (* FST(REP z)=0 *)
      qFeq0 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], h], gV], exDivZeroG]; (* qF = 0 *)
      lhsToQs = TRANS[
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], qFeq0], REFL[qS]],
        HOL`Bool`SPEC[qS, HOL`Stdlib`Num`addLeftZeroThm]];  (* qF + qS = qS *)
      sumArgEq = TRANS[
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], h], REFL[sndRepZ]],
        HOL`Bool`SPEC[sndRepZ, HOL`Stdlib`Num`addLeftZeroThm]];  (* FST(REP z)+SND(REP z) = SND(REP z) *)
      rhsEqQs = HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], sumArgEq], gV]; (* exDiv(sumArg)g = qS *)
      TRANS[lhsToQs, HOL`Equal`SYM[rhsEqQs]]];          (* qF + qS = exDiv(sumArg)g *)
    caseSnd = Module[{h, qSeq0, lhsToQf, sumArgEq, rhsEqQf},
      h = ASSUME[mkEq[sndRepZ, zeroN[]]];               (* SND(REP z)=0 *)
      qSeq0 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], h], gV], exDivZeroG]; (* qS = 0 *)
      lhsToQf = TRANS[
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[qF]], qSeq0],
        addZeroRightAt[qF]];                            (* qF + qS = qF *)
      sumArgEq = TRANS[
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[fstRepZ]], h],
        addZeroRightAt[fstRepZ]];                       (* FST(REP z)+SND(REP z) = FST(REP z) *)
      rhsEqQf = HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], sumArgEq], gV]; (* exDiv(sumArg)g = qF *)
      TRANS[lhsToQf, HOL`Equal`SYM[rhsEqQf]]];          (* qF + qS = exDiv(sumArg)g *)
    elim = HOL`Bool`DISJCASES[intRepDisj, caseFst, caseSnd]; (* qF + qS = exDiv(sumArg)g *)
    unfNAz = unfoldIntNatAbs[zV];                       (* intNatAbs z = FST(REP z)+SND(REP z) *)
    rhsArgEq = HOL`Equal`SYM[
      HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], unfNAz], gV]];
                                                        (* exDiv(sumArg)g = exDiv(intNatAbs z)g *)
    result = TRANS[TRANS[lhsEq, elim], rhsArgEq];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[gV,
      HOL`Bool`DISCH[notTm[mkEq[gV, zeroN[]]], result]]]
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

(* ============================================================ *)
(* ratCanon — gcd-reduction to lowest terms                     *)
(* ============================================================ *)

ratPairConsC[] := mkConst[",", tyFun[intTy, tyFun[numTy, ratPairTy]]];

ratCanonTy = tyFun[ratPairTy, ratPairTy];

ratCanonDefThm = newDefinition[mkEq[
  mkVar["ratCanon", ratCanonTy],
  Module[{pV, fstP, sndP, gExpr},
    pV = mkVar["p", ratPairTy];
    fstP = mkComb[fstIN[], pV]; sndP = mkComb[sndIN[], pV];
    gExpr = gcdTm[mkComb[intNatAbsConst[], fstP], sndP];
    mkAbs[pV, ratPairCons[intDivNatTm[fstP, gExpr], exDivTm[sndP, gExpr]]]]
]];

ratCanonConst[] := mkConst["ratCanon", ratCanonTy];
ratCanonTm[pT_] := mkComb[ratCanonConst[], pT];

(* ⊢ ratCanon p = (intDivNat (FST p) g, exDiv (SND p) g),  g = gcd (intNatAbs (FST p)) (SND p) *)
unfoldRatCanon[pT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[ratCanonDefThm, pT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ ∀p. ¬ (SND p = 0) ⇒ RAT_REP (ratCanon p) *)
ratCanonLandsThm =
  Module[{pV, fstP, sndP, aTm, bTm, gTm, numTmrt, denTm, ratCanonP,
          notB0, notG0, ucanon, sndCanon, divGB, bEq, denEq0Tm, denEq0,
          bEq0, falseTh, notDen0, notSndCanon0, fstCanon, naFstCanon,
          naDivEq, naFstCanonEq, gcdArgsEq, coprime, gcdCanonEq, conj},
    pV = mkVar["p", ratPairTy];
    fstP = mkComb[fstIN[], pV]; sndP = mkComb[sndIN[], pV];
    aTm = mkComb[intNatAbsConst[], fstP]; bTm = sndP;
    gTm = gcdTm[aTm, bTm];
    numTmrt = intDivNatTm[fstP, gTm]; denTm = exDivTm[bTm, gTm];
    ratCanonP = ratCanonTm[pV];
    notB0 = ASSUME[notTm[mkEq[bTm, zeroN[]]]];          (* ¬(SND p = 0) *)
    notG0 = HOL`Bool`MP[
      HOL`Bool`SPEC[bTm, HOL`Bool`SPEC[aTm, gcdNonzeroFromRightThm]], notB0]; (* ¬(gcd a b=0) *)
    ucanon = unfoldRatCanon[pV];                        (* ratCanon p = (numTmrt, denTm) *)
    sndCanon = TRANS[HOL`Equal`APTERM[sndIN[], ucanon], sndINatAt[numTmrt, denTm]];
                                                        (* SND(ratCanon p) = denTm *)
    (* ¬(SND(ratCanon p) = 0) *)
    divGB = HOL`Bool`SPEC[bTm, HOL`Bool`SPEC[aTm, HOL`Stdlib`Num`gcdDividesRightThm]];  (* divides g b *)
    bEq = HOL`Bool`MP[HOL`Bool`SPEC[bTm, HOL`Bool`SPEC[gTm, exDivThm]], divGB];  (* b = g * denTm *)
    denEq0Tm = mkEq[denTm, zeroN[]];
    denEq0 = ASSUME[denEq0Tm];
    bEq0 = TRANS[bEq, TRANS[
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], gTm], denEq0],
      HOL`Bool`SPEC[gTm, HOL`Stdlib`Num`timesZeroEqThm]]];   (* SND p = 0 *)
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notB0], bEq0];
    notDen0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[denEq0Tm, falseTh]];  (* ¬(denTm = 0) *)
    notSndCanon0 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndCanon]}, notDen0];  (* ¬(SND(ratCanon p)=0) *)
    (* gcd (intNatAbs (FST(ratCanon p))) (SND(ratCanon p)) = SUC 0 *)
    fstCanon = TRANS[HOL`Equal`APTERM[fstIN[], ucanon], fstINatAt[numTmrt, denTm]];
                                                        (* FST(ratCanon p) = numTmrt *)
    naFstCanon = HOL`Equal`APTERM[intNatAbsConst[], fstCanon]; (* intNatAbs(FST(ratCanon p)) = intNatAbs numTmrt *)
    naDivEq = HOL`Bool`MP[
      HOL`Bool`SPEC[gTm, HOL`Bool`SPEC[fstP, intNatAbsIntDivNatThm]], notG0];
                                                        (* intNatAbs numTmrt = exDiv a g *)
    naFstCanonEq = TRANS[naFstCanon, naDivEq];          (* intNatAbs(FST(ratCanon p)) = exDiv a g *)
    gcdArgsEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Num`gcdConst[], naFstCanonEq], sndCanon];
                                                        (* gcd .. .. = gcd (exDiv a g)(exDiv b g) *)
    coprime = HOL`Bool`MP[
      HOL`Bool`SPEC[bTm, HOL`Bool`SPEC[aTm, coprimeReducedThm]], notG0];  (* gcd(exDiv a g)(exDiv b g) = SUC 0 *)
    gcdCanonEq = TRANS[gcdArgsEq, coprime];
    conj = HOL`Bool`CONJ[notSndCanon0, gcdCanonEq];
    HOL`Bool`GEN[pV, HOL`Bool`DISCH[notTm[mkEq[bTm, zeroN[]]],
      EQMP[HOL`Equal`SYM[unfoldRatRep[ratCanonP]], conj]]]
  ];

(* ⊢ ∀p. RAT_REP p ⇒ ratCanon p = p *)
ratCanonIdThm =
  Module[{pV, fstP, sndP, aTm, bTm, gTm, numTmrt, denTm, ratRepAssume,
          gEq1, ucanon, numEq, denEq, pairEq, surjP, result},
    pV = mkVar["p", ratPairTy];
    fstP = mkComb[fstIN[], pV]; sndP = mkComb[sndIN[], pV];
    aTm = mkComb[intNatAbsConst[], fstP]; bTm = sndP;
    gTm = gcdTm[aTm, bTm];
    numTmrt = intDivNatTm[fstP, gTm]; denTm = exDivTm[bTm, gTm];
    ratRepAssume = ASSUME[mkComb[ratRepConst[], pV]];   (* RAT_REP p *)
    gEq1 = HOL`Bool`CONJUNCT2[EQMP[unfoldRatRep[pV], ratRepAssume]];  (* gcd a b = SUC 0 *)
    ucanon = unfoldRatCanon[pV];                        (* ratCanon p = (numTmrt, denTm) *)
    numEq = TRANS[
      HOL`Equal`APTERM[mkComb[intDivNatConst[], fstP], gEq1],
      HOL`Bool`SPEC[fstP, intDivNatOneThm]];            (* intDivNat (FST p) g = FST p *)
    denEq = TRANS[
      HOL`Equal`APTERM[mkComb[exDivConst[], sndP], gEq1],
      HOL`Bool`SPEC[sndP, exDivOneThm]];                (* exDiv (SND p) g = SND p *)
    pairEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];  (* (numTmrt, denTm) = (FST p, SND p) *)
    surjP = HOL`Bool`SPEC[pV,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                  (* (FST p, SND p) = p *)
    result = TRANS[TRANS[ucanon, pairEq], surjP];       (* ratCanon p = p *)
    HOL`Bool`GEN[pV, HOL`Bool`DISCH[mkComb[ratRepConst[], pV], result]]
  ];

(* ============================================================ *)
(* ratAdd — addition of reduced fractions                       *)
(* (a,b)+(c,d) = ratCanon (a·d + c·b, b·d)                       *)
(* ============================================================ *)

repRat[q_] := mkComb[repRatConst[], q];
intAddTm[zT_, wT_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], zT], wT];
intMulTm[zT_, wT_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], zT], wT];

(* ⊢ ∀m n. ¬ (m = 0) ⇒ ¬ (n = 0) ⇒ ¬ (m * n = 0) *)
multNonzeroThm =
  Module[{mV, nV, notM0, notN0, prodEq0Tm, prodEq0, disj, case1, case2, falseTh},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    notM0 = ASSUME[notTm[mkEq[mV, zeroN[]]]];
    notN0 = ASSUME[notTm[mkEq[nV, zeroN[]]]];
    prodEq0Tm = mkEq[timesTm[mV, nV], zeroN[]];
    prodEq0 = ASSUME[prodEq0Tm];
    disj = HOL`Bool`MP[
      HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, HOL`Stdlib`Num`multEqZeroThm]], prodEq0]; (* m=0∨n=0 *)
    case1 = HOL`Bool`MP[HOL`Bool`NOTELIM[notM0], ASSUME[mkEq[mV, zeroN[]]]];  (* F *)
    case2 = HOL`Bool`MP[HOL`Bool`NOTELIM[notN0], ASSUME[mkEq[nV, zeroN[]]]];  (* F *)
    falseTh = HOL`Bool`DISJCASES[disj, case1, case2];   (* F *)
    HOL`Bool`GEN[mV, HOL`Bool`GEN[nV,
      HOL`Bool`DISCH[notTm[mkEq[mV, zeroN[]]],
        HOL`Bool`DISCH[notTm[mkEq[nV, zeroN[]]],
          HOL`Bool`NOTINTRO[HOL`Bool`DISCH[prodEq0Tm, falseTh]]]]]]
  ];

(* ⊢ RAT_REP (REP_rat q)  (q free) *)
ratRepRepThm =
  Module[{qV, repQ, rVar, repAbsInst, aVar, absRepQ, rhsThm},
    qV = mkVar["q", ratTy]; repQ = repRat[qV];
    rVar = concl[repAbsRatThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> repQ}, repAbsRatThm];
    aVar = concl[absRepRatThm][[2]];
    absRepQ = HOL`Kernel`INST[{aVar -> qV}, absRepRatThm];
    rhsThm = HOL`Equal`APTERM[repRatConst[], absRepQ];
    EQMP[HOL`Equal`SYM[repAbsInst], rhsThm]
  ];

ratAddTy = tyFun[ratTy, tyFun[ratTy, ratTy]];

(* sum-pair (a·d + c·b, b·d) of two int×num reps repQ, repR *)
ratAddPair[repQ_, repR_] :=
  Module[{a, b, c, d},
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    c = mkComb[fstIN[], repR]; d = mkComb[sndIN[], repR];
    ratPairCons[
      intAddTm[intMulTm[a, intOfNum[d]], intMulTm[c, intOfNum[b]]],
      timesTm[b, d]]
  ];

ratAddDefThm = newDefinition[mkEq[
  mkVar["ratAdd", ratAddTy],
  Module[{qV, rV},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    mkAbs[qV, mkAbs[rV,
      mkComb[absRatConst[], ratCanonTm[ratAddPair[repRat[qV], repRat[rV]]]]]]]
]];

ratAddConst[] := mkConst["ratAdd", ratAddTy];
ratAddTm[qT_, rT_] := mkComb[mkComb[ratAddConst[], qT], rT];

(* ⊢ ratAdd q r = ABS_rat (ratCanon (sum-pair)) *)
unfoldRatAdd[qT_, rT_] :=
  Module[{ap1, beta1, ap2, beta2},
    ap1 = HOL`Equal`APTHM[ratAddDefThm, qT];
    beta1 = BETACONV[concl[ap1][[2]]];
    ap2 = HOL`Equal`APTHM[TRANS[ap1, beta1], rT];
    beta2 = BETACONV[concl[ap2][[2]]];
    TRANS[ap2, beta2]
  ];

(* ⊢ ∀q r. REP_rat (ratAdd q r) = ratCanon (sum-pair) *)
repRatAddThm =
  Module[{qV, rV, repQ, repR, bDen, dDen, pairTm, numTmrt, denTm,
          notBDen0, notDDen0, notDen0, sndPairEq, notSndPair0, lands,
          repAbsInst, repEqCanon, unfAdd, apRep, body},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    repQ = repRat[qV]; repR = repRat[rV];
    bDen = mkComb[sndIN[], repQ]; dDen = mkComb[sndIN[], repR];
    pairTm = ratAddPair[repQ, repR];
    numTmrt = pairTm[[1, 2]]; denTm = pairTm[[2]];  (* numerator, denominator of the sum-pair *)
    (* ¬(b=0), ¬(d=0) from RAT_REP(REP q/r); ¬(b*d=0) *)
    notBDen0 = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepRepThm]];
    notDDen0 = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repR],
      HOL`Kernel`INST[{qV -> rV}, ratRepRepThm]]];
    notDen0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[dDen, HOL`Bool`SPEC[bDen, multNonzeroThm]], notBDen0], notDDen0];  (* ¬(b*d=0) *)
    sndPairEq = sndINatAt[numTmrt, denTm];              (* SND pair = denTm *)
    notSndPair0 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndPairEq]}, notDen0];  (* ¬(SND pair = 0) *)
    lands = HOL`Bool`MP[HOL`Bool`SPEC[pairTm, ratCanonLandsThm], notSndPair0]; (* RAT_REP(ratCanon pair) *)
    repAbsInst = HOL`Kernel`INST[
      {concl[repAbsRatThm][[1, 2, 2]] -> ratCanonTm[pairTm]}, repAbsRatThm];
    repEqCanon = EQMP[repAbsInst, lands];               (* REP(ABS(ratCanon pair)) = ratCanon pair *)
    unfAdd = unfoldRatAdd[qV, rV];                      (* ratAdd q r = ABS(ratCanon pair) *)
    apRep = HOL`Equal`APTERM[repRatConst[], unfAdd];    (* REP(ratAdd q r) = REP(ABS(ratCanon pair)) *)
    body = TRANS[apRep, repEqCanon];                    (* REP(ratAdd q r) = ratCanon pair *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, body]]
  ];

(* From ⊢ REP_rat lhs = REP_rat rhs derive ⊢ lhs = rhs (REP_rat injective). *)
ratEqFromRepEq[repEq_, lhsT_, rhsT_] :=
  Module[{aVar, absL, absR, apAbs},
    aVar = concl[absRepRatThm][[2]];
    absL = HOL`Kernel`INST[{aVar -> lhsT}, absRepRatThm];   (* ABS(REP lhs) = lhs *)
    absR = HOL`Kernel`INST[{aVar -> rhsT}, absRepRatThm];   (* ABS(REP rhs) = rhs *)
    apAbs = HOL`Equal`APTERM[absRatConst[], repEq];         (* ABS(REP lhs) = ABS(REP rhs) *)
    TRANS[HOL`Equal`SYM[absL], TRANS[apAbs, absR]]
  ];

(* ⊢ ∀q r. ratAdd q r = ratAdd r q *)
ratAddCommThm =
  Module[{qV, rV, repQ, repR, a, b, c, d, adTm, cbTm, repQR, repRQ,
          numComm, denComm, pairEq, canonEq, repEq},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    repQ = repRat[qV]; repR = repRat[rV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    c = mkComb[fstIN[], repR]; d = mkComb[sndIN[], repR];
    adTm = intMulTm[a, intOfNum[d]]; cbTm = intMulTm[c, intOfNum[b]];
    repQR = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[qV, repRatAddThm]];  (* REP(ratAdd q r) = ratCanon(intAdd ad cb, b*d) *)
    repRQ = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[rV, repRatAddThm]];  (* REP(ratAdd r q) = ratCanon(intAdd cb ad, d*b) *)
    numComm = HOL`Bool`SPEC[cbTm, HOL`Bool`SPEC[adTm, HOL`Stdlib`Int`intAddCommThm]];  (* intAdd ad cb = intAdd cb ad *)
    denComm = HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesCommThm]];          (* b*d = d*b *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numComm], denComm];
    canonEq = HOL`Equal`APTERM[ratCanonConst[], pairEq];
    repEq = TRANS[repQR, TRANS[canonEq, HOL`Equal`SYM[repRQ]]];  (* REP(ratAdd q r) = REP(ratAdd r q) *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV,
      ratEqFromRepEq[repEq, ratAddTm[qV, rV], ratAddTm[rV, qV]]]]
  ];

(* ⊢ ∀q. ratAdd q (&ℚ (&ℤ 0)) = q *)
ratAddZeroThm =
  Module[{qV, zRat, z0, repAdd, repZeroEq, fstZero, sndZero, andZ,
          mulOne, commZ, mulZeroL, numEq, denEq, pairEq, canonPairEq,
          surjQ, canonSurjEq, canonRepQ, repEq, a, b},
    qV = mkVar["q", ratTy];
    z0 = intOfNum[zeroN[]];                              (* &ℤ 0 *)
    zRat = ratOfIntTm[z0];                               (* &ℚ (&ℤ 0) *)
    a = mkComb[fstIN[], repRat[qV]]; b = mkComb[sndIN[], repRat[qV]];
    repAdd = HOL`Bool`SPEC[zRat, HOL`Bool`SPEC[qV, repRatAddThm]];
    repZeroEq = HOL`Kernel`INST[{mkVar["q", intTy] -> z0}, repRatOfIntThm];  (* REP(&ℚ&ℤ0) = (&ℤ0, SUC0) *)
    fstZero = TRANS[HOL`Equal`APTERM[fstIN[], repZeroEq], fstINatAt[z0, oneN[]]];  (* FST(REP zRat) = &ℤ0 *)
    sndZero = TRANS[HOL`Equal`APTERM[sndIN[], repZeroEq], sndINatAt[z0, oneN[]]];  (* SND(REP zRat) = SUC0 *)
    (* numerator: intAdd (intMul a (&ℤ d')) (intMul c' (&ℤ b)) → a *)
    mulOne = TRANS[
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Int`intMulConst[], a],
        HOL`Equal`APTERM[HOL`Stdlib`Int`intOfNumConst[], sndZero]],
      HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulOneThm]];     (* intMul a (&ℤ d') = a *)
    commZ = TRANS[
      HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[z0, HOL`Stdlib`Int`intMulCommThm]],
      HOL`Bool`SPEC[intOfNum[b], HOL`Stdlib`Int`intMulZeroThm]];  (* intMul(&ℤ0)(&ℤ b) = &ℤ0 *)
    mulZeroL = TRANS[
      HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Int`intMulConst[], fstZero], intOfNum[b]],
      commZ];                                             (* intMul c' (&ℤ b) = &ℤ0 *)
    numEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Int`intAddConst[], mulOne], mulZeroL],
      HOL`Bool`SPEC[a, HOL`Stdlib`Int`intAddZeroThm]];    (* numerator = a *)
    denEq = TRANS[
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], b], sndZero],
      TRANS[HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesCommThm]],
        HOL`Bool`SPEC[b, HOL`Stdlib`Num`oneTimesEqThm]]]; (* denom = b *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];  (* (num,den) = (a,b) *)
    canonPairEq = HOL`Equal`APTERM[ratCanonConst[], pairEq];
    surjQ = HOL`Bool`SPEC[repRat[qV],
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                    (* (a,b) = REP q *)
    canonSurjEq = HOL`Equal`APTERM[ratCanonConst[], surjQ];
    canonRepQ = HOL`Bool`MP[HOL`Bool`SPEC[repRat[qV], ratCanonIdThm], ratRepRepThm]; (* ratCanon(REP q) = REP q *)
    repEq = TRANS[repAdd, TRANS[canonPairEq, TRANS[canonSurjEq, canonRepQ]]];
    HOL`Bool`GEN[qV, ratEqFromRepEq[repEq, ratAddTm[qV, zRat], qV]]
  ];

(* ============================================================ *)
(* ratNeg — negation of reduced fractions (numerator sign flip) *)
(* ============================================================ *)

intNegTm[zT_] := mkComb[HOL`Stdlib`Int`intNegConst[], zT];

(* ⊢ ∀z. intNatAbs (intNeg z) = intNatAbs z *)
intNatAbsNegThm =
  Module[{zV, repZ, fstRepZ, sndRepZ, naNegUnf, fstNeg, sndNeg, sumNeg,
          addCommEq, naZ},
    zV = mkVar["z", intTy];
    repZ = repInt[zV]; fstRepZ = mkComb[fstNN[], repZ]; sndRepZ = mkComb[sndNN[], repZ];
    naNegUnf = unfoldIntNatAbs[intNegTm[zV]];   (* intNatAbs(intNeg z) = FST(REP(intNeg z))+SND(REP(intNeg z)) *)
    fstNeg = TRANS[HOL`Equal`APTERM[fstNN[], HOL`Stdlib`Int`repIntNegThm], fstNumAt[sndRepZ, fstRepZ]];
    sndNeg = TRANS[HOL`Equal`APTERM[sndNN[], HOL`Stdlib`Int`repIntNegThm], sndNumAt[sndRepZ, fstRepZ]];
    sumNeg = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], fstNeg], sndNeg];  (* = SND(REP z)+FST(REP z) *)
    addCommEq = HOL`Bool`SPEC[fstRepZ, HOL`Bool`SPEC[sndRepZ, HOL`Stdlib`Num`addCommThm]]; (* = FST(REP z)+SND(REP z) *)
    naZ = HOL`Equal`SYM[unfoldIntNatAbs[zV]];   (* FST(REP z)+SND(REP z) = intNatAbs z *)
    HOL`Bool`GEN[zV, TRANS[naNegUnf, TRANS[sumNeg, TRANS[addCommEq, naZ]]]]
  ];

ratNegTy = tyFun[ratTy, ratTy];

ratNegDefThm = newDefinition[mkEq[
  mkVar["ratNeg", ratNegTy],
  Module[{qV}, qV = mkVar["q", ratTy];
    mkAbs[qV, mkComb[absRatConst[],
      ratPairCons[intNegTm[mkComb[fstIN[], repRat[qV]]], mkComb[sndIN[], repRat[qV]]]]]]
]];

ratNegConst[] := mkConst["ratNeg", ratNegTy];
ratNegTm[qT_] := mkComb[ratNegConst[], qT];

unfoldRatNeg[qT_] :=
  Module[{ap}, ap = HOL`Equal`APTHM[ratNegDefThm, qT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]];

(* ⊢ ∀q. REP_rat (ratNeg q) = (intNeg (FST(REP q)), SND(REP q)) *)
repRatNegThm =
  Module[{qV, repQ, a, b, pairTm, ratRepREPq, notSndREPq, gcdREPq,
          fstPairEq, sndPairEq, notSndPair0, naFstEq, gcdArgsEq, conj2,
          ratRepPair, repAbsInst, repEqPair, unfNeg, apRep, body},
    qV = mkVar["q", ratTy]; repQ = repRat[qV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    pairTm = ratPairCons[intNegTm[a], b];
    ratRepREPq = EQMP[unfoldRatRep[repQ], ratRepRepThm];
    notSndREPq = HOL`Bool`CONJUNCT1[ratRepREPq];
    gcdREPq = HOL`Bool`CONJUNCT2[ratRepREPq];
    fstPairEq = fstINatAt[intNegTm[a], b];                (* FST pair = intNeg a *)
    sndPairEq = sndINatAt[intNegTm[a], b];                (* SND pair = b *)
    notSndPair0 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndPairEq]}, notSndREPq];
    naFstEq = TRANS[HOL`Equal`APTERM[intNatAbsConst[], fstPairEq],
      HOL`Bool`SPEC[a, intNatAbsNegThm]];                 (* intNatAbs(FST pair) = intNatAbs a *)
    gcdArgsEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Num`gcdConst[], naFstEq], sndPairEq];
    conj2 = TRANS[gcdArgsEq, gcdREPq];                    (* gcd(..)(SND pair) = SUC0 *)
    ratRepPair = EQMP[HOL`Equal`SYM[unfoldRatRep[pairTm]],
      HOL`Bool`CONJ[notSndPair0, conj2]];                 (* RAT_REP pair *)
    repAbsInst = HOL`Kernel`INST[
      {concl[repAbsRatThm][[1, 2, 2]] -> pairTm}, repAbsRatThm];
    repEqPair = EQMP[repAbsInst, ratRepPair];             (* REP(ABS pair) = pair *)
    unfNeg = unfoldRatNeg[qV];
    apRep = HOL`Equal`APTERM[repRatConst[], unfNeg];
    body = TRANS[apRep, repEqPair];                       (* REP(ratNeg q) = pair *)
    HOL`Bool`GEN[qV, body]
  ];

End[];
EndPackage[];
