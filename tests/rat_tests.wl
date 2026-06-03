(* ::Package:: *)

(* Tests for M7-6 stdlib/Rat.wl. Stage a: ℕ helper lemmas, intNatAbs,
   RAT_REP carve + witness. *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Pair`"];
Needs["HOL`Stdlib`Num`"];
Needs["HOL`Stdlib`Int`"];
Needs["HOL`Stdlib`Rat`"];

(* ===== ℕ helper lemmas ===== *)

HOLTest`runTests["stdlib/Rat: dividesZeroImpZeroThm — ⊢ ∀n. divides 0 n ⇒ n = 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`dividesZeroImpZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`dividesZeroImpZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: dividesOneThm — ⊢ ∀d. divides d (SUC 0) ⇒ d = SUC 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`dividesOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`dividesOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdOneRightThm — ⊢ ∀a. gcd a (SUC 0) = SUC 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`gcdOneRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`gcdOneRightThm], "is a theorem"]];

(* ===== Bezout chain ===== *)

HOLTest`runTests["stdlib/Rat: dividesAntisymThm — ⊢ ∀a b. divides a b ⇒ divides b a ⇒ a = b",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`dividesAntisymThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`dividesAntisymThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdZeroRightThm — ⊢ ∀a. gcd a 0 = a",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`gcdZeroRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`gcdZeroRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdRecThm — ⊢ ∀a b. ¬(b=0) ⇒ gcd a b = gcd b (a MOD b)",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`gcdRecThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`gcdRecThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: bezoutNatThm — ⊢ ∀a b. ∃x y. a*x = b*y + gcd a b ∨ b*y = a*x + gcd a b",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`bezoutNatThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`FTA`bezoutNatThm],
      HOLTest`quantNestPat["∀", 2,
        HOLTest`quantNestPat["∃", 2, comb[comb[const["∨", _], _], _]]]],
    "shape: ∀a b. ∃x y. _ ∨ _"]];

HOLTest`runTests["stdlib/Rat: coprimeDividesProductThm — ⊢ ∀a b c. gcd a b = SUC 0 ⇒ divides a (b*c) ⇒ divides a c",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`coprimeDividesProductThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`FTA`coprimeDividesProductThm],
      HOLTest`quantNestPat["∀", 3,
        comb[comb[const["⇒", _], comb[comb[const["=", _], _], _]],
          comb[comb[const["⇒", _], comb[comb[const["divides", _], _], _]],
            comb[comb[const["divides", _], _], _]]]]],
    "shape: ∀a b c. gcd a b = SUC 0 ⇒ divides a (b*c) ⇒ divides a c"]];

(* ===== intNatAbs ===== *)

HOLTest`runTests["stdlib/Rat: intNatAbsZeroThm — ⊢ intNatAbs (&ℤ 0) = 0",
  Module[{c, zeroN},
    zeroN = HOL`Stdlib`Num`zeroConst[];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intNatAbsZeroThm], {}, "no hyps"];
    c = concl[HOL`Stdlib`Int`intNatAbsZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c[[2]], zeroN], "RHS is 0"]]];

(* ===== RAT_REP + carve ===== *)

HOLTest`runTests["stdlib/Rat: ratRepWitnessThm — ⊢ RAT_REP (&ℤ 0, SUC 0), no hyps",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratRepWitnessThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratRepWitnessThm],
      comb[const["RAT_REP", _], _]],
    "concl is RAT_REP applied to a pair"]];

HOLTest`runTests["stdlib/Rat: rat type carved — ABS_rat/REP_rat round-trips exist",
  Module[{ratTy},
    ratTy = mkType["rat", {}];
    HOLTest`assertEq[HOL`Kernel`constType["REP_rat"],
      tyFun[ratTy, HOL`Stdlib`Pair`prodTy[mkType["int", {}], mkType["num", {}]]],
      "REP_rat : rat → int × num"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`absRepRatThm], "absRepRatThm is a theorem"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Rat`absRepRatThm], {}, "absRepRatThm no hyps"]]];

(* ===== stage b: &ℚ embedding ===== *)

HOLTest`runTests["stdlib/Rat: ratRepOneDenomThm — ⊢ RAT_REP (q, SUC 0), no hyps",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratRepOneDenomThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratRepOneDenomThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: &ℚ : int → rat",
  HOLTest`assertEq[HOL`Kernel`constType["&ℚ"],
    tyFun[mkType["int", {}], mkType["rat", {}]], "&ℚ : int → rat"]];

HOLTest`runTests["stdlib/Rat: repRatOfIntThm — ⊢ REP_rat (&ℚ q) = (q, SUC 0), no hyps",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`repRatOfIntThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`repRatOfIntThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratOfIntInjThm — ⊢ ∀a b. &ℚ a = &ℚ b ⇒ a = b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratOfIntInjThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratOfIntInjThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["⇒", _], comb[comb[const["=", _], _], _]],
          comb[comb[const["=", _], _], _]]]],
    "shape: ∀a b. &ℚ a = &ℚ b ⇒ a = b"]];

(* ===== stage c: exDiv (exact quotient via Hilbert ε) ===== *)

HOLTest`runTests["stdlib/Num: exDivThm — ⊢ ∀g n. divides g n ⇒ n = g * exDiv n g (migrated from Rat)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`exDivThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Num`exDivThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["⇒", _], comb[comb[const["divides", _], _], _]],
          comb[comb[const["=", _], _], _]]]],
    "shape: ∀g n. divides g n ⇒ n = g * exDiv n g"]];

HOLTest`runTests["stdlib/Num: exDivOneThm — ⊢ ∀n. exDiv n (SUC 0) = n (migrated from Rat)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`exDivOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Num`exDivOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Num: exDivZeroThm — ⊢ ∀g. ¬(g = 0) ⇒ exDiv 0 g = 0 (migrated from Rat)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`exDivZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Num`exDivZeroThm], "is a theorem"]];

(* ===== stage c: gcd-reduction number theory ===== *)

HOLTest`runTests["stdlib/Rat: dividesMultBothLeftThm — ⊢ ∀g h x. divides h x ⇒ divides (g*h) (g*x)",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`dividesMultBothLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`dividesMultBothLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdNonzeroFromRightThm — ⊢ ∀a b. ¬(b=0) ⇒ ¬(gcd a b = 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`gcdNonzeroFromRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`gcdNonzeroFromRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: coprimeReducedThm — ⊢ ∀a b. ¬(gcd a b=0) ⇒ gcd (exDiv a (gcd a b)) (exDiv b (gcd a b)) = SUC 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`coprimeReducedThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`coprimeReducedThm], "is a theorem"]];

(* ===== stage c: intDivNat (exact division of an int by a nat) ===== *)

HOLTest`runTests["stdlib/Rat: intDivNat : int → num → int",
  HOLTest`assertEq[HOL`Kernel`constType["intDivNat"],
    tyFun[mkType["int", {}], tyFun[mkType["num", {}], mkType["int", {}]]],
    "intDivNat : int → num → int"]];

HOLTest`runTests["stdlib/Rat: repIntDivNatThm — ⊢ ∀z g. ¬(g=0) ⇒ REP_int (intDivNat z g) = (..,..)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`repIntDivNatThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`repIntDivNatThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intDivNatOneThm — ⊢ ∀z. intDivNat z (SUC 0) = z",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intDivNatOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intDivNatOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intNatAbsIntDivNatThm — ⊢ ∀z g. ¬(g=0) ⇒ intNatAbs (intDivNat z g) = exDiv (intNatAbs z) g",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intNatAbsIntDivNatThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intNatAbsIntDivNatThm], "is a theorem"]];

(* ===== stage c: ratCanon (gcd-reduction to lowest terms) ===== *)

HOLTest`runTests["stdlib/Rat: ratCanon : int × num → int × num",
  Module[{ratPairTy},
    ratPairTy = HOL`Stdlib`Pair`prodTy[mkType["int", {}], mkType["num", {}]];
    HOLTest`assertEq[HOL`Kernel`constType["ratCanon"],
      tyFun[ratPairTy, ratPairTy], "ratCanon : int × num → int × num"]]];

HOLTest`runTests["stdlib/Rat: ratCanonLandsThm — ⊢ ∀p. ¬(SND p = 0) ⇒ RAT_REP (ratCanon p)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCanonLandsThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratCanonLandsThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["⇒", _], _],
          comb[const["RAT_REP", _], comb[const["ratCanon", _], _]]]]],
    "shape: ∀p. ¬(SND p=0) ⇒ RAT_REP (ratCanon p)"]];

HOLTest`runTests["stdlib/Rat: ratCanonIdThm — ⊢ ∀p. RAT_REP p ⇒ ratCanon p = p",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCanonIdThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratCanonIdThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["⇒", _], comb[const["RAT_REP", _], _]],
          comb[comb[const["=", _], comb[const["ratCanon", _], _]], _]]]],
    "shape: ∀p. RAT_REP p ⇒ ratCanon p = p"]];

(* ===== stage d: ratAdd (addition of reduced fractions) ===== *)

HOLTest`runTests["stdlib/Rat: ratRepRepThm — ⊢ RAT_REP (REP_rat q)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratRepRepThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratRepRepThm],
      comb[const["RAT_REP", _], comb[const["REP_rat", _], _]]],
    "concl is RAT_REP (REP_rat q)"]];

HOLTest`runTests["stdlib/Num: multNonzeroThm — ⊢ ∀m n. ¬(m=0) ⇒ ¬(n=0) ⇒ ¬(m*n=0) (migrated from Rat)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`multNonzeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Num`multNonzeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratAdd : rat → rat → rat",
  HOLTest`assertEq[HOL`Kernel`constType["ratAdd"],
    tyFun[mkType["rat", {}], tyFun[mkType["rat", {}], mkType["rat", {}]]],
    "ratAdd : rat → rat → rat"]];

HOLTest`runTests["stdlib/Rat: repRatAddThm — ⊢ ∀q r. REP_rat (ratAdd q r) = ratCanon (..)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`repRatAddThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`repRatAddThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _], comb[const["REP_rat", _], comb[comb[const["ratAdd", _], _], _]]],
          comb[const["ratCanon", _], _]]]],
    "shape: ∀q r. REP_rat (ratAdd q r) = ratCanon (..)"]];

HOLTest`runTests["stdlib/Rat: ratAddCommThm — ⊢ ∀q r. ratAdd q r = ratAdd r q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratAddCommThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratAddCommThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _], comb[comb[const["ratAdd", _], _], _]],
          comb[comb[const["ratAdd", _], _], _]]]],
    "shape: ∀q r. ratAdd q r = ratAdd r q"]];

HOLTest`runTests["stdlib/Rat: ratAddZeroThm — ⊢ ∀q. ratAdd q (&ℚ (&ℤ 0)) = q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratAddZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratAddZeroThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[comb[const["ratAdd", _], _], _]], _]]],
    "shape: ∀q. ratAdd q (&ℚ&ℤ0) = q"]];

HOLTest`runTests["stdlib/Rat: intNatAbsNegThm — ⊢ ∀z. intNatAbs (intNeg z) = intNatAbs z",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intNatAbsNegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intNatAbsNegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratNeg : rat → rat",
  HOLTest`assertEq[HOL`Kernel`constType["ratNeg"],
    tyFun[mkType["rat", {}], mkType["rat", {}]], "ratNeg : rat → rat"]];

HOLTest`runTests["stdlib/Rat: repRatNegThm — ⊢ ∀q. REP_rat (ratNeg q) = (intNeg (FST(REP q)), SND(REP q))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`repRatNegThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`repRatNegThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[const["REP_rat", _], comb[const["ratNeg", _], _]]], _]]],
    "shape: ∀q. REP_rat (ratNeg q) = (..)"]];

(* ===== lowest-terms uniqueness (cross-multiplication) ===== *)

HOLTest`runTests["stdlib/Rat: gcdCommThm — ⊢ ∀a b. gcd a b = gcd b a",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`gcdCommThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`gcdCommThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intNatAbsMulOfNumThm — ⊢ ∀z n. intNatAbs (intMul z (&ℤ n)) = intNatAbs z * n",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intNatAbsMulOfNumThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intNatAbsMulOfNumThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratEqCrossThm — ⊢ ∀q r. (q = r) = (cross-mult)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratEqCrossThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratEqCrossThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _], comb[comb[const["=", _], _], _]],
          comb[comb[const["=", _], _], _]]]],
    "shape: ∀q r. (q = r) = (_ = _)"]];

(* ===== additive-inverse support lemmas ===== *)

HOLTest`runTests["stdlib/Rat: gcdZeroLeftThm — ⊢ ∀m. gcd 0 m = m",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`gcdZeroLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`gcdZeroLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: exDivSelfThm — ⊢ ∀m. ¬(m = 0) ⇒ exDiv m m = SUC 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`exDivSelfThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`exDivSelfThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intDivNatZeroThm — ⊢ ∀g. ¬(g = 0) ⇒ intDivNat (&ℤ 0) g = &ℤ 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intDivNatZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intDivNatZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratCanonZeroNumThm — ⊢ ∀m. ¬(m = 0) ⇒ ratCanon (&ℤ 0, m) = (&ℤ 0, SUC 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCanonZeroNumThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratCanonZeroNumThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratAddNegThm — ⊢ ∀q. ratAdd q (ratNeg q) = &ℚ (&ℤ 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratAddNegThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratAddNegThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[comb[const["ratAdd", _], _], comb[const["ratNeg", _], _]]], _]]],
    "shape: ∀q. ratAdd q (ratNeg q) = &ℚ&ℤ0"]];

(* ===== ratCanon-respects layer (→ ratAddAssoc) ===== *)

HOLTest`runTests["stdlib/Rat: intMulDivNatCancelThm — ⊢ ∀z g. ¬(g=0) ⇒ divides g (intNatAbs z) ⇒ intMul (intDivNat z g) (&ℤ g) = z",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intMulDivNatCancelThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intMulDivNatCancelThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratCanonEquivThm — ⊢ ∀p. ¬(SND p=0) ⇒ ratCanon p cross-equiv p",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCanonEquivThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratCanonEquivThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratCanonInjThm — ⊢ ∀p p'. RAT_REP p ⇒ RAT_REP p' ⇒ cross ⇒ p = p'",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCanonInjThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratCanonInjThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratCrossTransThm — ⊢ ∀a b c d e f. ¬(d=0) ⇒ cross ⇒ cross ⇒ cross (transitivity)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCrossTransThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratCrossTransThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratCanonRespectsThm — ⊢ ∀p p'. ¬(SND p=0) ⇒ ¬(SND p'=0) ⇒ cross ⇒ ratCanon p = ratCanon p'",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCanonRespectsThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratCanonRespectsThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratAddCongLeftThm — left-operand cross-equiv congruence for ratCanon of the sum-pair",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratAddCongLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratAddCongLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratAddCongRightThm — right-operand cross-equiv congruence for ratCanon of the sum-pair",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratAddCongRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratAddCongRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratAddAssocThm — ⊢ ∀q r v. ratAdd (ratAdd q r) v = ratAdd q (ratAdd r v)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratAddAssocThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratAddAssocThm],
      HOLTest`quantNestPat["∀", 3,
        comb[comb[const["=", _],
          comb[comb[const["ratAdd", _], comb[comb[const["ratAdd", _], _], _]], _]], _]]],
    "shape: ∀q r v. ratAdd (ratAdd q r) v = ratAdd q (ratAdd r v)"]];

(* ===== stage e: ratMul (multiplication of reduced fractions) ===== *)

HOLTest`runTests["stdlib/Rat: ratMul : rat → rat → rat",
  HOLTest`assertEq[HOL`Kernel`constType["ratMul"],
    tyFun[mkType["rat", {}], tyFun[mkType["rat", {}], mkType["rat", {}]]],
    "ratMul : rat → rat → rat"]];

HOLTest`runTests["stdlib/Rat: repRatMulThm — ⊢ ∀q r. REP_rat (ratMul q r) = ratCanon (..)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`repRatMulThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`repRatMulThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _], comb[const["REP_rat", _], comb[comb[const["ratMul", _], _], _]]],
          comb[const["ratCanon", _], _]]]],
    "shape: ∀q r. REP_rat (ratMul q r) = ratCanon (..)"]];

HOLTest`runTests["stdlib/Rat: ratMulCommThm — ⊢ ∀q r. ratMul q r = ratMul r q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulCommThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratMulCommThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _], comb[comb[const["ratMul", _], _], _]],
          comb[comb[const["ratMul", _], _], _]]]],
    "shape: ∀q r. ratMul q r = ratMul r q"]];

HOLTest`runTests["stdlib/Rat: ratMulOneThm — ⊢ ∀q. ratMul q (&ℚ (&ℤ (SUC 0))) = q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulOneThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratMulOneThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[comb[const["ratMul", _], _], _]], _]]],
    "shape: ∀q. ratMul q (&ℚ&ℤ1) = q"]];

HOLTest`runTests["stdlib/Rat: ratMulZeroThm — ⊢ ∀q. ratMul q (&ℚ (&ℤ 0)) = &ℚ (&ℤ 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratMulZeroThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[comb[const["ratMul", _], _], _]], _]]],
    "shape: ∀q. ratMul q (&ℚ&ℤ0) = &ℚ&ℤ0"]];

HOLTest`runTests["stdlib/Rat: ratMulCongLeftThm — left-operand cross-equiv congruence for ratCanon of the product-pair",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulCongLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratMulCongLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratMulCongRightThm — right-operand cross-equiv congruence for ratCanon of the product-pair",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulCongRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratMulCongRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratMulAssocThm — ⊢ ∀q r v. ratMul (ratMul q r) v = ratMul q (ratMul r v)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulAssocThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratMulAssocThm],
      HOLTest`quantNestPat["∀", 3,
        comb[comb[const["=", _],
          comb[comb[const["ratMul", _], comb[comb[const["ratMul", _], _], _]], _]], _]]],
    "shape: ∀q r v. ratMul (ratMul q r) v = ratMul q (ratMul r v)"]];

HOLTest`runTests["stdlib/Rat: ratMulDistribThm — ⊢ ∀z w v. ratMul z (ratAdd w v) = ratAdd (ratMul z w) (ratMul z v)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulDistribThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratMulDistribThm],
      HOLTest`quantNestPat["∀", 3,
        comb[comb[const["=", _], comb[comb[const["ratMul", _], _], comb[comb[const["ratAdd", _], _], _]]],
          comb[comb[const["ratAdd", _], comb[comb[const["ratMul", _], _], _]],
            comb[comb[const["ratMul", _], _], _]]]]],
    "shape: ∀z w v. ratMul z (ratAdd w v) = ratAdd (ratMul z w) (ratMul z v)"]];

(* ===== stage e: ratInv supporting lemmas ===== *)

HOLTest`runTests["stdlib/Rat: intNatAbsOfNumThm — ⊢ ∀n. intNatAbs (&ℤ n) = n",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intNatAbsOfNumThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intNatAbsOfNumThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intSqNatAbsThm — ⊢ ∀z. intMul z z = &ℤ (intNatAbs z * intNatAbs z)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intSqNatAbsThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intSqNatAbsThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdSelfThm — ⊢ ∀m. gcd m m = m",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`gcdSelfThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`FTA`gcdSelfThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratCanonSelfThm — ⊢ ∀m. ¬(m=0) ⇒ ratCanon (&ℤ m, m) = (&ℤ (SUC 0), SUC 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratCanonSelfThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratCanonSelfThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intNatAbsNonzeroThm — ⊢ ∀z. ¬(z=&ℤ0) ⇒ ¬(intNatAbs z = 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intNatAbsNonzeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intNatAbsNonzeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratNumNonzeroThm — ⊢ ∀q. ¬(q=&ℚ&ℤ0) ⇒ ¬(FST (REP_rat q) = &ℤ 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratNumNonzeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratNumNonzeroThm], "is a theorem"]];

(* ===== stage e: ratInv → ℚ is a FIELD ===== *)

HOLTest`runTests["stdlib/Rat: ratInv : rat → rat",
  HOLTest`assertEq[HOL`Kernel`constType["ratInv"],
    tyFun[mkType["rat", {}], mkType["rat", {}]], "ratInv : rat → rat"]];

HOLTest`runTests["stdlib/Rat: repRatInvThm — ⊢ ∀q. ¬(q=&ℚ&ℤ0) ⇒ REP_rat (ratInv q) = ratCanon (..)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`repRatInvThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`repRatInvThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratMulInvThm — ⊢ ∀q. ¬(q=&ℚ&ℤ0) ⇒ ratMul q (ratInv q) = &ℚ (&ℤ (SUC 0))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulInvThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratMulInvThm],
      HOLTest`quantNestPat["∀", 1,
        comb[comb[const["⇒", _], _],
          comb[comb[const["=", _], comb[comb[const["ratMul", _], _], comb[const["ratInv", _], _]]], _]]]],
    "shape: ∀q. ¬(q=&ℚ&ℤ0) ⇒ ratMul q (ratInv q) = &ℚ&ℤ1"]];

(* ===== stage f: order (ratLe / ratLt) ===== *)

HOLTest`runTests["stdlib/Rat: intLeMulNonnegCancelThm — ⊢ ∀u x y. intLe(&ℤ0)u ⇒ ¬(u=&ℤ0) ⇒ intLe(u·x)(u·y) ⇒ intLe x y",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`intLeMulNonnegCancelThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intLeMulNonnegCancelThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLe : rat → rat → bool",
  HOLTest`assertEq[HOL`Kernel`constType["ratLe"],
    tyFun[mkType["rat", {}], tyFun[mkType["rat", {}], mkType["bool", {}]]],
    "ratLe : rat → rat → bool"]];

HOLTest`runTests["stdlib/Rat: ratLeReflThm — ⊢ ∀q. ratLe q q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLeReflThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLeReflThm], "is a theorem"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratLeReflThm],
      HOLTest`quantNestPat["∀", 1, comb[comb[const["ratLe", _], _], _]]],
    "shape: ∀q. ratLe q q"]];

HOLTest`runTests["stdlib/Rat: ratLeAntisymThm — ⊢ ∀q r. ratLe q r ⇒ ratLe r q ⇒ q = r",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLeAntisymThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLeAntisymThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLeTransThm — ⊢ ∀q r v. ratLe q r ⇒ ratLe r v ⇒ ratLe q v",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLeTransThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLeTransThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLeTotalThm — ⊢ ∀q r. ratLe q r ∨ ratLe r q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLeTotalThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLeTotalThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLt : rat → rat → bool",
  HOLTest`assertEq[HOL`Kernel`constType["ratLt"],
    tyFun[mkType["rat", {}], tyFun[mkType["rat", {}], mkType["bool", {}]]],
    "ratLt : rat → rat → bool"]];

HOLTest`runTests["stdlib/Rat: ratLtNotLeThm — ⊢ ∀q r. ratLt q r = ¬(ratLe r q)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLtNotLeThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLtNotLeThm], "is a theorem"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratLtNotLeThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _], comb[comb[const["ratLt", _], _], _]],
          comb[const["¬", _], comb[comb[const["ratLe", _], _], _]]]]],
    "shape: ∀q r. ratLt q r = ¬(ratLe r q)"]];

(* ===== stage f: compatibility ===== *)

HOLTest`runTests["stdlib/Rat: pairLeCongLeftThm — cross-product order respects left cross-equiv",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`pairLeCongLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`pairLeCongLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: pairLeCongRightThm — cross-product order respects right cross-equiv",
  HOLTest`assertEq[hyp[HOL`Stdlib`Int`pairLeCongRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Int`pairLeCongRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLeAddMonoThm — ⊢ ∀q r u. ratLe q r ⇒ ratLe (ratAdd q u) (ratAdd r u)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLeAddMonoThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLeAddMonoThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLeMulNonnegThm — ⊢ ∀u q r. ratLe (&ℚ&ℤ0) u ⇒ ratLe q r ⇒ ratLe (ratMul u q) (ratMul u r)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLeMulNonnegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLeMulNonnegThm], "is a theorem"]];

(* ===== stage g: &ℚ ring/order homomorphism ===== *)

HOLTest`runTests["stdlib/Rat: ratOfIntAddThm — ⊢ ∀a b. &ℚ (intAdd a b) = ratAdd (&ℚ a) (&ℚ b)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratOfIntAddThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratOfIntAddThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratOfIntMulThm — ⊢ ∀a b. &ℚ (intMul a b) = ratMul (&ℚ a) (&ℚ b)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratOfIntMulThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratOfIntMulThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratOfIntLeThm — ⊢ ∀a b. ratLe (&ℚ a) (&ℚ b) = intLe a b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratOfIntLeThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratOfIntLeThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratAddSubCancelThm — ⊢ ∀q u. ratAdd (ratAdd q u) (ratNeg u) = q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratAddSubCancelThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratAddSubCancelThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLtAddMonoThm — ⊢ ∀q r u. ratLt q r ⇒ ratLt (ratAdd q u) (ratAdd r u)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLtAddMonoThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLtAddMonoThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratLtMulPosCancelThm — ⊢ ∀x y u. ratLe 0 u ⇒ ratLt (x·u)(y·u) ⇒ ratLt x y",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratLtMulPosCancelThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratLtMulPosCancelThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratMulTwoThm — ⊢ ∀x. ratMul x (&ℚ&ℤ2) = ratAdd x x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratMulTwoThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratMulTwoThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: ratDenseThm — ⊢ ∀q r. ratLt q r ⇒ ratLt q (½(q+r)) ∧ ratLt (½(q+r)) r",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`ratDenseThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`ratDenseThm], "is a theorem"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`ratDenseThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["⇒", _], comb[comb[const["ratLt", _], _], _]],
          comb[comb[const["∧", _], comb[comb[const["ratLt", _], _], _]],
            comb[comb[const["ratLt", _], _], _]]]]],
    "shape: ∀q r. ratLt q r ⇒ ratLt q m ∧ ratLt m r"]];
