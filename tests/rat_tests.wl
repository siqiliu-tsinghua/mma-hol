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
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`dividesZeroImpZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`dividesZeroImpZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: dividesOneThm — ⊢ ∀d. divides d (SUC 0) ⇒ d = SUC 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`dividesOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`dividesOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdOneRightThm — ⊢ ∀a. gcd a (SUC 0) = SUC 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`gcdOneRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`gcdOneRightThm], "is a theorem"]];

(* ===== Bezout chain ===== *)

HOLTest`runTests["stdlib/Rat: dividesAntisymThm — ⊢ ∀a b. divides a b ⇒ divides b a ⇒ a = b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`dividesAntisymThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`dividesAntisymThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdZeroRightThm — ⊢ ∀a. gcd a 0 = a",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`gcdZeroRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`gcdZeroRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdRecThm — ⊢ ∀a b. ¬(b=0) ⇒ gcd a b = gcd b (a MOD b)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`gcdRecThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`gcdRecThm], "is a theorem"]];

(* ===== intNatAbs ===== *)

HOLTest`runTests["stdlib/Rat: intNatAbsZeroThm — ⊢ intNatAbs (&ℤ 0) = 0",
  Module[{c, zeroN},
    zeroN = HOL`Stdlib`Num`zeroConst[];
    HOLTest`assertEq[hyp[HOL`Stdlib`Rat`intNatAbsZeroThm], {}, "no hyps"];
    c = concl[HOL`Stdlib`Rat`intNatAbsZeroThm];
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

HOLTest`runTests["stdlib/Rat: exDivThm — ⊢ ∀g n. divides g n ⇒ n = g * exDiv n g",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`exDivThm], {}, "no hyps"];
  HOLTest`assertTrue[
    MatchQ[concl[HOL`Stdlib`Rat`exDivThm],
      HOLTest`quantNestPat["∀", 2,
        comb[comb[const["⇒", _], comb[comb[const["divides", _], _], _]],
          comb[comb[const["=", _], _], _]]]],
    "shape: ∀g n. divides g n ⇒ n = g * exDiv n g"]];

HOLTest`runTests["stdlib/Rat: exDivOneThm — ⊢ ∀n. exDiv n (SUC 0) = n",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`exDivOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`exDivOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: exDivZeroThm — ⊢ ∀g. ¬(g = 0) ⇒ exDiv 0 g = 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`exDivZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`exDivZeroThm], "is a theorem"]];

(* ===== stage c: gcd-reduction number theory ===== *)

HOLTest`runTests["stdlib/Rat: dividesMultBothLeftThm — ⊢ ∀g h x. divides h x ⇒ divides (g*h) (g*x)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`dividesMultBothLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`dividesMultBothLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: gcdNonzeroFromRightThm — ⊢ ∀a b. ¬(b=0) ⇒ ¬(gcd a b = 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`gcdNonzeroFromRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`gcdNonzeroFromRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: coprimeReducedThm — ⊢ ∀a b. ¬(gcd a b=0) ⇒ gcd (exDiv a (gcd a b)) (exDiv b (gcd a b)) = SUC 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`coprimeReducedThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`coprimeReducedThm], "is a theorem"]];

(* ===== stage c: intDivNat (exact division of an int by a nat) ===== *)

HOLTest`runTests["stdlib/Rat: intDivNat : int → num → int",
  HOLTest`assertEq[HOL`Kernel`constType["intDivNat"],
    tyFun[mkType["int", {}], tyFun[mkType["num", {}], mkType["int", {}]]],
    "intDivNat : int → num → int"]];

HOLTest`runTests["stdlib/Rat: repIntDivNatThm — ⊢ ∀z g. ¬(g=0) ⇒ REP_int (intDivNat z g) = (..,..)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`repIntDivNatThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`repIntDivNatThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intDivNatOneThm — ⊢ ∀z. intDivNat z (SUC 0) = z",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`intDivNatOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`intDivNatOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Rat: intNatAbsIntDivNatThm — ⊢ ∀z g. ¬(g=0) ⇒ intNatAbs (intDivNat z g) = exDiv (intNatAbs z) g",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`intNatAbsIntDivNatThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`intNatAbsIntDivNatThm], "is a theorem"]];

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

HOLTest`runTests["stdlib/Rat: multNonzeroThm — ⊢ ∀m n. ¬(m=0) ⇒ ¬(n=0) ⇒ ¬(m*n=0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`multNonzeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`multNonzeroThm], "is a theorem"]];

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
  HOLTest`assertEq[hyp[HOL`Stdlib`Rat`intNatAbsNegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Rat`intNatAbsNegThm], "is a theorem"]];

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
