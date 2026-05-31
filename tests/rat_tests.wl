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
