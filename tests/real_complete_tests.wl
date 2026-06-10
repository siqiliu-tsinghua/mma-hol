(* ::Package:: *)

(* Tests for M7-7 stdlib/Real/Complete.wl — Dedekind completeness (realSup),
   the Archimedean property, and ℚ-density, plus the strict-order vocabulary
   (realLtImpLe / transitivity / the strict-order embedding realOfRatLt). *)

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
Needs["HOL`Stdlib`Real`"];

(* ===== strict-order vocabulary ===== *)

HOLTest`runTests["stdlib/Real: realLtImpLeThm — ⊢ ∀x y. realLt x y ⇒ realLe x y",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtImpLeThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtImpLeThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLtLeTransThm / realLeLtTransThm — mixed transitivity",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtLeTransThm], {}, "lt-le no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtLeTransThm], "lt-le is a theorem"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeLtTransThm], {}, "le-lt no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeLtTransThm], "le-lt is a theorem"]];

HOLTest`runTests["stdlib/Real: realLtTransThm — ⊢ ∀x y z. realLt x y ⇒ realLt y z ⇒ realLt x z",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtTransThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtTransThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realOfRatLtThm — ⊢ ∀a b. realLt (&ℝ a)(&ℝ b) = ratLt a b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatLtThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatLtThm], "is a theorem"]];

(* ===== realSup: definition + cut + rep/mem ===== *)

HOLTest`runTests["stdlib/Real: realSupDefThm — ⊢ realSup = (λS. ABS_real (λq. ∃a. S a ∧ REP_real a q))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realSupDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realSupDefThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: supCutIsCutThm — nonempty ⇒ bounded ⇒ IS_CUT (sup lower set)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`supCutIsCutThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`supCutIsCutThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: repRealSupThm — conditional carve round-trip for realSup",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repRealSupThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repRealSupThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realSupMemThm — membership in the sup cut",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realSupMemThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realSupMemThm], "is a theorem"]];

(* ===== sup is the least upper bound ===== *)

HOLTest`runTests["stdlib/Real: realSupUpperThm — sup is an upper bound",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realSupUpperThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realSupUpperThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realSupLeastThm — sup is below every upper bound",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realSupLeastThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realSupLeastThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: dedekindCompleteThm — ℝ is Dedekind-complete",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`dedekindCompleteThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`dedekindCompleteThm], "is a theorem"]];

(* ===== Archimedean + density ===== *)

HOLTest`runTests["stdlib/Real: realRatBoundThm — ⊢ ∀x. ∃q. realLt x (&ℝ q)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realRatBoundThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realRatBoundThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realArchThm — ⊢ ∀x. ∃n. realLt x (&ℝ (&ℚ (&ℤ n)))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realArchThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realArchThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realDenseThm — ℚ dense in ℝ",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realDenseThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realDenseThm], "is a theorem"]];
