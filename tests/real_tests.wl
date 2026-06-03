(* ::Package:: *)

(* Tests for M7-7 stdlib/Real/Cut.wl. Stage 1: reusable strict-order
   lemmas, the IS_CUT predicate, the principal-cut lemma, and the
   real type carve (ABS_real / REP_real). *)

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

(* ===== reusable strict-order lemmas ===== *)

HOLTest`runTests["stdlib/Real: intOfNumLtThm — ⊢ ∀m n. intLt (&ℤ m)(&ℤ n) = (m < n)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`intOfNumLtThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`intOfNumLtThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratOfIntLtThm — ⊢ ∀a b. ratLt (&ℚ a)(&ℚ b) = intLt a b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratOfIntLtThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratOfIntLtThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratLtIrreflThm — ⊢ ∀x. ¬ (ratLt x x)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratLtIrreflThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratLtIrreflThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratLtTransThm — ⊢ ∀a b c. ratLt a b ⇒ ratLt b c ⇒ ratLt a c",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratLtTransThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratLtTransThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratZeroLtOneThm — ⊢ ratLt (&ℚ(&ℤ 0)) (&ℚ(&ℤ(SUC 0)))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratZeroLtOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratZeroLtOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratNegOneLtZeroThm — ⊢ ratLt (ratNeg 1) (&ℚ(&ℤ 0))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratNegOneLtZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratNegOneLtZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratPredLtThm — ⊢ ∀q. ratLt (ratAdd q (ratNeg 1)) q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratPredLtThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratPredLtThm], "is a theorem"]];

(* ===== IS_CUT predicate + carve ===== *)

HOLTest`runTests["stdlib/Real: isCutDefThm — ⊢ IS_CUT = (λL. …)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`isCutDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`isCutDefThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`isCutDefThm][[1, 2]] === mkConst["IS_CUT", tyFun[tyFun[mkType["rat", {}], boolTy], boolTy]],
    "LHS is the IS_CUT constant"]];

HOLTest`runTests["stdlib/Real: principalCutIsCutThm — ⊢ ∀q. IS_CUT (λp. ratLt p q)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`principalCutIsCutThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`principalCutIsCutThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`principalCutIsCutThm][[1]] === mkConst["∀", tyFun[tyFun[mkType["rat", {}], boolTy], boolTy]],
    "outermost head is ∀ over rat"]];

HOLTest`runTests["stdlib/Real: isCutZeroWitnessThm — ⊢ IS_CUT (λp. ratLt p (&ℚ(&ℤ 0)))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`isCutZeroWitnessThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`isCutZeroWitnessThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`isCutZeroWitnessThm][[1]] === isCutConst[],
    "head constant is IS_CUT"]];

HOLTest`runTests["stdlib/Real: absRepRealThm — ⊢ ABS_real (REP_real x) = x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`absRepRealThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`absRepRealThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: repAbsRealThm — ⊢ IS_CUT L = (REP_real (ABS_real L) = L)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repAbsRealThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repAbsRealThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: repRealIsCutThm — ⊢ IS_CUT (REP_real x)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repRealIsCutThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repRealIsCutThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`repRealIsCutThm][[1]] === isCutConst[],
    "head constant is IS_CUT"]];

(* ===== cut accessors ===== *)

HOLTest`runTests["stdlib/Real: realNonemptyThm — ⊢ ∀x. ∃q. REP_real x q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNonemptyThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNonemptyThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realProperThm — ⊢ ∀x. ∃q. ¬ (REP_real x q)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realProperThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realProperThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realDownClosedThm — ⊢ ∀x q r. REP_real x q ⇒ ratLt r q ⇒ REP_real x r",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realDownClosedThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realDownClosedThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realOpenThm — ⊢ ∀x q. REP_real x q ⇒ ∃r. REP_real x r ∧ ratLt q r",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOpenThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOpenThm], "is a theorem"]];

(* ===== the order: realLe ===== *)

HOLTest`runTests["stdlib/Real: realLeDefThm — ⊢ realLe = (λx y. ∀q. REP_real x q ⇒ REP_real y q)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeDefThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`realLeDefThm][[1, 2]] === realLeConst[],
    "LHS is the realLe constant"]];

HOLTest`runTests["stdlib/Real: realLeReflThm — ⊢ ∀x. realLe x x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeReflThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeReflThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLeTransThm — ⊢ ∀x y z. realLe x y ⇒ realLe y z ⇒ realLe x z",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeTransThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeTransThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLeAntisymThm — ⊢ ∀x y. realLe x y ⇒ realLe y x ⇒ x = y",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeAntisymThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeAntisymThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratLeCasesThm — ⊢ ∀a b. ratLe a b ⇒ ratLt a b ∨ (a = b)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratLeCasesThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratLeCasesThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLeTotalThm — ⊢ ∀x y. realLe x y ∨ realLe y x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeTotalThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeTotalThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLtDefThm — ⊢ realLt = (λx y. ¬ (realLe y x))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtDefThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`realLtDefThm][[1, 2]] === realLtConst[],
    "LHS is the realLt constant"]];

HOLTest`runTests["stdlib/Real: realLtNotLeThm — ⊢ ∀x y. realLt x y = ¬ (realLe y x)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtNotLeThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtNotLeThm], "is a theorem"]];
