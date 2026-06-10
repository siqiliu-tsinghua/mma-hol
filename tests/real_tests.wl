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

(* ===== Field.wl Stage A: &ℝ embedding ===== *)

HOLTest`runTests["stdlib/Real: realOfRatDefThm — ⊢ &ℝ = (λq. ABS_real (λp. ratLt p q))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatDefThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`realOfRatDefThm][[1, 2]] === realOfRatConst[],
    "LHS is the &ℝ constant"]];

HOLTest`runTests["stdlib/Real: repRealOfRatThm — ⊢ REP_real (&ℝ q) = (λp. ratLt p q)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repRealOfRatThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repRealOfRatThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realOfRatMemThm — ⊢ ∀q p. REP_real (&ℝ q) p = ratLt p q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatMemThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatMemThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realOfRatInjThm — ⊢ ∀a b. &ℝ a = &ℝ b ⇒ a = b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatInjThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatInjThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realOfRatLeThm — ⊢ ∀a b. realLe (&ℝ a) (&ℝ b) = ratLe a b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatLeThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatLeThm], "is a theorem"]];

(* ===== Field.wl Stage B: realAdd (cut addition) ===== *)

HOLTest`runTests["stdlib/Real: memNotMemLtThm — ⊢ ∀x a b. REP_real x a ⇒ ¬(REP_real x b) ⇒ ratLt a b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`memNotMemLtThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`memNotMemLtThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: sumCutIsCutThm — ⊢ ∀x y. IS_CUT (λr. ∃s. REP x s ∧ REP y (r−s))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`sumCutIsCutThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`sumCutIsCutThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddDefThm — ⊢ realAdd = (λx y. ABS_real (…))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddDefThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`realAddDefThm][[1, 2]] === realAddConst[],
    "LHS is the realAdd constant"]];

HOLTest`runTests["stdlib/Real: repRealAddThm — ⊢ ∀x y. REP_real (realAdd x y) = (λr. …)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repRealAddThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repRealAddThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddMemThm — ⊢ ∀x y r. REP_real (realAdd x y) r = (∃s. …)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddMemThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddMemThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: sumMemSwapThm — sum-set symmetric in x,y",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`sumMemSwapThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`sumMemSwapThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddCommThm — ⊢ ∀x y. realAdd x y = realAdd y x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddCommThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddCommThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddZeroThm — ⊢ ∀x. realAdd x (&ℝ (&ℚ (&ℤ 0))) = x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratAddRightCancelThm — ⊢ ∀a b c. a+c = b+c ⇒ a = b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratAddRightCancelThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratAddRightCancelThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddAssocThm — ⊢ ∀x y z. realAdd (realAdd x y) z = realAdd x (realAdd y z)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddAssocThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddAssocThm], "is a theorem"]];

(* ===== Field.wl Stage C: ℚ negation algebra (foundation for realNeg) ===== *)

HOLTest`runTests["stdlib/Real: ratNegNegThm — ⊢ ∀q. ratNeg (ratNeg q) = q",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratNegNegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratNegNegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratAddLeftCancelThm — ⊢ ∀a x y. a+x = a+y ⇒ x = y",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratAddLeftCancelThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratAddLeftCancelThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratNegAddThm — ⊢ ∀a b. ratNeg (ratAdd a b) = ratAdd (ratNeg a) (ratNeg b)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratNegAddThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratNegAddThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratSubLtSelfThm — ⊢ ∀v r. 0<r ⇒ (v−r) < v",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratSubLtSelfThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratSubLtSelfThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratLtSubPosThm — ⊢ ∀a b. a<b ⇒ 0 < (b−a)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratLtSubPosThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratLtSubPosThm], "is a theorem"]];

(* ===== Field.wl Stage C: realNeg (Rudin cut negation) ===== *)

HOLTest`runTests["stdlib/Real: negCutIsCutThm — ⊢ ∀x. IS_CUT (negation set of REP x)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`negCutIsCutThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`negCutIsCutThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNegDefThm — ⊢ realNeg = (λx. ABS_real (…))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNegDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNegDefThm], "is a theorem"];
  HOLTest`assertTrue[
    concl[HOL`Stdlib`Real`realNegDefThm][[1, 2]] === realNegConst[],
    "LHS is the realNeg constant"]];

HOLTest`runTests["stdlib/Real: repRealNegThm — ⊢ ∀x. REP_real (realNeg x) = (λp. …)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repRealNegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repRealNegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNegMemThm — ⊢ ∀x p. REP_real (realNeg x) p = (∃r. …)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNegMemThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNegMemThm], "is a theorem"]];

(* ===== Field.wl Stage C: ℚ-Archimedean foundation (int side) ===== *)

HOLTest`runTests["stdlib/Real: intLtLeTransThm — ⊢ ∀a b c. intLt a b ⇒ intLe b c ⇒ intLt a c",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`intLtLeTransThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`intLtLeTransThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: intLeLtTransThm — ⊢ ∀a b c. intLe a b ⇒ intLt b c ⇒ intLt a c",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`intLeLtTransThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`intLeLtTransThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: intArchThm — ⊢ ∀z. ∃n. intLt z (&ℤ n)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`intArchThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`intArchThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratArchThm — ⊢ ∀q. ∃n. ratLt q (&ℚ (&ℤ n))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratArchThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratArchThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratMulRightCancelThm — ⊢ ∀w a b. w≠0 ⇒ a·w=b·w ⇒ a=b",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratMulRightCancelThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratMulRightCancelThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratLtMulPosThm — ⊢ ∀w a b. 0<w ⇒ a<b ⇒ a·w < b·w",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratLtMulPosThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratLtMulPosThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratNatMulGtThm — ⊢ ∀w r. 0<w ⇒ ∃n. r < (&ℚ(&ℤ n))·w",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratNatMulGtThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratNatMulGtThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: ratNatSucMulThm — ⊢ ∀w k. (&ℚ(&ℤ(SUC k)))·w = (&ℚ(&ℤ k))·w + w",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratNatSucMulThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratNatSucMulThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: cutStraddleThm — Rudin straddle (∃ boundary M)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`cutStraddleThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`cutStraddleThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddNegLeThm — ⊢ ∀x. realLe (realAdd x (realNeg x)) (&ℝ 0)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddNegLeThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddNegLeThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddNegGeThm — ⊢ ∀x. realLe (&ℝ 0) (realAdd x (realNeg x))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddNegGeThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddNegGeThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAddNegThm — ⊢ ∀x. realAdd x (realNeg x) = &ℝ (&ℚ (&ℤ 0))",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAddNegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAddNegThm], "is a theorem"]];

(* === Stage D Layer 1: non-negative multiplication core === *)

HOLTest`runTests["stdlib/Real: nnMulCutIsCutThm — ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ IS_CUT (nnMulBody x y)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`nnMulCutIsCutThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`nnMulCutIsCutThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: repRealNnMulThm — ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ REP_real (realNnMul x y) = nnMulBody x y",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repRealNnMulThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repRealNnMulThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNnMulMemThm — ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ ∀r. REP_real (realNnMul x y) r = …",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNnMulMemThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNnMulMemThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNnMulCommThm — ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ realNnMul x y = realNnMul y x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNnMulCommThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNnMulCommThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNnMulNonnegThm — ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ realLe (&ℝ 0) (realNnMul x y)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNnMulNonnegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNnMulNonnegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNnMulZeroThm — ⊢ ∀x. 0≤x ⇒ realNnMul x 0 = 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNnMulZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNnMulZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNnMulOneThm — ⊢ ∀x. 0≤x ⇒ realNnMul x 1 = x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNnMulOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNnMulOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNnMulAssocNonnegThm — ⊢ ∀x y z. 0≤x⇒0≤y⇒0≤z ⇒ (x·y)·z = x·(y·z)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNnMulAssocNonnegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNnMulAssocNonnegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNnMulDistribNonnegThm — ⊢ ∀x y z. 0≤x⇒0≤y⇒0≤z ⇒ x·(y+z) = x·y + x·z",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNnMulDistribNonnegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNnMulDistribNonnegThm], "is a theorem"]];

(* RatAux ℚ order/inverse extras (added for realNnMulOne) *)
HOLTest`runTests["stdlib/Real: RatAux extras — ratLeLtTrans / ratMulPos / ratInvPos / ratLtImpLe",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratLeLtTransThm], "ratLeLtTrans"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratMulPosThm], "ratMulPos"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratInvPosThm], "ratInvPos"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`ratLtImpLeThm], "ratLtImpLe"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`ratInvPosThm], {}, "ratInvPos no hyps"]];

(* === Stage D Layer 2: signed multiplication realMul === *)

HOLTest`runTests["stdlib/Real: realMul constant — realMul : real → real → real",
  With[{rTy = mkType["real", {}]},
    HOLTest`assertEq[HOL`Stdlib`Real`realMulConst[],
      mkConst["realMul", tyFun[rTy, tyFun[rTy, rTy]]], "realMul const type"]];
  HOLTest`assertEq[concl[HOL`Stdlib`Real`realMulDefThm][[1, 2]],
    HOL`Stdlib`Real`realMulConst[], "realMulDefThm LHS is realMul"]];

HOLTest`runTests["stdlib/Real: realMul case reductions (PP/PN/NP/NN)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulCasePPThm], {}, "PP no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulCasePPThm], "PP"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulCasePNThm], "PN"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulCaseNPThm], "NP"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulCaseNNThm], "NN"]];

HOLTest`runTests["stdlib/Real: realNeg sign algebra — realNegZero / realNegNeg / realLeNeg / realNegAdd",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNegNegThm], {}, "realNegNeg no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNegZeroThm], "realNegZero"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNegNegThm], "realNegNeg"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeNegThm], "realLeNeg"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNegAddThm], "realNegAdd"]];

HOLTest`runTests["stdlib/Real: realMulZeroThm — ⊢ ∀x. realMul x 0 = 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMulOneThm — ⊢ ∀x. realMul x 1 = x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulOneThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulOneThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMulCommThm — ⊢ ∀x y. realMul x y = realMul y x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulCommThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulCommThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMulNegRight/Left — sign homomorphism",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulNegRightThm], {}, "NegRight no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulNegRightThm], "NegRight"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulNegLeftThm], {}, "NegLeft no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulNegLeftThm], "NegLeft"]];

HOLTest`runTests["stdlib/Real: realMulNonneg / realLeMulNonneg — ⊢ ∀x y. 0≤x⇒0≤y⇒0≤(x·y)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulNonnegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulNonnegThm], "realMulNonneg"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeMulNonnegThm], "realLeMulNonneg"]];

HOLTest`runTests["stdlib/Real: realMulAssocThm — ⊢ ∀x y z. (x·y)·z = x·(y·z)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulAssocThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulAssocThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMulDistribThm — ⊢ ∀x y z. x·(y+z) = x·y + x·z (signed, Stage D capstone)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulDistribThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulDistribThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLtMulPosThm — ⊢ ∀x y. 0<x⇒0<y⇒0<(x·y)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtMulPosThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtMulPosThm], "is a theorem"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`notLeWitnessThm], "notLeWitness"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realPosHasPosMemThm], "realPosHasPosMem"]];

(* === Inv.wl: multiplicative inverse — increment 1 (positive-core foundation) === *)

HOLTest`runTests["stdlib/Real: invPos constant + def",
  With[{rTy = mkType["real", {}]},
    HOLTest`assertEq[HOL`Stdlib`Real`invPosConst[],
      mkConst["invPos", tyFun[rTy, rTy]], "invPos const type"];
    HOLTest`assertEq[HOL`Stdlib`Real`realInvConst[],
      mkConst["realInv", tyFun[rTy, rTy]], "realInv const type"]];
  HOLTest`assertEq[concl[HOL`Stdlib`Real`invPosDefThm][[1, 2]],
    HOL`Stdlib`Real`invPosConst[], "invPosDefThm LHS is invPos"];
  HOLTest`assertEq[concl[HOL`Stdlib`Real`realInvDefThm][[1, 2]],
    HOL`Stdlib`Real`realInvConst[], "realInvDefThm LHS is realInv"]];

HOLTest`runTests["stdlib/Real: invPosCutIsCutThm — ⊢ ∀x. 0<x ⇒ IS_CUT (reciprocal body)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`invPosCutIsCutThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`invPosCutIsCutThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: repInvPosThm / invPosMemThm — REP of invPos",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`repInvPosThm], {}, "repInvPos no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`repInvPosThm], "repInvPos"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`invPosMemThm], "invPosMem"]];

(* Inv.wl increment 2: the Rudin reciprocal law (positive core) *)
HOLTest`runTests["stdlib/Real: invPosNonnegThm — ⊢ ∀x. 0<x ⇒ 0≤invPos x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`invPosNonnegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`invPosNonnegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: invPosMulThm — ⊢ ∀x. 0<x ⇒ realNnMul x (invPos x) = 1",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`invPosMulThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`invPosMulThm], "is a theorem"]];

(* Inv.wl increment 3: signed wrapper + field law *)
HOLTest`runTests["stdlib/Real: realInvPos / realInvNeg / realNegPos case reductions",
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realInvPosThm], "realInvPos"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realInvNegThm], "realInvNeg"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNegPosThm], {}, "realNegPos no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNegPosThm], "realNegPos"]];

HOLTest`runTests["stdlib/Real: realMulInvThm — ⊢ ∀x. ¬(x=0) ⇒ realMul x (realInv x) = 1 (ℝ is a FIELD)",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMulInvThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMulInvThm], "is a theorem"]];

(* === ordered-field: additive-order compatibility === *)
HOLTest`runTests["stdlib/Real: realLe/LtAddMonoThm — additive monotonicity of ≤ / <",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeAddMonoThm], {}, "le no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeAddMonoThm], "realLeAddMono"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtAddMonoThm], {}, "lt no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtAddMonoThm], "realLtAddMono"]];

HOLTest`runTests["stdlib/Real: realLeSubNonneg / realLtSubPos — bridges a≤b⟺0≤b−a, a<b⟺0<b−a",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeSubNonnegThm], {}, "le bridge no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeSubNonnegThm], "realLeSubNonneg"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtSubPosThm], {}, "lt bridge no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtSubPosThm], "realLtSubPos"]];

(* === ordered-field: multiplicative-order compatibility === *)
HOLTest`runTests["stdlib/Real: realLeMulMono / realLtMulMono — multiply ≤/< by nonneg/pos",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeMulMonoThm], {}, "le-mul no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeMulMonoThm], "realLeMulMono"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLtMulMonoThm], {}, "lt-mul no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLtMulMonoThm], "realLtMulMono"]];

(* === Stage E: &ℝ ring/order homomorphism ℚ ↪ ℝ === *)
HOLTest`runTests["stdlib/Real: realOfRatAdd / realOfRatNeg — &ℝ additive homomorphism",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatAddThm], {}, "add no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatAddThm], "realOfRatAdd"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatNegThm], {}, "neg no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatNegThm], "realOfRatNeg"]];

HOLTest`runTests["stdlib/Real: realOfRatNnMul / realOfRatMul — &ℝ multiplicative homomorphism",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatNnMulThm], {}, "nnmul no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatNnMulThm], "realOfRatNnMul"];
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realOfRatMulThm], {}, "mul no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realOfRatMulThm], "realOfRatMul"]];
