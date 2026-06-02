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
gcdCommThm::usage = "gcdCommThm — ⊢ ∀a b. gcd a b = gcd b a. (proper home Num.wl)";

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
intNatAbsMulOfNumThm::usage = "intNatAbsMulOfNumThm — ⊢ ∀z n. intNatAbs (intMul z (&ℤ n)) = intNatAbs z * n. Multiplying a canonical rep by a nonneg integer keeps it canonical. (proper home Int.wl)";
ratNegConst::usage  = "ratNegConst[] — ratNeg : rat → rat, negation. ratNeg q = ABS_rat (intNeg (FST(REP q)), SND(REP q)) — negate the numerator; stays canonical (|−a|=|a|).";
ratNegDefThm::usage = "ratNegDefThm — ⊢ ratNeg = (λq. ABS_rat (intNeg (FST(REP q)), SND(REP q))).";
repRatNegThm::usage = "repRatNegThm — ⊢ ∀q. REP_rat (ratNeg q) = (intNeg (FST(REP q)), SND(REP q)). Negation lands in the carve with no reduction.";
ratEqCrossThm::usage = "ratEqCrossThm — ⊢ ∀q r. (q = r) = (intMul (FST(REP_rat q)) (&ℤ (SND(REP_rat r))) = intMul (FST(REP_rat r)) (&ℤ (SND(REP_rat q)))). Lowest-terms uniqueness via cross-multiplication.";
gcdZeroLeftThm::usage = "gcdZeroLeftThm — ⊢ ∀m. gcd 0 m = m. (proper home Num.wl)";
exDivSelfThm::usage = "exDivSelfThm — ⊢ ∀m. ¬ (m = 0) ⇒ exDiv m m = SUC 0. (proper home Num.wl)";
intDivNatZeroThm::usage = "intDivNatZeroThm — ⊢ ∀g. ¬ (g = 0) ⇒ intDivNat (&ℤ 0) g = &ℤ 0.";
ratCanonZeroNumThm::usage = "ratCanonZeroNumThm — ⊢ ∀m. ¬ (m = 0) ⇒ ratCanon (&ℤ 0, m) = (&ℤ 0, SUC 0). The rational 0/m reduces to 0/1.";
ratAddNegThm::usage = "ratAddNegThm — ⊢ ∀q. ratAdd q (ratNeg q) = &ℚ (&ℤ 0). Right additive inverse.";

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

intMulDivNatCancelThm::usage = "intMulDivNatCancelThm — ⊢ ∀z g. ¬ (g = 0) ⇒ divides g (intNatAbs z) ⇒ intMul (intDivNat z g) (&ℤ g) = z. Signed exact-division cancellation: multiplying the componentwise quotient back by the divisor recovers z. (proper home Int.wl)";
ratCanonEquivThm::usage = "ratCanonEquivThm — ⊢ ∀p. ¬ (SND p = 0) ⇒ intMul (FST (ratCanon p)) (&ℤ (SND p)) = intMul (FST p) (&ℤ (SND (ratCanon p))). ratCanon p is cross-multiplication-equivalent to p.";
ratCanonInjThm::usage = "ratCanonInjThm — ⊢ ∀p p'. RAT_REP p ⇒ RAT_REP p' ⇒ intMul (FST p) (&ℤ (SND p')) = intMul (FST p') (&ℤ (SND p)) ⇒ p = p'. Canonical reduced fractions with equal cross-products are equal (pair-level lowest-terms uniqueness; ratEqCross is this at the REP level).";
ratCrossTransThm::usage = "ratCrossTransThm — ⊢ ∀a b c d e f. ¬ (d = 0) ⇒ intMul a (&ℤ d) = intMul c (&ℤ b) ⇒ intMul c (&ℤ f) = intMul e (&ℤ d) ⇒ intMul a (&ℤ f) = intMul e (&ℤ b). Transitivity of cross-multiplication equivalence (cancels the shared middle denominator).";
ratCanonRespectsThm::usage = "ratCanonRespectsThm — ⊢ ∀p p'. ¬ (SND p = 0) ⇒ ¬ (SND p' = 0) ⇒ intMul (FST p) (&ℤ (SND p')) = intMul (FST p') (&ℤ (SND p)) ⇒ ratCanon p = ratCanon p'. ratCanon depends only on the cross-equivalence class.";
ratAddCongLeftThm::usage = "ratAddCongLeftThm — ⊢ ∀n1 m1 n1' m1' n2 m2. ¬(m1=0) ⇒ ¬(m1'=0) ⇒ ¬(m2=0) ⇒ intMul n1 (&ℤ m1') = intMul n1' (&ℤ m1) ⇒ ratCanon of the two sum-pairs (left operand replaced by a cross-equivalent one) are equal.";
ratAddCongRightThm::usage = "ratAddCongRightThm — ⊢ the analog of ratAddCongLeftThm with the right operand replaced by a cross-equivalent one.";
ratAddAssocThm::usage = "ratAddAssocThm — ⊢ ∀q r v. ratAdd (ratAdd q r) v = ratAdd q (ratAdd r v). Additive associativity (closes the additive abelian group).";

ratMulConst::usage  = "ratMulConst[] — ratMul : rat → rat → rat. (a,b)·(c,d) = ratCanon (a·c, b·d) over the int×num reps.";
ratMulDefThm::usage = "ratMulDefThm — ⊢ ratMul = (λq r. ABS_rat (ratCanon (intMul (FST(REP q)) (FST(REP r)), SND(REP q) * SND(REP r)))).";
repRatMulThm::usage = "repRatMulThm — ⊢ ∀q r. REP_rat (ratMul q r) = ratCanon (intMul (FST(REP q)) (FST(REP r)), SND(REP q) * SND(REP r)). REP of a product is the reduced product-pair.";
ratMulCommThm::usage = "ratMulCommThm — ⊢ ∀q r. ratMul q r = ratMul r q (multiplicative commutativity).";
ratMulOneThm::usage = "ratMulOneThm — ⊢ ∀q. ratMul q (&ℚ (&ℤ (SUC 0))) = q (right multiplicative identity, the rational 1 = 1/1).";
ratMulZeroThm::usage = "ratMulZeroThm — ⊢ ∀q. ratMul q (&ℚ (&ℤ 0)) = &ℚ (&ℤ 0) (right absorbing element).";
ratMulCongLeftThm::usage = "ratMulCongLeftThm — ⊢ ratCanon of the product-pair is invariant under swapping the left operand for a cross-equivalent one.";
ratMulCongRightThm::usage = "ratMulCongRightThm — the analog of ratMulCongLeftThm for the right operand.";
ratMulAssocThm::usage = "ratMulAssocThm — ⊢ ∀q r v. ratMul (ratMul q r) v = ratMul q (ratMul r v). Multiplicative associativity.";
ratMulDistribThm::usage = "ratMulDistribThm — ⊢ ∀z w v. ratMul z (ratAdd w v) = ratAdd (ratMul z w) (ratMul z v). Left distributivity of ratMul over ratAdd.";

intNatAbsOfNumThm::usage = "intNatAbsOfNumThm — ⊢ ∀n. intNatAbs (&ℤ n) = n. (proper home Int.wl)";
intSqNatAbsThm::usage = "intSqNatAbsThm — ⊢ ∀z. intMul z z = &ℤ (intNatAbs z * intNatAbs z). A square embeds as &ℤ of the square of its magnitude (sign drops). (proper home Int.wl)";
gcdSelfThm::usage = "gcdSelfThm — ⊢ ∀m. gcd m m = m. (proper home Num.wl)";
ratCanonSelfThm::usage = "ratCanonSelfThm — ⊢ ∀m. ¬ (m = 0) ⇒ ratCanon (&ℤ m, m) = (&ℤ (SUC 0), SUC 0). The rational m/m reduces to 1/1.";
intNatAbsNonzeroThm::usage = "intNatAbsNonzeroThm — ⊢ ∀z. ¬ (z = &ℤ 0) ⇒ ¬ (intNatAbs z = 0). (proper home Int.wl)";
ratNumNonzeroThm::usage = "ratNumNonzeroThm — ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ ¬ (FST (REP_rat q) = &ℤ 0). A nonzero rational has nonzero numerator.";
ratInvConst::usage  = "ratInvConst[] — ratInv : rat → rat, multiplicative inverse. ratInv q = ABS_rat (ratCanon (intMul a (&ℤ b), intNatAbs a * intNatAbs a)), (a,b) = REP q; sign carried by a. ratInv (&ℚ&ℤ0) is junk.";
ratInvDefThm::usage = "ratInvDefThm — ⊢ ratInv = (λq. ABS_rat (ratCanon (intMul (FST(REP q)) (&ℤ (SND(REP q))), intNatAbs (FST(REP q)) * intNatAbs (FST(REP q))))).";
repRatInvThm::usage = "repRatInvThm — ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ REP_rat (ratInv q) = ratCanon (intMul (FST(REP q)) (&ℤ (SND(REP q))), intNatAbs (FST(REP q)) * intNatAbs (FST(REP q))).";
ratMulInvThm::usage = "ratMulInvThm — ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ ratMul q (ratInv q) = &ℚ (&ℤ (SUC 0)). Right multiplicative inverse — ℚ is a FIELD.";

intLeMulNonnegCancelThm::usage = "intLeMulNonnegCancelThm — ⊢ ∀u x y. intLe (&ℤ 0) u ⇒ ¬ (u = &ℤ 0) ⇒ intLe (intMul u x) (intMul u y) ⇒ intLe x y. Cancellation of a positive (nonneg + nonzero) left factor in an int inequality. (proper home Int.wl)";

ratLeConst::usage  = "ratLeConst[] — ratLe : rat → rat → bool, order. ratLe q r ⟺ intLe (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q)))) — cross-multiplication with positive denominators.";
ratLeDefThm::usage = "ratLeDefThm — ⊢ ratLe = (λq r. intLe (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q))))).";
ratLeReflThm::usage = "ratLeReflThm — ⊢ ∀q. ratLe q q.";
ratLeAntisymThm::usage = "ratLeAntisymThm — ⊢ ∀q r. ratLe q r ⇒ ratLe r q ⇒ q = r.";
ratLeTransThm::usage = "ratLeTransThm — ⊢ ∀q r v. ratLe q r ⇒ ratLe r v ⇒ ratLe q v.";
ratLeTotalThm::usage = "ratLeTotalThm — ⊢ ∀q r. ratLe q r ∨ ratLe r q.";
ratLtConst::usage  = "ratLtConst[] — ratLt : rat → rat → bool, strict order. ratLt q r ⟺ intLt (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q)))).";
ratLtDefThm::usage = "ratLtDefThm — ⊢ ratLt = (λq r. intLt (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q))))).";
ratLtNotLeThm::usage = "ratLtNotLeThm — ⊢ ∀q r. ratLt q r = ¬ (ratLe r q).";

pairLeCongLeftThm::usage = "pairLeCongLeftThm — ⊢ ∀n1 m1 e f n2 m2. ¬(m1=0) ⇒ ¬(f=0) ⇒ intMul n1 (&ℤ f) = intMul e (&ℤ m1) ⇒ intLe (intMul n1 (&ℤ m2)) (intMul n2 (&ℤ m1)) ⇒ intLe (intMul e (&ℤ m2)) (intMul n2 (&ℤ f)). Cross-product order respects swapping the left operand for a cross-equivalent one. (proper home Int.wl)";
pairLeCongRightThm::usage = "pairLeCongRightThm — ⊢ ∀n1 m1 n2 m2 e f. ¬(m2=0) ⇒ ¬(f=0) ⇒ intMul n2 (&ℤ f) = intMul e (&ℤ m2) ⇒ intLe (intMul n1 (&ℤ m2)) (intMul n2 (&ℤ m1)) ⇒ intLe (intMul n1 (&ℤ f)) (intMul e (&ℤ m1)). Right-operand analog of pairLeCongLeftThm. (proper home Int.wl)";
ratLeAddMonoThm::usage = "ratLeAddMonoThm — ⊢ ∀q r u. ratLe q r ⇒ ratLe (ratAdd q u) (ratAdd r u). Additive monotonicity of the rational order.";
ratLeMulNonnegThm::usage = "ratLeMulNonnegThm — ⊢ ∀u q r. ratLe (&ℚ (&ℤ 0)) u ⇒ ratLe q r ⇒ ratLe (ratMul u q) (ratMul u r). Monotonicity of ratMul by a nonnegative factor.";

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
plusC[]        := HOL`Stdlib`Num`plusConst[];
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

(* ⊢ ∀a b. ¬ (b = 0) ⇒ gcd a b = gcd b (a MOD b) *)
(* g1 = gcd a b, g2 = gcd b r (r = a MOD b). Mutual divisibility:    *)
(*   g1 | a, g1 | b ⇒ g1 | (b*q+r)=a, so g1 | r (dividesAddRight),    *)
(*     hence g1 | gcd b r (gcdUniversal).                            *)
(*   g2 | b, g2 | r ⇒ g2 | b*q+r = a (dividesAdd), so g2 | gcd a b.   *)
(*   dividesAntisym closes g1 = g2. (a = b*q+r kept additive — no     *)
(*   monus.) The a→(b*q+r) rewrites use APTERM/EQMP, NOT SUBS, since  *)
(*   `a` also occurs inside gcd a b.                                  *)
gcdRecThm =
  Module[{aV, bV, notB0, qTm, rTm, bqTm, divPair, aEq, g1, g2,
          g1DivA, g1DivB, g1DivBq, g1DivBqR, g1DivR, g1Divg2,
          g2DivB, g2DivR, g2DivBq, g2DivBqR, g2DivA, g2Divg1, eq},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    notB0 = ASSUME[notTm[mkEq[bV, zeroN[]]]];
    qTm = divTmR[aV, bV]; rTm = modTmR[aV, bV]; bqTm = timesTm[bV, qTm];
    divPair = HOL`Bool`MP[
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`divisionPairThm]], notB0];
    aEq = HOL`Bool`CONJUNCT1[divPair];                    (* a = b*q + r *)
    g1 = gcdTm[aV, bV]; g2 = gcdTm[bV, rTm];
    g1DivA = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesLeftThm]];   (* g1 | a *)
    g1DivB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesRightThm]];  (* g1 | b *)
    g1DivBq = HOL`Bool`MP[HOL`Bool`SPEC[qTm, HOL`Bool`SPEC[bV,
      HOL`Bool`SPEC[g1, HOL`Stdlib`Num`dividesMultRightThm]]], g1DivB];  (* g1 | (b*q) *)
    g1DivBqR = EQMP[HOL`Equal`APTERM[dividesHead[g1], aEq], g1DivA];     (* g1 | (b*q + r) *)
    g1DivR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bqTm,
      HOL`Bool`SPEC[g1, HOL`Stdlib`Num`dividesAddRightThm]]], g1DivBq], g1DivBqR];  (* g1 | r *)
    g1Divg2 = HOL`Bool`MP[HOL`Bool`SPEC[g1, HOL`Bool`SPEC[rTm,
      HOL`Bool`SPEC[bV, HOL`Stdlib`Num`gcdUniversalThm]]],
      HOL`Bool`CONJ[g1DivB, g1DivR]];                     (* g1 | gcd b r *)
    g2DivB = HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`gcdDividesLeftThm]];   (* g2 | b *)
    g2DivR = HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`gcdDividesRightThm]];  (* g2 | r *)
    g2DivBq = HOL`Bool`MP[HOL`Bool`SPEC[qTm, HOL`Bool`SPEC[bV,
      HOL`Bool`SPEC[g2, HOL`Stdlib`Num`dividesMultRightThm]]], g2DivB];  (* g2 | (b*q) *)
    g2DivBqR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bqTm,
      HOL`Bool`SPEC[g2, HOL`Stdlib`Num`dividesAddThm]]], g2DivBq], g2DivR];  (* g2 | (b*q + r) *)
    g2DivA = EQMP[HOL`Equal`APTERM[dividesHead[g2], HOL`Equal`SYM[aEq]], g2DivBqR]; (* g2 | a *)
    g2Divg1 = HOL`Bool`MP[HOL`Bool`SPEC[g2, HOL`Bool`SPEC[bV,
      HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdUniversalThm]]],
      HOL`Bool`CONJ[g2DivA, g2DivB]];                     (* g2 | gcd a b *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[g2, HOL`Bool`SPEC[g1, dividesAntisymThm]], g1Divg2], g2Divg1];  (* g1 = g2 *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[notTm[mkEq[bV, zeroN[]]], eq]]]
  ];

(* ⊢ ∀a b. ∃x y. a*x = b*y + gcd a b ∨ b*y = a*x + gcd a b *)
(* Subtraction-free ℕ Bezout. Strong induction on b (the modulus).      *)
(*   b = 0: gcd a 0 = a, witness x = SUC 0, y = 0 (first disjunct).      *)
(*   b ≠ 0: r = a MOD b < b; gcd a b = gcd b r (gcdRec). IH at (b on r)  *)
(*     gives ∃x0 y0. b*x0 = r*y0 + g ∨ r*y0 = b*x0 + g, g = gcd b r.     *)
(*     With a = b*q + r (additive, q = a DIV b): multiply by y0 →        *)
(*       a*y0 = b*(q*y0) + r*y0.  Both cases share witnesses             *)
(*       X = y0, Y = q*y0 + x0; only the disjunct side differs:          *)
(*       case A (b*x0=r*y0+g):  a*y0 + g = b*Y  (second disjunct)         *)
(*       case B (r*y0=b*x0+g):  a*y0 = b*Y + g  (first disjunct)          *)
(*     g rewritten to gcd a b via gcdRec. No monus anywhere.             *)
bezoutNatThm =
  Module[{aV, bV, kV, xV, yV, aInner, disjAt, bezBody, pLam, specInd,
          specBeta, stepAnte, mainConcl},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; kV = mkVar["k", numTy];
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy]; aInner = mkVar["a", numTy];

    disjAt[aT_, nT_, xT_, yT_] := orTmR[
      mkEq[timesTm[aT, xT], plusTm[timesTm[nT, yT], gcdTm[aT, nT]]],
      mkEq[timesTm[nT, yT], plusTm[timesTm[aT, xT], gcdTm[aT, nT]]]];
    bezBody[aT_, nT_] := existsTmR[xV, existsTmR[yV, disjAt[aT, nT, xV, yV]]];

    pLam = mkAbs[bV, forallTm[aInner, bezBody[aInner, bV]]];
    specInd = HOL`Bool`ISPEC[pLam, HOL`Stdlib`Num`strongInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];

    stepAnte = Module[{nLoc, gN, exInnerTm, goalTm, ihHypTm, ihHyp,
                       em, case0, caseNZ, pnAtA, pnBody},
      nLoc = mkVar["b", numTy];
      gN = gcdTm[aInner, nLoc];
      exInnerTm[xT_] := existsTmR[yV, disjAt[aInner, nLoc, xT, yV]];
      goalTm = bezBody[aInner, nLoc];
      ihHypTm = forallTm[kV, implTm[ltTmR[kV, nLoc],
        forallTm[aInner, bezBody[aInner, kV]]]];
      ihHyp = ASSUME[ihHypTm];

      case0 = Module[{hN0, lhsStep1, a0eq, lhsStep2, addLeftZeroEq, lhsEq,
                      n0Eq, gcdAnEq, rhsStep1, rhsChain, firstDisjEq, disj, exY},
        hN0 = ASSUME[mkEq[nLoc, zeroN[]]];                      (* b = 0 *)
        lhsStep1 = HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`timesSucEqThm]];
        a0eq = HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`timesZeroEqThm];
        lhsStep2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], a0eq], REFL[aInner]];
        addLeftZeroEq = HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`addLeftZeroThm];
        lhsEq = TRANS[lhsStep1, TRANS[lhsStep2, addLeftZeroEq]];  (* a*(SUC 0) = a *)
        n0Eq = HOL`Bool`SPEC[nLoc, HOL`Stdlib`Num`timesZeroEqThm];  (* b*0 = 0 *)
        gcdAnEq = TRANS[
          HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`gcdConst[], aInner], hN0],
          HOL`Bool`SPEC[aInner, gcdZeroRightThm]];             (* gcd a b = a *)
        rhsStep1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], n0Eq], gcdAnEq];
        rhsChain = TRANS[rhsStep1, addLeftZeroEq];             (* b*0 + gcd a b = a *)
        firstDisjEq = TRANS[lhsEq, HOL`Equal`SYM[rhsChain]];   (* a*(SUC 0) = b*0 + gcd a b *)
        disj = HOL`Bool`DISJ1[firstDisjEq,
          mkEq[timesTm[nLoc, zeroN[]], plusTm[timesTm[aInner, oneN[]], gN]]];
        exY = HOL`Bool`EXISTS[exInnerTm[oneN[]], zeroN[], disj];
        HOL`Bool`EXISTS[goalTm, oneN[], exY]];

      caseNZ = Module[{hNnz, divPair, aEqDiv, rLtN, gRec, ihAtR, ihInst,
                       qN, rN, gR, bqTmN, x0V, y0V, bTimesQy0, rTimesY0,
                       bTimesX0, aTimesY0, ywit, bTimesYwit, step1, step2,
                       step2b, ay0Eq, distribLeftInst, distribN, caseA, caseB,
                       ihInnerYtm, gFromBody, chooseY, firstDisjTermA,
                       secondDisjTermA},
        hNnz = ASSUME[notTm[mkEq[nLoc, zeroN[]]]];
        divPair = HOL`Bool`MP[
          HOL`Bool`SPEC[nLoc, HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`divisionPairThm]], hNnz];
        aEqDiv = HOL`Bool`CONJUNCT1[divPair];                  (* a = b*q + r *)
        rLtN = HOL`Bool`CONJUNCT2[divPair];                    (* (a MOD b) < b *)
        qN = divTmR[aInner, nLoc]; rN = modTmR[aInner, nLoc];
        gR = gcdTm[nLoc, rN]; bqTmN = timesTm[nLoc, qN];
        gRec = HOL`Bool`MP[
          HOL`Bool`SPEC[nLoc, HOL`Bool`SPEC[aInner, gcdRecThm]], hNnz];  (* gcd a b = gcd b r *)
        ihAtR = HOL`Bool`MP[HOL`Bool`SPEC[rN, ihHyp], rLtN];   (* ∀a. bezBody[a, r] *)
        ihInst = HOL`Bool`SPEC[nLoc, ihAtR];                   (* bezBody[b, r] *)
        x0V = mkVar["x0", numTy]; y0V = mkVar["y0", numTy];
        bTimesQy0 = timesTm[nLoc, timesTm[qN, y0V]];           (* b*(q*y0) *)
        rTimesY0  = timesTm[rN, y0V];                          (* r*y0 *)
        bTimesX0  = timesTm[nLoc, x0V];                        (* b*x0 *)
        aTimesY0  = timesTm[aInner, y0V];                      (* a*y0 *)
        ywit      = plusTm[timesTm[qN, y0V], x0V];             (* q*y0 + x0 *)
        bTimesYwit = timesTm[nLoc, ywit];                      (* b*(q*y0 + x0) *)
        firstDisjTermA  = mkEq[aTimesY0, plusTm[bTimesYwit, gN]];  (* a*y0 = b*Y + gcd a b *)
        secondDisjTermA = mkEq[bTimesYwit, plusTm[aTimesY0, gN]];  (* b*Y = a*y0 + gcd a b *)
        step1 = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], aEqDiv], y0V];
                                                               (* a*y0 = (b*q + r)*y0 *)
        step2 = HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[rN,
          HOL`Bool`SPEC[bqTmN, HOL`Stdlib`Num`timesDistribRightThm]]];
                                                               (* (b*q + r)*y0 = (b*q)*y0 + r*y0 *)
        step2b = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[],
            HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[qN, HOL`Bool`SPEC[nLoc, HOL`Stdlib`Num`timesAssocThm]]]],
          REFL[rTimesY0]];                                     (* (b*q)*y0 + r*y0 = b*(q*y0) + r*y0 *)
        ay0Eq = TRANS[step1, TRANS[step2, step2b]];            (* a*y0 = b*(q*y0) + r*y0 *)
        distribLeftInst = HOL`Bool`SPEC[x0V, HOL`Bool`SPEC[timesTm[qN, y0V],
          HOL`Bool`SPEC[nLoc, HOL`Stdlib`Num`timesDistribLeftThm]]];
        distribN = HOL`Equal`SYM[distribLeftInst];             (* b*(q*y0) + b*x0 = b*(q*y0+x0) *)

        caseA = Module[{hyp, e1, e2, e3, caseAeq, secondDisjProof, cdisj, exY},
          hyp = ASSUME[mkEq[bTimesX0, plusTm[rTimesY0, gR]]];  (* b*x0 = r*y0 + g *)
          e1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], ay0Eq], REFL[gR]];
          e2 = HOL`Bool`SPEC[gR, HOL`Bool`SPEC[rTimesY0,
            HOL`Bool`SPEC[bTimesQy0, HOL`Stdlib`Num`addAssocThm]]];
          e3 = HOL`Kernel`MKCOMB[
            HOL`Equal`APTERM[plusC[], REFL[bTimesQy0]], HOL`Equal`SYM[hyp]];
          caseAeq = TRANS[e1, TRANS[e2, TRANS[e3, distribN]]];  (* (a*y0)+g = b*(q*y0+x0) *)
          secondDisjProof = TRANS[HOL`Equal`SYM[caseAeq],
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[aTimesY0]], HOL`Equal`SYM[gRec]]];
          cdisj = HOL`Bool`DISJ2[secondDisjProof, firstDisjTermA];
          exY = HOL`Bool`EXISTS[exInnerTm[y0V], ywit, cdisj];
          HOL`Bool`EXISTS[goalTm, y0V, exY]];

        caseB = Module[{hyp, f2, f3, caseBeqG, firstDisjProof, cdisj, exY},
          hyp = ASSUME[mkEq[rTimesY0, plusTm[bTimesX0, gR]]];  (* r*y0 = b*x0 + g *)
          f2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[bTimesQy0]], hyp];
          f3 = HOL`Equal`SYM[HOL`Bool`SPEC[gR, HOL`Bool`SPEC[bTimesX0,
            HOL`Bool`SPEC[bTimesQy0, HOL`Stdlib`Num`addAssocThm]]]];
          caseBeqG = TRANS[ay0Eq, TRANS[f2, TRANS[f3,
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], distribN], REFL[gR]]]]];
                                                               (* a*y0 = b*(q*y0+x0) + g *)
          firstDisjProof = TRANS[caseBeqG,
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[bTimesYwit]], HOL`Equal`SYM[gRec]]];
          cdisj = HOL`Bool`DISJ1[firstDisjProof, secondDisjTermA];
          exY = HOL`Bool`EXISTS[exInnerTm[y0V], ywit, cdisj];
          HOL`Bool`EXISTS[goalTm, y0V, exY]];

        ihInnerYtm = existsTmR[yV, disjAt[nLoc, rN, x0V, yV]];
        gFromBody = HOL`Bool`DISJCASES[
          ASSUME[disjAt[nLoc, rN, x0V, y0V]], caseA, caseB];
        chooseY = HOL`Bool`CHOOSE[y0V, ASSUME[ihInnerYtm], gFromBody];
        HOL`Bool`CHOOSE[x0V, ihInst, chooseY]];

      em = HOL`Bool`EXCLUDEDMIDDLE[mkEq[nLoc, zeroN[]]];
      pnAtA = HOL`Bool`DISJCASES[em, case0, caseNZ];           (* bezBody[a,b], hyp {ihHypTm} *)
      pnBody = HOL`Bool`GEN[aInner, pnAtA];                    (* ∀a. bezBody[a,b] *)
      HOL`Bool`GEN[nLoc, HOL`Bool`DISCH[ihHypTm, pnBody]]
    ];

    mainConcl = HOL`Bool`MP[specBeta, stepAnte];               (* ∀b. ∀a. bezBody[a,b] *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, mainConcl]]]]
  ];

(* ⊢ ∀a b c. gcd a b = SUC 0 ⇒ divides a (b*c) ⇒ divides a c   (ℕ Gauss) *)
(* From Bezout at (a,b): ∃x0 y0. a*x0 = b*y0 + 1 ∨ b*y0 = a*x0 + 1 (g=1). *)
(* Multiply the chosen identity by c and use a | a*(x0*c) and a | (b*c)*y0 *)
(* (= a | (b*y0)*c) to peel c off with dividesAddRight.                    *)
coprimeDividesProductThm =
  Module[{aV, bV, cV, xV, yV, x0V, y0V, oneN1, gab, bc, ax0, by0, x0c, axc,
          by0c, disjAtXY, gcdEq1, aDivBc, bez, aDivA, aDivAxc, aDivBcy0,
          bycEq1, bycEq2, bycEq3, bycEq, aDivBy0c, disj1Tm, disj2Tm,
          disjBodyTm, case1, case2, innerProof, exYtm, chooseY, chooseX},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    x0V = mkVar["x0", numTy]; y0V = mkVar["y0", numTy];
    oneN1 = oneN[]; gab = gcdTm[aV, bV]; bc = timesTm[bV, cV];
    ax0 = timesTm[aV, x0V]; by0 = timesTm[bV, y0V];
    x0c = timesTm[x0V, cV]; axc = timesTm[aV, x0c]; by0c = timesTm[by0, cV];
    disjAtXY[xT_, yT_] := orTmR[
      mkEq[timesTm[aV, xT], plusTm[timesTm[bV, yT], gab]],
      mkEq[timesTm[bV, yT], plusTm[timesTm[aV, xT], gab]]];
    gcdEq1 = ASSUME[mkEq[gab, oneN1]];                  (* gcd a b = SUC 0 *)
    aDivBc = ASSUME[dividesTm[aV, bc]];                 (* divides a (b*c) *)
    bez = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, bezoutNatThm]];

    aDivA = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesReflThm];        (* divides a a *)
    aDivAxc = HOL`Bool`MP[HOL`Bool`SPEC[x0c, HOL`Bool`SPEC[aV,
      HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesMultRightThm]]], aDivA];  (* a | a*(x0*c) *)
    aDivBcy0 = HOL`Bool`MP[HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[bc,
      HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesMultRightThm]]], aDivBc]; (* a | (b*c)*y0 *)
    bycEq1 = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`timesAssocThm]]];
                                                        (* (b*y0)*c = b*(y0*c) *)
    bycEq2 = HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], bV],
      HOL`Bool`SPEC[cV, HOL`Bool`SPEC[y0V, HOL`Stdlib`Num`timesCommThm]]];  (* b*(y0*c) = b*(c*y0) *)
    bycEq3 = HOL`Equal`SYM[HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[cV, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`timesAssocThm]]]];
                                                        (* b*(c*y0) = (b*c)*y0 *)
    bycEq = TRANS[bycEq1, TRANS[bycEq2, bycEq3]];       (* (b*y0)*c = (b*c)*y0 *)
    aDivBy0c = EQMP[HOL`Equal`APTERM[dividesHead[aV], HOL`Equal`SYM[bycEq]], aDivBcy0]; (* a | (b*y0)*c *)

    disj1Tm = mkEq[ax0, plusTm[by0, gab]];
    disj2Tm = mkEq[by0, plusTm[ax0, gab]];
    disjBodyTm = orTmR[disj1Tm, disj2Tm];

    case1 = Module[{d1, caseEq1, l1, l2, l3, l4, axcEq, aDivBycC},
      d1 = ASSUME[disj1Tm];                             (* a*x0 = b*y0 + gab *)
      caseEq1 = TRANS[d1,
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[by0]], gcdEq1]];  (* a*x0 = b*y0 + SUC 0 *)
      l1 = HOL`Equal`SYM[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[x0V, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`timesAssocThm]]]];
                                                        (* a*(x0*c) = (a*x0)*c *)
      l2 = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], caseEq1], cV];
                                                        (* (a*x0)*c = (b*y0+SUC0)*c *)
      l3 = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[oneN1, HOL`Bool`SPEC[by0, HOL`Stdlib`Num`timesDistribRightThm]]];
                                                        (* (b*y0+SUC0)*c = (b*y0)*c + (SUC0)*c *)
      l4 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[by0c]],
        HOL`Bool`SPEC[cV, HOL`Stdlib`Num`oneTimesEqThm]];  (* (b*y0)*c + (SUC0)*c = (b*y0)*c + c *)
      axcEq = TRANS[l1, TRANS[l2, TRANS[l3, l4]]];      (* a*(x0*c) = (b*y0)*c + c *)
      aDivBycC = EQMP[HOL`Equal`APTERM[dividesHead[aV], axcEq], aDivAxc];  (* a | ((b*y0)*c + c) *)
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[by0c,
        HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesAddRightThm]]], aDivBy0c], aDivBycC]];  (* a | c *)

    case2 = Module[{d2, caseEq2, m1, m2, m3, byccEq, aDivAxcC},
      d2 = ASSUME[disj2Tm];                             (* b*y0 = a*x0 + gab *)
      caseEq2 = TRANS[d2,
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[ax0]], gcdEq1]];  (* b*y0 = a*x0 + SUC 0 *)
      m1 = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], caseEq2], cV];
                                                        (* (b*y0)*c = (a*x0+SUC0)*c *)
      m2 = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[oneN1, HOL`Bool`SPEC[ax0, HOL`Stdlib`Num`timesDistribRightThm]]];
                                                        (* (a*x0+SUC0)*c = (a*x0)*c + (SUC0)*c *)
      m3 = HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[plusC[],
          HOL`Bool`SPEC[cV, HOL`Bool`SPEC[x0V, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`timesAssocThm]]]],
        HOL`Bool`SPEC[cV, HOL`Stdlib`Num`oneTimesEqThm]];  (* (a*x0)*c + (SUC0)*c = a*(x0*c) + c *)
      byccEq = TRANS[m1, TRANS[m2, m3]];                (* (b*y0)*c = a*(x0*c) + c *)
      aDivAxcC = EQMP[HOL`Equal`APTERM[dividesHead[aV], byccEq], aDivBy0c];  (* a | (a*(x0*c) + c) *)
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[axc,
        HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesAddRightThm]]], aDivAxc], aDivAxcC]];  (* a | c *)

    innerProof = HOL`Bool`DISJCASES[ASSUME[disjBodyTm], case1, case2];  (* a | c *)
    exYtm = existsTmR[yV, disjAtXY[x0V, yV]];
    chooseY = HOL`Bool`CHOOSE[y0V, ASSUME[exYtm], innerProof];
    chooseX = HOL`Bool`CHOOSE[x0V, bez, chooseY];      (* a | c, hyps {gcd a b=1, a|(b*c)} *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[mkEq[gab, oneN1],
        HOL`Bool`DISCH[dividesTm[aV, bc], chooseX]]]]]
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

absIntC[] := HOL`Stdlib`Int`absIntConst[];  (* plusC[] now defined in the Bezout-helper block above *)
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

(* ============================================================ *)
(* gcdCommThm — gcd commutativity (proper home Num.wl).         *)
(* mutual divisibility via gcdUniversal + dividesAntisym.        *)
(* ============================================================ *)

(* ⊢ ∀a b. gcd a b = gcd b a *)
gcdCommThm =
  Module[{aV, bV, gAB, gBA, abDivA, abDivB, abDivBA, baDivA, baDivB, baDivAB, eq},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    gAB = gcdTm[aV, bV]; gBA = gcdTm[bV, aV];
    abDivA = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesLeftThm]];   (* gcd a b | a *)
    abDivB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdDividesRightThm]];  (* gcd a b | b *)
    abDivBA = HOL`Bool`MP[
      HOL`Bool`SPEC[gAB, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`gcdUniversalThm]]],
      HOL`Bool`CONJ[abDivB, abDivA]];                  (* gcd a b | gcd b a *)
    baDivB = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`gcdDividesLeftThm]];   (* gcd b a | b *)
    baDivA = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`gcdDividesRightThm]];  (* gcd b a | a *)
    baDivAB = HOL`Bool`MP[
      HOL`Bool`SPEC[gBA, HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`gcdUniversalThm]]],
      HOL`Bool`CONJ[baDivA, baDivB]];                  (* gcd b a | gcd a b *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[gBA, HOL`Bool`SPEC[gAB, dividesAntisymThm]], abDivBA], baDivAB];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, eq]]
  ];

(* ============================================================ *)
(* intNatAbsMulOfNumThm — |z · &ℤ n| = |z| · n (proper home      *)
(* Int.wl). REP(z·&ℤn) = intCanon(z1·n, z2·n); since REP z is     *)
(* canonical (z1=0 ∨ z2=0), one of z1·n, z2·n is 0, so the pair   *)
(* is already canonical and intCanon is the identity — no monus.  *)
(* ============================================================ *)

(* ⊢ ∀z n. intNatAbs (intMul z (&ℤ n)) = intNatAbs z * n *)
intNatAbsMulOfNumThm =
  Module[{zV, nV, repZ, z1, z2, repW, w1, w2, w1eq, w2eq,
          z1w1eq, z2w2eq, z1w2eq, z2w1eq, firstCompEq, secondCompEq,
          pairTm, pairEq, repMul, fstPairEq, sndPairEq, intRepDisjZ,
          caseFst, caseSnd, repPairDisj, intRepProd, canonId,
          canonOfPairEq, repMulPair, fstRepMul, sndRepMul, sumEq,
          lhsEq, unfNAz, rhsStep1, distrib, rhsEq, timesC},
    zV = mkVar["z", intTy]; nV = mkVar["n", numTy];
    timesC = HOL`Stdlib`Num`timesConst[];
    repZ = repInt[zV];
    z1 = mkComb[fstNN[], repZ]; z2 = mkComb[sndNN[], repZ];
    repW = HOL`Kernel`INST[{mkVar["n", numTy] -> nV}, HOL`Stdlib`Int`repIntOfNumThm];
                                                       (* REP(&ℤ n) = (n, 0) *)
    w1 = mkComb[fstNN[], repInt[intOfNum[nV]]];
    w2 = mkComb[sndNN[], repInt[intOfNum[nV]]];
    w1eq = TRANS[HOL`Equal`APTERM[fstNN[], repW], fstNumAt[nV, zeroN[]]];  (* FST(REP(&ℤn)) = n *)
    w2eq = TRANS[HOL`Equal`APTERM[sndNN[], repW], sndNumAt[nV, zeroN[]]];  (* SND(REP(&ℤn)) = 0 *)
    (* first component z1*w1 + z2*w2 = z1*n *)
    z1w1eq = HOL`Equal`APTERM[mkComb[timesC, z1], w1eq];                   (* z1*w1 = z1*n *)
    z2w2eq = TRANS[HOL`Equal`APTERM[mkComb[timesC, z2], w2eq],
      HOL`Bool`SPEC[z2, HOL`Stdlib`Num`timesZeroEqThm]];                   (* z2*w2 = z2*0 = 0 *)
    firstCompEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], z1w1eq], z2w2eq],
      addZeroRightAt[timesTm[z1, nV]]];                                    (* z1*w1+z2*w2 = z1*n *)
    (* second component z1*w2 + z2*w1 = z2*n *)
    z1w2eq = TRANS[HOL`Equal`APTERM[mkComb[timesC, z1], w2eq],
      HOL`Bool`SPEC[z1, HOL`Stdlib`Num`timesZeroEqThm]];                   (* z1*w2 = z1*0 = 0 *)
    z2w1eq = HOL`Equal`APTERM[mkComb[timesC, z2], w1eq];                   (* z2*w1 = z2*n *)
    secondCompEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], z1w2eq], z2w1eq],
      HOL`Bool`SPEC[timesTm[z2, nV], HOL`Stdlib`Num`addLeftZeroThm]];      (* z1*w2+z2*w1 = z2*n *)
    pairTm = numPairCons[timesTm[z1, nV], timesTm[z2, nV]];
    pairEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[numPairConsC[], firstCompEq], secondCompEq];        (* intMulPair = (z1*n, z2*n) *)
    (* intCanon (z1*n, z2*n) = (z1*n, z2*n): one component is 0 *)
    fstPairEq = fstNumAt[timesTm[z1, nV], timesTm[z2, nV]];                (* FST pairTm = z1*n *)
    sndPairEq = sndNumAt[timesTm[z1, nV], timesTm[z2, nV]];                (* SND pairTm = z2*n *)
    intRepDisjZ = EQMP[unfoldIntRep[repZ], HOL`Stdlib`Int`intRepRepThm];   (* z1=0 ∨ z2=0 *)
    caseFst = Module[{h, z1n0, fstP0},
      h = ASSUME[mkEq[z1, zeroN[]]];
      z1n0 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[timesC, h], nV],
        HOL`Bool`SPEC[nV, HOL`Stdlib`Num`timesLeftZeroThm]];               (* z1*n = 0*n = 0 *)
      fstP0 = TRANS[fstPairEq, z1n0];                                      (* FST pairTm = 0 *)
      HOL`Bool`DISJ1[fstP0, mkEq[mkComb[sndNN[], pairTm], zeroN[]]]];
    caseSnd = Module[{h, z2n0, sndP0},
      h = ASSUME[mkEq[z2, zeroN[]]];
      z2n0 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[timesC, h], nV],
        HOL`Bool`SPEC[nV, HOL`Stdlib`Num`timesLeftZeroThm]];               (* z2*n = 0*n = 0 *)
      sndP0 = TRANS[sndPairEq, z2n0];                                      (* SND pairTm = 0 *)
      HOL`Bool`DISJ2[sndP0, mkEq[mkComb[fstNN[], pairTm], zeroN[]]]];
    repPairDisj = HOL`Bool`DISJCASES[intRepDisjZ, caseFst, caseSnd];       (* FST pairTm=0 ∨ SND pairTm=0 *)
    intRepProd = EQMP[HOL`Equal`SYM[unfoldIntRep[pairTm]], repPairDisj];   (* INT_REP pairTm *)
    canonId = HOL`Bool`MP[
      HOL`Bool`SPEC[pairTm, HOL`Stdlib`Int`intCanonIdThm], intRepProd];    (* intCanon pairTm = pairTm *)
    repMul = HOL`Bool`SPEC[intOfNum[nV], HOL`Bool`SPEC[zV, HOL`Stdlib`Int`repIntMulThm]];
                                            (* REP(intMul z (&ℤn)) = intCanon(intMulPair) *)
    canonOfPairEq = HOL`Equal`APTERM[HOL`Stdlib`Int`intCanonConst[], pairEq];
    repMulPair = TRANS[repMul, TRANS[canonOfPairEq, canonId]];             (* REP(intMul z (&ℤn)) = pairTm *)
    fstRepMul = TRANS[HOL`Equal`APTERM[fstNN[], repMulPair], fstPairEq];    (* FST(REP ..) = z1*n *)
    sndRepMul = TRANS[HOL`Equal`APTERM[sndNN[], repMulPair], sndPairEq];    (* SND(REP ..) = z2*n *)
    sumEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], fstRepMul], sndRepMul];
    lhsEq = TRANS[unfoldIntNatAbs[intMulTm[zV, intOfNum[nV]]], sumEq];
                                            (* intNatAbs(intMul z (&ℤn)) = z1*n + z2*n *)
    unfNAz = unfoldIntNatAbs[zV];                                          (* intNatAbs z = z1 + z2 *)
    rhsStep1 = HOL`Equal`APTHM[HOL`Equal`APTERM[timesC, unfNAz], nV];       (* |z|*n = (z1+z2)*n *)
    distrib = HOL`Bool`SPEC[nV, HOL`Bool`SPEC[z2, HOL`Bool`SPEC[z1,
      HOL`Stdlib`Num`timesDistribRightThm]]];                              (* (z1+z2)*n = z1*n + z2*n *)
    rhsEq = TRANS[rhsStep1, distrib];                                      (* |z|*n = z1*n + z2*n *)
    HOL`Bool`GEN[zV, HOL`Bool`GEN[nV, TRANS[lhsEq, HOL`Equal`SYM[rhsEq]]]]
  ];

(* ============================================================ *)
(* ratEqCross — lowest-terms uniqueness via cross-multiplication. *)
(* q = r ⟺ a·&ℤd = c·&ℤb, (a,b)=REP q, (c,d)=REP r. Backward:     *)
(* magnitudes give |a|·d = |c|·b; b | |a|·d with gcd(|a|,b)=1 ⟹    *)
(* b|d (Gauss), symmetric ⟹ b=d; then intMulCancel on the shared  *)
(* denom ⟹ a=c, so REP q = REP r and q = r.                       *)
(* ============================================================ *)

(* ⊢ ∀q r. (q = r) =
       (intMul (FST(REP q)) (&ℤ(SND(REP r))) = intMul (FST(REP r)) (&ℤ(SND(REP q)))) *)
ratEqCrossThm =
  Module[{qV, rV, repQ, repR, a, b, c, d, naA, naC, crossTm,
          hypEq, repEqF, aEqCF, bEqDF, fStep1, fStep2, forwardE,
          hypE, ratRepQ, notB0, gcdAB1, ratRepR, notD0, gcdCD1,
          naE, lhsNA, rhsNA, M, bDivB, bDivBnaC, commBnaC, bDivNcB,
          bDivNaD, gcdCommAB, gcdBnaA1, bDivD, dDivD, dDivDnaA,
          commDnaA, dDivNaD, dDivNcB, gcdCommCD, gcdDnaC1, dDivB,
          bEqD, zbEqZd, ebbLhs, ebb, commA, commC, ecomm, hZ, bEq0,
          falseB, notZbZ0, aEqC, pairEqQR, surjQ, surjR, repEqQR,
          result, iff, intMulC, intOfNumC},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    intMulC = HOL`Stdlib`Int`intMulConst[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    repQ = repRat[qV]; repR = repRat[rV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    c = mkComb[fstIN[], repR]; d = mkComb[sndIN[], repR];
    naA = mkComb[intNatAbsConst[], a]; naC = mkComb[intNatAbsConst[], c];
    crossTm = mkEq[intMulTm[a, intOfNum[d]], intMulTm[c, intOfNum[b]]];

    (* ---- forward: q = r ⟹ cross ---- *)
    hypEq = ASSUME[mkEq[qV, rV]];
    repEqF = HOL`Equal`APTERM[repRatConst[], hypEq];           (* REP q = REP r *)
    aEqCF = HOL`Equal`APTERM[fstIN[], repEqF];                 (* a = c *)
    bEqDF = HOL`Equal`APTERM[sndIN[], repEqF];                 (* b = d *)
    fStep1 = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, aEqCF], intOfNum[d]];
                                                               (* intMul a (&ℤd) = intMul c (&ℤd) *)
    fStep2 = HOL`Equal`APTERM[mkComb[intMulC, c],
      HOL`Equal`SYM[HOL`Equal`APTERM[intOfNumC, bEqDF]]];
                                                               (* intMul c (&ℤd) = intMul c (&ℤb) *)
    forwardE = TRANS[fStep1, fStep2];                          (* {q=r} ⊢ cross *)

    (* ---- backward: cross ⟹ q = r ---- *)
    hypE = ASSUME[crossTm];
    ratRepQ = EQMP[unfoldRatRep[repQ], ratRepRepThm];
    notB0 = HOL`Bool`CONJUNCT1[ratRepQ];                       (* ¬(b = 0) *)
    gcdAB1 = HOL`Bool`CONJUNCT2[ratRepQ];                      (* gcd (intNatAbs a) b = SUC 0 *)
    ratRepR = EQMP[unfoldRatRep[repR], HOL`Kernel`INST[{qV -> rV}, ratRepRepThm]];
    notD0 = HOL`Bool`CONJUNCT1[ratRepR];                       (* ¬(d = 0) *)
    gcdCD1 = HOL`Bool`CONJUNCT2[ratRepR];                      (* gcd (intNatAbs c) d = SUC 0 *)
    (* magnitude equation |a|*d = |c|*b *)
    naE = HOL`Equal`APTERM[intNatAbsConst[], hypE];
    lhsNA = HOL`Bool`SPEC[d, HOL`Bool`SPEC[a, intNatAbsMulOfNumThm]];      (* |a·&ℤd| = |a|*d *)
    rhsNA = HOL`Bool`SPEC[b, HOL`Bool`SPEC[c, intNatAbsMulOfNumThm]];      (* |c·&ℤb| = |c|*b *)
    M = TRANS[HOL`Equal`SYM[lhsNA], TRANS[naE, rhsNA]];        (* |a|*d = |c|*b *)
    (* b | d *)
    bDivB = HOL`Bool`SPEC[b, HOL`Stdlib`Num`dividesReflThm];
    bDivBnaC = HOL`Bool`MP[HOL`Bool`SPEC[naC, HOL`Bool`SPEC[b, HOL`Bool`SPEC[b,
      HOL`Stdlib`Num`dividesMultRightThm]]], bDivB];           (* b | (b*|c|) *)
    commBnaC = HOL`Bool`SPEC[naC, HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesCommThm]];  (* b*|c| = |c|*b *)
    bDivNcB = EQMP[HOL`Equal`APTERM[dividesHead[b], commBnaC], bDivBnaC];  (* b | (|c|*b) *)
    bDivNaD = EQMP[HOL`Equal`APTERM[dividesHead[b], HOL`Equal`SYM[M]], bDivNcB];  (* b | (|a|*d) *)
    gcdCommAB = HOL`Bool`SPEC[b, HOL`Bool`SPEC[naA, gcdCommThm]];          (* gcd |a| b = gcd b |a| *)
    gcdBnaA1 = TRANS[HOL`Equal`SYM[gcdCommAB], gcdAB1];        (* gcd b |a| = SUC 0 *)
    bDivD = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[naA, HOL`Bool`SPEC[b, coprimeDividesProductThm]]],
      gcdBnaA1], bDivNaD];                                     (* b | d *)
    (* d | b *)
    dDivD = HOL`Bool`SPEC[d, HOL`Stdlib`Num`dividesReflThm];
    dDivDnaA = HOL`Bool`MP[HOL`Bool`SPEC[naA, HOL`Bool`SPEC[d, HOL`Bool`SPEC[d,
      HOL`Stdlib`Num`dividesMultRightThm]]], dDivD];           (* d | (d*|a|) *)
    commDnaA = HOL`Bool`SPEC[naA, HOL`Bool`SPEC[d, HOL`Stdlib`Num`timesCommThm]];  (* d*|a| = |a|*d *)
    dDivNaD = EQMP[HOL`Equal`APTERM[dividesHead[d], commDnaA], dDivDnaA];  (* d | (|a|*d) *)
    dDivNcB = EQMP[HOL`Equal`APTERM[dividesHead[d], M], dDivNaD];          (* d | (|c|*b) *)
    gcdCommCD = HOL`Bool`SPEC[d, HOL`Bool`SPEC[naC, gcdCommThm]];          (* gcd |c| d = gcd d |c| *)
    gcdDnaC1 = TRANS[HOL`Equal`SYM[gcdCommCD], gcdCD1];        (* gcd d |c| = SUC 0 *)
    dDivB = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[b, HOL`Bool`SPEC[naC, HOL`Bool`SPEC[d, coprimeDividesProductThm]]],
      gcdDnaC1], dDivNcB];                                     (* d | b *)
    (* b = d *)
    bEqD = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, dividesAntisymThm]], bDivD], dDivB];  (* b = d *)
    (* a = c by cancellation on the shared denominator &ℤ b *)
    zbEqZd = HOL`Equal`APTERM[intOfNumC, bEqD];                (* &ℤb = &ℤd *)
    ebbLhs = HOL`Equal`APTERM[mkComb[intMulC, a], HOL`Equal`SYM[zbEqZd]];
                                                               (* intMul a (&ℤd) = intMul a (&ℤb) *)
    ebb = TRANS[HOL`Equal`SYM[ebbLhs], hypE];                  (* intMul a (&ℤb) = intMul c (&ℤb) *)
    commA = HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulCommThm]];
    commC = HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[c, HOL`Stdlib`Int`intMulCommThm]];
    ecomm = TRANS[HOL`Equal`SYM[commA], TRANS[ebb, commC]];    (* intMul (&ℤb) a = intMul (&ℤb) c *)
    hZ = ASSUME[mkEq[intOfNum[b], intOfNum[zeroN[]]]];
    bEq0 = HOL`Bool`MP[
      HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[b, HOL`Stdlib`Int`intOfNumInjThm]], hZ];  (* b = 0 *)
    falseB = HOL`Bool`MP[HOL`Bool`NOTELIM[notB0], bEq0];
    notZbZ0 = HOL`Bool`NOTINTRO[
      HOL`Bool`DISCH[mkEq[intOfNum[b], intOfNum[zeroN[]]], falseB]];       (* ¬(&ℤb = &ℤ0) *)
    aEqC = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[c, HOL`Bool`SPEC[a, HOL`Bool`SPEC[intOfNum[b],
        HOL`Stdlib`Int`intMulCancelThm]]], notZbZ0], ecomm];   (* a = c *)
    (* q = r *)
    pairEqQR = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], aEqC], bEqD];
                                                               (* (a,b) = (c,d) *)
    surjQ = HOL`Bool`SPEC[repQ,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                         (* (a,b) = REP q *)
    surjR = HOL`Bool`SPEC[repR,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                         (* (c,d) = REP r *)
    repEqQR = TRANS[HOL`Equal`SYM[surjQ], TRANS[pairEqQR, surjR]];         (* REP q = REP r *)
    result = ratEqFromRepEq[repEqQR, qV, rV];                  (* {cross} ⊢ q = r *)

    iff = HOL`Kernel`DEDUCTANTISYM[result, forwardE];          (* ⊢ (q=r) = cross *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, iff]]
  ];

(* ============================================================ *)
(* Additive-inverse support lemmas (mostly small ℕ/int facts).   *)
(* ============================================================ *)

(* ⊢ ∀m. gcd 0 m = m  (proper home Num.wl) *)
gcdZeroLeftThm =
  Module[{mV},
    mV = mkVar["m", numTy];
    HOL`Bool`GEN[mV, TRANS[
      HOL`Bool`SPEC[mV, HOL`Bool`SPEC[zeroN[], gcdCommThm]],   (* gcd 0 m = gcd m 0 *)
      HOL`Bool`SPEC[mV, gcdZeroRightThm]]]                     (* gcd m 0 = m *)
  ];

(* ⊢ ∀m. ¬ (m = 0) ⇒ exDiv m m = SUC 0  (proper home Num.wl) *)
exDivSelfThm =
  Module[{mV, notM0, mDivM, mEq, mTimesOne, cancelEq, suc0Eq},
    mV = mkVar["m", numTy];
    notM0 = ASSUME[notTm[mkEq[mV, zeroN[]]]];
    mDivM = HOL`Bool`SPEC[mV, HOL`Stdlib`Num`dividesReflThm];           (* divides m m *)
    mEq = HOL`Bool`MP[HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, exDivThm]], mDivM];  (* m = m * exDiv m m *)
    mTimesOne = TRANS[
      HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[mV, HOL`Stdlib`Num`timesCommThm]],
      HOL`Bool`SPEC[mV, HOL`Stdlib`Num`oneTimesEqThm]];                 (* m * SUC 0 = m *)
    cancelEq = TRANS[mTimesOne, mEq];                                   (* m * SUC 0 = m * exDiv m m *)
    suc0Eq = HOL`Bool`MP[
      HOL`Bool`SPEC[exDivTm[mV, mV], HOL`Bool`SPEC[oneN[],
        HOL`Bool`MP[HOL`Bool`SPEC[mV, HOL`Stdlib`FTA`multLeftCancelThm], notM0]]],
      cancelEq];                                                        (* SUC 0 = exDiv m m *)
    HOL`Bool`GEN[mV, HOL`Bool`DISCH[notTm[mkEq[mV, zeroN[]]], HOL`Equal`SYM[suc0Eq]]]
  ];

(* ⊢ ∀g. ¬ (g = 0) ⇒ intDivNat (&ℤ 0) g = &ℤ 0 *)
intDivNatZeroThm =
  Module[{gV, z0, notG0, repDiv, repZ0, fstRepZ0, sndRepZ0, exDivZeroG,
          exF, exS, pairEq, repDivEq, repEqZ0, aVar, absL, absR, apAbs},
    gV = mkVar["g", numTy]; z0 = intOfNum[zeroN[]];
    notG0 = ASSUME[notTm[mkEq[gV, zeroN[]]]];
    repDiv = HOL`Bool`MP[HOL`Bool`SPEC[gV, HOL`Bool`SPEC[z0, repIntDivNatThm]], notG0];
                                            (* REP(intDivNat &ℤ0 g) = (exDiv(FST(REP&ℤ0))g, exDiv(SND(REP&ℤ0))g) *)
    repZ0 = HOL`Kernel`INST[{mkVar["n", numTy] -> zeroN[]}, HOL`Stdlib`Int`repIntOfNumThm];
                                            (* REP(&ℤ0) = (0, 0) *)
    fstRepZ0 = TRANS[HOL`Equal`APTERM[fstNN[], repZ0], fstNumAt[zeroN[], zeroN[]]];  (* FST(REP&ℤ0) = 0 *)
    sndRepZ0 = TRANS[HOL`Equal`APTERM[sndNN[], repZ0], sndNumAt[zeroN[], zeroN[]]];  (* SND(REP&ℤ0) = 0 *)
    exDivZeroG = HOL`Bool`MP[HOL`Bool`SPEC[gV, exDivZeroThm], notG0];   (* exDiv 0 g = 0 *)
    exF = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], fstRepZ0], gV], exDivZeroG];
                                            (* exDiv(FST(REP&ℤ0))g = 0 *)
    exS = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], sndRepZ0], gV], exDivZeroG];
                                            (* exDiv(SND(REP&ℤ0))g = 0 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[numPairConsC[], exF], exS];  (* (.. , ..) = (0, 0) *)
    repDivEq = TRANS[repDiv, pairEq];       (* REP(intDivNat &ℤ0 g) = (0, 0) *)
    repEqZ0 = TRANS[repDivEq, HOL`Equal`SYM[repZ0]];   (* REP(intDivNat &ℤ0 g) = REP(&ℤ0) *)
    aVar = concl[HOL`Stdlib`Int`absRepIntThm][[2]];
    absL = HOL`Kernel`INST[{aVar -> intDivNatTm[z0, gV]}, HOL`Stdlib`Int`absRepIntThm];
    absR = HOL`Kernel`INST[{aVar -> z0}, HOL`Stdlib`Int`absRepIntThm];
    apAbs = HOL`Equal`APTERM[HOL`Stdlib`Int`absIntConst[], repEqZ0];
    HOL`Bool`GEN[gV, HOL`Bool`DISCH[notTm[mkEq[gV, zeroN[]]],
      TRANS[HOL`Equal`SYM[absL], TRANS[apAbs, absR]]]]   (* intDivNat &ℤ0 g = &ℤ0 *)
  ];

(* ⊢ ∀m. ¬ (m = 0) ⇒ ratCanon (&ℤ 0, m) = (&ℤ 0, SUC 0) *)
(* The reduced form of the rational 0/m is 0/1 — g = gcd 0 m = m, so   *)
(* numerator = intDivNat (&ℤ 0) m = &ℤ 0 and denominator = exDiv m m = 1. *)
ratCanonZeroNumThm =
  Module[{mV, z0, p, notM0, ucanon, fstP, sndP, gTerm, fstPEq, naFstP,
          sndPEq, gEq, numEq, denEq, pairEq},
    mV = mkVar["m", numTy]; z0 = intOfNum[zeroN[]];
    p = ratPairCons[z0, mV];
    notM0 = ASSUME[notTm[mkEq[mV, zeroN[]]]];
    ucanon = unfoldRatCanon[p];             (* ratCanon p = (intDivNat (FST p) G, exDiv (SND p) G) *)
    fstP = mkComb[fstIN[], p]; sndP = mkComb[sndIN[], p];
    gTerm = gcdTm[mkComb[intNatAbsConst[], fstP], sndP];   (* G = gcd (intNatAbs (FST p)) (SND p) *)
    fstPEq = fstINatAt[z0, mV];             (* FST p = &ℤ0 *)
    naFstP = TRANS[HOL`Equal`APTERM[intNatAbsConst[], fstPEq], intNatAbsZeroThm];  (* intNatAbs(FST p) = 0 *)
    sndPEq = sndINatAt[z0, mV];             (* SND p = m *)
    gEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Num`gcdConst[], naFstP], sndPEq],
      HOL`Bool`SPEC[mV, gcdZeroLeftThm]];   (* G = gcd 0 m = m *)
    numEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intDivNatConst[], fstPEq], gEq],
      HOL`Bool`MP[HOL`Bool`SPEC[mV, intDivNatZeroThm], notM0]];   (* intDivNat (FST p) G = intDivNat &ℤ0 m = &ℤ0 *)
    denEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[exDivConst[], sndPEq], gEq],
      HOL`Bool`MP[HOL`Bool`SPEC[mV, exDivSelfThm], notM0]];       (* exDiv (SND p) G = exDiv m m = SUC 0 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];
    HOL`Bool`GEN[mV, HOL`Bool`DISCH[notTm[mkEq[mV, zeroN[]]],
      TRANS[ucanon, pairEq]]]               (* ratCanon (&ℤ0, m) = (&ℤ0, SUC 0) *)
  ];

(* ============================================================ *)
(* ratAddNegThm — additive inverse: q + (−q) = 0.                *)
(* The sum-pair numerator a·b + (−a)·b = &ℤ 0 (intAddNeg after   *)
(* intMulNeg), denominator b·b; so REP = ratCanon(&ℤ0, b·b) =     *)
(* (&ℤ 0, SUC 0) = REP(&ℚ(&ℤ 0)).                                 *)
(* ============================================================ *)

intNegC[] := HOL`Stdlib`Int`intNegConst[];
intAddC[] := HOL`Stdlib`Int`intAddConst[];

(* ⊢ ∀q. ratAdd q (ratNeg q) = &ℚ (&ℤ 0) *)
ratAddNegThm =
  Module[{qV, repQ, a, b, negQ, notB0, repNeg, cNeg, dNeg, fstNegEq,
          sndNegEq, repAdd, term1, term1Eq, term2, term2Eq, numEq1,
          denEq1, comm1, mulNeg, comm2, mulNegEq, numToNeg, addNeg,
          numZero, spEq, canonEq, bbNeq0, canonZero, repAddEq, repZero,
          repEq, intMulC, intOfNumC, timesC, zRat},
    qV = mkVar["q", ratTy];
    intMulC = HOL`Stdlib`Int`intMulConst[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    timesC = HOL`Stdlib`Num`timesConst[];
    repQ = repRat[qV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    negQ = ratNegTm[qV];
    notB0 = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepRepThm]];  (* ¬(b = 0) *)
    repNeg = HOL`Bool`SPEC[qV, repRatNegThm];           (* REP(ratNeg q) = (intNeg a, b) *)
    cNeg = mkComb[fstIN[], repRat[negQ]]; dNeg = mkComb[sndIN[], repRat[negQ]];
    fstNegEq = TRANS[HOL`Equal`APTERM[fstIN[], repNeg], fstINatAt[intNegTm[a], b]];  (* FST(REP(ratNeg q)) = intNeg a *)
    sndNegEq = TRANS[HOL`Equal`APTERM[sndIN[], repNeg], sndINatAt[intNegTm[a], b]];  (* SND(REP(ratNeg q)) = b *)
    repAdd = HOL`Bool`SPEC[negQ, HOL`Bool`SPEC[qV, repRatAddThm]];
                                            (* REP(ratAdd q (ratNeg q)) = ratCanon(sum-pair) *)
    (* rewrite the negated rep's components in the sum-pair *)
    term1 = intMulTm[a, intOfNum[dNeg]];
    term1Eq = HOL`Equal`APTERM[mkComb[intMulC, a],
      HOL`Equal`APTERM[intOfNumC, sndNegEq]];            (* intMul a (&ℤ dNeg) = intMul a (&ℤ b) *)
    term2 = intMulTm[cNeg, intOfNum[b]];
    term2Eq = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, fstNegEq], intOfNum[b]];
                                            (* intMul cNeg (&ℤ b) = intMul (intNeg a) (&ℤ b) *)
    numEq1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddC[], term1Eq], term2Eq];
                                            (* numerator = intAdd (a·&ℤb) ((intNeg a)·&ℤb) *)
    denEq1 = HOL`Equal`APTERM[mkComb[timesC, b], sndNegEq];   (* b * dNeg = b * b *)
    (* (intNeg a)·&ℤb = intNeg (a·&ℤb), then intAddNeg ⟹ &ℤ0 *)
    comm1 = HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[intNegTm[a], HOL`Stdlib`Int`intMulCommThm]];
                                            (* intMul (intNeg a)(&ℤb) = intMul (&ℤb)(intNeg a) *)
    mulNeg = HOL`Bool`SPEC[a, HOL`Bool`SPEC[intOfNum[b], HOL`Stdlib`Int`intMulNegThm]];
                                            (* intMul (&ℤb)(intNeg a) = intNeg(intMul (&ℤb) a) *)
    comm2 = HOL`Bool`SPEC[a, HOL`Bool`SPEC[intOfNum[b], HOL`Stdlib`Int`intMulCommThm]];
                                            (* intMul (&ℤb) a = intMul a (&ℤb) *)
    mulNegEq = TRANS[comm1, TRANS[mulNeg, HOL`Equal`APTERM[intNegC[], comm2]]];
                                            (* intMul (intNeg a)(&ℤb) = intNeg(intMul a (&ℤb)) *)
    numToNeg = HOL`Equal`APTERM[mkComb[intAddC[], intMulTm[a, intOfNum[b]]], mulNegEq];
                                            (* intAdd (a·&ℤb) ((intNeg a)·&ℤb) = intAdd (a·&ℤb) (intNeg(a·&ℤb)) *)
    addNeg = HOL`Bool`SPEC[intMulTm[a, intOfNum[b]], HOL`Stdlib`Int`intAddNegThm];
                                            (* intAdd (a·&ℤb) (intNeg(a·&ℤb)) = &ℤ0 *)
    numZero = TRANS[numEq1, TRANS[numToNeg, addNeg]];   (* numerator = &ℤ0 *)
    spEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numZero], denEq1];
                                            (* sum-pair = (&ℤ0, b*b) *)
    canonEq = HOL`Equal`APTERM[ratCanonConst[], spEq];  (* ratCanon(sum-pair) = ratCanon(&ℤ0, b*b) *)
    bbNeq0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[b, HOL`Bool`SPEC[b, multNonzeroThm]], notB0], notB0];  (* ¬(b*b = 0) *)
    canonZero = HOL`Bool`MP[HOL`Bool`SPEC[timesTm[b, b], ratCanonZeroNumThm], bbNeq0];
                                            (* ratCanon(&ℤ0, b*b) = (&ℤ0, SUC0) *)
    repAddEq = TRANS[repAdd, TRANS[canonEq, canonZero]];  (* REP(ratAdd q (ratNeg q)) = (&ℤ0, SUC0) *)
    repZero = HOL`Kernel`INST[{mkVar["q", intTy] -> intOfNum[zeroN[]]}, repRatOfIntThm];
                                            (* REP(&ℚ(&ℤ0)) = (&ℤ0, SUC0) *)
    repEq = TRANS[repAddEq, HOL`Equal`SYM[repZero]];    (* REP(ratAdd q (ratNeg q)) = REP(&ℚ(&ℤ0)) *)
    zRat = ratOfIntTm[intOfNum[zeroN[]]];
    HOL`Bool`GEN[qV, ratEqFromRepEq[repEq, ratAddTm[qV, negQ], zRat]]
  ];

(* ============================================================ *)
(* ratCanon-respects layer — the cross-multiplication analog of  *)
(* Int's Grothendieck canonRespects, one tower up. Goal: ratAdd  *)
(* associativity. (a,b) ≈ (c,d) :⟺ a·&ℤd = c·&ℤb is rational     *)
(* equality; ratCanon picks the canonical reduced representative.*)
(*   intMulDivNatCancelThm — multiply the quotient back by g.    *)
(*   ratCanonEquivThm      — ratCanon p ≈ p.                     *)
(*   ratCanonInjThm        — equivalent canonical pairs are =.   *)
(*   ratCrossTransThm      — ≈ is transitive (cancel mid denom). *)
(*   ratCanonRespectsThm   — equivalent pairs canonicalize =.    *)
(* ============================================================ *)

(* ⊢ ∀z g. ¬(g=0) ⇒ divides g (intNatAbs z) ⇒
        intMul (intDivNat z g) (&ℤ g) = z.
   REP(intMul (intDivNat z g) (&ℤg)) expands (repIntMul) to
   intCanon((exDiv z1 g)·g + (exDiv z2 g)·0, (exDiv z1 g)·0 + (exDiv z2 g)·g);
   each surviving (exDiv zi g)·g = zi (g | zi via the INT_REP split),
   so the pair is REP z and intCanon is the identity there.        *)
intMulDivNatCancelThm =
  Module[{zV, gV, notG0, naZ, divHyp, repZ, z1, z2, dz1, dz2, repDivNat,
          fstDivNat, sndDivNat, repG, fstG, sndG, naUnfold, divSum,
          intRepDisj, gDivZero, gDivZ1, gDivZ2, z1Eq, z2Eq, dz1gEqZ1,
          dz2gEqZ2, repMul, plusC, timesC, prod1, prod2, comp1Eq, prod3,
          prod4, comp2Eq, pairEq, surjZ, canonIdZ, canonEq, repMulFinal,
          aVar, absL, absR, result, mulTm, intCanonC},
    zV = mkVar["z", intTy]; gV = mkVar["g", numTy];
    plusC = HOL`Stdlib`Num`plusConst[]; timesC = HOL`Stdlib`Num`timesConst[];
    intCanonC = HOL`Stdlib`Int`intCanonConst[];
    naZ = mkComb[intNatAbsConst[], zV];
    notG0 = ASSUME[notTm[mkEq[gV, zeroN[]]]];
    divHyp = ASSUME[dividesTm[gV, naZ]];
    repZ = repInt[zV];
    z1 = mkComb[fstNN[], repZ]; z2 = mkComb[sndNN[], repZ];
    dz1 = exDivTm[z1, gV]; dz2 = exDivTm[z2, gV];
    mulTm = intMulTm[intDivNatTm[zV, gV], intOfNum[gV]];
    repDivNat = HOL`Bool`MP[
      HOL`Bool`SPEC[gV, HOL`Bool`SPEC[zV, repIntDivNatThm]], notG0];
    fstDivNat = TRANS[HOL`Equal`APTERM[fstNN[], repDivNat], fstNumAt[dz1, dz2]];
    sndDivNat = TRANS[HOL`Equal`APTERM[sndNN[], repDivNat], sndNumAt[dz1, dz2]];
    repG = HOL`Kernel`INST[{mkVar["n", numTy] -> gV}, HOL`Stdlib`Int`repIntOfNumThm];
    fstG = TRANS[HOL`Equal`APTERM[fstNN[], repG], fstNumAt[gV, zeroN[]]];
    sndG = TRANS[HOL`Equal`APTERM[sndNN[], repG], sndNumAt[gV, zeroN[]]];
    naUnfold = unfoldIntNatAbs[zV];                  (* intNatAbs z = z1 + z2 *)
    divSum = EQMP[HOL`Equal`APTERM[dividesHead[gV], naUnfold], divHyp];  (* divides g (z1+z2) *)
    intRepDisj = EQMP[unfoldIntRep[repZ], HOL`Stdlib`Int`intRepRepThm];  (* z1=0 ∨ z2=0 *)
    gDivZero = HOL`Bool`SPEC[gV, HOL`Stdlib`Num`dividesZeroThm];         (* divides g 0 *)
    gDivZ1 = HOL`Bool`DISJCASES[intRepDisj,
      Module[{h}, h = ASSUME[mkEq[z1, zeroN[]]];
        EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[dividesHead[gV], h]], gDivZero]],
      Module[{h, shift}, h = ASSUME[mkEq[z2, zeroN[]]];
        shift = TRANS[
          HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, REFL[z1]], h],   (* z1+z2 = z1+0 *)
          addZeroRightAt[z1]];                                       (* z1+0 = z1 *)
        EQMP[HOL`Equal`APTERM[dividesHead[gV], shift], divSum]]];
    gDivZ2 = HOL`Bool`DISJCASES[intRepDisj,
      Module[{h, shift}, h = ASSUME[mkEq[z1, zeroN[]]];
        shift = TRANS[
          HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, h], REFL[z2]],   (* z1+z2 = 0+z2 *)
          HOL`Bool`SPEC[z2, HOL`Stdlib`Num`addLeftZeroThm]];         (* 0+z2 = z2 *)
        EQMP[HOL`Equal`APTERM[dividesHead[gV], shift], divSum]],
      Module[{h}, h = ASSUME[mkEq[z2, zeroN[]]];
        EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[dividesHead[gV], h]], gDivZero]]];
    z1Eq = HOL`Bool`MP[HOL`Bool`SPEC[z1, HOL`Bool`SPEC[gV, exDivThm]], gDivZ1]; (* z1 = g·dz1 *)
    z2Eq = HOL`Bool`MP[HOL`Bool`SPEC[z2, HOL`Bool`SPEC[gV, exDivThm]], gDivZ2];
    dz1gEqZ1 = TRANS[
      HOL`Bool`SPEC[gV, HOL`Bool`SPEC[dz1, HOL`Stdlib`Num`timesCommThm]],  (* dz1·g = g·dz1 *)
      HOL`Equal`SYM[z1Eq]];                                                (* g·dz1 = z1 *)
    dz2gEqZ2 = TRANS[
      HOL`Bool`SPEC[gV, HOL`Bool`SPEC[dz2, HOL`Stdlib`Num`timesCommThm]],
      HOL`Equal`SYM[z2Eq]];
    repMul = HOL`Bool`SPEC[intOfNum[gV],
      HOL`Bool`SPEC[intDivNatTm[zV, gV], HOL`Stdlib`Int`repIntMulThm]];
    prod1 = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, fstDivNat], fstG],
      dz1gEqZ1];                                            (* z1·... → dz1·g → z1 *)
    prod2 = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sndDivNat], sndG],
      HOL`Bool`SPEC[dz2, HOL`Stdlib`Num`timesZeroEqThm]];   (* dz2·0 = 0 *)
    comp1Eq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, prod1], prod2],
      HOL`Bool`SPEC[z1, HOL`Stdlib`Num`plusZeroEqThm]];     (* z1+0 = z1 *)
    prod3 = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, fstDivNat], sndG],
      HOL`Bool`SPEC[dz1, HOL`Stdlib`Num`timesZeroEqThm]];   (* dz1·0 = 0 *)
    prod4 = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sndDivNat], fstG],
      dz2gEqZ2];                                            (* dz2·g = z2 *)
    comp2Eq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, prod3], prod4],
      HOL`Bool`SPEC[z2, HOL`Stdlib`Num`addLeftZeroThm]];    (* 0+z2 = z2 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[numPairConsC[], comp1Eq], comp2Eq];
    surjZ = HOL`Bool`SPEC[repZ,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                      (* (z1,z2) = REP z *)
    canonIdZ = HOL`Bool`MP[HOL`Bool`SPEC[repZ, HOL`Stdlib`Int`intCanonIdThm],
      HOL`Stdlib`Int`intRepRepThm];                         (* intCanon(REP z) = REP z *)
    canonEq = TRANS[HOL`Equal`APTERM[intCanonC, TRANS[pairEq, surjZ]], canonIdZ];
    repMulFinal = TRANS[repMul, canonEq];                   (* REP(intMul ..) = REP z *)
    aVar = concl[HOL`Stdlib`Int`absRepIntThm][[2]];
    absL = HOL`Kernel`INST[{aVar -> mulTm}, HOL`Stdlib`Int`absRepIntThm];
    absR = HOL`Kernel`INST[{aVar -> zV}, HOL`Stdlib`Int`absRepIntThm];
    result = TRANS[HOL`Equal`SYM[absL],
      TRANS[HOL`Equal`APTERM[absIntC[], repMulFinal], absR]];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[gV,
      HOL`Bool`DISCH[notTm[mkEq[gV, zeroN[]]],
        HOL`Bool`DISCH[dividesTm[gV, naZ], result]]]]
  ];

(* ⊢ ∀p. ¬(SND p = 0) ⇒
        intMul (FST (ratCanon p)) (&ℤ (SND p)) =
        intMul (FST p) (&ℤ (SND (ratCanon p))).
   With g = gcd(|FST p|, SND p): &ℤ(SND p) = &ℤg · &ℤ(exDiv (SND p) g)
   (g | SND p), and intMul (intDivNat (FST p) g) (&ℤg) = FST p (cancel),
   so reassociating collapses the g.                               *)
ratCanonEquivThm =
  Module[{pV, a, b, aTm, g, numTmrt, denTm, ucanon, fstCanonEq, sndCanonEq,
          notB0, notG0, gDivB, gDivNA, bEq, cancel, step1, step2, zbEq,
          lhsStep1, assocInst, lhsStep2, cancelStep, result, lhsRewrite,
          rhsRewrite, goalEq, intMulC, intOfNumC},
    pV = mkVar["p", ratPairTy];
    intMulC = HOL`Stdlib`Int`intMulConst[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    a = mkComb[fstIN[], pV]; b = mkComb[sndIN[], pV];
    aTm = mkComb[intNatAbsConst[], a];
    g = gcdTm[aTm, b];
    numTmrt = intDivNatTm[a, g]; denTm = exDivTm[b, g];
    ucanon = unfoldRatCanon[pV];
    fstCanonEq = TRANS[HOL`Equal`APTERM[fstIN[], ucanon], fstINatAt[numTmrt, denTm]];  (* FST(ratCanon p) = intDivNat a g *)
    sndCanonEq = TRANS[HOL`Equal`APTERM[sndIN[], ucanon], sndINatAt[numTmrt, denTm]];  (* SND(ratCanon p) = exDiv b g *)
    notB0 = ASSUME[notTm[mkEq[b, zeroN[]]]];
    notG0 = HOL`Bool`MP[
      HOL`Bool`SPEC[b, HOL`Bool`SPEC[aTm, gcdNonzeroFromRightThm]], notB0];
    gDivB = HOL`Bool`SPEC[b, HOL`Bool`SPEC[aTm, HOL`Stdlib`Num`gcdDividesRightThm]];
    gDivNA = HOL`Bool`SPEC[b, HOL`Bool`SPEC[aTm, HOL`Stdlib`Num`gcdDividesLeftThm]];
    bEq = HOL`Bool`MP[HOL`Bool`SPEC[b, HOL`Bool`SPEC[g, exDivThm]], gDivB];  (* b = g · exDiv b g *)
    cancel = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[g, HOL`Bool`SPEC[a, intMulDivNatCancelThm]], notG0], gDivNA];
                                                  (* intMul (intDivNat a g) (&ℤg) = a *)
    step1 = HOL`Equal`APTERM[intOfNumC, bEq];     (* &ℤb = &ℤ(g · exDiv b g) *)
    step2 = HOL`Bool`SPEC[denTm, HOL`Bool`SPEC[g, HOL`Stdlib`Int`intOfNumMulThm]];
                                                  (* &ℤ(g · exDiv b g) = intMul(&ℤg)(&ℤ exDiv b g) *)
    zbEq = TRANS[step1, step2];
    lhsStep1 = HOL`Equal`APTERM[mkComb[intMulC, numTmrt], zbEq];
    assocInst = HOL`Bool`SPEC[intOfNum[denTm], HOL`Bool`SPEC[intOfNum[g],
      HOL`Bool`SPEC[numTmrt, HOL`Stdlib`Int`intMulAssocThm]]];
    lhsStep2 = HOL`Equal`SYM[assocInst];
    cancelStep = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, cancel], intOfNum[denTm]];
    result = TRANS[lhsStep1, TRANS[lhsStep2, cancelStep]];
                                                  (* intMul(intDivNat a g)(&ℤb) = intMul a (&ℤ exDiv b g) *)
    lhsRewrite = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, fstCanonEq], intOfNum[b]];
    rhsRewrite = HOL`Equal`APTERM[mkComb[intMulC, a],
      HOL`Equal`APTERM[intOfNumC, sndCanonEq]];
    goalEq = TRANS[lhsRewrite, TRANS[result, HOL`Equal`SYM[rhsRewrite]]];
    HOL`Bool`GEN[pV, HOL`Bool`DISCH[notTm[mkEq[b, zeroN[]]], goalEq]]
  ];

(* ⊢ ∀p p'. RAT_REP p ⇒ RAT_REP p' ⇒
        intMul (FST p) (&ℤ (SND p')) = intMul (FST p') (&ℤ (SND p)) ⇒ p = p'.
   The backward direction of ratEqCross lifted to arbitrary canonical
   pairs: |a|*d = |c|*b, then b|d and d|b (Gauss, coprimality), so b=d
   (antisym), then a=c (intMulCancel on the shared &ℤb), then pairSurj.  *)
ratCanonInjThm =
  Module[{pV, pV2, a, b, c, d, naA, naC, crossTm, repP, repP2, notB0,
          gcdAB1, notD0, gcdCD1, hypE, naE, lhsNA, rhsNA, M, bDivB,
          bDivBnaC, commBnaC, bDivNcB, bDivNaD, gcdCommAB, gcdBnaA1, bDivD,
          dDivD, dDivDnaA, commDnaA, dDivNaD, dDivNcB, gcdCommCD, gcdDnaC1,
          dDivB, bEqD, zbEqZd, ebbLhs, ebb, commA, commC, ecomm, hZ, bEq0,
          falseB, notZbZ0, aEqC, pairEqPP, surjP, surjP2, result,
          intMulC, intOfNumC},
    pV = mkVar["p", ratPairTy]; pV2 = mkVar["q", ratPairTy];
    intMulC = HOL`Stdlib`Int`intMulConst[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    a = mkComb[fstIN[], pV]; b = mkComb[sndIN[], pV];
    c = mkComb[fstIN[], pV2]; d = mkComb[sndIN[], pV2];
    naA = mkComb[intNatAbsConst[], a]; naC = mkComb[intNatAbsConst[], c];
    crossTm = mkEq[intMulTm[a, intOfNum[d]], intMulTm[c, intOfNum[b]]];
    repP = EQMP[unfoldRatRep[pV], ASSUME[mkComb[ratRepConst[], pV]]];
    notB0 = HOL`Bool`CONJUNCT1[repP];
    gcdAB1 = HOL`Bool`CONJUNCT2[repP];
    repP2 = EQMP[unfoldRatRep[pV2], ASSUME[mkComb[ratRepConst[], pV2]]];
    notD0 = HOL`Bool`CONJUNCT1[repP2];
    gcdCD1 = HOL`Bool`CONJUNCT2[repP2];
    hypE = ASSUME[crossTm];
    naE = HOL`Equal`APTERM[intNatAbsConst[], hypE];
    lhsNA = HOL`Bool`SPEC[d, HOL`Bool`SPEC[a, intNatAbsMulOfNumThm]];   (* |a·&ℤd| = |a|*d *)
    rhsNA = HOL`Bool`SPEC[b, HOL`Bool`SPEC[c, intNatAbsMulOfNumThm]];   (* |c·&ℤb| = |c|*b *)
    M = TRANS[HOL`Equal`SYM[lhsNA], TRANS[naE, rhsNA]];        (* |a|*d = |c|*b *)
    bDivB = HOL`Bool`SPEC[b, HOL`Stdlib`Num`dividesReflThm];
    bDivBnaC = HOL`Bool`MP[HOL`Bool`SPEC[naC, HOL`Bool`SPEC[b, HOL`Bool`SPEC[b,
      HOL`Stdlib`Num`dividesMultRightThm]]], bDivB];           (* b | (b*|c|) *)
    commBnaC = HOL`Bool`SPEC[naC, HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesCommThm]];
    bDivNcB = EQMP[HOL`Equal`APTERM[dividesHead[b], commBnaC], bDivBnaC];  (* b | (|c|*b) *)
    bDivNaD = EQMP[HOL`Equal`APTERM[dividesHead[b], HOL`Equal`SYM[M]], bDivNcB];  (* b | (|a|*d) *)
    gcdCommAB = HOL`Bool`SPEC[b, HOL`Bool`SPEC[naA, gcdCommThm]];
    gcdBnaA1 = TRANS[HOL`Equal`SYM[gcdCommAB], gcdAB1];        (* gcd b |a| = SUC 0 *)
    bDivD = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[naA, HOL`Bool`SPEC[b, coprimeDividesProductThm]]],
      gcdBnaA1], bDivNaD];                                     (* b | d *)
    dDivD = HOL`Bool`SPEC[d, HOL`Stdlib`Num`dividesReflThm];
    dDivDnaA = HOL`Bool`MP[HOL`Bool`SPEC[naA, HOL`Bool`SPEC[d, HOL`Bool`SPEC[d,
      HOL`Stdlib`Num`dividesMultRightThm]]], dDivD];           (* d | (d*|a|) *)
    commDnaA = HOL`Bool`SPEC[naA, HOL`Bool`SPEC[d, HOL`Stdlib`Num`timesCommThm]];
    dDivNaD = EQMP[HOL`Equal`APTERM[dividesHead[d], commDnaA], dDivDnaA];  (* d | (|a|*d) *)
    dDivNcB = EQMP[HOL`Equal`APTERM[dividesHead[d], M], dDivNaD];          (* d | (|c|*b) *)
    gcdCommCD = HOL`Bool`SPEC[d, HOL`Bool`SPEC[naC, gcdCommThm]];
    gcdDnaC1 = TRANS[HOL`Equal`SYM[gcdCommCD], gcdCD1];        (* gcd d |c| = SUC 0 *)
    dDivB = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[b, HOL`Bool`SPEC[naC, HOL`Bool`SPEC[d, coprimeDividesProductThm]]],
      gcdDnaC1], dDivNcB];                                     (* d | b *)
    bEqD = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, dividesAntisymThm]], bDivD], dDivB];  (* b = d *)
    zbEqZd = HOL`Equal`APTERM[intOfNumC, bEqD];               (* &ℤb = &ℤd *)
    ebbLhs = HOL`Equal`APTERM[mkComb[intMulC, a], HOL`Equal`SYM[zbEqZd]];
                                                              (* intMul a (&ℤd) = intMul a (&ℤb) *)
    ebb = TRANS[HOL`Equal`SYM[ebbLhs], hypE];                 (* intMul a (&ℤb) = intMul c (&ℤb) *)
    commA = HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulCommThm]];
    commC = HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[c, HOL`Stdlib`Int`intMulCommThm]];
    ecomm = TRANS[HOL`Equal`SYM[commA], TRANS[ebb, commC]];   (* intMul (&ℤb) a = intMul (&ℤb) c *)
    hZ = ASSUME[mkEq[intOfNum[b], intOfNum[zeroN[]]]];
    bEq0 = HOL`Bool`MP[
      HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[b, HOL`Stdlib`Int`intOfNumInjThm]], hZ];  (* b = 0 *)
    falseB = HOL`Bool`MP[HOL`Bool`NOTELIM[notB0], bEq0];
    notZbZ0 = HOL`Bool`NOTINTRO[
      HOL`Bool`DISCH[mkEq[intOfNum[b], intOfNum[zeroN[]]], falseB]];  (* ¬(&ℤb = &ℤ0) *)
    aEqC = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[c, HOL`Bool`SPEC[a, HOL`Bool`SPEC[intOfNum[b],
        HOL`Stdlib`Int`intMulCancelThm]]], notZbZ0], ecomm];  (* a = c *)
    pairEqPP = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], aEqC], bEqD];  (* (a,b)=(c,d) *)
    surjP = HOL`Bool`SPEC[pV,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                        (* (a,b) = p *)
    surjP2 = HOL`Bool`SPEC[pV2,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                        (* (c,d) = p' *)
    result = TRANS[HOL`Equal`SYM[surjP], TRANS[pairEqPP, surjP2]];  (* p = p' *)
    HOL`Bool`GEN[pV, HOL`Bool`GEN[pV2,
      HOL`Bool`DISCH[mkComb[ratRepConst[], pV],
        HOL`Bool`DISCH[mkComb[ratRepConst[], pV2],
          HOL`Bool`DISCH[crossTm, result]]]]]
  ];

(* ⊢ ∀a b c d e f. ¬(d=0) ⇒ a·&ℤd = c·&ℤb ⇒ c·&ℤf = e·&ℤd ⇒ a·&ℤf = e·&ℤb.
   Transitivity of cross-equivalence: (a·&ℤf)·&ℤd = (e·&ℤb)·&ℤd by the
   ring chain through the two hyps, then cancel the shared &ℤd (≠0).     *)
ratCrossTransThm =
  Module[{aV, bV, cV, dV, eV, fV, intMulC, swap, hyp1, hyp2, notD0,
          r1, h1, r2, h2, r3, P, comm1, comm2, cancelInput, hZ, dEq0,
          falseD, notZd0, cancelInst, body},
    aV = mkVar["a", intTy]; cV = mkVar["c", intTy]; eV = mkVar["e", intTy];
    bV = mkVar["b", numTy]; dV = mkVar["d", numTy]; fV = mkVar["f", numTy];
    intMulC = HOL`Stdlib`Int`intMulConst[];
    (* (x·&ℤm)·&ℤn = (x·&ℤn)·&ℤm *)
    swap[xT_, mN_, nN_] := Module[{zm = intOfNum[mN], zn = intOfNum[nN]},
      TRANS[
        HOL`Bool`SPEC[zn, HOL`Bool`SPEC[zm, HOL`Bool`SPEC[xT,
          HOL`Stdlib`Int`intMulAssocThm]]],
        TRANS[
          HOL`Equal`APTERM[mkComb[intMulC, xT],
            HOL`Bool`SPEC[zn, HOL`Bool`SPEC[zm, HOL`Stdlib`Int`intMulCommThm]]],
          HOL`Equal`SYM[HOL`Bool`SPEC[zm, HOL`Bool`SPEC[zn, HOL`Bool`SPEC[xT,
            HOL`Stdlib`Int`intMulAssocThm]]]]]]];
    hyp1 = ASSUME[mkEq[intMulTm[aV, intOfNum[dV]], intMulTm[cV, intOfNum[bV]]]];
    hyp2 = ASSUME[mkEq[intMulTm[cV, intOfNum[fV]], intMulTm[eV, intOfNum[dV]]]];
    notD0 = ASSUME[notTm[mkEq[dV, zeroN[]]]];
    r1 = swap[aV, fV, dV];     (* (a·&ℤf)·&ℤd = (a·&ℤd)·&ℤf *)
    h1 = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, hyp1], intOfNum[fV]];  (* = (c·&ℤb)·&ℤf *)
    r2 = swap[cV, bV, fV];     (* (c·&ℤb)·&ℤf = (c·&ℤf)·&ℤb *)
    h2 = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, hyp2], intOfNum[bV]];  (* = (e·&ℤd)·&ℤb *)
    r3 = swap[eV, dV, bV];     (* (e·&ℤd)·&ℤb = (e·&ℤb)·&ℤd *)
    P = TRANS[r1, TRANS[h1, TRANS[r2, TRANS[h2, r3]]]];  (* (a·&ℤf)·&ℤd = (e·&ℤb)·&ℤd *)
    comm1 = HOL`Bool`SPEC[intOfNum[dV], HOL`Bool`SPEC[intMulTm[aV, intOfNum[fV]],
      HOL`Stdlib`Int`intMulCommThm]];     (* (a·&ℤf)·&ℤd = &ℤd·(a·&ℤf) *)
    comm2 = HOL`Bool`SPEC[intMulTm[eV, intOfNum[bV]], HOL`Bool`SPEC[intOfNum[dV],
      HOL`Stdlib`Int`intMulCommThm]];     (* &ℤd·(e·&ℤb) = (e·&ℤb)·&ℤd *)
    cancelInput = TRANS[HOL`Equal`SYM[comm1], TRANS[P, HOL`Equal`SYM[comm2]]];
                                          (* &ℤd·(a·&ℤf) = &ℤd·(e·&ℤb) *)
    hZ = ASSUME[mkEq[intOfNum[dV], intOfNum[zeroN[]]]];
    dEq0 = HOL`Bool`MP[
      HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[dV, HOL`Stdlib`Int`intOfNumInjThm]], hZ];
    falseD = HOL`Bool`MP[HOL`Bool`NOTELIM[notD0], dEq0];
    notZd0 = HOL`Bool`NOTINTRO[
      HOL`Bool`DISCH[mkEq[intOfNum[dV], intOfNum[zeroN[]]], falseD]];  (* ¬(&ℤd = &ℤ0) *)
    cancelInst = HOL`Bool`SPEC[intMulTm[eV, intOfNum[bV]],
      HOL`Bool`SPEC[intMulTm[aV, intOfNum[fV]],
        HOL`Bool`SPEC[intOfNum[dV], HOL`Stdlib`Int`intMulCancelThm]]];
    body = HOL`Bool`MP[HOL`Bool`MP[cancelInst, notZd0], cancelInput];  (* a·&ℤf = e·&ℤb *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`GEN[dV,
      HOL`Bool`GEN[eV, HOL`Bool`GEN[fV,
        HOL`Bool`DISCH[notTm[mkEq[dV, zeroN[]]],
          HOL`Bool`DISCH[concl[hyp1],
            HOL`Bool`DISCH[concl[hyp2], body]]]]]]]]]
  ];

(* ⊢ ∀p p'. ¬(SND p=0) ⇒ ¬(SND p'=0) ⇒
        intMul (FST p) (&ℤ (SND p')) = intMul (FST p') (&ℤ (SND p)) ⇒
        ratCanon p = ratCanon p'.
   ratCanon p ≈ p ≈ p' ≈ ratCanon p' (equiv, hyp, equiv), chained by
   ratCrossTrans; both canon results are canonical, so ratCanonInj gives
   equality.                                                            *)
ratCanonRespectsThm =
  Module[{pV, pV2, a, b, c, d, cp, cp2, ca, cb, cc, cd, crossTm, notB0,
          notD0, crossHyp, landsP, landsP2, equivP, equivP2, step1, step2,
          injInst, final},
    pV = mkVar["p", ratPairTy]; pV2 = mkVar["q", ratPairTy];
    a = mkComb[fstIN[], pV]; b = mkComb[sndIN[], pV];
    c = mkComb[fstIN[], pV2]; d = mkComb[sndIN[], pV2];
    cp = ratCanonTm[pV]; cp2 = ratCanonTm[pV2];
    ca = mkComb[fstIN[], cp]; cb = mkComb[sndIN[], cp];
    cc = mkComb[fstIN[], cp2]; cd = mkComb[sndIN[], cp2];
    crossTm = mkEq[intMulTm[a, intOfNum[d]], intMulTm[c, intOfNum[b]]];
    notB0 = ASSUME[notTm[mkEq[b, zeroN[]]]];
    notD0 = ASSUME[notTm[mkEq[d, zeroN[]]]];
    crossHyp = ASSUME[crossTm];
    landsP = HOL`Bool`MP[HOL`Bool`SPEC[pV, ratCanonLandsThm], notB0];   (* RAT_REP (ratCanon p) *)
    landsP2 = HOL`Bool`MP[HOL`Bool`SPEC[pV2, ratCanonLandsThm], notD0]; (* RAT_REP (ratCanon p') *)
    equivP = HOL`Bool`MP[HOL`Bool`SPEC[pV, ratCanonEquivThm], notB0];   (* ca·&ℤb = a·&ℤcb *)
    equivP2 = HOL`Bool`MP[HOL`Bool`SPEC[pV2, ratCanonEquivThm], notD0]; (* cc·&ℤd = c·&ℤcd *)
    (* (ca,cb) ≈ (a,b) ≈ (c,d) ⟹ (ca,cb) ≈ (c,d); middle denom b *)
    step1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[c, HOL`Bool`SPEC[b, HOL`Bool`SPEC[a,
        HOL`Bool`SPEC[cb, HOL`Bool`SPEC[ca, ratCrossTransThm]]]]]],
      notB0], equivP], crossHyp];                                      (* ca·&ℤd = c·&ℤcb *)
    (* (ca,cb) ≈ (c,d) ≈ (cc,cd) ⟹ (ca,cb) ≈ (cc,cd); middle denom d *)
    step2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[cd, HOL`Bool`SPEC[cc, HOL`Bool`SPEC[d, HOL`Bool`SPEC[c,
        HOL`Bool`SPEC[cb, HOL`Bool`SPEC[ca, ratCrossTransThm]]]]]],
      notD0], step1], HOL`Equal`SYM[equivP2]];                         (* ca·&ℤcd = cc·&ℤcb *)
    injInst = HOL`Bool`SPEC[cp2, HOL`Bool`SPEC[cp, ratCanonInjThm]];
    final = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[injInst, landsP], landsP2], step2];
    HOL`Bool`GEN[pV, HOL`Bool`GEN[pV2,
      HOL`Bool`DISCH[notTm[mkEq[b, zeroN[]]],
        HOL`Bool`DISCH[notTm[mkEq[d, zeroN[]]],
          HOL`Bool`DISCH[crossTm, final]]]]]
  ];

(* ============================================================ *)
(* ratAdd associativity. The unreduced sum-pairs:                *)
(*   sumPairTm n1 m1 n2 m2 = (n1·&ℤm2 + n2·&ℤm1, m1·m2)           *)
(* matches ratAddPair on int×num reps. cong-left/right show       *)
(* ratCanon is unchanged when an operand is swapped for a cross-  *)
(* equivalent one; assoc then aligns the fully unreduced pairs.   *)
(* ============================================================ *)

intMulCC[] := HOL`Stdlib`Int`intMulConst[];

(* ⊢ (x·&ℤm)·&ℤn = (x·&ℤn)·&ℤm  (swap the two embedded num factors) *)
crossSwapAt[xT_, mN_, nN_] := Module[{zm = intOfNum[mN], zn = intOfNum[nN]},
  TRANS[
    HOL`Bool`SPEC[zn, HOL`Bool`SPEC[zm, HOL`Bool`SPEC[xT,
      HOL`Stdlib`Int`intMulAssocThm]]],
    TRANS[
      HOL`Equal`APTERM[mkComb[intMulCC[], xT],
        HOL`Bool`SPEC[zn, HOL`Bool`SPEC[zm, HOL`Stdlib`Int`intMulCommThm]]],
      HOL`Equal`SYM[HOL`Bool`SPEC[zm, HOL`Bool`SPEC[zn, HOL`Bool`SPEC[xT,
        HOL`Stdlib`Int`intMulAssocThm]]]]]]];

(* ⊢ intMul (intAdd p q) z = intAdd (intMul p z) (intMul q z)  (right distrib) *)
intRDistAt[pT_, qT_, zT_] :=
  TRANS[
    HOL`Bool`SPEC[zT, HOL`Bool`SPEC[intAddTm[pT, qT], HOL`Stdlib`Int`intMulCommThm]],
    TRANS[
      HOL`Bool`SPEC[qT, HOL`Bool`SPEC[pT, HOL`Bool`SPEC[zT, HOL`Stdlib`Int`intMulDistribThm]]],
      HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[intAddC[],
          HOL`Bool`SPEC[pT, HOL`Bool`SPEC[zT, HOL`Stdlib`Int`intMulCommThm]]],
        HOL`Bool`SPEC[qT, HOL`Bool`SPEC[zT, HOL`Stdlib`Int`intMulCommThm]]]]];

sumPairTm[n1_, m1_, n2_, m2_] :=
  ratPairCons[
    intAddTm[intMulTm[n1, intOfNum[m2]], intMulTm[n2, intOfNum[m1]]],
    timesTm[m1, m2]];

(* ⊢ ∀n1 m1 n1' m1' n2 m2. ¬(m1=0) ⇒ ¬(m1'=0) ⇒ ¬(m2=0) ⇒
        intMul n1 (&ℤ m1') = intMul n1' (&ℤ m1) ⇒
        ratCanon (sumPair n1 m1 n2 m2) = ratCanon (sumPair n1' m1' n2 m2).   *)
ratAddCongLeftThm =
  Module[{n1, m1, n1p, m1p, n2, m2, hyp, notM10, notM10p, notM20, intMulC,
          intAddCl, P, Q, Pp, Qp, X, Xp, rdL, term1Eq, term2Eq, rdR, key,
          zmL, zmR, lstep, lassoc, keyM2, rassoc, rstep, crossPoly,
          suml, sumlp, fstEqL, sndEqL, fstEqLp, sndEqLp, notProd0, notProd0p,
          notSndL, notSndLp, crossUnred, respInst, congEq},
    n1 = mkVar["n1", intTy]; n1p = mkVar["e", intTy]; n2 = mkVar["c", intTy];
    m1 = mkVar["m1", numTy]; m1p = mkVar["f", numTy]; m2 = mkVar["g", numTy];
    intMulC = intMulCC[]; intAddCl = intAddC[];
    hyp = ASSUME[mkEq[intMulTm[n1, intOfNum[m1p]], intMulTm[n1p, intOfNum[m1]]]];
    notM10 = ASSUME[notTm[mkEq[m1, zeroN[]]]];
    notM10p = ASSUME[notTm[mkEq[m1p, zeroN[]]]];
    notM20 = ASSUME[notTm[mkEq[m2, zeroN[]]]];
    P = intMulTm[n1, intOfNum[m2]]; Q = intMulTm[n2, intOfNum[m1]];
    Pp = intMulTm[n1p, intOfNum[m2]]; Qp = intMulTm[n2, intOfNum[m1p]];
    X = intAddTm[P, Q]; Xp = intAddTm[Pp, Qp];
    rdL = intRDistAt[P, Q, intOfNum[m1p]];   (* X·&ℤm1' = P·&ℤm1' + Q·&ℤm1' *)
    term1Eq = TRANS[crossSwapAt[n1, m2, m1p],        (* (n1·&ℤm2)·&ℤm1' = (n1·&ℤm1')·&ℤm2 *)
      TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, hyp], intOfNum[m2]],  (* = (n1'·&ℤm1)·&ℤm2 *)
        crossSwapAt[n1p, m1, m2]]];                  (* = (n1'·&ℤm2)·&ℤm1 *)
    term2Eq = crossSwapAt[n2, m1, m1p];      (* (n2·&ℤm1)·&ℤm1' = (n2·&ℤm1')·&ℤm1 *)
    rdR = intRDistAt[Pp, Qp, intOfNum[m1]];  (* X'·&ℤm1 = P'·&ℤm1 + Q'·&ℤm1 *)
    key = TRANS[rdL, TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, term1Eq], term2Eq],
      HOL`Equal`SYM[rdR]]];                  (* intMul X (&ℤm1') = intMul X' (&ℤm1) *)
    zmL = HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1p, HOL`Stdlib`Int`intOfNumMulThm]];
    zmR = HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1, HOL`Stdlib`Int`intOfNumMulThm]];
    lstep = HOL`Equal`APTERM[mkComb[intMulC, X], zmL];
    lassoc = HOL`Equal`SYM[HOL`Bool`SPEC[intOfNum[m2], HOL`Bool`SPEC[intOfNum[m1p],
      HOL`Bool`SPEC[X, HOL`Stdlib`Int`intMulAssocThm]]]];
    keyM2 = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, key], intOfNum[m2]];
    rassoc = HOL`Bool`SPEC[intOfNum[m2], HOL`Bool`SPEC[intOfNum[m1],
      HOL`Bool`SPEC[Xp, HOL`Stdlib`Int`intMulAssocThm]]];
    rstep = HOL`Equal`SYM[HOL`Equal`APTERM[mkComb[intMulC, Xp], zmR]];
    crossPoly = TRANS[lstep, TRANS[lassoc, TRANS[keyM2, TRANS[rassoc, rstep]]]];
                (* intMul X (&ℤ(m1'·m2)) = intMul X' (&ℤ(m1·m2)) *)
    suml = sumPairTm[n1, m1, n2, m2]; sumlp = sumPairTm[n1p, m1p, n2, m2];
    fstEqL = fstINatAt[X, timesTm[m1, m2]]; sndEqL = sndINatAt[X, timesTm[m1, m2]];
    fstEqLp = fstINatAt[Xp, timesTm[m1p, m2]]; sndEqLp = sndINatAt[Xp, timesTm[m1p, m2]];
    notProd0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1, multNonzeroThm]], notM10], notM20];
    notProd0p = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1p, multNonzeroThm]], notM10p], notM20];
    notSndL = HOL`Drule`SUBS[{HOL`Equal`SYM[sndEqL]}, notProd0];   (* ¬(SND suml = 0) *)
    notSndLp = HOL`Drule`SUBS[{HOL`Equal`SYM[sndEqLp]}, notProd0p];
    crossUnred = Module[{lhsRw, rhsRw, intOfNumC = HOL`Stdlib`Int`intOfNumConst[]},
      lhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqL],
        HOL`Equal`APTERM[intOfNumC, sndEqLp]];   (* intMul(FST suml)(&ℤ(SND sumlp)) = intMul X (&ℤ(m1'·m2)) *)
      rhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqLp],
        HOL`Equal`APTERM[intOfNumC, sndEqL]];    (* intMul(FST sumlp)(&ℤ(SND suml)) = intMul X' (&ℤ(m1·m2)) *)
      TRANS[lhsRw, TRANS[crossPoly, HOL`Equal`SYM[rhsRw]]]];
    respInst = HOL`Bool`SPEC[sumlp, HOL`Bool`SPEC[suml, ratCanonRespectsThm]];
    congEq = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[respInst, notSndL], notSndLp], crossUnred];
    HOL`Bool`GEN[n1, HOL`Bool`GEN[m1, HOL`Bool`GEN[n1p, HOL`Bool`GEN[m1p,
      HOL`Bool`GEN[n2, HOL`Bool`GEN[m2,
        HOL`Bool`DISCH[notTm[mkEq[m1, zeroN[]]],
          HOL`Bool`DISCH[notTm[mkEq[m1p, zeroN[]]],
            HOL`Bool`DISCH[notTm[mkEq[m2, zeroN[]]],
              HOL`Bool`DISCH[concl[hyp], congEq]]]]]]]]]]
  ];

(* ⊢ sumPair n1 m1 n2 m2 = sumPair n2 m2 n1 m1 (commutativity, via intAddComm + timesComm) *)
sumFlipAt[n1_, m1_, n2_, m2_] :=
  HOL`Kernel`MKCOMB[
    HOL`Equal`APTERM[ratPairConsC[],
      HOL`Bool`SPEC[intMulTm[n2, intOfNum[m1]],
        HOL`Bool`SPEC[intMulTm[n1, intOfNum[m2]], HOL`Stdlib`Int`intAddCommThm]]],
    HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1, HOL`Stdlib`Num`timesCommThm]]];

(* ⊢ ∀a b n2 m2 n2' m2'. ¬(b=0) ⇒ ¬(m2=0) ⇒ ¬(m2'=0) ⇒
        intMul n2 (&ℤ m2') = intMul n2' (&ℤ m2) ⇒
        ratCanon (sumPair a b n2 m2) = ratCanon (sumPair a b n2' m2').
   Derived from ratAddCongLeftThm by flipping both sum-pairs.            *)
ratAddCongRightThm =
  Module[{a1, b1, n2, m2, n2p, m2p, hyp, congMid, result},
    a1 = mkVar["a", intTy]; b1 = mkVar["b", numTy];
    n2 = mkVar["c", intTy]; m2 = mkVar["d", numTy];
    n2p = mkVar["e", intTy]; m2p = mkVar["f", numTy];
    hyp = ASSUME[mkEq[intMulTm[n2, intOfNum[m2p]], intMulTm[n2p, intOfNum[m2]]]];
    congMid = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[b1, HOL`Bool`SPEC[a1, HOL`Bool`SPEC[m2p, HOL`Bool`SPEC[n2p,
        HOL`Bool`SPEC[m2, HOL`Bool`SPEC[n2, ratAddCongLeftThm]]]]]],
      ASSUME[notTm[mkEq[m2, zeroN[]]]]], ASSUME[notTm[mkEq[m2p, zeroN[]]]]],
      ASSUME[notTm[mkEq[b1, zeroN[]]]]], hyp];
                (* ratCanon(sumPair c d a b) = ratCanon(sumPair e f a b) *)
    result = TRANS[HOL`Equal`APTERM[ratCanonConst[], sumFlipAt[a1, b1, n2, m2]],
      TRANS[congMid,
        HOL`Equal`APTERM[ratCanonConst[], HOL`Equal`SYM[sumFlipAt[a1, b1, n2p, m2p]]]]];
    HOL`Bool`GEN[a1, HOL`Bool`GEN[b1, HOL`Bool`GEN[n2, HOL`Bool`GEN[m2,
      HOL`Bool`GEN[n2p, HOL`Bool`GEN[m2p,
        HOL`Bool`DISCH[notTm[mkEq[b1, zeroN[]]],
          HOL`Bool`DISCH[notTm[mkEq[m2, zeroN[]]],
            HOL`Bool`DISCH[notTm[mkEq[m2p, zeroN[]]],
              HOL`Bool`DISCH[concl[hyp], result]]]]]]]]]]
  ];

(* ⊢ intMul (FST (REP (ratAdd q r))) (&ℤ Uden) = intMul Unum (&ℤ (SND (REP (ratAdd q r))))
   where (Unum, Uden) = ratAddPair (REP q) (REP r): REP (ratAdd q r) is
   cross-equivalent to its unreduced sum-pair (repRatAdd + ratCanonEquiv).  *)
repAddEquivAt[qT_, rT_] :=
  Module[{repQ, repR, U1, U1num, U1den, repQR, notSndQ, notSndR, sndU1e,
          notSndU1, fstU1, sndU1, equivU1, fstEqA, denEqA, lhsRw, fstEqB,
          sndEqB, rhsRw, intMulC, intOfNumC, ratRepQ},
    intMulC = intMulCC[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    repQ = repRat[qT]; repR = repRat[rT];
    U1 = ratAddPair[repQ, repR]; U1num = U1[[1, 2]]; U1den = U1[[2]];
    repQR = HOL`Bool`SPEC[rT, HOL`Bool`SPEC[qT, repRatAddThm]];  (* REP(ratAdd q r) = ratCanon U1 *)
    ratRepQ = HOL`Kernel`INST[{mkVar["q", ratTy] -> qT}, ratRepRepThm];
    notSndQ = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepQ]];          (* ¬(SND repQ = 0) *)
    notSndR = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repR],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> rT}, ratRepRepThm]]];             (* ¬(SND repR = 0) *)
    sndU1e = sndINatAt[U1num, U1den];                                         (* SND U1 = U1den *)
    notSndU1 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndU1e]},
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[mkComb[sndIN[], repR],
        HOL`Bool`SPEC[mkComb[sndIN[], repQ], multNonzeroThm]], notSndQ], notSndR]];
    fstU1 = fstINatAt[U1num, U1den];                                          (* FST U1 = U1num *)
    sndU1 = sndU1e;
    equivU1 = HOL`Bool`MP[HOL`Bool`SPEC[U1, ratCanonEquivThm], notSndU1];
    fstEqA = HOL`Equal`APTERM[fstIN[], repQR];                                (* FST(REP qr) = FST(ratCanon U1) *)
    denEqA = HOL`Equal`APTERM[intOfNumC, HOL`Equal`SYM[sndU1]];               (* &ℤU1den = &ℤ(SND U1) *)
    lhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqA], denEqA];
    fstEqB = HOL`Equal`SYM[fstU1];                                           (* U1num = FST U1 *)
    sndEqB = HOL`Equal`APTERM[intOfNumC, HOL`Equal`APTERM[sndIN[], repQR]];   (* &ℤ(SND(REP qr)) = &ℤ(SND(ratCanon U1)) *)
    rhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqB], sndEqB];
    TRANS[lhsRw, TRANS[equivU1, HOL`Equal`SYM[rhsRw]]]
  ];

(* ⊢ ∀q r v. ratAdd (ratAdd q r) v = ratAdd q (ratAdd r v).
   Both sides reduce (repRatAdd) to ratCanon of a sum-pair built on a
   reduced inner sum; cong-left/right swap that inner sum for the unreduced
   one (cross-equivalent), and the two fully-unreduced pairs are literally
   equal after intAddAssoc + int-ring normalization.                       *)
ratAddAssocThm =
  Module[{qV, rV, vV, repQ, repR, repV, a, b, c, d, eN, fN, qr, rv, repQR,
          repRV, U1, U1num, U1den, U2, U2num, U2den, intMulC, intAddCl,
          intOfNumC, amA, repLHS, repRHS, equivQR, equivRV, notSndQ, notSndR,
          notSndV, notSndQR, notSndRV, notSndU1den, notSndU2den, congLeftInst,
          respL, congRightInst, respR, aT, cT, eT, rd, asc1, asc2, part1Eq,
          iom, part2Eq, lhsAddAdd, assocL, lhsMid, iomp, part1pEq, rdp, asc1p,
          commFB, cEq, asc2p, commDB, eEq, part2pEq, rhsMid, numEq, denEq,
          eqLR, canonEqLR, repEq},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy]; vV = mkVar["v", ratTy];
    intMulC = intMulCC[]; intAddCl = intAddC[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    amA[xT_, yT_, zT_] := HOL`Bool`SPEC[zT, HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT,
      HOL`Stdlib`Int`intMulAssocThm]]];   (* (x·y)·z = x·(y·z) *)
    repQ = repRat[qV]; repR = repRat[rV]; repV = repRat[vV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    c = mkComb[fstIN[], repR]; d = mkComb[sndIN[], repR];
    eN = mkComb[fstIN[], repV]; fN = mkComb[sndIN[], repV];
    qr = ratAddTm[qV, rV]; rv = ratAddTm[rV, vV];
    repQR = repRat[qr]; repRV = repRat[rv];
    U1 = ratAddPair[repQ, repR]; U1num = U1[[1, 2]]; U1den = U1[[2]];   (* b*d *)
    U2 = ratAddPair[repR, repV]; U2num = U2[[1, 2]]; U2den = U2[[2]];   (* d*fN *)
    repLHS = HOL`Bool`SPEC[vV, HOL`Bool`SPEC[qr, repRatAddThm]];   (* REP(LHS) = ratCanon(ratAddPair(repQR, repV)) *)
    repRHS = HOL`Bool`SPEC[rv, HOL`Bool`SPEC[qV, repRatAddThm]];   (* REP(RHS) = ratCanon(ratAddPair(repQ, repRV)) *)
    equivQR = repAddEquivAt[qV, rV];   (* intMul(FST repQR)(&ℤU1den) = intMul U1num (&ℤ(SND repQR)) *)
    equivRV = repAddEquivAt[rV, vV];   (* intMul(FST repRV)(&ℤU2den) = intMul U2num (&ℤ(SND repRV)) *)
    notSndQ = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepRepThm]];
    notSndR = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repR],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> rV}, ratRepRepThm]]];
    notSndV = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repV],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> vV}, ratRepRepThm]]];
    notSndQR = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQR],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> qr}, ratRepRepThm]]];
    notSndRV = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repRV],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> rv}, ratRepRepThm]]];
    notSndU1den = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, multNonzeroThm]], notSndQ], notSndR]; (* ¬(b*d=0) *)
    notSndU2den = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[fN, HOL`Bool`SPEC[d, multNonzeroThm]], notSndR], notSndV]; (* ¬(d*fN=0) *)
    (* respL: ratCanon(LeftArg) = ratCanon(sumPair U1num U1den eN fN) *)
    congLeftInst = HOL`Bool`SPEC[fN, HOL`Bool`SPEC[eN, HOL`Bool`SPEC[U1den,
      HOL`Bool`SPEC[U1num, HOL`Bool`SPEC[mkComb[sndIN[], repQR],
        HOL`Bool`SPEC[mkComb[fstIN[], repQR], ratAddCongLeftThm]]]]]];
    respL = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[congLeftInst,
      notSndQR], notSndU1den], notSndV], equivQR];
    (* respR: ratCanon(RightArg) = ratCanon(sumPair a b U2num U2den) *)
    congRightInst = HOL`Bool`SPEC[U2den, HOL`Bool`SPEC[U2num,
      HOL`Bool`SPEC[mkComb[sndIN[], repRV], HOL`Bool`SPEC[mkComb[fstIN[], repRV],
        HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, ratAddCongRightThm]]]]]];
    respR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[congRightInst,
      notSndQ], notSndRV], notSndU2den], equivRV];
    (* L1 = sumPair U1num U1den eN fN, R1 = sumPair a b U2num U2den; L1 = R1 *)
    aT = intMulTm[a, intMulTm[intOfNum[d], intOfNum[fN]]];
    cT = intMulTm[c, intMulTm[intOfNum[b], intOfNum[fN]]];
    eT = intMulTm[eN, intMulTm[intOfNum[b], intOfNum[d]]];
    (* LHS_num = intMul U1num (&ℤfN) + intMul eN (&ℤ(b*d)) → MID = aT+(cT+eT) *)
    rd = intRDistAt[intMulTm[a, intOfNum[d]], intMulTm[c, intOfNum[b]], intOfNum[fN]];
    asc1 = amA[a, intOfNum[d], intOfNum[fN]];   (* (a·&ℤd)·&ℤfN = a·(&ℤd·&ℤfN) = aT *)
    asc2 = amA[c, intOfNum[b], intOfNum[fN]];   (* (c·&ℤb)·&ℤfN = cT *)
    part1Eq = TRANS[rd, HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, asc1], asc2]];
    iom = HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, HOL`Stdlib`Int`intOfNumMulThm]];  (* &ℤ(b*d) = &ℤb·&ℤd *)
    part2Eq = HOL`Equal`APTERM[mkComb[intMulC, eN], iom];   (* eN·&ℤ(b*d) = eT *)
    lhsAddAdd = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, part1Eq], part2Eq];
                (* LHS_num = (aT+cT)+eT *)
    assocL = HOL`Bool`SPEC[eT, HOL`Bool`SPEC[cT, HOL`Bool`SPEC[aT, HOL`Stdlib`Int`intAddAssocThm]]];
    lhsMid = TRANS[lhsAddAdd, assocL];   (* LHS_num = aT+(cT+eT) = MID *)
    (* RHS_num = intMul a (&ℤ(d*fN)) + intMul U2num (&ℤb) → MID *)
    iomp = HOL`Bool`SPEC[fN, HOL`Bool`SPEC[d, HOL`Stdlib`Int`intOfNumMulThm]];  (* &ℤ(d*fN) = &ℤd·&ℤfN *)
    part1pEq = HOL`Equal`APTERM[mkComb[intMulC, a], iomp];   (* a·&ℤ(d*fN) = aT *)
    rdp = intRDistAt[intMulTm[c, intOfNum[fN]], intMulTm[eN, intOfNum[d]], intOfNum[b]];
    asc1p = amA[c, intOfNum[fN], intOfNum[b]];   (* (c·&ℤfN)·&ℤb = c·(&ℤfN·&ℤb) *)
    commFB = HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[intOfNum[fN], HOL`Stdlib`Int`intMulCommThm]];
    cEq = TRANS[asc1p, HOL`Equal`APTERM[mkComb[intMulC, c], commFB]];   (* = c·(&ℤb·&ℤfN) = cT *)
    asc2p = amA[eN, intOfNum[d], intOfNum[b]];   (* (eN·&ℤd)·&ℤb = eN·(&ℤd·&ℤb) *)
    commDB = HOL`Bool`SPEC[intOfNum[b], HOL`Bool`SPEC[intOfNum[d], HOL`Stdlib`Int`intMulCommThm]];
    eEq = TRANS[asc2p, HOL`Equal`APTERM[mkComb[intMulC, eN], commDB]];   (* = eN·(&ℤb·&ℤd) = eT *)
    part2pEq = TRANS[rdp, HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, cEq], eEq]];
    rhsMid = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, part1pEq], part2pEq];
                (* RHS_num = aT+(cT+eT) = MID *)
    numEq = TRANS[lhsMid, HOL`Equal`SYM[rhsMid]];
    denEq = HOL`Bool`SPEC[fN, HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesAssocThm]]];
                (* (b*d)*fN = b*(d*fN) *)
    eqLR = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];  (* L1 = R1 *)
    canonEqLR = HOL`Equal`APTERM[ratCanonConst[], eqLR];
    repEq = TRANS[repLHS, TRANS[respL, TRANS[canonEqLR,
      TRANS[HOL`Equal`SYM[respR], HOL`Equal`SYM[repRHS]]]]];
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, HOL`Bool`GEN[vV,
      ratEqFromRepEq[repEq, ratAddTm[qr, vV], ratAddTm[qV, rv]]]]]
  ];

(* ============================================================ *)
(* ratMul — multiplication of reduced fractions                 *)
(* (a,b)·(c,d) = ratCanon (a·c, b·d)                            *)
(* ============================================================ *)

ratMulTy = tyFun[ratTy, tyFun[ratTy, ratTy]];

(* product-pair (a·c, b·d) of two int×num reps repQ, repR *)
ratMulPair[repQ_, repR_] :=
  Module[{a, b, c, d},
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    c = mkComb[fstIN[], repR]; d = mkComb[sndIN[], repR];
    ratPairCons[intMulTm[a, c], timesTm[b, d]]
  ];

ratMulDefThm = newDefinition[mkEq[
  mkVar["ratMul", ratMulTy],
  Module[{qV, rV},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    mkAbs[qV, mkAbs[rV,
      mkComb[absRatConst[], ratCanonTm[ratMulPair[repRat[qV], repRat[rV]]]]]]]
]];

ratMulConst[] := mkConst["ratMul", ratMulTy];
ratMulTm[qT_, rT_] := mkComb[mkComb[ratMulConst[], qT], rT];

(* ⊢ ratMul q r = ABS_rat (ratCanon (product-pair)) *)
unfoldRatMul[qT_, rT_] :=
  Module[{ap1, beta1, ap2, beta2},
    ap1 = HOL`Equal`APTHM[ratMulDefThm, qT];
    beta1 = BETACONV[concl[ap1][[2]]];
    ap2 = HOL`Equal`APTHM[TRANS[ap1, beta1], rT];
    beta2 = BETACONV[concl[ap2][[2]]];
    TRANS[ap2, beta2]
  ];

(* ⊢ ∀q r. REP_rat (ratMul q r) = ratCanon (product-pair) *)
repRatMulThm =
  Module[{qV, rV, repQ, repR, bDen, dDen, pairTm, numTmrt, denTm,
          notBDen0, notDDen0, notDen0, sndPairEq, notSndPair0, lands,
          repAbsInst, repEqCanon, unfMul, apRep, body},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    repQ = repRat[qV]; repR = repRat[rV];
    bDen = mkComb[sndIN[], repQ]; dDen = mkComb[sndIN[], repR];
    pairTm = ratMulPair[repQ, repR];
    numTmrt = pairTm[[1, 2]]; denTm = pairTm[[2]];
    notBDen0 = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepRepThm]];
    notDDen0 = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repR],
      HOL`Kernel`INST[{qV -> rV}, ratRepRepThm]]];
    notDen0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[dDen, HOL`Bool`SPEC[bDen, multNonzeroThm]], notBDen0], notDDen0];
    sndPairEq = sndINatAt[numTmrt, denTm];
    notSndPair0 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndPairEq]}, notDen0];
    lands = HOL`Bool`MP[HOL`Bool`SPEC[pairTm, ratCanonLandsThm], notSndPair0];
    repAbsInst = HOL`Kernel`INST[
      {concl[repAbsRatThm][[1, 2, 2]] -> ratCanonTm[pairTm]}, repAbsRatThm];
    repEqCanon = EQMP[repAbsInst, lands];
    unfMul = unfoldRatMul[qV, rV];
    apRep = HOL`Equal`APTERM[repRatConst[], unfMul];
    body = TRANS[apRep, repEqCanon];
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, body]]
  ];

(* ⊢ ∀q r. ratMul q r = ratMul r q *)
ratMulCommThm =
  Module[{qV, rV, repQ, repR, a, b, c, d, repQR, repRQ,
          numComm, denComm, pairEq, canonEq, repEq},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    repQ = repRat[qV]; repR = repRat[rV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    c = mkComb[fstIN[], repR]; d = mkComb[sndIN[], repR];
    repQR = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[qV, repRatMulThm]];  (* REP(ratMul q r) = ratCanon(a·c, b·d) *)
    repRQ = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[rV, repRatMulThm]];  (* REP(ratMul r q) = ratCanon(c·a, d·b) *)
    numComm = HOL`Bool`SPEC[c, HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulCommThm]];  (* a·c = c·a *)
    denComm = HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesCommThm]];   (* b·d = d·b *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numComm], denComm];
    canonEq = HOL`Equal`APTERM[ratCanonConst[], pairEq];
    repEq = TRANS[repQR, TRANS[canonEq, HOL`Equal`SYM[repRQ]]];
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV,
      ratEqFromRepEq[repEq, ratMulTm[qV, rV], ratMulTm[rV, qV]]]]
  ];

(* ⊢ ∀q. ratMul q (&ℚ (&ℤ (SUC 0))) = q *)
ratMulOneThm =
  Module[{qV, oneInt, oneRat, repMul, repOneEq, fstOne, sndOne, numEq, denEq,
          pairEq, canonPairEq, surjQ, canonSurjEq, canonRepQ, repEq, a, b},
    qV = mkVar["q", ratTy];
    oneInt = intOfNum[oneN[]];                              (* &ℤ (SUC 0) *)
    oneRat = ratOfIntTm[oneInt];                            (* &ℚ (&ℤ (SUC 0)) *)
    a = mkComb[fstIN[], repRat[qV]]; b = mkComb[sndIN[], repRat[qV]];
    repMul = HOL`Bool`SPEC[oneRat, HOL`Bool`SPEC[qV, repRatMulThm]];
    repOneEq = HOL`Kernel`INST[{mkVar["q", intTy] -> oneInt}, repRatOfIntThm];  (* REP(&ℚ&ℤ1) = (&ℤ1, SUC0) *)
    fstOne = TRANS[HOL`Equal`APTERM[fstIN[], repOneEq], fstINatAt[oneInt, oneN[]]];  (* FST(REP oneRat) = &ℤ1 *)
    sndOne = TRANS[HOL`Equal`APTERM[sndIN[], repOneEq], sndINatAt[oneInt, oneN[]]];  (* SND(REP oneRat) = SUC0 *)
    numEq = TRANS[
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Int`intMulConst[], a], fstOne],
      HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulOneThm]];       (* intMul a (FST..) = a *)
    denEq = TRANS[
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], b], sndOne],
      TRANS[HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesCommThm]],
        HOL`Bool`SPEC[b, HOL`Stdlib`Num`oneTimesEqThm]]];    (* b * SUC0 = b *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];
    canonPairEq = HOL`Equal`APTERM[ratCanonConst[], pairEq];
    surjQ = HOL`Bool`SPEC[repRat[qV],
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];
    canonSurjEq = HOL`Equal`APTERM[ratCanonConst[], surjQ];
    canonRepQ = HOL`Bool`MP[HOL`Bool`SPEC[repRat[qV], ratCanonIdThm], ratRepRepThm];
    repEq = TRANS[repMul, TRANS[canonPairEq, TRANS[canonSurjEq, canonRepQ]]];
    HOL`Bool`GEN[qV, ratEqFromRepEq[repEq, ratMulTm[qV, oneRat], qV]]
  ];

(* ⊢ ∀q. ratMul q (&ℚ (&ℤ 0)) = &ℚ (&ℤ 0) *)
ratMulZeroThm =
  Module[{qV, z0, zRat, repMul, repZeroEq, fstZero, sndZero, numEq, denEq,
          pairEq, canonPairEq, bNeq0, canonZero, repMulEq, repZero, repEq, a, b},
    qV = mkVar["q", ratTy];
    z0 = intOfNum[zeroN[]];
    zRat = ratOfIntTm[z0];
    a = mkComb[fstIN[], repRat[qV]]; b = mkComb[sndIN[], repRat[qV]];
    repMul = HOL`Bool`SPEC[zRat, HOL`Bool`SPEC[qV, repRatMulThm]];
    repZeroEq = HOL`Kernel`INST[{mkVar["q", intTy] -> z0}, repRatOfIntThm];
    fstZero = TRANS[HOL`Equal`APTERM[fstIN[], repZeroEq], fstINatAt[z0, oneN[]]];  (* FST(REP zRat) = &ℤ0 *)
    sndZero = TRANS[HOL`Equal`APTERM[sndIN[], repZeroEq], sndINatAt[z0, oneN[]]];  (* SND(REP zRat) = SUC0 *)
    numEq = TRANS[
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Int`intMulConst[], a], fstZero],
      HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulZeroThm]];      (* intMul a (FST..) = &ℤ0 *)
    denEq = TRANS[
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], b], sndZero],
      TRANS[HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesCommThm]],
        HOL`Bool`SPEC[b, HOL`Stdlib`Num`oneTimesEqThm]]];    (* b * SUC0 = b *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];
                                                            (* product-pair = (&ℤ0, b) *)
    canonPairEq = HOL`Equal`APTERM[ratCanonConst[], pairEq];
    bNeq0 = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repRat[qV]], ratRepRepThm]];  (* ¬(b=0) *)
    canonZero = HOL`Bool`MP[HOL`Bool`SPEC[b, ratCanonZeroNumThm], bNeq0];  (* ratCanon(&ℤ0, b) = (&ℤ0, SUC0) *)
    repMulEq = TRANS[repMul, TRANS[canonPairEq, canonZero]];
    repZero = HOL`Kernel`INST[{mkVar["q", intTy] -> z0}, repRatOfIntThm];  (* REP(&ℚ&ℤ0) = (&ℤ0, SUC0) *)
    repEq = TRANS[repMulEq, HOL`Equal`SYM[repZero]];
    HOL`Bool`GEN[qV, ratEqFromRepEq[repEq, ratMulTm[qV, zRat], zRat]]
  ];

(* ============================================================ *)
(* ratMul associativity. The unreduced product-pairs:            *)
(*   mulPairTm n1 m1 n2 m2 = (intMul n1 n2, m1·m2)               *)
(* matches ratMulPair on int×num reps. cong-left/right show       *)
(* ratCanon is unchanged when an operand is swapped for a cross-  *)
(* equivalent one; assoc then aligns the fully-unreduced pairs    *)
(* (num via intMulAssoc, denom via timesAssoc — literally equal). *)
(* ============================================================ *)

mulPairTm[n1_, m1_, n2_, m2_] :=
  ratPairCons[intMulTm[n1, n2], timesTm[m1, m2]];

(* ⊢ (w·x)·(y·z) = (w·y)·(x·z)  (commutative-monoid middle swap) *)
mul4SwapAt[w_, x_, y_, z_] :=
  Module[{im = intMulCC[], yz = intMulTm[y, z], xz = intMulTm[x, z]},
    TRANS[
      HOL`Bool`SPEC[yz, HOL`Bool`SPEC[x, HOL`Bool`SPEC[w, HOL`Stdlib`Int`intMulAssocThm]]],
                          (* (w·x)·(y·z) = w·(x·(y·z)) *)
      TRANS[
        HOL`Equal`APTERM[mkComb[im, w], HOL`Equal`SYM[
          HOL`Bool`SPEC[z, HOL`Bool`SPEC[y, HOL`Bool`SPEC[x, HOL`Stdlib`Int`intMulAssocThm]]]]],
                          (* w·(x·(y·z)) = w·((x·y)·z) *)
        TRANS[
          HOL`Equal`APTERM[mkComb[im, w],
            HOL`Equal`APTHM[HOL`Equal`APTERM[im,
              HOL`Bool`SPEC[y, HOL`Bool`SPEC[x, HOL`Stdlib`Int`intMulCommThm]]], z]],
                          (* w·((x·y)·z) = w·((y·x)·z) *)
          TRANS[
            HOL`Equal`APTERM[mkComb[im, w],
              HOL`Bool`SPEC[z, HOL`Bool`SPEC[x, HOL`Bool`SPEC[y, HOL`Stdlib`Int`intMulAssocThm]]]],
                          (* w·((y·x)·z) = w·(y·(x·z)) *)
            HOL`Equal`SYM[
              HOL`Bool`SPEC[xz, HOL`Bool`SPEC[y, HOL`Bool`SPEC[w, HOL`Stdlib`Int`intMulAssocThm]]]]]]]]
                          (* w·(y·(x·z)) = (w·y)·(x·z) *)
  ];

(* ⊢ &ℤ (m * n) = intMul (&ℤ m) (&ℤ n) *)
intOfNumMulAt[mN_, nN_] :=
  HOL`Bool`SPEC[nN, HOL`Bool`SPEC[mN, HOL`Stdlib`Int`intOfNumMulThm]];

(* ⊢ ∀n1 m1 n1' m1' n2 m2. ¬(m1=0) ⇒ ¬(m1'=0) ⇒ ¬(m2=0) ⇒
        intMul n1 (&ℤ m1') = intMul n1' (&ℤ m1) ⇒
        ratCanon (mulPair n1 m1 n2 m2) = ratCanon (mulPair n1' m1' n2 m2).   *)
ratMulCongLeftThm =
  Module[{n1, m1, n1p, m1p, n2, m2, hyp, notM10, notM10p, notM20, intMulC,
          P1, P2, n2m2, e0, e1, e2, e3, e4, crossPoly, mulP1, mulP2,
          fstEqL, sndEqL, fstEqLp, sndEqLp, notProd0, notProd0p, notSndL,
          notSndLp, crossUnred, respInst, congEq, intOfNumC},
    n1 = mkVar["n1", intTy]; n1p = mkVar["e", intTy]; n2 = mkVar["c", intTy];
    m1 = mkVar["m1", numTy]; m1p = mkVar["f", numTy]; m2 = mkVar["g", numTy];
    intMulC = intMulCC[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    hyp = ASSUME[mkEq[intMulTm[n1, intOfNum[m1p]], intMulTm[n1p, intOfNum[m1]]]];
    notM10 = ASSUME[notTm[mkEq[m1, zeroN[]]]];
    notM10p = ASSUME[notTm[mkEq[m1p, zeroN[]]]];
    notM20 = ASSUME[notTm[mkEq[m2, zeroN[]]]];
    P1 = intMulTm[n1, n2]; P2 = intMulTm[n1p, n2];
    n2m2 = intMulTm[n2, intOfNum[m2]];
    e0 = HOL`Equal`APTERM[mkComb[intMulC, P1], intOfNumMulAt[m1p, m2]];
            (* P1·&ℤ(m1'·m2) = P1·(&ℤm1'·&ℤm2) *)
    e1 = mul4SwapAt[n1, n2, intOfNum[m1p], intOfNum[m2]];
            (* (n1·n2)·(&ℤm1'·&ℤm2) = (n1·&ℤm1')·(n2·&ℤm2) *)
    e2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, hyp], REFL[n2m2]];
            (* (n1·&ℤm1')·(n2·&ℤm2) = (n1'·&ℤm1)·(n2·&ℤm2) *)
    e3 = HOL`Equal`SYM[mul4SwapAt[n1p, n2, intOfNum[m1], intOfNum[m2]]];
            (* (n1'·&ℤm1)·(n2·&ℤm2) = (n1'·n2)·(&ℤm1·&ℤm2) *)
    e4 = HOL`Equal`APTERM[mkComb[intMulC, P2], HOL`Equal`SYM[intOfNumMulAt[m1, m2]]];
            (* P2·(&ℤm1·&ℤm2) = P2·&ℤ(m1·m2) *)
    crossPoly = TRANS[e0, TRANS[e1, TRANS[e2, TRANS[e3, e4]]]];
            (* P1·&ℤ(m1'·m2) = P2·&ℤ(m1·m2) *)
    mulP1 = mulPairTm[n1, m1, n2, m2]; mulP2 = mulPairTm[n1p, m1p, n2, m2];
    fstEqL = fstINatAt[P1, timesTm[m1, m2]]; sndEqL = sndINatAt[P1, timesTm[m1, m2]];
    fstEqLp = fstINatAt[P2, timesTm[m1p, m2]]; sndEqLp = sndINatAt[P2, timesTm[m1p, m2]];
    notProd0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1, multNonzeroThm]], notM10], notM20];
    notProd0p = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1p, multNonzeroThm]], notM10p], notM20];
    notSndL = HOL`Drule`SUBS[{HOL`Equal`SYM[sndEqL]}, notProd0];
    notSndLp = HOL`Drule`SUBS[{HOL`Equal`SYM[sndEqLp]}, notProd0p];
    crossUnred = Module[{lhsRw, rhsRw},
      lhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqL],
        HOL`Equal`APTERM[intOfNumC, sndEqLp]];
            (* intMul(FST mulP1)(&ℤ(SND mulP2)) = P1·&ℤ(m1'·m2) *)
      rhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqLp],
        HOL`Equal`APTERM[intOfNumC, sndEqL]];
            (* intMul(FST mulP2)(&ℤ(SND mulP1)) = P2·&ℤ(m1·m2) *)
      TRANS[lhsRw, TRANS[crossPoly, HOL`Equal`SYM[rhsRw]]]];
    respInst = HOL`Bool`SPEC[mulP2, HOL`Bool`SPEC[mulP1, ratCanonRespectsThm]];
    congEq = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[respInst, notSndL], notSndLp], crossUnred];
    HOL`Bool`GEN[n1, HOL`Bool`GEN[m1, HOL`Bool`GEN[n1p, HOL`Bool`GEN[m1p,
      HOL`Bool`GEN[n2, HOL`Bool`GEN[m2,
        HOL`Bool`DISCH[notTm[mkEq[m1, zeroN[]]],
          HOL`Bool`DISCH[notTm[mkEq[m1p, zeroN[]]],
            HOL`Bool`DISCH[notTm[mkEq[m2, zeroN[]]],
              HOL`Bool`DISCH[concl[hyp], congEq]]]]]]]]]]
  ];

(* ⊢ mulPair n1 m1 n2 m2 = mulPair n2 m2 n1 m1 *)
mulFlipAt[n1_, m1_, n2_, m2_] :=
  HOL`Kernel`MKCOMB[
    HOL`Equal`APTERM[ratPairConsC[],
      HOL`Bool`SPEC[n2, HOL`Bool`SPEC[n1, HOL`Stdlib`Int`intMulCommThm]]],
    HOL`Bool`SPEC[m2, HOL`Bool`SPEC[m1, HOL`Stdlib`Num`timesCommThm]]];

(* ⊢ ∀a b n2 m2 n2' m2'. ¬(b=0) ⇒ ¬(m2=0) ⇒ ¬(m2'=0) ⇒
        intMul n2 (&ℤ m2') = intMul n2' (&ℤ m2) ⇒
        ratCanon (mulPair a b n2 m2) = ratCanon (mulPair a b n2' m2').  *)
ratMulCongRightThm =
  Module[{a1, b1, n2, m2, n2p, m2p, hyp, congMid, result},
    a1 = mkVar["a", intTy]; b1 = mkVar["b", numTy];
    n2 = mkVar["c", intTy]; m2 = mkVar["d", numTy];
    n2p = mkVar["e", intTy]; m2p = mkVar["f", numTy];
    hyp = ASSUME[mkEq[intMulTm[n2, intOfNum[m2p]], intMulTm[n2p, intOfNum[m2]]]];
    congMid = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[b1, HOL`Bool`SPEC[a1, HOL`Bool`SPEC[m2p, HOL`Bool`SPEC[n2p,
        HOL`Bool`SPEC[m2, HOL`Bool`SPEC[n2, ratMulCongLeftThm]]]]]],
      ASSUME[notTm[mkEq[m2, zeroN[]]]]], ASSUME[notTm[mkEq[m2p, zeroN[]]]]],
      ASSUME[notTm[mkEq[b1, zeroN[]]]]], hyp];
            (* ratCanon(mulPair c d a b) = ratCanon(mulPair e f a b) *)
    result = TRANS[HOL`Equal`APTERM[ratCanonConst[], mulFlipAt[a1, b1, n2, m2]],
      TRANS[congMid,
        HOL`Equal`APTERM[ratCanonConst[], HOL`Equal`SYM[mulFlipAt[a1, b1, n2p, m2p]]]]];
    HOL`Bool`GEN[a1, HOL`Bool`GEN[b1, HOL`Bool`GEN[n2, HOL`Bool`GEN[m2,
      HOL`Bool`GEN[n2p, HOL`Bool`GEN[m2p,
        HOL`Bool`DISCH[notTm[mkEq[b1, zeroN[]]],
          HOL`Bool`DISCH[notTm[mkEq[m2, zeroN[]]],
            HOL`Bool`DISCH[notTm[mkEq[m2p, zeroN[]]],
              HOL`Bool`DISCH[concl[hyp], result]]]]]]]]]]
  ];

(* ⊢ intMul (FST (REP (ratMul q r))) (&ℤ Uden) = intMul Unum (&ℤ (SND (REP (ratMul q r))))
   where (Unum, Uden) = ratMulPair (REP q) (REP r): REP (ratMul q r) is
   cross-equivalent to its unreduced product-pair (repRatMul + ratCanonEquiv).  *)
repMulEquivAt[qT_, rT_] :=
  Module[{repQ, repR, U1, U1num, U1den, repQR, notSndQ, notSndR, sndU1e,
          notSndU1, fstU1, sndU1, equivU1, fstEqA, denEqA, lhsRw, fstEqB,
          sndEqB, rhsRw, intMulC, intOfNumC, ratRepQ},
    intMulC = intMulCC[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    repQ = repRat[qT]; repR = repRat[rT];
    U1 = ratMulPair[repQ, repR]; U1num = U1[[1, 2]]; U1den = U1[[2]];
    repQR = HOL`Bool`SPEC[rT, HOL`Bool`SPEC[qT, repRatMulThm]];
    ratRepQ = HOL`Kernel`INST[{mkVar["q", ratTy] -> qT}, ratRepRepThm];
    notSndQ = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepQ]];
    notSndR = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repR],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> rT}, ratRepRepThm]]];
    sndU1e = sndINatAt[U1num, U1den];
    notSndU1 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndU1e]},
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[mkComb[sndIN[], repR],
        HOL`Bool`SPEC[mkComb[sndIN[], repQ], multNonzeroThm]], notSndQ], notSndR]];
    fstU1 = fstINatAt[U1num, U1den];
    sndU1 = sndU1e;
    equivU1 = HOL`Bool`MP[HOL`Bool`SPEC[U1, ratCanonEquivThm], notSndU1];
    fstEqA = HOL`Equal`APTERM[fstIN[], repQR];
    denEqA = HOL`Equal`APTERM[intOfNumC, HOL`Equal`SYM[sndU1]];
    lhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqA], denEqA];
    fstEqB = HOL`Equal`SYM[fstU1];
    sndEqB = HOL`Equal`APTERM[intOfNumC, HOL`Equal`APTERM[sndIN[], repQR]];
    rhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqB], sndEqB];
    TRANS[lhsRw, TRANS[equivU1, HOL`Equal`SYM[rhsRw]]]
  ];

(* ⊢ ∀q r v. ratMul (ratMul q r) v = ratMul q (ratMul r v).
   Both sides → ratCanon of a product-pair on a reduced inner product;
   cong-left/right swap that for the unreduced cross-equivalent one, and
   the two fully-unreduced pairs are literally equal (num intMulAssoc,
   denom timesAssoc).                                                      *)
ratMulAssocThm =
  Module[{qV, rV, vV, repQ, repR, repV, a, b, c, d, eN, fN, qr, rv, repQR,
          repRV, U1, U1num, U1den, U2, U2num, U2den, repLHS, repRHS,
          equivQR, equivRV, notSndQ, notSndR, notSndV, notSndQR, notSndRV,
          notSndU1den, notSndU2den, congLeftInst, respL, congRightInst, respR,
          numEq, denEq, eqLR, canonEqLR, repEq},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy]; vV = mkVar["v", ratTy];
    repQ = repRat[qV]; repR = repRat[rV]; repV = repRat[vV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    c = mkComb[fstIN[], repR]; d = mkComb[sndIN[], repR];
    eN = mkComb[fstIN[], repV]; fN = mkComb[sndIN[], repV];
    qr = ratMulTm[qV, rV]; rv = ratMulTm[rV, vV];
    repQR = repRat[qr]; repRV = repRat[rv];
    U1 = ratMulPair[repQ, repR]; U1num = U1[[1, 2]]; U1den = U1[[2]];   (* (a·c, b·d) *)
    U2 = ratMulPair[repR, repV]; U2num = U2[[1, 2]]; U2den = U2[[2]];   (* (c·e, d·f) *)
    repLHS = HOL`Bool`SPEC[vV, HOL`Bool`SPEC[qr, repRatMulThm]];
    repRHS = HOL`Bool`SPEC[rv, HOL`Bool`SPEC[qV, repRatMulThm]];
    equivQR = repMulEquivAt[qV, rV];
    equivRV = repMulEquivAt[rV, vV];
    notSndQ = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepRepThm]];
    notSndR = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repR],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> rV}, ratRepRepThm]]];
    notSndV = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repV],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> vV}, ratRepRepThm]]];
    notSndQR = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQR],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> qr}, ratRepRepThm]]];
    notSndRV = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repRV],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> rv}, ratRepRepThm]]];
    notSndU1den = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, multNonzeroThm]], notSndQ], notSndR];
    notSndU2den = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[fN, HOL`Bool`SPEC[d, multNonzeroThm]], notSndR], notSndV];
    congLeftInst = HOL`Bool`SPEC[fN, HOL`Bool`SPEC[eN, HOL`Bool`SPEC[U1den,
      HOL`Bool`SPEC[U1num, HOL`Bool`SPEC[mkComb[sndIN[], repQR],
        HOL`Bool`SPEC[mkComb[fstIN[], repQR], ratMulCongLeftThm]]]]]];
    respL = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[congLeftInst,
      notSndQR], notSndU1den], notSndV], equivQR];
    congRightInst = HOL`Bool`SPEC[U2den, HOL`Bool`SPEC[U2num,
      HOL`Bool`SPEC[mkComb[sndIN[], repRV], HOL`Bool`SPEC[mkComb[fstIN[], repRV],
        HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, ratMulCongRightThm]]]]]];
    respR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[congRightInst,
      notSndQ], notSndRV], notSndU2den], equivRV];
    (* L1 = (intMul (a·c) eN, (b·d)·fN), R1 = (intMul a (c·e), b·(d·f)) *)
    numEq = HOL`Bool`SPEC[eN, HOL`Bool`SPEC[c, HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulAssocThm]]];
            (* (a·c)·e = a·(c·e) *)
    denEq = HOL`Bool`SPEC[fN, HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesAssocThm]]];
            (* (b·d)·f = b·(d·f) *)
    eqLR = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];
    canonEqLR = HOL`Equal`APTERM[ratCanonConst[], eqLR];
    repEq = TRANS[repLHS, TRANS[respL, TRANS[canonEqLR,
      TRANS[HOL`Equal`SYM[respR], HOL`Equal`SYM[repRHS]]]]];
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, HOL`Bool`GEN[vV,
      ratEqFromRepEq[repEq, ratMulTm[qr, vV], ratMulTm[qV, rv]]]]]
  ];

(* ============================================================ *)
(* ratMul distributivity over ratAdd.                            *)
(*   ratMul z (ratAdd w v) = ratAdd (ratMul z w) (ratMul z v).   *)
(* LHS reduces (cong-right) to ratCanon(a·(c·F+e·D), b·(d·f));    *)
(* RHS reduces (cong-left+right) to ratCanon((a·c)·&ℤ(b·f) +      *)
(* (a·e)·&ℤ(b·d), (b·d)·(b·f)). The two pairs are NOT literal —    *)
(* RHS carries a redundant factor b in num and denom — so close   *)
(* via ratCanonRespects with an explicit int-ring cross-equation. *)
(* ============================================================ *)

(* ⊢ ∀z w v. ratMul z (ratAdd w v) = ratAdd (ratMul z w) (ratMul z v) *)
ratMulDistribThm =
  Module[{zV, wV, vV, repZ, repW, repV, a, b, c, d, eN, fN, B, D, F, BF, BD,
          cF, eD, NSUM, ac, ae, Lnum, Lden, Rnum, Rden, G, L1, R1, wvT, zwT,
          zvT, repWV, repZW, repZV, intMulC, intAddCl, intOfNumC, timesC,
          imA, imC2, notSndZ, notSndW, notSndV, notSndWV, notSndZW, notSndZV,
          notDF, notBD, notBF, notLden0, notRden0, fstL1, sndL1, fstR1, sndR1,
          notSndL1, notSndR1, repLHS, respLHS, acBF, aeBD, cBFeq, eBDeq,
          rstep1, rstep2, rstep3, RnumEq, RHScrossEq, natEq, nn1, nn2, nn3,
          nn4, zRdenEq, lhsCross1, lhsCross2, lhsCross3, LHScrossEq, crossEq,
          lhsRwR, rhsRwR, crossResp, respInst, respEq, repRHS, congLeftRHS,
          congRightRHS, repEq, lhsT, rhsT},
    zV = mkVar["z", ratTy]; wV = mkVar["w", ratTy]; vV = mkVar["v", ratTy];
    intMulC = intMulCC[]; intAddCl = intAddC[];
    intOfNumC = HOL`Stdlib`Int`intOfNumConst[]; timesC = HOL`Stdlib`Num`timesConst[];
    imA[xT_, yT_, zT_] := HOL`Bool`SPEC[zT, HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT,
      HOL`Stdlib`Int`intMulAssocThm]]];                 (* (x·y)·z = x·(y·z) *)
    imC2[xT_, yT_] := HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, HOL`Stdlib`Int`intMulCommThm]];
    repZ = repRat[zV]; repW = repRat[wV]; repV = repRat[vV];
    a = mkComb[fstIN[], repZ]; b = mkComb[sndIN[], repZ];
    c = mkComb[fstIN[], repW]; d = mkComb[sndIN[], repW];
    eN = mkComb[fstIN[], repV]; fN = mkComb[sndIN[], repV];
    B = intOfNum[b]; D = intOfNum[d]; F = intOfNum[fN];
    BF = intOfNum[timesTm[b, fN]]; BD = intOfNum[timesTm[b, d]];
    cF = intMulTm[c, F]; eD = intMulTm[eN, D];
    NSUM = intAddTm[cF, eD];                            (* numerator of ratAddPair (w,v) *)
    ac = intMulTm[a, c]; ae = intMulTm[a, eN];
    Lnum = intMulTm[a, NSUM]; Lden = timesTm[b, timesTm[d, fN]];   (* b·(d·f) *)
    Rnum = intAddTm[intMulTm[ac, BF], intMulTm[ae, BD]];
    Rden = timesTm[timesTm[b, d], timesTm[b, fN]];      (* (b·d)·(b·f) *)
    G = intOfNum[Lden];                                 (* &ℤ Lden *)
    L1 = ratPairCons[Lnum, Lden]; R1 = ratPairCons[Rnum, Rden];
    wvT = ratAddTm[wV, vV]; zwT = ratMulTm[zV, wV]; zvT = ratMulTm[zV, vV];
    repWV = repRat[wvT]; repZW = repRat[zwT]; repZV = repRat[zvT];
    (* ----- nonzero facts ----- *)
    notSndZ = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repZ],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> zV}, ratRepRepThm]]];
    notSndW = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repW],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> wV}, ratRepRepThm]]];
    notSndV = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repV],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> vV}, ratRepRepThm]]];
    notSndWV = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repWV],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> wvT}, ratRepRepThm]]];
    notSndZW = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repZW],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> zwT}, ratRepRepThm]]];
    notSndZV = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repZV],
      HOL`Kernel`INST[{mkVar["q", ratTy] -> zvT}, ratRepRepThm]]];
    notDF = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[fN, HOL`Bool`SPEC[d, multNonzeroThm]], notSndW], notSndV];
    notBD = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, multNonzeroThm]], notSndZ], notSndW];
    notBF = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[fN, HOL`Bool`SPEC[b, multNonzeroThm]], notSndZ], notSndV];
    notLden0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[timesTm[d, fN], HOL`Bool`SPEC[b, multNonzeroThm]], notSndZ], notDF];
    notRden0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[timesTm[b, fN], HOL`Bool`SPEC[timesTm[b, d], multNonzeroThm]], notBD], notBF];
    fstL1 = fstINatAt[Lnum, Lden]; sndL1 = sndINatAt[Lnum, Lden];
    fstR1 = fstINatAt[Rnum, Rden]; sndR1 = sndINatAt[Rnum, Rden];
    notSndL1 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndL1]}, notLden0];
    notSndR1 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndR1]}, notRden0];
    (* ----- LHS: REP(ratMul z (ratAdd w v)) = ratCanon(L1) ----- *)
    repLHS = HOL`Bool`SPEC[wvT, HOL`Bool`SPEC[zV, repRatMulThm]];
                                          (* = ratCanon(ratMulPair(repZ, repWV)) *)
    respLHS = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[timesTm[d, fN], HOL`Bool`SPEC[NSUM,
        HOL`Bool`SPEC[mkComb[sndIN[], repWV], HOL`Bool`SPEC[mkComb[fstIN[], repWV],
          HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, ratMulCongRightThm]]]]]],
      notSndZ], notSndWV], notDF], repAddEquivAt[wV, vV]];
                                          (* ratCanon(ratMulPair(repZ,repWV)) = ratCanon(L1) *)
    (* ----- RHS_cross = intMul Rnum G → COMMON = (a·(NSUM·B))·G ----- *)
    cBFeq = TRANS[HOL`Equal`APTERM[mkComb[intMulC, c], intOfNumMulAt[b, fN]],
      TRANS[HOL`Equal`APTERM[mkComb[intMulC, c], imC2[B, F]],
        HOL`Equal`SYM[imA[c, F, B]]]];     (* c·BF = (c·F)·B *)
    acBF = TRANS[imA[a, c, BF], HOL`Equal`APTERM[mkComb[intMulC, a], cBFeq]];
                                          (* (a·c)·BF = a·((c·F)·B) *)
    eBDeq = TRANS[HOL`Equal`APTERM[mkComb[intMulC, eN], intOfNumMulAt[b, d]],
      TRANS[HOL`Equal`APTERM[mkComb[intMulC, eN], imC2[B, D]],
        HOL`Equal`SYM[imA[eN, D, B]]]];    (* e·BD = (e·D)·B *)
    aeBD = TRANS[imA[a, eN, BD], HOL`Equal`APTERM[mkComb[intMulC, a], eBDeq]];
                                          (* (a·e)·BD = a·((e·D)·B) *)
    rstep1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, acBF], aeBD];
                                          (* Rnum = a·((c·F)·B) + a·((e·D)·B) *)
    rstep2 = HOL`Equal`SYM[HOL`Bool`SPEC[intMulTm[eD, B], HOL`Bool`SPEC[intMulTm[cF, B],
      HOL`Bool`SPEC[a, HOL`Stdlib`Int`intMulDistribThm]]]];
                                          (* a·X + a·Y = a·(X+Y) *)
    rstep3 = HOL`Equal`APTERM[mkComb[intMulC, a], HOL`Equal`SYM[intRDistAt[cF, eD, B]]];
                                          (* a·((c·F)·B+(e·D)·B) = a·(NSUM·B) *)
    RnumEq = TRANS[rstep1, TRANS[rstep2, rstep3]];   (* Rnum = a·(NSUM·B) *)
    RHScrossEq = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, RnumEq], G];
                                          (* intMul Rnum G = (a·(NSUM·B))·G *)
    (* ----- LHS_cross = intMul Lnum (&ℤ Rden) → COMMON ----- *)
    nn1 = HOL`Bool`SPEC[timesTm[b, fN], HOL`Bool`SPEC[d, HOL`Bool`SPEC[b,
      HOL`Stdlib`Num`timesAssocThm]]];     (* (b·d)·(b·f) = b·(d·(b·f)) *)
    nn2 = HOL`Equal`APTERM[mkComb[timesC, b], HOL`Equal`SYM[
      HOL`Bool`SPEC[fN, HOL`Bool`SPEC[b, HOL`Bool`SPEC[d, HOL`Stdlib`Num`timesAssocThm]]]]];
                                          (* b·(d·(b·f)) = b·((d·b)·f) *)
    nn3 = HOL`Equal`APTERM[mkComb[timesC, b],
      HOL`Equal`APTHM[HOL`Equal`APTERM[timesC,
        HOL`Bool`SPEC[b, HOL`Bool`SPEC[d, HOL`Stdlib`Num`timesCommThm]]], fN]];
                                          (* b·((d·b)·f) = b·((b·d)·f) *)
    nn4 = HOL`Equal`APTERM[mkComb[timesC, b],
      HOL`Bool`SPEC[fN, HOL`Bool`SPEC[d, HOL`Bool`SPEC[b, HOL`Stdlib`Num`timesAssocThm]]]];
                                          (* b·((b·d)·f) = b·(b·(d·f)) *)
    natEq = TRANS[nn1, TRANS[nn2, TRANS[nn3, nn4]]];   (* (b·d)·(b·f) = b·(b·(d·f)) *)
    zRdenEq = TRANS[HOL`Equal`APTERM[intOfNumC, natEq], intOfNumMulAt[b, Lden]];
                                          (* &ℤ Rden = intMul B G *)
    lhsCross1 = HOL`Equal`APTERM[mkComb[intMulC, Lnum], zRdenEq];
                                          (* intMul Lnum (&ℤ Rden) = (a·NSUM)·(B·G) *)
    lhsCross2 = HOL`Equal`SYM[imA[Lnum, B, G]];   (* (a·NSUM)·(B·G) = ((a·NSUM)·B)·G *)
    lhsCross3 = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, imA[a, NSUM, B]], G];
                                          (* ((a·NSUM)·B)·G = (a·(NSUM·B))·G *)
    LHScrossEq = TRANS[lhsCross1, TRANS[lhsCross2, lhsCross3]];
    crossEq = TRANS[LHScrossEq, HOL`Equal`SYM[RHScrossEq]];
                                          (* intMul Lnum (&ℤ Rden) = intMul Rnum (&ℤ Lden) *)
    (* ----- recast cross to FST/SND form, feed ratCanonRespects ----- *)
    lhsRwR = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstL1],
      HOL`Equal`APTERM[intOfNumC, sndR1]];   (* intMul(FST L1)(&ℤ(SND R1)) = intMul Lnum (&ℤ Rden) *)
    rhsRwR = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstR1],
      HOL`Equal`APTERM[intOfNumC, sndL1]];   (* intMul(FST R1)(&ℤ(SND L1)) = intMul Rnum (&ℤ Lden) *)
    crossResp = TRANS[lhsRwR, TRANS[crossEq, HOL`Equal`SYM[rhsRwR]]];
    respInst = HOL`Bool`SPEC[R1, HOL`Bool`SPEC[L1, ratCanonRespectsThm]];
    respEq = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[respInst, notSndL1], notSndR1], crossResp];
                                          (* ratCanon L1 = ratCanon R1 *)
    (* ----- RHS: REP(ratAdd (ratMul z w) (ratMul z v)) = ratCanon(R1) ----- *)
    repRHS = HOL`Bool`SPEC[zvT, HOL`Bool`SPEC[zwT, repRatAddThm]];
                                          (* = ratCanon(ratAddPair(repZW, repZV)) *)
    congLeftRHS = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[mkComb[sndIN[], repZV], HOL`Bool`SPEC[mkComb[fstIN[], repZV],
        HOL`Bool`SPEC[timesTm[b, d], HOL`Bool`SPEC[ac,
          HOL`Bool`SPEC[mkComb[sndIN[], repZW], HOL`Bool`SPEC[mkComb[fstIN[], repZW],
            ratAddCongLeftThm]]]]]],
      notSndZW], notBD], notSndZV], repMulEquivAt[zV, wV]];
                                          (* ratCanon(addPair repZW repZV) = ratCanon(sumPair (a·c)(b·d) repZV-comps) *)
    congRightRHS = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[timesTm[b, fN], HOL`Bool`SPEC[ae,
        HOL`Bool`SPEC[mkComb[sndIN[], repZV], HOL`Bool`SPEC[mkComb[fstIN[], repZV],
          HOL`Bool`SPEC[timesTm[b, d], HOL`Bool`SPEC[ac, ratAddCongRightThm]]]]]],
      notBD], notSndZV], notBF], repMulEquivAt[zV, vV]];
                                          (* ratCanon(sumPair (a·c)(b·d) repZV-comps) = ratCanon(R1) *)
    repEq = TRANS[repLHS, TRANS[respLHS, TRANS[respEq,
      TRANS[HOL`Equal`SYM[congRightRHS], TRANS[HOL`Equal`SYM[congLeftRHS],
        HOL`Equal`SYM[repRHS]]]]]];
    lhsT = ratMulTm[zV, wvT]; rhsT = ratAddTm[zwT, zvT];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV, HOL`Bool`GEN[vV,
      ratEqFromRepEq[repEq, lhsT, rhsT]]]]
  ];

(* ============================================================ *)
(* ratInv — multiplicative inverse → ℚ is a FIELD.               *)
(* ratInv (a/b) = (a·&ℤb)/|a|²: numerator a·&ℤb carries sign(a)   *)
(* and magnitude |a|·b, denominator |a|²; value sign(a)·b/|a| =    *)
(* 1/q. q·(1/q): pair (a·(a·&ℤb), b·|a|²); a·(a·&ℤb) = (a·a)·&ℤb = *)
(* &ℤ|a|²·&ℤb = &ℤ(b·|a|²) (intSqNatAbs), so pair = (&ℤm, m),      *)
(* m=b·|a|², which ratCanon reduces to (&ℤ1, 1).                  *)
(* ============================================================ *)

(* ⊢ ∀n. intNatAbs (&ℤ n) = n  (proper home Int.wl) *)
intNatAbsOfNumThm =
  Module[{nV, zn, repZ, fstZ, sndZ, sumEq},
    nV = mkVar["n", numTy]; zn = intOfNum[nV];
    repZ = HOL`Kernel`INST[{mkVar["n", numTy] -> nV}, HOL`Stdlib`Int`repIntOfNumThm];
    fstZ = TRANS[HOL`Equal`APTERM[fstNN[], repZ], fstNumAt[nV, zeroN[]]];   (* FST(REP&ℤn) = n *)
    sndZ = TRANS[HOL`Equal`APTERM[sndNN[], repZ], sndNumAt[nV, zeroN[]]];   (* SND(REP&ℤn) = 0 *)
    sumEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], fstZ], sndZ];       (* .. + .. = n + 0 *)
    HOL`Bool`GEN[nV, TRANS[unfoldIntNatAbs[zn], TRANS[sumEq, addZeroRightAt[nV]]]]
  ];

(* ⊢ ∀m. gcd m m = m  (proper home Num.wl) *)
gcdSelfThm =
  Module[{mV, gDivM, mDivG, eq},
    mV = mkVar["m", numTy];
    gDivM = HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, HOL`Stdlib`Num`gcdDividesLeftThm]];  (* divides (gcd m m) m *)
    mDivG = HOL`Bool`MP[
      HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, HOL`Stdlib`Num`gcdUniversalThm]]],
      HOL`Bool`CONJ[HOL`Bool`SPEC[mV, HOL`Stdlib`Num`dividesReflThm],
                    HOL`Bool`SPEC[mV, HOL`Stdlib`Num`dividesReflThm]]];   (* divides m (gcd m m) *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[mV, HOL`Bool`SPEC[gcdTm[mV, mV], dividesAntisymThm]], gDivM], mDivG];
    HOL`Bool`GEN[mV, eq]
  ];

(* ⊢ ∀z. intMul z z = &ℤ (intNatAbs z * intNatAbs z) *)
intSqNatAbsThm =
  Module[{zV, repZ, z1, z2, naZ, fc, repMul, intRepDisj, sndZero, canonArgEq,
          sndFC0, intRepFC, canonId, repZZpair, repFCnum, repEqFC, aVar,
          absL, absR, zzEqFc, sqEqNat, naSq, plusCt, timesCt, fcPair},
    zV = mkVar["z", intTy];
    plusCt = HOL`Stdlib`Num`plusConst[]; timesCt = HOL`Stdlib`Num`timesConst[];
    repZ = repInt[zV];
    z1 = mkComb[fstNN[], repZ]; z2 = mkComb[sndNN[], repZ];
    naZ = mkComb[intNatAbsConst[], zV];
    fc = plusTm[timesTm[z1, z1], timesTm[z2, z2]];      (* z1·z1 + z2·z2 *)
    fcPair = numPairCons[fc, zeroN[]];
    repMul = HOL`Bool`SPEC[zV, HOL`Bool`SPEC[zV, HOL`Stdlib`Int`repIntMulThm]];
       (* REP(z·z) = intCanon(z1·z1+z2·z2, z1·z2+z2·z1) *)
    intRepDisj = EQMP[unfoldIntRep[repZ], HOL`Stdlib`Int`intRepRepThm];   (* z1=0 ∨ z2=0 *)
    sndZero = HOL`Bool`DISJCASES[intRepDisj,
      Module[{h, t1, t2}, h = ASSUME[mkEq[z1, zeroN[]]];
        t1 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[timesCt, h], z2],
          HOL`Bool`SPEC[z2, HOL`Stdlib`Num`timesLeftZeroThm]];           (* z1·z2 = 0 *)
        t2 = TRANS[HOL`Equal`APTERM[mkComb[timesCt, z2], h],
          HOL`Bool`SPEC[z2, HOL`Stdlib`Num`timesZeroEqThm]];             (* z2·z1 = 0 *)
        TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusCt, t1], t2],
          HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`addLeftZeroThm]]],
      Module[{h, t1, t2}, h = ASSUME[mkEq[z2, zeroN[]]];
        t1 = TRANS[HOL`Equal`APTERM[mkComb[timesCt, z1], h],
          HOL`Bool`SPEC[z1, HOL`Stdlib`Num`timesZeroEqThm]];             (* z1·z2 = 0 *)
        t2 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[timesCt, h], z1],
          HOL`Bool`SPEC[z1, HOL`Stdlib`Num`timesLeftZeroThm]];           (* z2·z1 = 0 *)
        TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusCt, t1], t2],
          HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`addLeftZeroThm]]]];
       (* z1·z2 + z2·z1 = 0 *)
    canonArgEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[numPairConsC[], REFL[fc]], sndZero];
       (* (fc, z1·z2+z2·z1) = (fc, 0) *)
    sndFC0 = sndNumAt[fc, zeroN[]];                     (* SND(fc,0) = 0 *)
    intRepFC = EQMP[HOL`Equal`SYM[unfoldIntRep[fcPair]],
      HOL`Bool`DISJ2[sndFC0, mkEq[mkComb[fstNN[], fcPair], zeroN[]]]];   (* INT_REP(fc,0) *)
    canonId = HOL`Bool`MP[HOL`Bool`SPEC[fcPair, HOL`Stdlib`Int`intCanonIdThm], intRepFC];
       (* intCanon(fc,0) = (fc,0) *)
    repZZpair = TRANS[repMul,
      TRANS[HOL`Equal`APTERM[HOL`Stdlib`Int`intCanonConst[], canonArgEq], canonId]];
       (* REP(z·z) = (fc, 0) *)
    repFCnum = HOL`Kernel`INST[{mkVar["n", numTy] -> fc}, HOL`Stdlib`Int`repIntOfNumThm];
       (* REP(&ℤ fc) = (fc, 0) *)
    repEqFC = TRANS[repZZpair, HOL`Equal`SYM[repFCnum]];   (* REP(z·z) = REP(&ℤ fc) *)
    aVar = concl[HOL`Stdlib`Int`absRepIntThm][[2]];
    absL = HOL`Kernel`INST[{aVar -> intMulTm[zV, zV]}, HOL`Stdlib`Int`absRepIntThm];
    absR = HOL`Kernel`INST[{aVar -> intOfNum[fc]}, HOL`Stdlib`Int`absRepIntThm];
    zzEqFc = TRANS[HOL`Equal`SYM[absL], TRANS[HOL`Equal`APTERM[absIntC[], repEqFC], absR]];
       (* z·z = &ℤ fc *)
    sqEqNat = HOL`Bool`DISJCASES[intRepDisj,
      Module[{h, lz1, fcL, argEq, rhsR},
        h = ASSUME[mkEq[z1, zeroN[]]];
        lz1 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[timesCt, h], z1],
          HOL`Bool`SPEC[z1, HOL`Stdlib`Num`timesLeftZeroThm]];           (* z1·z1 = 0 *)
        fcL = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusCt, lz1], REFL[timesTm[z2, z2]]],
          HOL`Bool`SPEC[timesTm[z2, z2], HOL`Stdlib`Num`addLeftZeroThm]];  (* fc = z2·z2 *)
        argEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusCt, h], REFL[z2]],
          HOL`Bool`SPEC[z2, HOL`Stdlib`Num`addLeftZeroThm]];             (* z1+z2 = z2 *)
        rhsR = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesCt, argEq], argEq];  (* (z1+z2)·(z1+z2) = z2·z2 *)
        TRANS[fcL, HOL`Equal`SYM[rhsR]]],
      Module[{h, lz2, fcR, argEq, rhsR},
        h = ASSUME[mkEq[z2, zeroN[]]];
        lz2 = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[timesCt, h], z2],
          HOL`Bool`SPEC[z2, HOL`Stdlib`Num`timesLeftZeroThm]];           (* z2·z2 = 0 *)
        fcR = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusCt, REFL[timesTm[z1, z1]]], lz2],
          addZeroRightAt[timesTm[z1, z1]]];                              (* fc = z1·z1 *)
        argEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusCt, REFL[z1]], h],
          addZeroRightAt[z1]];                                           (* z1+z2 = z1 *)
        rhsR = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesCt, argEq], argEq];  (* (z1+z2)·(z1+z2) = z1·z1 *)
        TRANS[fcR, HOL`Equal`SYM[rhsR]]]];
       (* fc = (z1+z2)·(z1+z2) *)
    naSq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesCt, unfoldIntNatAbs[zV]], unfoldIntNatAbs[zV]];
       (* naZ·naZ = (z1+z2)·(z1+z2) *)
    HOL`Bool`GEN[zV, TRANS[zzEqFc, HOL`Equal`APTERM[HOL`Stdlib`Int`intOfNumConst[],
      TRANS[sqEqNat, HOL`Equal`SYM[naSq]]]]]   (* z·z = &ℤ(naZ·naZ) *)
  ];

(* ⊢ ∀m. ¬ (m = 0) ⇒ ratCanon (&ℤ m, m) = (&ℤ (SUC 0), SUC 0) *)
ratCanonSelfThm =
  Module[{mV, zm, p, notM0, ucanon, fstP, sndP, fstPEq, naFstP, sndPEq, gEq,
          intDivSelf, numEq, denEq, pairEq},
    mV = mkVar["m", numTy]; zm = intOfNum[mV];
    p = ratPairCons[zm, mV];
    notM0 = ASSUME[notTm[mkEq[mV, zeroN[]]]];
    ucanon = unfoldRatCanon[p];
    fstP = mkComb[fstIN[], p]; sndP = mkComb[sndIN[], p];
    fstPEq = fstINatAt[zm, mV];                          (* FST p = &ℤm *)
    naFstP = TRANS[HOL`Equal`APTERM[intNatAbsConst[], fstPEq],
      HOL`Bool`SPEC[mV, intNatAbsOfNumThm]];             (* intNatAbs(FST p) = m *)
    sndPEq = sndINatAt[zm, mV];                          (* SND p = m *)
    gEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Num`gcdConst[], naFstP], sndPEq],
      HOL`Bool`SPEC[mV, gcdSelfThm]];                    (* G = gcd m m = m *)
    intDivSelf = Module[{repDiv, repZm, fstZm, sndZm, exMM, ex0M, prF, prS,
                         repEqSuc, repSuc, absL2, absR2, aV2},
      aV2 = concl[HOL`Stdlib`Int`absRepIntThm][[2]];
      repDiv = HOL`Bool`MP[HOL`Bool`SPEC[mV, HOL`Bool`SPEC[zm, repIntDivNatThm]], notM0];
      repZm = HOL`Kernel`INST[{mkVar["n", numTy] -> mV}, HOL`Stdlib`Int`repIntOfNumThm];
      fstZm = TRANS[HOL`Equal`APTERM[fstNN[], repZm], fstNumAt[mV, zeroN[]]];   (* FST(REP&ℤm)=m *)
      sndZm = TRANS[HOL`Equal`APTERM[sndNN[], repZm], sndNumAt[mV, zeroN[]]];   (* SND(REP&ℤm)=0 *)
      exMM = HOL`Bool`MP[HOL`Bool`SPEC[mV, exDivSelfThm], notM0];   (* exDiv m m = SUC0 *)
      ex0M = HOL`Bool`MP[HOL`Bool`SPEC[mV, exDivZeroThm], notM0];   (* exDiv 0 m = 0 *)
      prF = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], fstZm], mV], exMM]; (* exDiv(FST(REP&ℤm))m = SUC0 *)
      prS = TRANS[HOL`Equal`APTHM[HOL`Equal`APTERM[exDivConst[], sndZm], mV], ex0M]; (* exDiv(SND(REP&ℤm))m = 0 *)
      repEqSuc = TRANS[repDiv,
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[numPairConsC[], prF], prS]];   (* REP(intDivNat &ℤm m) = (SUC0, 0) *)
      repSuc = HOL`Kernel`INST[{mkVar["n", numTy] -> oneN[]}, HOL`Stdlib`Int`repIntOfNumThm]; (* REP(&ℤ SUC0)=(SUC0,0) *)
      absL2 = HOL`Kernel`INST[{aV2 -> intDivNatTm[zm, mV]}, HOL`Stdlib`Int`absRepIntThm];
      absR2 = HOL`Kernel`INST[{aV2 -> intOfNum[oneN[]]}, HOL`Stdlib`Int`absRepIntThm];
      TRANS[HOL`Equal`SYM[absL2],
        TRANS[HOL`Equal`APTERM[absIntC[], TRANS[repEqSuc, HOL`Equal`SYM[repSuc]]], absR2]]];
       (* intDivNat (&ℤm) m = &ℤ(SUC0) *)
    numEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intDivNatConst[], fstPEq], gEq], intDivSelf];
       (* intDivNat (FST p) G = &ℤ(SUC0) *)
    denEq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[exDivConst[], sndPEq], gEq],
      HOL`Bool`MP[HOL`Bool`SPEC[mV, exDivSelfThm], notM0]];   (* exDiv (SND p) G = SUC0 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denEq];
    HOL`Bool`GEN[mV, HOL`Bool`DISCH[notTm[mkEq[mV, zeroN[]]],
      TRANS[ucanon, pairEq]]]
  ];

(* ⊢ ∀z. ¬ (z = &ℤ 0) ⇒ ¬ (intNatAbs z = 0)  (proper home Int.wl) *)
intNatAbsNonzeroThm =
  Module[{zV, repZ, z1, z2, naUnf, hNa0, sumEq0, z1eq0, z2eq0, pairEq, surjZ,
          repZ0, repEqZ0, aVar, absL, absR, zEq0, notZ0, falseTh, z0Tm},
    zV = mkVar["z", intTy]; z0Tm = intOfNum[zeroN[]];
    repZ = repInt[zV]; z1 = mkComb[fstNN[], repZ]; z2 = mkComb[sndNN[], repZ];
    naUnf = unfoldIntNatAbs[zV];                          (* intNatAbs z = z1 + z2 *)
    hNa0 = ASSUME[mkEq[mkComb[intNatAbsConst[], zV], zeroN[]]];   (* intNatAbs z = 0 *)
    sumEq0 = TRANS[HOL`Equal`SYM[naUnf], hNa0];           (* z1 + z2 = 0 *)
    z1eq0 = HOL`Bool`MP[HOL`Bool`SPEC[z2, HOL`Bool`SPEC[z1, HOL`Stdlib`Num`addEqZeroLeftThm]], sumEq0];
    z2eq0 = HOL`Bool`MP[HOL`Bool`SPEC[z2, HOL`Bool`SPEC[z1, HOL`Stdlib`Num`addEqZeroRightThm]], sumEq0];
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[numPairConsC[], z1eq0], z2eq0];   (* (z1,z2) = (0,0) *)
    surjZ = HOL`Bool`SPEC[repZ,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                    (* (z1, z2) = REP z *)
    repZ0 = HOL`Kernel`INST[{mkVar["n", numTy] -> zeroN[]}, HOL`Stdlib`Int`repIntOfNumThm]; (* REP(&ℤ0)=(0,0) *)
    repEqZ0 = TRANS[HOL`Equal`SYM[surjZ], TRANS[pairEq, HOL`Equal`SYM[repZ0]]]; (* REP z = REP(&ℤ0) *)
    aVar = concl[HOL`Stdlib`Int`absRepIntThm][[2]];
    absL = HOL`Kernel`INST[{aVar -> zV}, HOL`Stdlib`Int`absRepIntThm];
    absR = HOL`Kernel`INST[{aVar -> z0Tm}, HOL`Stdlib`Int`absRepIntThm];
    zEq0 = TRANS[HOL`Equal`SYM[absL], TRANS[HOL`Equal`APTERM[absIntC[], repEqZ0], absR]];  (* z = &ℤ0 *)
    notZ0 = ASSUME[notTm[mkEq[zV, z0Tm]]];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notZ0], zEq0];
    HOL`Bool`GEN[zV, HOL`Bool`DISCH[notTm[mkEq[zV, z0Tm]],
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[
        mkEq[mkComb[intNatAbsConst[], zV], zeroN[]], falseTh]]]]
  ];

(* ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ ¬ (FST (REP_rat q) = &ℤ 0) *)
ratNumNonzeroThm =
  Module[{qV, repQ, a, b, ratRepQ, gcdEq1, ha0, naA0, gcdArg, gcdZb, bEqSuc0,
          pairEq, surjQ, repZ0rat, repEqZ0, qEq0, notQ0, falseTh, z0Tm, zRat0},
    qV = mkVar["q", ratTy]; repQ = repRat[qV]; z0Tm = intOfNum[zeroN[]];
    zRat0 = ratOfIntTm[z0Tm];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    ratRepQ = EQMP[unfoldRatRep[repQ], ratRepRepThm];
    gcdEq1 = HOL`Bool`CONJUNCT2[ratRepQ];                 (* gcd(intNatAbs a, b) = SUC0 *)
    ha0 = ASSUME[mkEq[a, z0Tm]];                          (* a = &ℤ0 *)
    naA0 = TRANS[HOL`Equal`APTERM[intNatAbsConst[], ha0], intNatAbsZeroThm];  (* intNatAbs a = 0 *)
    gcdArg = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Num`gcdConst[], naA0], b];
                                                          (* gcd(intNatAbs a, b) = gcd(0, b) *)
    gcdZb = HOL`Bool`SPEC[b, gcdZeroLeftThm];             (* gcd(0, b) = b *)
    bEqSuc0 = TRANS[HOL`Equal`SYM[TRANS[gcdArg, gcdZb]], gcdEq1];   (* b = SUC0 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], ha0], bEqSuc0];  (* (a,b) = (&ℤ0, SUC0) *)
    surjQ = HOL`Bool`SPEC[repQ,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairSurjThm]];                    (* (a, b) = REP q *)
    repZ0rat = HOL`Kernel`INST[{mkVar["q", intTy] -> z0Tm}, repRatOfIntThm];  (* REP(&ℚ&ℤ0)=(&ℤ0,SUC0) *)
    repEqZ0 = TRANS[HOL`Equal`SYM[surjQ], TRANS[pairEq, HOL`Equal`SYM[repZ0rat]]]; (* REP q = REP(&ℚ&ℤ0) *)
    qEq0 = ratEqFromRepEq[repEqZ0, qV, zRat0];            (* q = &ℚ&ℤ0 *)
    notQ0 = ASSUME[notTm[mkEq[qV, zRat0]]];
    falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[notQ0], qEq0];
    HOL`Bool`GEN[qV, HOL`Bool`DISCH[notTm[mkEq[qV, zRat0]],
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[a, z0Tm], falseTh]]]]
  ];

(* ============================================================ *)
(* ratInv + ratMulInv → ℚ is a FIELD.                            *)
(* ============================================================ *)

ratInvTy = tyFun[ratTy, ratTy];

(* inverse-pair (intMul a (&ℤ b), |a|·|a|) of a rep repQ *)
ratInvPair[repQ_] :=
  Module[{a, b, na},
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    na = mkComb[intNatAbsConst[], a];
    ratPairCons[intMulTm[a, intOfNum[b]], timesTm[na, na]]
  ];

ratInvDefThm = newDefinition[mkEq[
  mkVar["ratInv", ratInvTy],
  Module[{qV}, qV = mkVar["q", ratTy];
    mkAbs[qV, mkComb[absRatConst[], ratCanonTm[ratInvPair[repRat[qV]]]]]]
]];

ratInvConst[] := mkConst["ratInv", ratInvTy];
ratInvTm[qT_] := mkComb[ratInvConst[], qT];

unfoldRatInv[qT_] :=
  Module[{ap}, ap = HOL`Equal`APTHM[ratInvDefThm, qT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]];

(* ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ REP_rat (ratInv q) = ratCanon (inverse-pair) *)
repRatInvThm =
  Module[{qV, repQ, a, b, na, pairTm, numTmrt, denTm, notQ0, notA0, notNa0,
          notDen0, sndPairEq, notSndPair0, lands, repAbsInst, repEqCanon,
          unfInv, apRep, body, z0Tm},
    qV = mkVar["q", ratTy]; z0Tm = intOfNum[zeroN[]];
    repQ = repRat[qV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ];
    na = mkComb[intNatAbsConst[], a];
    pairTm = ratInvPair[repQ];
    numTmrt = pairTm[[1, 2]]; denTm = pairTm[[2]];   (* denTm = na·na *)
    notQ0 = ASSUME[notTm[mkEq[qV, ratOfIntTm[z0Tm]]]];
    notA0 = HOL`Bool`MP[HOL`Bool`SPEC[qV, ratNumNonzeroThm], notQ0];      (* ¬(a = &ℤ0) *)
    notNa0 = HOL`Bool`MP[HOL`Bool`SPEC[a, intNatAbsNonzeroThm], notA0];   (* ¬(na = 0) *)
    notDen0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[na, HOL`Bool`SPEC[na, multNonzeroThm]], notNa0], notNa0];  (* ¬(na·na = 0) *)
    sndPairEq = sndINatAt[numTmrt, denTm];
    notSndPair0 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndPairEq]}, notDen0];
    lands = HOL`Bool`MP[HOL`Bool`SPEC[pairTm, ratCanonLandsThm], notSndPair0];
    repAbsInst = HOL`Kernel`INST[
      {concl[repAbsRatThm][[1, 2, 2]] -> ratCanonTm[pairTm]}, repAbsRatThm];
    repEqCanon = EQMP[repAbsInst, lands];
    unfInv = unfoldRatInv[qV];
    apRep = HOL`Equal`APTERM[repRatConst[], unfInv];
    body = TRANS[apRep, repEqCanon];
    HOL`Bool`GEN[qV, HOL`Bool`DISCH[notTm[mkEq[qV, ratOfIntTm[z0Tm]]], body]]
  ];

(* intMul (FST(REP(ratInv q))) (&ℤ Uden) = intMul Unum (&ℤ(SND(REP(ratInv q)))),
   (Unum, Uden) = ratInvPair (REP q); carries hyp ¬(q = &ℚ&ℤ0). *)
repInvEquivAt[qT_] :=
  Module[{repQ, a, b, na, U1, U1num, U1den, repInvQ, notQ0, notA0, notNa0,
          notSndU1, fstU1, sndU1, equivU1, fstEqA, denEqA, lhsRw, fstEqB,
          sndEqB, rhsRw, intMulC, intOfNumC, z0Tm},
    intMulC = intMulCC[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    z0Tm = intOfNum[zeroN[]];
    repQ = repRat[qT];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ]; na = mkComb[intNatAbsConst[], a];
    U1 = ratInvPair[repQ]; U1num = U1[[1, 2]]; U1den = U1[[2]];
    notQ0 = ASSUME[notTm[mkEq[qT, ratOfIntTm[z0Tm]]]];
    repInvQ = HOL`Bool`MP[HOL`Bool`SPEC[qT, repRatInvThm], notQ0];
    notA0 = HOL`Bool`MP[HOL`Bool`SPEC[qT, ratNumNonzeroThm], notQ0];
    notNa0 = HOL`Bool`MP[HOL`Bool`SPEC[a, intNatAbsNonzeroThm], notA0];
    notSndU1 = HOL`Drule`SUBS[{HOL`Equal`SYM[sndINatAt[U1num, U1den]]},
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[na, HOL`Bool`SPEC[na, multNonzeroThm]],
        notNa0], notNa0]];
    fstU1 = fstINatAt[U1num, U1den]; sndU1 = sndINatAt[U1num, U1den];
    equivU1 = HOL`Bool`MP[HOL`Bool`SPEC[U1, ratCanonEquivThm], notSndU1];
    fstEqA = HOL`Equal`APTERM[fstIN[], repInvQ];
    denEqA = HOL`Equal`APTERM[intOfNumC, HOL`Equal`SYM[sndU1]];
    lhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqA], denEqA];
    fstEqB = HOL`Equal`SYM[fstU1];
    sndEqB = HOL`Equal`APTERM[intOfNumC, HOL`Equal`APTERM[sndIN[], repInvQ]];
    rhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstEqB], sndEqB];
    TRANS[lhsRw, TRANS[equivU1, HOL`Equal`SYM[rhsRw]]]
  ];

(* ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ ratMul q (ratInv q) = &ℚ (&ℤ (SUC 0)) *)
ratMulInvThm =
  Module[{qV, repQ, a, b, na, invQ, z0Tm, oneRat, m, U1num, U1den, repInvQrep,
          notQ0, notB0, notA0, notNa0, notNaNa0, notMden, repMul, congRInst,
          congR, amul, s1, s2, s3, s4, numRewrite, pairEqSelf, canonStep,
          canonSelf, repOne, repEq, intMulC, timesC},
    qV = mkVar["q", ratTy]; z0Tm = intOfNum[zeroN[]];
    intMulC = intMulCC[]; timesC = HOL`Stdlib`Num`timesConst[];
    oneRat = ratOfIntTm[intOfNum[oneN[]]];               (* &ℚ(&ℤ(SUC 0)) *)
    repQ = repRat[qV];
    a = mkComb[fstIN[], repQ]; b = mkComb[sndIN[], repQ]; na = mkComb[intNatAbsConst[], a];
    invQ = ratInvTm[qV]; repInvQrep = repRat[invQ];
    U1num = intMulTm[a, intOfNum[b]]; U1den = timesTm[na, na];   (* inverse-pair components *)
    m = timesTm[b, timesTm[na, na]];                     (* b·(|a|·|a|) *)
    amul[xT_, yT_, zT_] := HOL`Bool`SPEC[zT, HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT,
      HOL`Stdlib`Int`intMulAssocThm]]];                  (* (x·y)·z = x·(y·z) *)
    notQ0 = ASSUME[notTm[mkEq[qV, ratOfIntTm[z0Tm]]]];
    notB0 = HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repQ], ratRepRepThm]];   (* ¬(b=0) *)
    notA0 = HOL`Bool`MP[HOL`Bool`SPEC[qV, ratNumNonzeroThm], notQ0];
    notNa0 = HOL`Bool`MP[HOL`Bool`SPEC[a, intNatAbsNonzeroThm], notA0];   (* ¬(na=0) *)
    notNaNa0 = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[na, HOL`Bool`SPEC[na, multNonzeroThm]], notNa0], notNa0];  (* ¬(na·na=0) *)
    notMden = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[timesTm[na, na], HOL`Bool`SPEC[b, multNonzeroThm]], notB0], notNaNa0];
       (* ¬(b·(na·na) = 0) *)
    repMul = HOL`Bool`SPEC[invQ, HOL`Bool`SPEC[qV, repRatMulThm]];
       (* REP(ratMul q (ratInv q)) = ratCanon(ratMulPair(repQ, repInvQ)) *)
    congRInst = HOL`Bool`SPEC[U1den, HOL`Bool`SPEC[U1num,
      HOL`Bool`SPEC[mkComb[sndIN[], repInvQrep], HOL`Bool`SPEC[mkComb[fstIN[], repInvQrep],
        HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, ratMulCongRightThm]]]]]];
    congR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[congRInst,
      notB0],
      HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repInvQrep],
        HOL`Kernel`INST[{mkVar["q", ratTy] -> invQ}, ratRepRepThm]]]],
      notNaNa0], repInvEquivAt[qV]];
       (* ratCanon(mulPair a b (FST(REP invQ))(SND(REP invQ))) = ratCanon(mulPair a b U1num U1den) *)
    (* numerator a·(a·&ℤb) = &ℤ m *)
    s1 = HOL`Equal`SYM[amul[a, a, intOfNum[b]]];          (* a·(a·&ℤb) = (a·a)·&ℤb *)
    s2 = HOL`Equal`APTHM[HOL`Equal`APTERM[intMulC, HOL`Bool`SPEC[a, intSqNatAbsThm]], intOfNum[b]];
                                                          (* (a·a)·&ℤb = &ℤ(na·na)·&ℤb *)
    s3 = HOL`Equal`SYM[intOfNumMulAt[timesTm[na, na], b]];  (* &ℤ(na·na)·&ℤb = &ℤ((na·na)·b) *)
    s4 = HOL`Equal`APTERM[HOL`Stdlib`Int`intOfNumConst[],
      HOL`Bool`SPEC[b, HOL`Bool`SPEC[timesTm[na, na], HOL`Stdlib`Num`timesCommThm]]];
                                                          (* &ℤ((na·na)·b) = &ℤ(b·(na·na)) = &ℤ m *)
    numRewrite = TRANS[s1, TRANS[s2, TRANS[s3, s4]]];     (* a·(a·&ℤb) = &ℤ m *)
    pairEqSelf = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numRewrite], REFL[m]];
                                                          (* (a·(a·&ℤb), m) = (&ℤ m, m) *)
    canonStep = HOL`Equal`APTERM[ratCanonConst[], pairEqSelf];
    canonSelf = HOL`Bool`MP[HOL`Bool`SPEC[m, ratCanonSelfThm], notMden];
                                                          (* ratCanon(&ℤ m, m) = (&ℤ(SUC0), SUC0) *)
    repOne = HOL`Kernel`INST[{mkVar["q", intTy] -> intOfNum[oneN[]]}, repRatOfIntThm];
                                                          (* REP(&ℚ&ℤ1) = (&ℤ(SUC0), SUC0) *)
    repEq = TRANS[repMul, TRANS[congR, TRANS[canonStep, TRANS[canonSelf, HOL`Equal`SYM[repOne]]]]];
    HOL`Bool`GEN[qV, HOL`Bool`DISCH[notTm[mkEq[qV, ratOfIntTm[z0Tm]]],
      ratEqFromRepEq[repEq, ratMulTm[qV, invQ], oneRat]]]
  ];

(* ============================================================ *)
(* Stage f — order. ratLe / ratLt by cross-multiplication with   *)
(* positive denominators, reducing to Int's intLe / intLt on the *)
(* cross-products. The cross-products are intMul (opaque to      *)
(* ARITH), so the order axioms run on Int order + intMul ring    *)
(* lemmas, not on ℕ ARITH (unlike Int's own order layer).        *)
(* ============================================================ *)

intLeCC[] := HOL`Stdlib`Int`intLeConst[];
intLtCC[] := HOL`Stdlib`Int`intLtConst[];
intLeTmR[zT_, wT_] := mkComb[mkComb[intLeCC[], zT], wT];
intLtTmR[zT_, wT_] := mkComb[mkComb[intLtCC[], zT], wT];
intZeroR := intOfNum[zeroN[]];

imComm[zT_, wT_]      := HOL`Bool`SPEC[wT, HOL`Bool`SPEC[zT, HOL`Stdlib`Int`intMulCommThm]];
imAssoc[zT_, wT_, vT_] := HOL`Bool`SPEC[vT, HOL`Bool`SPEC[wT, HOL`Bool`SPEC[zT,
  HOL`Stdlib`Int`intMulAssocThm]]];

(* ⊢ ∀u x y. intLe (&ℤ 0) u ⇒ ¬(u = &ℤ 0)                       *)
(*           ⇒ intLe (intMul u x) (intMul u y) ⇒ intLe x y       *)
(* Cancellation of a positive left factor. By totality: if the   *)
(* goal's reverse holds, mul-nonneg + antisym give u·x = u·y,    *)
(* and intMulCancel (u ≠ 0) collapses it to x = y. (Int.wl home.) *)
intLeMulNonnegCancelThm =
  Module[{uV, xV, yV, ux, uy, z0, nonneg, notU0, hyp, total, caseA, caseB,
          monoBA, eqUxUy, xEqY, reflXX, leXYb, result, intLeC},
    uV = mkVar["u", intTy]; xV = mkVar["x", intTy]; yV = mkVar["y", intTy];
    z0 = intZeroR; intLeC = intLeCC[];
    ux = intMulTm[uV, xV]; uy = intMulTm[uV, yV];
    nonneg = ASSUME[intLeTmR[z0, uV]];
    notU0  = ASSUME[notTm[mkEq[uV, z0]]];
    hyp    = ASSUME[intLeTmR[ux, uy]];
    total  = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, HOL`Stdlib`Int`intLeTotalThm]];
    caseA  = ASSUME[intLeTmR[xV, yV]];
    caseB  = ASSUME[intLeTmR[yV, xV]];
    monoBA = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[uV, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV,
        HOL`Stdlib`Int`intLeMulNonnegThm]]], nonneg], caseB];   (* intLe (u·y) (u·x) *)
    eqUxUy = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[uy, HOL`Bool`SPEC[ux, HOL`Stdlib`Int`intLeAntisymThm]], hyp],
      monoBA];                                                  (* u·x = u·y *)
    xEqY = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[uV,
        HOL`Stdlib`Int`intMulCancelThm]]], notU0], eqUxUy];     (* x = y *)
    reflXX = HOL`Bool`SPEC[xV, HOL`Stdlib`Int`intLeReflThm];
    leXYb  = EQMP[HOL`Equal`APTERM[mkComb[intLeC, xV], xEqY], reflXX];  (* intLe x y *)
    result = HOL`Bool`DISJCASES[total, caseA, leXYb];
    HOL`Bool`GEN[uV, HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[intLeTmR[z0, uV],
        HOL`Bool`DISCH[notTm[mkEq[uV, z0]],
          HOL`Bool`DISCH[intLeTmR[ux, uy], result]]]]]]
  ];

ratNumOf[qT_] := mkComb[fstIN[], repRat[qT]];                   (* FST(REP q) : int *)
ratDenOf[qT_] := mkComb[sndIN[], repRat[qT]];                   (* SND(REP q) : num *)
ratCrossL[qT_, rT_] := intMulTm[ratNumOf[qT], intOfNum[ratDenOf[rT]]];  (* a·&ℤd *)
ratCrossR[qT_, rT_] := intMulTm[ratNumOf[rT], intOfNum[ratDenOf[qT]]];  (* c·&ℤb *)

ratLeTy = tyFun[ratTy, tyFun[ratTy, boolT]];
ratLeDefThm = newDefinition[mkEq[mkVar["ratLe", ratLeTy],
  Module[{qV, rV}, qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    mkAbs[qV, mkAbs[rV, intLeTmR[ratCrossL[qV, rV], ratCrossR[qV, rV]]]]]]];
ratLeConst[] := mkConst["ratLe", ratLeTy];
ratLeTm[qT_, rT_] := mkComb[mkComb[ratLeConst[], qT], rT];

unfoldRatLe[qT_, rT_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[ratLeDefThm, qT];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, rT];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]];

(* intLe (&ℤ 0) (&ℤ n) — &ℤ of a natural is nonnegative. *)
intOfNumNonneg[nTm_] :=
  EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[nTm, HOL`Bool`SPEC[zeroN[],
    HOL`Stdlib`Int`intOfNumLeThm]]], HOL`Bool`SPEC[nTm, HOL`Stdlib`Num`leqZeroThm]];

(* ¬(&ℤ n = &ℤ 0) from ¬(n = 0), via intOfNumInj contrapositive. *)
intOfNumNeqZero[notN0_, nTm_] :=
  Module[{inj, eqHyp, nEq0, contra},
    inj = HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[nTm, HOL`Stdlib`Int`intOfNumInjThm]];
    eqHyp = ASSUME[mkEq[intOfNum[nTm], intZeroR]];
    nEq0 = HOL`Bool`MP[inj, eqHyp];
    contra = HOL`Bool`MP[HOL`Bool`NOTELIM[notN0], nEq0];
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[intOfNum[nTm], intZeroR], contra]]
  ];

(* ¬(SND(REP q) = 0) — denominators are positive. *)
ratDenNeq0[qT_] :=
  HOL`Bool`CONJUNCT1[EQMP[unfoldRatRep[repRat[qT]],
    HOL`Kernel`INST[{mkVar["q", ratTy] -> qT}, ratRepRepThm]]];

(* ⊢ ∀q. ratLe q q *)
ratLeReflThm =
  Module[{qV, x, refl},
    qV = mkVar["q", ratTy];
    x = ratCrossL[qV, qV];                                      (* a·&ℤb = ratCrossR[q,q] *)
    refl = HOL`Bool`SPEC[x, HOL`Stdlib`Int`intLeReflThm];
    HOL`Bool`GEN[qV, EQMP[HOL`Equal`SYM[unfoldRatLe[qV, qV]], refl]]
  ];

(* ⊢ ∀q r. ratLe q r ⇒ ratLe r q ⇒ q = r *)
ratLeAntisymThm =
  Module[{qV, rV, ad, cb, h1, h2, le1, le2, crossEq, crossIff, qEqR},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    ad = ratCrossL[qV, rV]; cb = ratCrossR[qV, rV];
    h1 = ASSUME[ratLeTm[qV, rV]]; h2 = ASSUME[ratLeTm[rV, qV]];
    le1 = EQMP[unfoldRatLe[qV, rV], h1];                        (* intLe ad cb *)
    le2 = EQMP[unfoldRatLe[rV, qV], h2];                        (* intLe cb ad *)
    crossEq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[cb, HOL`Bool`SPEC[ad, HOL`Stdlib`Int`intLeAntisymThm]], le1],
      le2];                                                     (* ad = cb *)
    crossIff = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[qV, ratEqCrossThm]];
    qEqR = EQMP[HOL`Equal`SYM[crossIff], crossEq];
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV,
      HOL`Bool`DISCH[ratLeTm[qV, rV], HOL`Bool`DISCH[ratLeTm[rV, qV], qEqR]]]]
  ];

(* ⊢ ∀q r v. ratLe q r ⇒ ratLe r v ⇒ ratLe q v *)
(* a/b ≤ c/d and c/d ≤ e/f: multiply the first by &ℤf, the second *)
(* by &ℤb (both nonneg), chain through the shared &ℤf·CB = &ℤb·CF, *)
(* reassociate to a common right factor &ℤd, then cancel &ℤd (>0). *)
ratLeTransThm =
  Module[{qV, rV, vV, a, b, c, d, e, f, zb, zd, zf, ad, cb, cf, ed, af, eb,
          h1, h2, le1, le2, notD0, le0b, le0f, le0d, notZd, intLeC, intMulC,
          m1, m2, e1, e2, e3, eqMid, congLe1, m1p, mid, l1, l2, eqL, r1, r2,
          eqR, congMid, midCanc, commAF, commEB, congComm, cancForm, leAFEB},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy]; vV = mkVar["v", ratTy];
    a = ratNumOf[qV]; b = ratDenOf[qV];
    c = ratNumOf[rV]; d = ratDenOf[rV];
    e = ratNumOf[vV]; f = ratDenOf[vV];
    zb = intOfNum[b]; zd = intOfNum[d]; zf = intOfNum[f];
    ad = intMulTm[a, zd]; cb = intMulTm[c, zb]; cf = intMulTm[c, zf];
    ed = intMulTm[e, zd]; af = intMulTm[a, zf]; eb = intMulTm[e, zb];
    intLeC = intLeCC[]; intMulC = intMulCC[];
    h1 = ASSUME[ratLeTm[qV, rV]]; h2 = ASSUME[ratLeTm[rV, vV]];
    le1 = EQMP[unfoldRatLe[qV, rV], h1];                        (* intLe ad cb *)
    le2 = EQMP[unfoldRatLe[rV, vV], h2];                        (* intLe cf ed *)
    notD0 = ratDenNeq0[rV];                                     (* ¬(d = 0) *)
    le0b = intOfNumNonneg[b]; le0f = intOfNumNonneg[f]; le0d = intOfNumNonneg[d];
    notZd = intOfNumNeqZero[notD0, d];                          (* ¬(&ℤd = &ℤ0) *)
    m1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zf,
      HOL`Bool`SPEC[cb, HOL`Bool`SPEC[ad, HOL`Stdlib`Int`intLeMulNonnegThm]]],
      le0f], le1];                                              (* intLe (zf·ad) (zf·cb) *)
    m2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zb,
      HOL`Bool`SPEC[ed, HOL`Bool`SPEC[cf, HOL`Stdlib`Int`intLeMulNonnegThm]]],
      le0b], le2];                                              (* intLe (zb·cf) (zb·ed) *)
    e1 = HOL`Equal`SYM[imAssoc[zf, c, zb]];                     (* zf·(c·zb) = (zf·c)·zb *)
    e2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, imComm[zf, c]], REFL[zb]];
                                                                (* (zf·c)·zb = (c·zf)·zb *)
    e3 = imComm[intMulTm[c, zf], zb];                           (* (c·zf)·zb = zb·(c·zf) *)
    eqMid = TRANS[e1, TRANS[e2, e3]];                           (* zf·cb = zb·cf *)
    congLe1 = HOL`Equal`APTERM[mkComb[intLeC, intMulTm[zf, ad]], eqMid];
    m1p = EQMP[congLe1, m1];                                    (* intLe (zf·ad) (zb·cf) *)
    mid = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[intMulTm[zb, ed], HOL`Bool`SPEC[intMulTm[zb, cf],
        HOL`Bool`SPEC[intMulTm[zf, ad], HOL`Stdlib`Int`intLeTransThm]]], m1p], m2];
                                                                (* intLe (zf·ad) (zb·ed) *)
    l1 = HOL`Equal`SYM[imAssoc[zf, a, zd]];                     (* zf·(a·zd) = (zf·a)·zd *)
    l2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, imComm[zf, a]], REFL[zd]];
    eqL = TRANS[l1, l2];                                        (* zf·ad = af·zd *)
    r1 = HOL`Equal`SYM[imAssoc[zb, e, zd]];
    r2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, imComm[zb, e]], REFL[zd]];
    eqR = TRANS[r1, r2];                                        (* zb·ed = eb·zd *)
    congMid = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, eqL], eqR];
    midCanc = EQMP[congMid, mid];                               (* intLe (af·zd) (eb·zd) *)
    commAF = imComm[af, zd]; commEB = imComm[eb, zd];
    congComm = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, commAF], commEB];
    cancForm = EQMP[congComm, midCanc];                         (* intLe (zd·af) (zd·eb) *)
    leAFEB = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[eb, HOL`Bool`SPEC[af, HOL`Bool`SPEC[zd,
        intLeMulNonnegCancelThm]]], le0d], notZd], cancForm];   (* intLe af eb *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, HOL`Bool`GEN[vV,
      HOL`Bool`DISCH[ratLeTm[qV, rV], HOL`Bool`DISCH[ratLeTm[rV, vV],
        EQMP[HOL`Equal`SYM[unfoldRatLe[qV, vV]], leAFEB]]]]]]
  ];

(* ⊢ ∀q r. ratLe q r ∨ ratLe r q *)
ratLeTotalThm =
  Module[{qV, rV, total, eqL, eqR, disjEq},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    total = HOL`Bool`SPEC[ratCrossR[qV, rV], HOL`Bool`SPEC[ratCrossL[qV, rV],
      HOL`Stdlib`Int`intLeTotalThm]];
    eqL = HOL`Equal`SYM[unfoldRatLe[qV, rV]];
    eqR = HOL`Equal`SYM[unfoldRatLe[rV, qV]];
    disjEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[orCR[], eqL], eqR];
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, EQMP[disjEq, total]]]
  ];

ratLtTy = tyFun[ratTy, tyFun[ratTy, boolT]];
ratLtDefThm = newDefinition[mkEq[mkVar["ratLt", ratLtTy],
  Module[{qV, rV}, qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    mkAbs[qV, mkAbs[rV, intLtTmR[ratCrossL[qV, rV], ratCrossR[qV, rV]]]]]]];
ratLtConst[] := mkConst["ratLt", ratLtTy];
ratLtTm[qT_, rT_] := mkComb[mkComb[ratLtConst[], qT], rT];

unfoldRatLt[qT_, rT_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[ratLtDefThm, qT];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, rT];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]];

(* ⊢ ∀q r. ratLt q r = ¬(ratLe r q) *)
ratLtNotLeThm =
  Module[{qV, rV, step1, nleEqLt, unfoldLtQR},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    step1 = HOL`Equal`APTERM[notC[], unfoldRatLe[rV, qV]];      (* ¬(ratLe r q) = ¬(intLe cb ad) *)
    nleEqLt = HOL`Bool`SPEC[ratCrossR[qV, rV], HOL`Bool`SPEC[ratCrossL[qV, rV],
      HOL`Stdlib`Int`intLtNotLeThm]];                          (* intLt ad cb = ¬(intLe cb ad) *)
    unfoldLtQR = unfoldRatLt[qV, rV];                          (* ratLt q r = intLt ad cb *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV,
      TRANS[unfoldLtQR, HOL`Equal`SYM[TRANS[step1, HOL`Equal`SYM[nleEqLt]]]]]]
  ];

(* ============================================================ *)
(* Stage f — order/arithmetic compatibility.                    *)
(* The cross-product order respects cross-equivalence of either  *)
(* operand (pairLeCong{Left,Right}); each is a multiply-by-the-  *)
(* new-denominator, cross-swap, cancel-the-old-denominator chain *)
(* — the order analog of ratAddCong{Left,Right}. ratLeAddMono /  *)
(* ratLeMulNonneg then reduce ratLe at ratAdd/ratMul (REP = a     *)
(* ratCanon, opaque) to the unreduced cross-product (via         *)
(* repAddEquivAt/repMulEquivAt) and discharge the int-ring core.  *)
(* ============================================================ *)

(* swap the LEFT cross-operand for a cross-equivalent one (cancel &ℤm1) *)
pairLeCongLeftThm =
  Module[{n1, m1, eV, fV, n2, m2, intLeC, intMulC, zf, zm1, zm2, le0f, mulL,
          lhsEq, rhsEq, congMul, scaled, commL, commR, congC, cf, le0m1,
          notZm1, result},
    n1 = mkVar["n1", intTy]; eV = mkVar["e", intTy]; n2 = mkVar["c", intTy];
    m1 = mkVar["m1", numTy]; fV = mkVar["f", numTy]; m2 = mkVar["g", numTy];
    intLeC = intLeCC[]; intMulC = intMulCC[];
    zf = intOfNum[fV]; zm1 = intOfNum[m1]; zm2 = intOfNum[m2];
    le0f = intOfNumNonneg[fV];
    mulL = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zf,
      HOL`Bool`SPEC[intMulTm[n2, zm1], HOL`Bool`SPEC[intMulTm[n1, zm2],
        HOL`Stdlib`Int`intLeMulNonnegThm]]], le0f],
      ASSUME[intLeTmR[intMulTm[n1, zm2], intMulTm[n2, zm1]]]];
        (* intLe (&ℤf·(n1·&ℤm2)) (&ℤf·(n2·&ℤm1)) *)
    lhsEq = TRANS[HOL`Equal`SYM[imAssoc[zf, n1, zm2]],
      TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, imComm[zf, n1]], REFL[zm2]],
        TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC,
          ASSUME[mkEq[intMulTm[n1, zf], intMulTm[eV, zm1]]]], REFL[zm2]],
          crossSwapAt[eV, m1, m2]]]];   (* &ℤf·(n1·&ℤm2) = (e·&ℤm2)·&ℤm1 *)
    rhsEq = TRANS[HOL`Equal`SYM[imAssoc[zf, n2, zm1]],
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, imComm[zf, n2]], REFL[zm1]]];
        (* &ℤf·(n2·&ℤm1) = (n2·&ℤf)·&ℤm1 *)
    congMul = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, lhsEq], rhsEq];
    scaled = EQMP[congMul, mulL];   (* intLe ((e·&ℤm2)·&ℤm1) ((n2·&ℤf)·&ℤm1) *)
    commL = imComm[intMulTm[eV, zm2], zm1]; commR = imComm[intMulTm[n2, zf], zm1];
    congC = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, commL], commR];
    cf = EQMP[congC, scaled];        (* intLe (&ℤm1·(e·&ℤm2)) (&ℤm1·(n2·&ℤf)) *)
    le0m1 = intOfNumNonneg[m1]; notZm1 = intOfNumNeqZero[ASSUME[notTm[mkEq[m1, zeroN[]]]], m1];
    result = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[intMulTm[n2, zf], HOL`Bool`SPEC[intMulTm[eV, zm2],
        HOL`Bool`SPEC[zm1, intLeMulNonnegCancelThm]]], le0m1], notZm1], cf];
        (* intLe (e·&ℤm2)(n2·&ℤf) *)
    HOL`Bool`GEN[n1, HOL`Bool`GEN[m1, HOL`Bool`GEN[eV, HOL`Bool`GEN[fV,
      HOL`Bool`GEN[n2, HOL`Bool`GEN[m2,
        HOL`Bool`DISCH[notTm[mkEq[m1, zeroN[]]],
          HOL`Bool`DISCH[notTm[mkEq[fV, zeroN[]]],
            HOL`Bool`DISCH[mkEq[intMulTm[n1, zf], intMulTm[eV, zm1]],
              HOL`Bool`DISCH[intLeTmR[intMulTm[n1, zm2], intMulTm[n2, zm1]],
                result]]]]]]]]]]
  ];

(* swap the RIGHT cross-operand for a cross-equivalent one (cancel &ℤm2) *)
pairLeCongRightThm =
  Module[{n1, m1, n2, m2, eV, fV, intLeC, intMulC, zf, zm1, zm2, le0f, mulL,
          lhsEq, rhsEq, congMul, scaled, commL, commR, congC, cf, le0m2,
          notZm2, result},
    n1 = mkVar["n1", intTy]; n2 = mkVar["c", intTy]; eV = mkVar["e", intTy];
    m1 = mkVar["m1", numTy]; m2 = mkVar["g", numTy]; fV = mkVar["f", numTy];
    intLeC = intLeCC[]; intMulC = intMulCC[];
    zf = intOfNum[fV]; zm1 = intOfNum[m1]; zm2 = intOfNum[m2];
    le0f = intOfNumNonneg[fV];
    mulL = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zf,
      HOL`Bool`SPEC[intMulTm[n2, zm1], HOL`Bool`SPEC[intMulTm[n1, zm2],
        HOL`Stdlib`Int`intLeMulNonnegThm]]], le0f],
      ASSUME[intLeTmR[intMulTm[n1, zm2], intMulTm[n2, zm1]]]];
    lhsEq = TRANS[HOL`Equal`SYM[imAssoc[zf, n1, zm2]],
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, imComm[zf, n1]], REFL[zm2]]];
        (* &ℤf·(n1·&ℤm2) = (n1·&ℤf)·&ℤm2 *)
    rhsEq = TRANS[HOL`Equal`SYM[imAssoc[zf, n2, zm1]],
      TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, imComm[zf, n2]], REFL[zm1]],
        TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC,
          ASSUME[mkEq[intMulTm[n2, zf], intMulTm[eV, zm2]]]], REFL[zm1]],
          crossSwapAt[eV, m2, m1]]]];   (* &ℤf·(n2·&ℤm1) = (e·&ℤm1)·&ℤm2 *)
    congMul = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, lhsEq], rhsEq];
    scaled = EQMP[congMul, mulL];   (* intLe ((n1·&ℤf)·&ℤm2) ((e·&ℤm1)·&ℤm2) *)
    commL = imComm[intMulTm[n1, zf], zm2]; commR = imComm[intMulTm[eV, zm1], zm2];
    congC = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, commL], commR];
    cf = EQMP[congC, scaled];        (* intLe (&ℤm2·(n1·&ℤf)) (&ℤm2·(e·&ℤm1)) *)
    le0m2 = intOfNumNonneg[m2]; notZm2 = intOfNumNeqZero[ASSUME[notTm[mkEq[m2, zeroN[]]]], m2];
    result = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[intMulTm[eV, zm1], HOL`Bool`SPEC[intMulTm[n1, zf],
        HOL`Bool`SPEC[zm2, intLeMulNonnegCancelThm]]], le0m2], notZm2], cf];
        (* intLe (n1·&ℤf)(e·&ℤm1) *)
    HOL`Bool`GEN[n1, HOL`Bool`GEN[m1, HOL`Bool`GEN[n2, HOL`Bool`GEN[m2,
      HOL`Bool`GEN[eV, HOL`Bool`GEN[fV,
        HOL`Bool`DISCH[notTm[mkEq[m2, zeroN[]]],
          HOL`Bool`DISCH[notTm[mkEq[fV, zeroN[]]],
            HOL`Bool`DISCH[mkEq[intMulTm[n2, zf], intMulTm[eV, zm2]],
              HOL`Bool`DISCH[intLeTmR[intMulTm[n1, zm2], intMulTm[n2, zm1]],
                result]]]]]]]]]]
  ];

(* ⊢ ∀q r u. ratLe q r ⇒ ratLe (ratAdd q u) (ratAdd r u) *)
(* Reduce ratLe at the two sums to the unreduced cross-product       *)
(* intLe (N1·&ℤD2)(N2·&ℤD1) (UNRED): distribute, the g·b·d·h terms    *)
(* are a common addend (intLeAddMono), and the core a·&ℤd ≤ c·&ℤb     *)
(* scaled by &ℤh·&ℤh ≥ 0 (intLeMulNonneg) is the hypothesis. Then     *)
(* swap each operand to its canon'd REP via repAddEquivAt + cong.     *)
ratLeAddMonoThm =
  Module[{qV, rV, uV, a, b, c, d, g, h, zb, zd, zh, intLeC, intMulC, intAddCl,
          leQR, qu, ru, n1, d1, n2, d2, p1, q1, p2, q2, kk, coreL, coreR, gterm,
          nonnegKK, coreLM, cL, cR, congCore, core, addG, rdistL, t1eqL, t2eqL,
          eqN1, rdistR, t1eqR, t2eqR, eqN2, congU, unred, notB0, notH0, notD0r,
          notD1, notQ1, e1, swap1, notD2, notQ2, e2, swap2},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy]; uV = mkVar["u", ratTy];
    a = ratNumOf[qV]; b = ratDenOf[qV]; c = ratNumOf[rV]; d = ratDenOf[rV];
    g = ratNumOf[uV]; h = ratDenOf[uV];
    zb = intOfNum[b]; zd = intOfNum[d]; zh = intOfNum[h];
    intLeC = intLeCC[]; intMulC = intMulCC[]; intAddCl = intAddC[];
    leQR = EQMP[unfoldRatLe[qV, rV], ASSUME[ratLeTm[qV, rV]]];   (* intLe (a·&ℤd)(c·&ℤb) *)
    qu = ratAddTm[qV, uV]; ru = ratAddTm[rV, uV];
    n1 = intAddTm[intMulTm[a, zh], intMulTm[g, zb]]; d1 = timesTm[b, h];
    n2 = intAddTm[intMulTm[c, zh], intMulTm[g, zd]]; d2 = timesTm[d, h];
    p1 = mkComb[fstIN[], repRat[qu]]; q1 = mkComb[sndIN[], repRat[qu]];
    p2 = mkComb[fstIN[], repRat[ru]]; q2 = mkComb[sndIN[], repRat[ru]];
    kk = intMulTm[zh, zh];
    coreL = intMulTm[intMulTm[a, zd], kk]; coreR = intMulTm[intMulTm[c, zb], kk];
    gterm = intMulTm[intMulTm[g, zb], intMulTm[zd, zh]];   (* (g·&ℤb)·(&ℤd·&ℤh) *)
    nonnegKK = EQMP[HOL`Equal`APTERM[mkComb[intLeC, intZeroR], intOfNumMulAt[h, h]],
      intOfNumNonneg[timesTm[h, h]]];   (* intLe &ℤ0 (&ℤh·&ℤh) *)
    coreLM = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[kk,
      HOL`Bool`SPEC[intMulTm[c, zb], HOL`Bool`SPEC[intMulTm[a, zd],
        HOL`Stdlib`Int`intLeMulNonnegThm]]], nonnegKK], leQR];   (* intLe (KK·(a·&ℤd))(KK·(c·&ℤb)) *)
    cL = imComm[kk, intMulTm[a, zd]]; cR = imComm[kk, intMulTm[c, zb]];
    congCore = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, cL], cR];
    core = EQMP[congCore, coreLM];   (* intLe (coreL)(coreR) *)
    addG = HOL`Bool`MP[HOL`Bool`SPEC[gterm, HOL`Bool`SPEC[coreR,
      HOL`Bool`SPEC[coreL, HOL`Stdlib`Int`intLeAddMonoThm]]], core];
        (* intLe (coreL + G)(coreR + G) *)
    rdistL = intRDistAt[intMulTm[a, zh], intMulTm[g, zb], intOfNum[d2]];
    t1eqL = TRANS[HOL`Equal`APTERM[mkComb[intMulC, intMulTm[a, zh]], intOfNumMulAt[d, h]],
      mul4SwapAt[a, zh, zd, zh]];   (* (a·&ℤh)·&ℤ(d·h) = coreL *)
    t2eqL = HOL`Equal`APTERM[mkComb[intMulC, intMulTm[g, zb]], intOfNumMulAt[d, h]];
        (* (g·&ℤb)·&ℤ(d·h) = G *)
    eqN1 = TRANS[rdistL, HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, t1eqL], t2eqL]];
        (* n1·&ℤd2 = coreL + G *)
    rdistR = intRDistAt[intMulTm[c, zh], intMulTm[g, zd], intOfNum[d1]];
    t1eqR = TRANS[HOL`Equal`APTERM[mkComb[intMulC, intMulTm[c, zh]], intOfNumMulAt[b, h]],
      mul4SwapAt[c, zh, zb, zh]];   (* (c·&ℤh)·&ℤ(b·h) = coreR *)
    t2eqR = TRANS[HOL`Equal`APTERM[mkComb[intMulC, intMulTm[g, zd]], intOfNumMulAt[b, h]],
      mul4SwapAt[g, zd, zb, zh]];   (* (g·&ℤd)·&ℤ(b·h) = G *)
    eqN2 = TRANS[rdistR, HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, t1eqR], t2eqR]];
        (* n2·&ℤd1 = coreR + G *)
    congU = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, eqN1], eqN2];
    unred = EQMP[HOL`Equal`SYM[congU], addG];   (* intLe (n1·&ℤd2)(n2·&ℤd1) *)
    notB0 = ratDenNeq0[qV]; notH0 = ratDenNeq0[uV]; notD0r = ratDenNeq0[rV];
    notD1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[h, HOL`Bool`SPEC[b, multNonzeroThm]],
      notB0], notH0];   (* ¬(b·h = 0) *)
    notQ1 = ratDenNeq0[qu];
    e1 = repAddEquivAt[qV, uV];   (* p1·&ℤd1 = n1·&ℤq1 *)
    swap1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d2, HOL`Bool`SPEC[n2, HOL`Bool`SPEC[q1, HOL`Bool`SPEC[p1,
        HOL`Bool`SPEC[d1, HOL`Bool`SPEC[n1, pairLeCongLeftThm]]]]]],
      notD1], notQ1], HOL`Equal`SYM[e1]], unred];   (* intLe (p1·&ℤd2)(n2·&ℤq1) *)
    notD2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[h, HOL`Bool`SPEC[d, multNonzeroThm]],
      notD0r], notH0];   (* ¬(d·h = 0) *)
    notQ2 = ratDenNeq0[ru];
    e2 = repAddEquivAt[rV, uV];   (* p2·&ℤd2 = n2·&ℤq2 *)
    swap2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[q2, HOL`Bool`SPEC[p2, HOL`Bool`SPEC[d2, HOL`Bool`SPEC[n2,
        HOL`Bool`SPEC[q1, HOL`Bool`SPEC[p1, pairLeCongRightThm]]]]]],
      notD2], notQ2], HOL`Equal`SYM[e2]], swap1];   (* intLe (p1·&ℤq2)(p2·&ℤq1) *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, HOL`Bool`GEN[uV,
      HOL`Bool`DISCH[ratLeTm[qV, rV],
        EQMP[HOL`Equal`SYM[unfoldRatLe[qu, ru]], swap2]]]]]
  ];

(* ⊢ ∀u q r. ratLe (&ℚ (&ℤ 0)) u ⇒ ratLe q r ⇒ ratLe (ratMul u q) (ratMul u r) *)
(* ratLe 0 u gives g = FST(REP u) ≥ 0, hence g·&ℤh ≥ 0. The unreduced *)
(* product cross-products (g·a)·&ℤ(h·d) / (g·c)·&ℤ(h·b) factor as     *)
(* (g·&ℤh)·(a·&ℤd) / (g·&ℤh)·(c·&ℤb) (mul4Swap), so UNRED is the       *)
(* hypothesis a·&ℤd ≤ c·&ℤb scaled by g·&ℤh ≥ 0; then swap to REP.     *)
ratLeMulNonnegThm =
  Module[{uV, qV, rV, a, b, c, d, g, h, zb, zd, zh, intLeC, intMulC, zr, repZr,
          fstZr, sndZr, le0uRaw, lz, z0h, lhsZeq, rz, g1, rhsGeq, congLe0,
          gNonneg, ghm, gz0, congGh, ghNonneg, leQR, uq, ur, gh, n1m, d1m, n2m,
          d2m, p1, q1, p2, q2, coreMul, s1, s2, eqM1, t1, t2, eqM2, congM,
          unred, notH0, notB0, notD0r, notD1m, notQ1, e1, swap1, notD2m, notQ2,
          e2, swap2},
    uV = mkVar["u", ratTy]; qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    a = ratNumOf[qV]; b = ratDenOf[qV]; c = ratNumOf[rV]; d = ratDenOf[rV];
    g = ratNumOf[uV]; h = ratDenOf[uV];
    zb = intOfNum[b]; zd = intOfNum[d]; zh = intOfNum[h];
    intLeC = intLeCC[]; intMulC = intMulCC[];
    zr = ratOfIntTm[intZeroR];   (* &ℚ(&ℤ0) *)
    repZr = HOL`Kernel`INST[{mkVar["q", intTy] -> intZeroR}, repRatOfIntThm];
        (* REP(&ℚ&ℤ0) = (&ℤ0, SUC0) *)
    fstZr = TRANS[HOL`Equal`APTERM[fstIN[], repZr], fstINatAt[intZeroR, oneN[]]];
    sndZr = TRANS[HOL`Equal`APTERM[sndIN[], repZr], sndINatAt[intZeroR, oneN[]]];
    le0uRaw = EQMP[unfoldRatLe[zr, uV], ASSUME[ratLeTm[zr, uV]]];
        (* intLe (FST(REP zr)·&ℤh) (g·&ℤ(SND(REP zr))) *)
    lz = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fstZr], REFL[zh]];
    z0h = TRANS[imComm[intZeroR, zh], HOL`Bool`SPEC[zh, HOL`Stdlib`Int`intMulZeroThm]];
    lhsZeq = TRANS[lz, z0h];   (* FST(REP zr)·&ℤh = &ℤ0 *)
    rz = HOL`Equal`APTERM[mkComb[intMulC, g],
      HOL`Equal`APTERM[HOL`Stdlib`Int`intOfNumConst[], sndZr]];
    g1 = HOL`Bool`SPEC[g, HOL`Stdlib`Int`intMulOneThm];
    rhsGeq = TRANS[rz, g1];   (* g·&ℤ(SND(REP zr)) = g *)
    congLe0 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, lhsZeq], rhsGeq];
    gNonneg = EQMP[congLe0, le0uRaw];   (* intLe &ℤ0 g *)
    ghm = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[g, HOL`Bool`SPEC[zh,
      HOL`Bool`SPEC[intZeroR, HOL`Stdlib`Int`intLeMulNonnegThm]]], gNonneg],
      intOfNumNonneg[h]];   (* intLe (g·&ℤ0)(g·&ℤh) *)
    gz0 = HOL`Bool`SPEC[g, HOL`Stdlib`Int`intMulZeroThm];
    congGh = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, gz0], REFL[intMulTm[g, zh]]];
    ghNonneg = EQMP[congGh, ghm];   (* intLe &ℤ0 (g·&ℤh) *)
    leQR = EQMP[unfoldRatLe[qV, rV], ASSUME[ratLeTm[qV, rV]]];   (* intLe (a·&ℤd)(c·&ℤb) *)
    uq = ratMulTm[uV, qV]; ur = ratMulTm[uV, rV];
    gh = intMulTm[g, zh];
    n1m = intMulTm[g, a]; d1m = timesTm[h, b]; n2m = intMulTm[g, c]; d2m = timesTm[h, d];
    p1 = mkComb[fstIN[], repRat[uq]]; q1 = mkComb[sndIN[], repRat[uq]];
    p2 = mkComb[fstIN[], repRat[ur]]; q2 = mkComb[sndIN[], repRat[ur]];
    coreMul = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[gh,
      HOL`Bool`SPEC[intMulTm[c, zb], HOL`Bool`SPEC[intMulTm[a, zd],
        HOL`Stdlib`Int`intLeMulNonnegThm]]], ghNonneg], leQR];
        (* intLe (gh·(a·&ℤd))(gh·(c·&ℤb)) *)
    s1 = HOL`Equal`APTERM[mkComb[intMulC, n1m], intOfNumMulAt[h, d]];
    s2 = mul4SwapAt[g, a, zh, zd];
    eqM1 = TRANS[s1, s2];   (* (g·a)·&ℤ(h·d) = gh·(a·&ℤd) *)
    t1 = HOL`Equal`APTERM[mkComb[intMulC, n2m], intOfNumMulAt[h, b]];
    t2 = mul4SwapAt[g, c, zh, zb];
    eqM2 = TRANS[t1, t2];   (* (g·c)·&ℤ(h·b) = gh·(c·&ℤb) *)
    congM = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, eqM1], eqM2];
    unred = EQMP[HOL`Equal`SYM[congM], coreMul];   (* intLe ((g·a)·&ℤ(h·d))((g·c)·&ℤ(h·b)) *)
    notH0 = ratDenNeq0[uV]; notB0 = ratDenNeq0[qV]; notD0r = ratDenNeq0[rV];
    notD1m = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[b, HOL`Bool`SPEC[h, multNonzeroThm]],
      notH0], notB0];   (* ¬(h·b = 0) *)
    notQ1 = ratDenNeq0[uq];
    e1 = repMulEquivAt[uV, qV];   (* p1·&ℤd1m = n1m·&ℤq1 *)
    swap1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[d2m, HOL`Bool`SPEC[n2m, HOL`Bool`SPEC[q1, HOL`Bool`SPEC[p1,
        HOL`Bool`SPEC[d1m, HOL`Bool`SPEC[n1m, pairLeCongLeftThm]]]]]],
      notD1m], notQ1], HOL`Equal`SYM[e1]], unred];   (* intLe (p1·&ℤd2m)(n2m·&ℤq1) *)
    notD2m = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[d, HOL`Bool`SPEC[h, multNonzeroThm]],
      notH0], notD0r];   (* ¬(h·d = 0) *)
    notQ2 = ratDenNeq0[ur];
    e2 = repMulEquivAt[uV, rV];   (* p2·&ℤd2m = n2m·&ℤq2 *)
    swap2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[q2, HOL`Bool`SPEC[p2, HOL`Bool`SPEC[d2m, HOL`Bool`SPEC[n2m,
        HOL`Bool`SPEC[q1, HOL`Bool`SPEC[p1, pairLeCongRightThm]]]]]],
      notD2m], notQ2], HOL`Equal`SYM[e2]], swap1];   (* intLe (p1·&ℤq2)(p2·&ℤq1) *)
    HOL`Bool`GEN[uV, HOL`Bool`GEN[qV, HOL`Bool`GEN[rV,
      HOL`Bool`DISCH[ratLeTm[zr, uV], HOL`Bool`DISCH[ratLeTm[qV, rV],
        EQMP[HOL`Equal`SYM[unfoldRatLe[uq, ur]], swap2]]]]]]
  ];

End[];
EndPackage[];
