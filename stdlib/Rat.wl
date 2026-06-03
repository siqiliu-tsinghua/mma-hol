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

(* exDiv (exact quotient) migrated to Num.wl — exDivConst / exDivDefThm /
   exDivThm / exDivOneThm / exDivZeroThm are now public HOL`Stdlib`Num` symbols.
   The gcd / divisibility / Bezout / coprime ℕ lemmas (dividesZeroImpZero,
   dividesOne, gcdOneRight, dividesMultBothLeft, gcdNonzeroFromRight,
   coprimeReduced, dividesAntisym, gcdZeroRight, gcdRec, bezoutNat,
   coprimeDividesProduct, gcdComm, gcdZeroLeft, gcdSelf, exDivSelf) are now
   public HOL`Stdlib`FTA` symbols. *)


ratCanonConst::usage  = "ratCanonConst[] — ratCanon : int × num → int × num, reduces a fraction to lowest terms: ratCanon p = (intDivNat (FST p) g, exDiv (SND p) g) with g = gcd (intNatAbs (FST p)) (SND p).";
ratCanonDefThm::usage = "ratCanonDefThm — ⊢ ratCanon = (λp. (intDivNat (FST p) g, exDiv (SND p) g)) where g = gcd (intNatAbs (FST p)) (SND p).";
ratCanonLandsThm::usage = "ratCanonLandsThm — ⊢ ∀p. ¬ (SND p = 0) ⇒ RAT_REP (ratCanon p). gcd-reduction of a positive-denominator fraction is canonical.";
ratCanonIdThm::usage = "ratCanonIdThm — ⊢ ∀p. RAT_REP p ⇒ ratCanon p = p. ratCanon is the identity on already-canonical reps.";

ratRepRepThm::usage = "ratRepRepThm — ⊢ RAT_REP (REP_rat q) (q free): REP_rat lands in the carve. Mirror of Int's intRepRepThm.";

ratAddConst::usage  = "ratAddConst[] — ratAdd : rat → rat → rat. (a,b)+(c,d) = ratCanon (a·d + c·b, b·d) over the int×num reps.";
ratAddDefThm::usage = "ratAddDefThm — ⊢ ratAdd = (λq r. ABS_rat (ratCanon (intAdd (intMul (FST(REP q)) (&ℤ(SND(REP r)))) (intMul (FST(REP r)) (&ℤ(SND(REP q)))), SND(REP q) * SND(REP r)))).";
repRatAddThm::usage = "repRatAddThm — ⊢ ∀q r. REP_rat (ratAdd q r) = ratCanon (intAdd (intMul (FST(REP q)) (&ℤ(SND(REP r)))) (intMul (FST(REP r)) (&ℤ(SND(REP q)))), SND(REP q) * SND(REP r)). REP of a sum is the reduced sum-pair (lands via ratCanonLandsThm).";
ratAddCommThm::usage = "ratAddCommThm — ⊢ ∀q r. ratAdd q r = ratAdd r q (additive commutativity).";
ratAddZeroThm::usage = "ratAddZeroThm — ⊢ ∀q. ratAdd q (&ℚ (&ℤ 0)) = q (right additive identity, the rational 0 = 0/1).";

ratNegConst::usage  = "ratNegConst[] — ratNeg : rat → rat, negation. ratNeg q = ABS_rat (intNeg (FST(REP q)), SND(REP q)) — negate the numerator; stays canonical (|−a|=|a|).";
ratNegDefThm::usage = "ratNegDefThm — ⊢ ratNeg = (λq. ABS_rat (intNeg (FST(REP q)), SND(REP q))).";
repRatNegThm::usage = "repRatNegThm — ⊢ ∀q. REP_rat (ratNeg q) = (intNeg (FST(REP q)), SND(REP q)). Negation lands in the carve with no reduction.";
ratEqCrossThm::usage = "ratEqCrossThm — ⊢ ∀q r. (q = r) = (intMul (FST(REP_rat q)) (&ℤ (SND(REP_rat r))) = intMul (FST(REP_rat r)) (&ℤ (SND(REP_rat q)))). Lowest-terms uniqueness via cross-multiplication.";
ratCanonZeroNumThm::usage = "ratCanonZeroNumThm — ⊢ ∀m. ¬ (m = 0) ⇒ ratCanon (&ℤ 0, m) = (&ℤ 0, SUC 0). The rational 0/m reduces to 0/1.";
ratAddNegThm::usage = "ratAddNegThm — ⊢ ∀q. ratAdd q (ratNeg q) = &ℚ (&ℤ 0). Right additive inverse.";


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

ratCanonSelfThm::usage = "ratCanonSelfThm — ⊢ ∀m. ¬ (m = 0) ⇒ ratCanon (&ℤ m, m) = (&ℤ (SUC 0), SUC 0). The rational m/m reduces to 1/1.";
ratNumNonzeroThm::usage = "ratNumNonzeroThm — ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ ¬ (FST (REP_rat q) = &ℤ 0). A nonzero rational has nonzero numerator.";
ratInvConst::usage  = "ratInvConst[] — ratInv : rat → rat, multiplicative inverse. ratInv q = ABS_rat (ratCanon (intMul a (&ℤ b), intNatAbs a * intNatAbs a)), (a,b) = REP q; sign carried by a. ratInv (&ℚ&ℤ0) is junk.";
ratInvDefThm::usage = "ratInvDefThm — ⊢ ratInv = (λq. ABS_rat (ratCanon (intMul (FST(REP q)) (&ℤ (SND(REP q))), intNatAbs (FST(REP q)) * intNatAbs (FST(REP q))))).";
repRatInvThm::usage = "repRatInvThm — ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ REP_rat (ratInv q) = ratCanon (intMul (FST(REP q)) (&ℤ (SND(REP q))), intNatAbs (FST(REP q)) * intNatAbs (FST(REP q))).";
ratMulInvThm::usage = "ratMulInvThm — ⊢ ∀q. ¬ (q = &ℚ (&ℤ 0)) ⇒ ratMul q (ratInv q) = &ℚ (&ℤ (SUC 0)). Right multiplicative inverse — ℚ is a FIELD.";


ratLeConst::usage  = "ratLeConst[] — ratLe : rat → rat → bool, order. ratLe q r ⟺ intLe (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q)))) — cross-multiplication with positive denominators.";
ratLeDefThm::usage = "ratLeDefThm — ⊢ ratLe = (λq r. intLe (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q))))).";
ratLeReflThm::usage = "ratLeReflThm — ⊢ ∀q. ratLe q q.";
ratLeAntisymThm::usage = "ratLeAntisymThm — ⊢ ∀q r. ratLe q r ⇒ ratLe r q ⇒ q = r.";
ratLeTransThm::usage = "ratLeTransThm — ⊢ ∀q r v. ratLe q r ⇒ ratLe r v ⇒ ratLe q v.";
ratLeTotalThm::usage = "ratLeTotalThm — ⊢ ∀q r. ratLe q r ∨ ratLe r q.";
ratLtConst::usage  = "ratLtConst[] — ratLt : rat → rat → bool, strict order. ratLt q r ⟺ intLt (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q)))).";
ratLtDefThm::usage = "ratLtDefThm — ⊢ ratLt = (λq r. intLt (intMul (FST(REP q)) (&ℤ (SND(REP r)))) (intMul (FST(REP r)) (&ℤ (SND(REP q))))).";
ratLtNotLeThm::usage = "ratLtNotLeThm — ⊢ ∀q r. ratLt q r = ¬ (ratLe r q).";

ratLeAddMonoThm::usage = "ratLeAddMonoThm — ⊢ ∀q r u. ratLe q r ⇒ ratLe (ratAdd q u) (ratAdd r u). Additive monotonicity of the rational order.";
ratLeMulNonnegThm::usage = "ratLeMulNonnegThm — ⊢ ∀u q r. ratLe (&ℚ (&ℤ 0)) u ⇒ ratLe q r ⇒ ratLe (ratMul u q) (ratMul u r). Monotonicity of ratMul by a nonnegative factor.";

ratOfIntAddThm::usage = "ratOfIntAddThm — ⊢ ∀a b. &ℚ (intAdd a b) = ratAdd (&ℚ a) (&ℚ b). &ℚ is an additive homomorphism.";
ratOfIntMulThm::usage = "ratOfIntMulThm — ⊢ ∀a b. &ℚ (intMul a b) = ratMul (&ℚ a) (&ℚ b). &ℚ is a multiplicative homomorphism.";
ratOfIntLeThm::usage = "ratOfIntLeThm — ⊢ ∀a b. ratLe (&ℚ a) (&ℚ b) = intLe a b. &ℚ is an order embedding.";

ratAddSubCancelThm::usage = "ratAddSubCancelThm — ⊢ ∀q u. ratAdd (ratAdd q u) (ratNeg u) = q. Adding then subtracting cancels.";
ratLtAddMonoThm::usage = "ratLtAddMonoThm — ⊢ ∀q r u. ratLt q r ⇒ ratLt (ratAdd q u) (ratAdd r u). Strict additive monotonicity.";
ratLtMulPosCancelThm::usage = "ratLtMulPosCancelThm — ⊢ ∀x y u. ratLe (&ℚ (&ℤ 0)) u ⇒ ratLt (ratMul x u) (ratMul y u) ⇒ ratLt x y. Cancellation of a nonnegative right factor in a strict inequality.";
ratMulTwoThm::usage = "ratMulTwoThm — ⊢ ∀x. ratMul x (&ℚ (&ℤ (SUC (SUC 0)))) = ratAdd x x. Multiplying by the rational 2 doubles.";
ratDenseThm::usage = "ratDenseThm — ⊢ ∀q r. ratLt q r ⇒ ratLt q (ratMul (ratAdd q r) (ratInv (&ℚ (&ℤ (SUC (SUC 0)))))) ∧ ratLt (ratMul (ratAdd q r) (ratInv (&ℚ (&ℤ (SUC (SUC 0)))))) r. ℚ is densely ordered: the midpoint ½(q+r) lies strictly between q and r.";

Begin["`Private`"];

numTy = mkType["num", {}];
intTy = mkType["int", {}];
boolT = mkType["bool", {}];

zeroN[] := HOL`Stdlib`Num`zeroConst[];
sucC[]  := HOL`Stdlib`Num`sucConst[];
oneN[]  := mkComb[sucC[], zeroN[]];           (* SUC 0 *)

plusTm[a_, b_]  := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], a], b];
timesTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`timesConst[], a], b];
gcdTm[a_, b_]   := mkComb[mkComb[HOL`Stdlib`FTA`gcdConst[], a], b];

andC[] := mkConst["∧", tyFun[boolT, tyFun[boolT, boolT]]];
andTm[a_, b_] := mkComb[mkComb[andC[], a], b];
notC[] := mkConst["¬", tyFun[boolT, boolT]];
notTm[a_] := mkComb[notC[], a];


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

(* small term constructors still used by the surviving rat proofs *)
orCR[]         := mkConst["∨", tyFun[boolT, tyFun[boolT, boolT]]];
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


(* exDiv (exact quotient) migrated to Num.wl; exDivConst / exDivDefThm /
   exDivThm / exDivOneThm / exDivZeroThm are now public HOL`Stdlib`Num`
   symbols. Rat keeps only this exDivTm term-builder (binds the public
   constant), used by ratCanon below. *)
exDivTm[nT_, gT_] := mkComb[mkComb[exDivConst[], nT], gT];

(* ¬(SUC 0 = 0): a local one-liner Rat still needs (the gcd/divisibility
   lemmas that used it moved to FTA, where it is a private helper). *)
oneNotZeroThm = HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`sucNotZeroThm];



(* ============================================================ *)
(* intNatAbs / intDivNat / int-magnitude lemmas migrated to     *)
(* Int.wl (2026-06). Rat keeps only the term-builder helpers     *)
(* its surviving ratCanon / ratInv code uses; the constants and  *)
(* theorems are now public HOL`Stdlib`Int` symbols.             *)
(* ============================================================ *)

absIntC[] := HOL`Stdlib`Int`absIntConst[];
numPairConsC[] := mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]];
intDivNatTm[zT_, gT_] := mkComb[mkComb[intDivNatConst[], zT], gT];

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
      HOL`Equal`APTERM[HOL`Stdlib`FTA`gcdConst[], naFst], sndEq]; (* gcd(intNatAbs(FST p0))(SND p0) = gcd 0 (SUC 0) *)
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
      HOL`Equal`APTERM[HOL`Stdlib`FTA`gcdConst[], naFst], sndEq]; (* gcd .. = gcd (intNatAbs q) (SUC 0) *)
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
    divGB = HOL`Bool`SPEC[bTm, HOL`Bool`SPEC[aTm, HOL`Stdlib`FTA`gcdDividesRightThm]];  (* divides g b *)
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
      HOL`Equal`APTERM[HOL`Stdlib`FTA`gcdConst[], naFstCanonEq], sndCanon];
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

(* multNonzeroThm migrated to Num.wl (public HOL`Stdlib`Num`multNonzeroThm). *)

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
      HOL`Equal`APTERM[HOL`Stdlib`FTA`gcdConst[], naFstEq], sndPairEq];
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
(* intNatAbsMulOfNumThm — |z · &ℤ n| = |z| · n (proper home      *)
(* Int.wl). REP(z·&ℤn) = intCanon(z1·n, z2·n); since REP z is     *)
(* canonical (z1=0 ∨ z2=0), one of z1·n, z2·n is 0, so the pair   *)
(* is already canonical and intCanon is the identity — no monus.  *)
(* ============================================================ *)

(* ⊢ ∀z n. intNatAbs (intMul z (&ℤ n)) = intNatAbs z * n *)

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



(* ⊢ ∀g. ¬ (g = 0) ⇒ intDivNat (&ℤ 0) g = &ℤ 0 *)

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
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`FTA`gcdConst[], naFstP], sndPEq],
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
    gDivB = HOL`Bool`SPEC[b, HOL`Bool`SPEC[aTm, HOL`Stdlib`FTA`gcdDividesRightThm]];
    gDivNA = HOL`Bool`SPEC[b, HOL`Bool`SPEC[aTm, HOL`Stdlib`FTA`gcdDividesLeftThm]];
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


(* ⊢ ∀z. intMul z z = &ℤ (intNatAbs z * intNatAbs z) *)

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
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`FTA`gcdConst[], naFstP], sndPEq],
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
    gcdArg = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`FTA`gcdConst[], naA0], b];
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

(* swap the RIGHT cross-operand for a cross-equivalent one (cancel &ℤm2) *)

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

(* ============================================================ *)
(* Stage g — &ℚ : int → rat is a ring/order homomorphism.       *)
(* REP(&ℚ z) = (z, SUC 0) is canonical, so the operation pair    *)
(* collapses (intMulOne on the &ℤ(SUC0) factors, SUC0·SUC0=SUC0)  *)
(* and ratCanonId returns it unchanged; order needs no canon.    *)
(* ============================================================ *)

(* {FST(REP(&ℚ z)) = z, SND(REP(&ℚ z)) = SUC 0} *)
repRatFstSnd[zTm_] :=
  Module[{rep},
    rep = HOL`Kernel`INST[{mkVar["q", intTy] -> zTm}, repRatOfIntThm];
    {TRANS[HOL`Equal`APTERM[fstIN[], rep], fstINatAt[zTm, oneN[]]],
     TRANS[HOL`Equal`APTERM[sndIN[], rep], sndINatAt[zTm, oneN[]]]}];

(* ⊢ ∀a b. &ℚ (intAdd a b) = ratAdd (&ℚ a) (&ℚ b) *)
ratOfIntAddThm =
  Module[{aV, bV, qa, qb, fa, sa, fb, sb, intMulC, intAddCl, timesC, intOfNumC,
          t1eq, t2eq, numEq, denomEq, pairEq, sumPairT, lands, canonId, repAddExp,
          repR, repL, repEq},
    aV = mkVar["a", intTy]; bV = mkVar["b", intTy];
    qa = ratOfIntTm[aV]; qb = ratOfIntTm[bV];
    intMulC = intMulCC[]; intAddCl = intAddC[];
    timesC = HOL`Stdlib`Num`timesConst[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    {fa, sa} = repRatFstSnd[aV]; {fb, sb} = repRatFstSnd[bV];
    t1eq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fa],
        HOL`Equal`APTERM[intOfNumC, sb]], HOL`Bool`SPEC[aV, HOL`Stdlib`Int`intMulOneThm]];
        (* FST(REP qa)·&ℤ(SND(REP qb)) = a *)
    t2eq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fb],
        HOL`Equal`APTERM[intOfNumC, sa]], HOL`Bool`SPEC[bV, HOL`Stdlib`Int`intMulOneThm]];
    numEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddCl, t1eq], t2eq];   (* = intAdd a b *)
    denomEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sa], sb],
      HOL`Bool`SPEC[oneN[], HOL`Stdlib`Num`oneTimesEqThm]];   (* SUC0·SUC0 = SUC0 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denomEq];
    sumPairT = ratPairCons[intAddTm[aV, bV], oneN[]];
    lands = HOL`Kernel`INST[{mkVar["q", intTy] -> intAddTm[aV, bV]}, ratRepOneDenomThm];
    canonId = HOL`Bool`MP[HOL`Bool`SPEC[sumPairT, ratCanonIdThm], lands];
    repAddExp = HOL`Bool`SPEC[qb, HOL`Bool`SPEC[qa, repRatAddThm]];
    repR = TRANS[repAddExp, TRANS[HOL`Equal`APTERM[ratCanonConst[], pairEq], canonId]];
        (* REP(ratAdd qa qb) = (intAdd a b, SUC0) *)
    repL = HOL`Kernel`INST[{mkVar["q", intTy] -> intAddTm[aV, bV]}, repRatOfIntThm];
    repEq = TRANS[repL, HOL`Equal`SYM[repR]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      ratEqFromRepEq[repEq, ratOfIntTm[intAddTm[aV, bV]], ratAddTm[qa, qb]]]]
  ];

(* ⊢ ∀a b. &ℚ (intMul a b) = ratMul (&ℚ a) (&ℚ b) *)
ratOfIntMulThm =
  Module[{aV, bV, qa, qb, fa, sa, fb, sb, intMulC, timesC, numEq, denomEq,
          pairEq, prodPairT, lands, canonId, repMulExp, repR, repL, repEq},
    aV = mkVar["a", intTy]; bV = mkVar["b", intTy];
    qa = ratOfIntTm[aV]; qb = ratOfIntTm[bV];
    intMulC = intMulCC[]; timesC = HOL`Stdlib`Num`timesConst[];
    {fa, sa} = repRatFstSnd[aV]; {fb, sb} = repRatFstSnd[bV];
    numEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fa], fb];   (* FST·FST = intMul a b *)
    denomEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sa], sb],
      HOL`Bool`SPEC[oneN[], HOL`Stdlib`Num`oneTimesEqThm]];
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratPairConsC[], numEq], denomEq];
    prodPairT = ratPairCons[intMulTm[aV, bV], oneN[]];
    lands = HOL`Kernel`INST[{mkVar["q", intTy] -> intMulTm[aV, bV]}, ratRepOneDenomThm];
    canonId = HOL`Bool`MP[HOL`Bool`SPEC[prodPairT, ratCanonIdThm], lands];
    repMulExp = HOL`Bool`SPEC[qb, HOL`Bool`SPEC[qa, repRatMulThm]];
    repR = TRANS[repMulExp, TRANS[HOL`Equal`APTERM[ratCanonConst[], pairEq], canonId]];
    repL = HOL`Kernel`INST[{mkVar["q", intTy] -> intMulTm[aV, bV]}, repRatOfIntThm];
    repEq = TRANS[repL, HOL`Equal`SYM[repR]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      ratEqFromRepEq[repEq, ratOfIntTm[intMulTm[aV, bV]], ratMulTm[qa, qb]]]]
  ];

(* ⊢ ∀a b. ratLe (&ℚ a) (&ℚ b) = intLe a b *)
ratOfIntLeThm =
  Module[{aV, bV, qa, qb, fa, sa, fb, sb, intMulC, intLeC, intOfNumC, lhsEq,
          rhsEq, leqEq},
    aV = mkVar["a", intTy]; bV = mkVar["b", intTy];
    qa = ratOfIntTm[aV]; qb = ratOfIntTm[bV];
    intMulC = intMulCC[]; intLeC = intLeCC[]; intOfNumC = HOL`Stdlib`Int`intOfNumConst[];
    {fa, sa} = repRatFstSnd[aV]; {fb, sb} = repRatFstSnd[bV];
    lhsEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fa],
        HOL`Equal`APTERM[intOfNumC, sb]], HOL`Bool`SPEC[aV, HOL`Stdlib`Int`intMulOneThm]];
        (* FST(REP qa)·&ℤ(SND(REP qb)) = a *)
    rhsEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intMulC, fb],
        HOL`Equal`APTERM[intOfNumC, sa]], HOL`Bool`SPEC[bV, HOL`Stdlib`Int`intMulOneThm]];
    leqEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC, lhsEq], rhsEq];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, TRANS[unfoldRatLe[qa, qb], leqEq]]]
  ];

(* ============================================================ *)
(* Stage g — density. Strict-order arithmetic + the midpoint     *)
(* identity ½(q+r)·2 = q+r give q < ½(q+r) < r from q < r.       *)
(* ============================================================ *)

(* ⊢ ∀q u. ratAdd (ratAdd q u) (ratNeg u) = q *)
ratAddSubCancelThm =
  Module[{qV, uV, assoc, negEq, addZ},
    qV = mkVar["q", ratTy]; uV = mkVar["u", ratTy];
    assoc = HOL`Bool`SPEC[ratNegTm[uV], HOL`Bool`SPEC[uV, HOL`Bool`SPEC[qV, ratAddAssocThm]]];
    negEq = HOL`Bool`SPEC[uV, ratAddNegThm];   (* ratAdd u (ratNeg u) = &ℚ&ℤ0 *)
    addZ = HOL`Bool`SPEC[qV, ratAddZeroThm];   (* ratAdd q (&ℚ&ℤ0) = q *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[uV,
      TRANS[assoc, TRANS[HOL`Equal`APTERM[mkComb[ratAddConst[], qV], negEq], addZ]]]]
  ];

(* ⊢ ∀q r u. ratLt q r ⇒ ratLt (ratAdd q u) (ratAdd r u) *)
ratLtAddMonoThm =
  Module[{qV, rV, uV, qu, ru, ltDef1, notLeRQ, assumeLe, leMono, subR, subQ,
          congLe, leRQ, contra, notLe2, ltDef2},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy]; uV = mkVar["u", ratTy];
    qu = ratAddTm[qV, uV]; ru = ratAddTm[rV, uV];
    ltDef1 = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[qV, ratLtNotLeThm]];
    notLeRQ = EQMP[ltDef1, ASSUME[ratLtTm[qV, rV]]];   (* ¬(ratLe r q) *)
    assumeLe = ASSUME[ratLeTm[ru, qu]];
    leMono = HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[uV], HOL`Bool`SPEC[qu,
      HOL`Bool`SPEC[ru, ratLeAddMonoThm]]], assumeLe];
        (* ratLe (ratAdd (r+u)(-u)) (ratAdd (q+u)(-u)) *)
    subR = HOL`Bool`SPEC[uV, HOL`Bool`SPEC[rV, ratAddSubCancelThm]];
    subQ = HOL`Bool`SPEC[uV, HOL`Bool`SPEC[qV, ratAddSubCancelThm]];
    congLe = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeConst[], subR], subQ];
    leRQ = EQMP[congLe, leMono];   (* ratLe r q *)
    contra = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeRQ], leRQ];
    notLe2 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[ratLeTm[ru, qu], contra]];
    ltDef2 = HOL`Bool`SPEC[ru, HOL`Bool`SPEC[qu, ratLtNotLeThm]];
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV, HOL`Bool`GEN[uV,
      HOL`Bool`DISCH[ratLtTm[qV, rV], EQMP[HOL`Equal`SYM[ltDef2], notLe2]]]]]
  ];

(* ⊢ ∀x y u. ratLe (&ℚ&ℤ0) u ⇒ ratLt (ratMul x u) (ratMul y u) ⇒ ratLt x y *)
ratLtMulPosCancelThm =
  Module[{xV, yV, uV, xu, yu, z0, nonneg, ltDef1, notLeYUXU, assumeLeYX,
          leMonoUV, commYU, commXU, congComm, leYUXU, contra, notLeYX, ltDef2},
    xV = mkVar["x", ratTy]; yV = mkVar["y", ratTy]; uV = mkVar["u", ratTy];
    z0 = ratOfIntTm[intZeroR];
    xu = ratMulTm[xV, uV]; yu = ratMulTm[yV, uV];
    nonneg = ASSUME[ratLeTm[z0, uV]];
    ltDef1 = HOL`Bool`SPEC[yu, HOL`Bool`SPEC[xu, ratLtNotLeThm]];   (* ratLt (x·u)(y·u) = ¬(ratLe (y·u)(x·u)) *)
    notLeYUXU = EQMP[ltDef1, ASSUME[ratLtTm[xu, yu]]];
    assumeLeYX = ASSUME[ratLeTm[yV, xV]];
    leMonoUV = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV,
      HOL`Bool`SPEC[uV, ratLeMulNonnegThm]]], nonneg], assumeLeYX];
        (* ratLe (u·y)(u·x) *)
    commYU = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[uV, ratMulCommThm]];   (* u·y = y·u *)
    commXU = HOL`Bool`SPEC[xV, HOL`Bool`SPEC[uV, ratMulCommThm]];
    congComm = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeConst[], commYU], commXU];
    leYUXU = EQMP[congComm, leMonoUV];   (* ratLe (y·u)(x·u) *)
    contra = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeYUXU], leYUXU];
    notLeYX = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[ratLeTm[yV, xV], contra]];
    ltDef2 = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, ratLtNotLeThm]];   (* ratLt x y = ¬(ratLe y x) *)
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[uV,
      HOL`Bool`DISCH[ratLeTm[z0, uV], HOL`Bool`DISCH[ratLtTm[xu, yu],
        EQMP[HOL`Equal`SYM[ltDef2], notLeYX]]]]]]
  ];

(* ⊢ ∀x. ratMul x (&ℚ&ℤ2) = ratAdd x x  (the rational 2 = 1+1 doubles) *)
ratMulTwoThm =
  Module[{xV, twoT, oneRatT, intTwoT, oneAddOne, ionAdd, intAddEq, eA, eB,
          twoEq, distrib, mulOne},
    xV = mkVar["x", ratTy];
    intTwoT = intOfNum[mkComb[sucC[], oneN[]]];          (* &ℤ(SUC(SUC0)) *)
    twoT = ratOfIntTm[intTwoT]; oneRatT = ratOfIntTm[intOfNum[oneN[]]];
    oneAddOne = TRANS[HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[oneN[], HOL`Stdlib`Num`plusSucEqThm]],
      HOL`Equal`APTERM[sucC[], HOL`Bool`SPEC[oneN[], HOL`Stdlib`Num`plusZeroEqThm]]];
        (* SUC0 + SUC0 = SUC(SUC0) *)
    ionAdd = HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[oneN[], HOL`Stdlib`Int`intOfNumAddThm]];
        (* &ℤ(SUC0+SUC0) = intAdd (&ℤ1)(&ℤ1) *)
    intAddEq = TRANS[HOL`Equal`SYM[ionAdd],
      HOL`Equal`APTERM[HOL`Stdlib`Int`intOfNumConst[], oneAddOne]];   (* intAdd(&ℤ1)(&ℤ1) = &ℤ2 *)
    eA = HOL`Equal`APTERM[ratOfIntConst[], HOL`Equal`SYM[intAddEq]];   (* &ℚ&ℤ2 = &ℚ(intAdd(&ℤ1)(&ℤ1)) *)
    eB = HOL`Bool`SPEC[intOfNum[oneN[]], HOL`Bool`SPEC[intOfNum[oneN[]], ratOfIntAddThm]];
        (* &ℚ(intAdd(&ℤ1)(&ℤ1)) = ratAdd (&ℚ&ℤ1)(&ℚ&ℤ1) *)
    twoEq = TRANS[eA, eB];   (* &ℚ&ℤ2 = ratAdd oneRat oneRat *)
    distrib = HOL`Bool`SPEC[oneRatT, HOL`Bool`SPEC[oneRatT, HOL`Bool`SPEC[xV, ratMulDistribThm]]];
        (* ratMul x (ratAdd oneRat oneRat) = ratAdd (ratMul x oneRat)(ratMul x oneRat) *)
    mulOne = HOL`Bool`SPEC[xV, ratMulOneThm];   (* ratMul x oneRat = x *)
    HOL`Bool`GEN[xV,
      TRANS[HOL`Equal`APTERM[mkComb[ratMulConst[], xV], twoEq],
        TRANS[distrib, HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratAddConst[], mulOne], mulOne]]]]
  ];

(* ⊢ ∀q r. ratLt q r ⇒ ratLt q (½(q+r)) ∧ ratLt (½(q+r)) r,  ½(q+r) = (q+r)·inv 2 *)
ratDenseThm =
  Module[{qV, rV, intTwoT, twoT, halfT, qr, mT, z0rat, hyp, leInt, ratLeEq,
          twoNonneg, notSuc, intTwoNeq, inj, twoNeqZero, qTwoEq, rTwoEq, assoc,
          commHT, invEq, halfTwoEq, mulOneQr, mTwoEq, ltAddQ, commRQ, congQQ,
          ltQQ, congLt1, ltQt, qLtM, ltQRRR, congLt2, ltMt, mLtR},
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    intTwoT = intOfNum[mkComb[sucC[], oneN[]]];
    twoT = ratOfIntTm[intTwoT]; halfT = ratInvTm[twoT];
    qr = ratAddTm[qV, rV]; mT = ratMulTm[qr, halfT];
    z0rat = ratOfIntTm[intZeroR];
    hyp = ASSUME[ratLtTm[qV, rV]];
    (* two > 0 *)
    leInt = intOfNumNonneg[mkComb[sucC[], oneN[]]];   (* intLe (&ℤ0) intTwoT *)
    ratLeEq = HOL`Bool`SPEC[intTwoT, HOL`Bool`SPEC[intZeroR, ratOfIntLeThm]];
    twoNonneg = EQMP[HOL`Equal`SYM[ratLeEq], leInt];   (* ratLe (&ℚ&ℤ0) two *)
    notSuc = HOL`Bool`SPEC[oneN[], HOL`Stdlib`Num`sucNotZeroThm];   (* ¬(SUC(SUC0)=0) *)
    intTwoNeq = intOfNumNeqZero[notSuc, mkComb[sucC[], oneN[]]];   (* ¬(intTwoT = &ℤ0) *)
    inj = HOL`Bool`SPEC[intZeroR, HOL`Bool`SPEC[intTwoT, ratOfIntInjThm]];
        (* &ℚ intTwoT = &ℚ&ℤ0 ⇒ intTwoT = &ℤ0 *)
    twoNeqZero = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[twoT, z0rat],
      HOL`Bool`MP[HOL`Bool`NOTELIM[intTwoNeq], HOL`Bool`MP[inj, ASSUME[mkEq[twoT, z0rat]]]]]];
        (* ¬(two = &ℚ&ℤ0) *)
    qTwoEq = HOL`Bool`SPEC[qV, ratMulTwoThm];   (* ratMul q two = ratAdd q q *)
    rTwoEq = HOL`Bool`SPEC[rV, ratMulTwoThm];   (* ratMul r two = ratAdd r r *)
    (* midpoint: ratMul m two = ratAdd q r *)
    assoc = HOL`Bool`SPEC[twoT, HOL`Bool`SPEC[halfT, HOL`Bool`SPEC[qr, ratMulAssocThm]]];
        (* ratMul (ratMul qr half) two = ratMul qr (ratMul half two) *)
    commHT = HOL`Bool`SPEC[twoT, HOL`Bool`SPEC[halfT, ratMulCommThm]];   (* half·two = two·half *)
    invEq = HOL`Bool`MP[HOL`Bool`SPEC[twoT, ratMulInvThm], twoNeqZero];   (* two·(inv two) = &ℚ&ℤ1 *)
    halfTwoEq = TRANS[commHT, invEq];   (* half·two = &ℚ&ℤ1 *)
    mulOneQr = HOL`Bool`SPEC[qr, ratMulOneThm];   (* ratMul qr (&ℚ&ℤ1) = qr *)
    mTwoEq = TRANS[assoc, TRANS[HOL`Equal`APTERM[mkComb[ratMulConst[], qr], halfTwoEq],
      mulOneQr]];   (* ratMul m two = ratAdd q r *)
    (* q < m : from q+q < q+r and cancellation *)
    ltAddQ = HOL`Bool`MP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[rV, HOL`Bool`SPEC[qV,
      ratLtAddMonoThm]]], hyp];   (* ratLt (q+q)(r+q) *)
    commRQ = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[rV, ratAddCommThm]];   (* r+q = q+r *)
    congQQ = HOL`Equal`APTERM[mkComb[ratLtConst[], ratAddTm[qV, qV]], commRQ];
        (* ratLt (q+q)(r+q) = ratLt (q+q)(q+r) *)
    ltQQ = EQMP[congQQ, ltAddQ];   (* ratLt (q+q)(q+r) *)
    congLt1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtConst[], qTwoEq], mTwoEq];
        (* ratLt (q·two)(m·two) = ratLt (q+q)(q+r) *)
    ltQt = EQMP[HOL`Equal`SYM[congLt1], ltQQ];   (* ratLt (q·two)(m·two) *)
    qLtM = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[twoT, HOL`Bool`SPEC[mT,
      HOL`Bool`SPEC[qV, ratLtMulPosCancelThm]]], twoNonneg], ltQt];   (* ratLt q m *)
    (* m < r : from q+r < r+r and cancellation *)
    ltQRRR = HOL`Bool`MP[HOL`Bool`SPEC[rV, HOL`Bool`SPEC[rV, HOL`Bool`SPEC[qV,
      ratLtAddMonoThm]]], hyp];   (* ratLt (q+r)(r+r) *)
    congLt2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtConst[], mTwoEq], rTwoEq];
        (* ratLt (m·two)(r·two) = ratLt (q+r)(r+r) *)
    ltMt = EQMP[HOL`Equal`SYM[congLt2], ltQRRR];   (* ratLt (m·two)(r·two) *)
    mLtR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[twoT, HOL`Bool`SPEC[rV,
      HOL`Bool`SPEC[mT, ratLtMulPosCancelThm]]], twoNonneg], ltMt];   (* ratLt m r *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[rV,
      HOL`Bool`DISCH[ratLtTm[qV, rV], HOL`Bool`CONJ[qLtM, mLtR]]]]
  ];

End[];
EndPackage[];
