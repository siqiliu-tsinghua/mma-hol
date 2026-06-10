(* M7-7 / stdlib/Real/Mul.wl — Stage D: ℝ multiplication (Rudin sign-case).

   Part of the stdlib/Real/ folder (PLAN §8.1): shares context HOL`Stdlib`Real`
   with Cut.wl / RatAux.wl / Field.wl.  Loads LAST in the folder
   (Cut → RatAux → Field → Mul); consumes the ℚ mul-order layer from RatAux
   (ratLtMulPosThm, ratMulRightCancelThm, ratNatMulGtThm, ratArchThm, …), the
   additive group from Field (realAdd, realNeg, realAddNegThm, realEqFromRepEq),
   and the cut vocabulary from Cut (REP_real, IS_CUT, realLe/realLt, the
   realNonempty/Proper/DownClosed/Open accessors).

   ============================================================================
   Stage D design — 3 layers (PLAN Phase-3 "Stage D realMul 架构";
   GPT-5.5 review + ../archive/tautology Lean post-mortem).  Isolated in this
   file precisely so the hardest stage's proofs don't entangle with Field.
   ============================================================================

   (1) NON-NEGATIVE CORE  realNnMul x y
         cut body  { r | r < 0  ∨  ∃p q. REP_real x p ∧ REP_real y q
                                         ∧ 0 < p ∧ 0 < q ∧ ratLt r (p·q) }
       · STRICT  r < p·q  (NOT Lean's  r ≤ p·q): openness is then a pure
         ratDenseThm midpoint — no a.no_max "bump p to p'" sub-case
         (cf. Lean Cut/Mul.lean 108–127, the cost of ≤).
       · the  r < 0  disjunct keeps the product a cut when x or y is 0 (the
         positive-product set is then empty, but {r<0} = the cut of 0).
       · bounded/proper: a non-negative cut can still BE 0 (= {r<0}, no
         positive member) ⇒ clamp the upper bound with COND
         (if 0<u then u else 0); bound = u_x'·u_y' + 1.  [Lean Mul.lean 26–73]
       · ALL semantic theorems carry  0≤x ∧ 0≤y  and are named  …NonnegThm.
         Unconditional assoc/distrib are FALSE off the non-negative domain
         (e.g. x,y>0, z<0, y+z<0 ⇒ realNnMul x (y+z)=0 ≠ x·y).

   (2) SIGNED WRAPPER  realMul x y  via COND on  0≤x / 0≤y  (BINARY split —
       zero folds into the non-negative branch; NOT a zero/pos/neg ternary):
         0≤x ∧ 0≤y →  realNnMul x y
         0≤x ∧ ¬   → realNeg (realNnMul x (realNeg y))
         ¬   ∧ 0≤y → realNeg (realNnMul (realNeg x) y)
         ¬   ∧ ¬   →  realNnMul (realNeg x) (realNeg y)
       + a realMulSignCases theorem-builder so comm/assoc/distrib do not each
       hand-write the case tree.  [Lean's ternary → 27-case, ~93-line
       mul_assoc (Cut/MulComm.lean) is the cautionary tale this avoids.]

   (3) ABSTRACT ORDERED-FIELD SURFACE  realMul{Comm,Assoc,One,Zero,Distrib}Thm,
       realLeMulNonnegThm, realLtMulPosThm — REAL_ARITH / downstream consume
       THIS layer, never REP_real / IS_CUT.

   Blueprint: ../archive/tautology Cut/Mul.lean + MulComm.lean + MulDistrib.lean
   (no sorry: non-negative core + signed comm/one/assoc + NON-NEGATIVE
   distributivity all proven).  The ONE unreferenced step = SIGNED
   distributivity — Stage D's deliverable MUST include full realMulDistribThm.
   Reusable cut lemmas to port: exists_pos_of_zero_lt (0<a ⇒ ∃ positive member),
   exists_gt_both (two members have a common upper member).

   STATUS: Layer 1 core + comm/nonneg/zero/one DONE — realNnMul +
   nnMulCutIsCutThm (4 conds) + rep/mem + membership helpers
   (nnMemEq/IntroL/IntroR) + realNnMul{Comm,Nonneg,Zero,One}Thm.
   NEXT: realNnMul{AssocNonneg,DistribNonneg}, then Layer 2 (signed realMul). *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

realNnMulConst::usage = "realNnMulConst[] — realNnMul : real → real → real, the non-negative product core. Cut body { r | r<0 ∨ ∃p q. REP x p ∧ REP y q ∧ 0<p ∧ 0<q ∧ r<p·q }. Semantics only contracted under 0≤x ∧ 0≤y (the …Nonneg theorems).";
realNnMulDefThm::usage = "realNnMulDefThm — ⊢ realNnMul = (λx y. ABS_real (λr. ratLt r 0 ∨ ∃p q. REP_real x p ∧ REP_real y q ∧ ratLt 0 p ∧ ratLt 0 q ∧ ratLt r (ratMul p q))).";
nnMulCutIsCutThm::usage = "nnMulCutIsCutThm — ⊢ ∀x y. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ IS_CUT (nnMulBody x y). The product-set of two non-negative cuts is a cut.";
repRealNnMulThm::usage = "repRealNnMulThm — ⊢ ∀x y. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ REP_real (realNnMul x y) = (λr. ratLt r 0 ∨ ∃p q. REP_real x p ∧ REP_real y q ∧ ratLt 0 p ∧ ratLt 0 q ∧ ratLt r (ratMul p q)).";
realNnMulMemThm::usage = "realNnMulMemThm — ⊢ ∀x y. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ ∀r. REP_real (realNnMul x y) r = (ratLt r 0 ∨ ∃p q. REP_real x p ∧ REP_real y q ∧ ratLt 0 p ∧ ratLt 0 q ∧ ratLt r (ratMul p q)).";
realNnMulCommThm::usage = "realNnMulCommThm — ⊢ ∀x y. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ realNnMul x y = realNnMul y x.";
realNnMulNonnegThm::usage = "realNnMulNonnegThm — ⊢ ∀x y. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ realLe (&ℝ 0) (realNnMul x y). The non-negative product is non-negative.";
realNnMulZeroThm::usage = "realNnMulZeroThm — ⊢ ∀x. realLe (&ℝ 0) x ⇒ realNnMul x (&ℝ (&ℚ (&ℤ 0))) = &ℝ (&ℚ (&ℤ 0)).";
realNnMulOneThm::usage = "realNnMulOneThm — ⊢ ∀x. realLe (&ℝ 0) x ⇒ realNnMul x (&ℝ (&ℚ (&ℤ (SUC 0)))) = x.";
realNnMulAssocNonnegThm::usage = "realNnMulAssocNonnegThm — ⊢ ∀x y z. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ realLe (&ℝ 0) z ⇒ realNnMul (realNnMul x y) z = realNnMul x (realNnMul y z).";
realNnMulDistribNonnegThm::usage = "realNnMulDistribNonnegThm — ⊢ ∀x y z. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ realLe (&ℝ 0) z ⇒ realNnMul x (realAdd y z) = realAdd (realNnMul x y) (realNnMul x z). Non-negative left distributivity (last Layer-1 piece).";

(* ---- Layer 2: signed realMul (COND binary 0≤x/0≤y split) ---- *)
realMulConst::usage = "realMulConst[] — realMul : real → real → real, the signed product. COND binary on 0≤x / 0≤y: nonneg×nonneg → realNnMul; one factor negative → realNeg of the realNnMul of the absolute values; both negative → realNnMul of the negations.";
realMulDefThm::usage = "realMulDefThm — ⊢ realMul = (λx y. COND (realLe 0 x) (COND (realLe 0 y) (realNnMul x y) (realNeg (realNnMul x (realNeg y)))) (COND (realLe 0 y) (realNeg (realNnMul (realNeg x) y)) (realNnMul (realNeg x) (realNeg y)))).";
realMulCasePPThm::usage = "realMulCasePPThm — ⊢ ∀x y. realLe 0 x ⇒ realLe 0 y ⇒ realMul x y = realNnMul x y.";
realMulCasePNThm::usage = "realMulCasePNThm — ⊢ ∀x y. realLe 0 x ⇒ ¬(realLe 0 y) ⇒ realMul x y = realNeg (realNnMul x (realNeg y)).";
realMulCaseNPThm::usage = "realMulCaseNPThm — ⊢ ∀x y. ¬(realLe 0 x) ⇒ realLe 0 y ⇒ realMul x y = realNeg (realNnMul (realNeg x) y).";
realMulCaseNNThm::usage = "realMulCaseNNThm — ⊢ ∀x y. ¬(realLe 0 x) ⇒ ¬(realLe 0 y) ⇒ realMul x y = realNnMul (realNeg x) (realNeg y).";
realNegZeroThm::usage = "realNegZeroThm — ⊢ realNeg (&ℝ 0) = &ℝ 0.";
realNegNegThm::usage = "realNegNegThm — ⊢ ∀x. realNeg (realNeg x) = x.";
realLeNegThm::usage = "realLeNegThm — ⊢ ∀x y. realLe x y ⇒ realLe (realNeg y) (realNeg x). Negation reverses the order.";
realNegAddThm::usage = "realNegAddThm — ⊢ ∀x y. realNeg (realAdd x y) = realAdd (realNeg x) (realNeg y).";
realMulCommThm::usage = "realMulCommThm — ⊢ ∀x y. realMul x y = realMul y x.";
realMulZeroThm::usage = "realMulZeroThm — ⊢ ∀x. realMul x (&ℝ 0) = &ℝ 0.";
realMulOneThm::usage = "realMulOneThm — ⊢ ∀x. realMul x (&ℝ (&ℚ (&ℤ (SUC 0)))) = x.";
realMulNegRightThm::usage = "realMulNegRightThm — ⊢ ∀x y. realMul x (realNeg y) = realNeg (realMul x y).";
realMulNegLeftThm::usage = "realMulNegLeftThm — ⊢ ∀x y. realMul (realNeg x) y = realNeg (realMul x y).";
realMulNonnegThm::usage = "realMulNonnegThm — ⊢ ∀x y. realLe 0 x ⇒ realLe 0 y ⇒ realLe 0 (realMul x y).";
realMulAssocThm::usage = "realMulAssocThm — ⊢ ∀x y z. realMul (realMul x y) z = realMul x (realMul y z).";
realMulDistribThm::usage = "realMulDistribThm — ⊢ ∀x y z. realMul x (realAdd y z) = realAdd (realMul x y) (realMul x z). Signed left distributivity (Stage D capstone, the no-reference step).";
realLeMulNonnegThm::usage = "realLeMulNonnegThm — ⊢ ∀x y. realLe 0 x ⇒ realLe 0 y ⇒ realLe 0 (realMul x y).";
realLtMulPosThm::usage = "realLtMulPosThm — ⊢ ∀x y. realLt 0 x ⇒ realLt 0 y ⇒ realLt 0 (realMul x y).";
notLeWitnessThm::usage = "notLeWitnessThm — ⊢ ∀a b. ¬(realLe a b) ⇒ ∃q. REP_real a q ∧ ¬(REP_real b q). Failure of inclusion yields a separating point.";
realPosHasPosMemThm::usage = "realPosHasPosMemThm — ⊢ ∀x. realLt (&ℝ 0) x ⇒ ∃p. REP_real x p ∧ ratLt (&ℚ (&ℤ 0)) p. A positive real's cut has a positive member.";
realLeAddMonoThm::usage = "realLeAddMonoThm — ⊢ ∀a b c. realLe a b ⇒ realLe (realAdd a c) (realAdd b c). Additive monotonicity of ≤.";
realLtAddMonoThm::usage = "realLtAddMonoThm — ⊢ ∀a b c. realLt a b ⇒ realLt (realAdd a c) (realAdd b c). Additive monotonicity of <.";
realLeSubNonnegThm::usage = "realLeSubNonnegThm — ⊢ ∀a b. realLe a b = realLe (&ℝ 0) (realAdd b (realNeg a)). a ≤ b ⟺ 0 ≤ b − a.";
realLtSubPosThm::usage = "realLtSubPosThm — ⊢ ∀a b. realLt a b = realLt (&ℝ 0) (realAdd b (realNeg a)). a < b ⟺ 0 < b − a.";
realLeMulMonoThm::usage = "realLeMulMonoThm — ⊢ ∀a b c. realLe (&ℝ 0) c ⇒ realLe a b ⇒ realLe (realMul c a) (realMul c b). Multiply ≤ by a nonnegative.";
realLtMulMonoThm::usage = "realLtMulMonoThm — ⊢ ∀a b c. realLt (&ℝ 0) c ⇒ realLt a b ⇒ realLt (realMul c a) (realMul c b). Multiply < by a positive.";
realOfRatAddThm::usage = "realOfRatAddThm — ⊢ ∀a b. &ℝ (ratAdd a b) = realAdd (&ℝ a) (&ℝ b). &ℝ is an additive homomorphism.";
realOfRatNegThm::usage = "realOfRatNegThm — ⊢ ∀a. &ℝ (ratNeg a) = realNeg (&ℝ a). &ℝ preserves negation.";
realOfRatNnMulThm::usage = "realOfRatNnMulThm — ⊢ ∀a b. ratLe (&ℚ (&ℤ 0)) a ⇒ ratLe (&ℚ (&ℤ 0)) b ⇒ realNnMul (&ℝ a) (&ℝ b) = &ℝ (ratMul a b). &ℝ preserves the non-negative product.";
realOfRatMulThm::usage = "realOfRatMulThm — ⊢ ∀a b. &ℝ (ratMul a b) = realMul (&ℝ a) (&ℝ b). &ℝ is a multiplicative homomorphism (so a ring/order embedding ℚ ↪ ℝ).";

Begin["`Private`"];

(* ============================================================ *)
(* Layer 1 — non-negative multiplication core  realNnMul.       *)
(* Blueprint: ../archive/tautology Cut/Mul.lean (mul_nonneg),    *)
(* but STRICT  r < p·q  and using 0≤x to drop the bound clamp.   *)
(* ============================================================ *)

realNnMulTy = tyFun[realTy, tyFun[realTy, realTy]];

(* ∨ builder (no disjTm in the shared cut vocab) *)
disjTm[a_, b_] := mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];

zeroRealTm[] := realOfRatTm[zeroQ[]];   (* &ℝ (&ℚ (&ℤ 0)) *)
nonnegTm[xT_] := realLeTm[zeroRealTm[], xT];   (* 0 ≤ x *)

(* cut body: λr. r<0 ∨ ∃p q. REP x p ∧ REP y q ∧ 0<p ∧ 0<q ∧ r < p·q *)
nnMulBodyTm[xT_, yT_] :=
  Module[{rV, pV, qV, prodCond, ex},
    rV = mkVar["r", ratTy]; pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy];
    prodCond = conjTm[repApp[xT, pV], conjTm[repApp[yT, qV],
      conjTm[ratLtTm[zeroQ[], pV], conjTm[ratLtTm[zeroQ[], qV],
        ratLtTm[rV, ratMulTm[pV, qV]]]]]];
    ex = existsTm[pV, existsTm[qV, prodCond]];
    mkAbs[rV, disjTm[ratLtTm[rV, zeroQ[]], ex]]
  ];

realNnMulDefThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = mkAbs[xV, mkAbs[yV, mkComb[absRealConst[], nnMulBodyTm[xV, yV]]]];
    newDefinition[mkEq[mkVar["realNnMul", realNnMulTy], body]]
  ];

realNnMulConst[] := mkConst["realNnMul", realNnMulTy];
realNnMulTm[xT_, yT_] := mkComb[mkComb[realNnMulConst[], xT], yT];

(* ⊢ realNnMul x y = ABS_real (nnMulBody x y) *)
unfoldRealNnMul[xT_, yT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[realNnMulDefThm, xT];
    s1b = TRANS[s1, BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, yT];
    TRANS[s2, BETACONV[concl[s2][[2]]]]
  ];

(* ⊢ ∀x y. realLe (&ℝ 0) x ⇒ realLe (&ℝ 0) y ⇒ IS_CUT (nnMulBody x y).
   0≤x is used only in c2 (proper): it makes every non-member ≥0, which
   drops Lean's COND clamp.  Strict r<p·q makes c4 (open) pure ratDense. *)
nnMulCutIsCutThm =
  Module[{xV, yV, nnBody, hNX, hNY, pV, qV, rVar, leUnfX, leUnfY, memEqX,
          negInX, negInY, betaAt, rhsAt, leftAt, prodCondAt, innerExAt, exPartAt,
          c4ExTerm, unfold, rhsConj, c1Tm, rest1, c2Tm, rest2, c3Tm, c4Tm,
          c1Thm, c2Thm, c3Thm, c4Thm, conjAll, isCutXY},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    nnBody = nnMulBodyTm[xV, yV];
    hNX = ASSUME[nonnegTm[xV]]; hNY = ASSUME[nonnegTm[yV]];
    pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy]; rVar = mkVar["r", ratTy];

    betaAt[rT_] := BETACONV[mkComb[nnBody, rT]];
    rhsAt[rT_]  := concl[betaAt[rT]][[2]];
    leftAt[rT_] := ratLtTm[rT, zeroQ[]];
    prodCondAt[rT_, pT_, qT_] := conjTm[repApp[xV, pT], conjTm[repApp[yV, qT],
      conjTm[ratLtTm[zeroQ[], pT], conjTm[ratLtTm[zeroQ[], qT],
        ratLtTm[rT, ratMulTm[pT, qT]]]]]];
    innerExAt[rT_, pT_] := existsTm[qV, prodCondAt[rT, pT, qV]];
    exPartAt[rT_] := existsTm[pV, innerExAt[rT, pV]];
    c4ExTerm[qT_] := existsTm[rVar, conjTm[mkComb[nnBody, rVar], ratLtTm[qT, rVar]]];

    leUnfX = EQMP[unfoldRealLe[zeroRealTm[], xV], hNX];
    leUnfY = EQMP[unfoldRealLe[zeroRealTm[], yV], hNY];
    memEqX[qT_] := HOL`Bool`SPEC[qT, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];
    negInX[qT_, ltPf_] := HOL`Bool`MP[HOL`Bool`SPEC[qT, leUnfX],
                            EQMP[HOL`Equal`SYM[memEqX[qT]], ltPf]];
    negInY[qT_, ltPf_] := HOL`Bool`MP[HOL`Bool`SPEC[qT, leUnfY],
                            EQMP[HOL`Equal`SYM[memEqX[qT]], ltPf]];

    unfold = unfoldIsCut[nnBody];
    rhsConj = concl[unfold][[2]];
    c1Tm = rhsConj[[1, 2]]; rest1 = rhsConj[[2]];
    c2Tm = rest1[[1, 2]]; rest2 = rest1[[2]];
    c3Tm = rest2[[1, 2]]; c4Tm = rest2[[2]];

    (* --- c1 nonempty: witness −1 (left disjunct r<0) --- *)
    c1Thm = Module[{sublt, addEq, negOneLtZero, witDisj, nnAtNeg},
      sublt = HOL`Bool`MP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[], ratSubLtSelfThm]],
                ratZeroLtOneThm];   (* ratLt (0+(−1)) 0 *)
      addEq = TRANS[HOL`Bool`SPEC[negOne[], HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
                HOL`Bool`SPEC[negOne[], HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+(−1) = −1 *)
      negOneLtZero = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], addEq], REFL[zeroQ[]]], sublt];
      witDisj = HOL`Bool`DISJ1[negOneLtZero, exPartAt[negOne[]]];
      nnAtNeg = EQMP[HOL`Equal`SYM[betaAt[negOne[]]], witDisj];
      HOL`Bool`EXISTS[c1Tm, negOne[], nnAtNeg]
    ];

    (* --- c2 proper: u = ux·uy, ux/uy = realProper witnesses --- *)
    c2Thm = Module[{prX, prY, ux, uy, uTm, hNMx, hNMy, notLtUx, notLtUy, le0ux,
                    le0uy, mulNN, uNonneg, notLtU, hConj, memXp, t1, memYq, t2,
                    hpp, t3, hqq, hltU, pLtUx, qLtUy, uxPos, pqLtUxq, qUxLtUyUx,
                    comm1, comm2, uxqLtU, pqLtU, uLtU, falseBody, fChooseQ,
                    caseRight, hDisj, caseLeft, falseDisj, notRhs, notBody, ex},
      prX = HOL`Bool`SPEC[xV, realProperThm];
      prY = HOL`Bool`SPEC[yV, realProperThm];
      ux = mkVar["ux", ratTy]; uy = mkVar["uy", ratTy];
      uTm = ratMulTm[ux, uy];
      hNMx = ASSUME[notTm[repApp[xV, ux]]]; hNMy = ASSUME[notTm[repApp[yV, uy]]];
      notLtUx = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[leftAt[ux],
                  HOL`Bool`MP[HOL`Bool`NOTELIM[hNMx], negInX[ux, ASSUME[leftAt[ux]]]]]];
      le0ux = HOL`Bool`CCONTR[ratLeTm[zeroQ[], ux],
                HOL`Bool`MP[HOL`Bool`NOTELIM[notLtUx],
                  EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[ux,
                    HOL`Stdlib`Rat`ratLtNotLeThm]]], ASSUME[notTm[ratLeTm[zeroQ[], ux]]]]]];
      notLtUy = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[leftAt[uy],
                  HOL`Bool`MP[HOL`Bool`NOTELIM[hNMy], negInY[uy, ASSUME[leftAt[uy]]]]]];
      le0uy = HOL`Bool`CCONTR[ratLeTm[zeroQ[], uy],
                HOL`Bool`MP[HOL`Bool`NOTELIM[notLtUy],
                  EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[uy,
                    HOL`Stdlib`Rat`ratLtNotLeThm]]], ASSUME[notTm[ratLeTm[zeroQ[], uy]]]]]];
      mulNN = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uy, HOL`Bool`SPEC[zeroQ[],
                HOL`Bool`SPEC[ux, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], le0ux], le0uy];
      (* ratLe (ux·0)(ux·uy) *)
      uNonneg = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[],
                  HOL`Bool`SPEC[ux, HOL`Stdlib`Rat`ratMulZeroThm]], REFL[uTm]], mulNN];
      (* ratLe 0 (ux·uy) *)
      notLtU = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[leftAt[uTm],
                 HOL`Bool`MP[HOL`Bool`NOTELIM[EQMP[HOL`Bool`SPEC[zeroQ[],
                   HOL`Bool`SPEC[uTm, HOL`Stdlib`Rat`ratLtNotLeThm]], ASSUME[leftAt[uTm]]]],
                   uNonneg]]];
      hConj = ASSUME[prodCondAt[uTm, pV, qV]];
      memXp = HOL`Bool`CONJUNCT1[hConj];
      t1 = HOL`Bool`CONJUNCT2[hConj]; memYq = HOL`Bool`CONJUNCT1[t1];
      t2 = HOL`Bool`CONJUNCT2[t1]; hpp = HOL`Bool`CONJUNCT1[t2];
      t3 = HOL`Bool`CONJUNCT2[t2]; hqq = HOL`Bool`CONJUNCT1[t3]; hltU = HOL`Bool`CONJUNCT2[t3];
      pLtUx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ux, HOL`Bool`SPEC[pV,
                HOL`Bool`SPEC[xV, memNotMemLtThm]]], memXp], hNMx];
      qLtUy = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uy, HOL`Bool`SPEC[qV,
                HOL`Bool`SPEC[yV, memNotMemLtThm]]], memYq], hNMy];
      uxPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ux, HOL`Bool`SPEC[pV,
                HOL`Bool`SPEC[zeroQ[], ratLtTransThm]]], hpp], pLtUx];
      pqLtUxq = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ux, HOL`Bool`SPEC[pV,
                  HOL`Bool`SPEC[qV, ratLtMulPosThm]]], hqq], pLtUx];   (* (p·q)<(ux·q) *)
      qUxLtUyUx = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uy, HOL`Bool`SPEC[qV,
                    HOL`Bool`SPEC[ux, ratLtMulPosThm]]], uxPos], qLtUy];   (* (q·ux)<(uy·ux) *)
      comm1 = HOL`Bool`SPEC[ux, HOL`Bool`SPEC[qV, HOL`Stdlib`Rat`ratMulCommThm]];   (* q·ux = ux·q *)
      comm2 = HOL`Bool`SPEC[ux, HOL`Bool`SPEC[uy, HOL`Stdlib`Rat`ratMulCommThm]];   (* uy·ux = ux·uy *)
      uxqLtU = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], comm1], comm2], qUxLtUyUx];
      (* (ux·q) < (ux·uy) *)
      pqLtU = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uTm, HOL`Bool`SPEC[ratMulTm[ux, qV],
                HOL`Bool`SPEC[ratMulTm[pV, qV], ratLtTransThm]]], pqLtUxq], uxqLtU];
      uLtU = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uTm, HOL`Bool`SPEC[ratMulTm[pV, qV],
               HOL`Bool`SPEC[uTm, ratLtTransThm]]], hltU], pqLtU];
      falseBody = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[uTm, ratLtIrreflThm]], uLtU];
      fChooseQ = HOL`Bool`CHOOSE[qV, ASSUME[innerExAt[uTm, pV]], falseBody];
      caseRight = HOL`Bool`CHOOSE[pV, ASSUME[exPartAt[uTm]], fChooseQ];
      hDisj = ASSUME[rhsAt[uTm]];
      caseLeft = HOL`Bool`MP[HOL`Bool`NOTELIM[notLtU], ASSUME[leftAt[uTm]]];
      falseDisj = HOL`Bool`DISJCASES[hDisj, caseLeft, caseRight];
      notRhs = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[rhsAt[uTm], falseDisj]];
      notBody = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[], betaAt[uTm]]], notRhs];
      ex = HOL`Bool`EXISTS[c2Tm, uTm, notBody];
      HOL`Bool`CHOOSE[uy, prY, HOL`Bool`CHOOSE[ux, prX, ex]]
    ];

    (* --- c3 downward closed --- *)
    c3Thm = Module[{qBig, rSmall, hBig, hLt, redBig, caseL, caseR, result},
      qBig = mkVar["a", ratTy]; rSmall = mkVar["b", ratTy];
      hBig = ASSUME[mkComb[nnBody, qBig]];
      hLt = ASSUME[ratLtTm[rSmall, qBig]];
      redBig = EQMP[betaAt[qBig], hBig];
      caseL = Module[{hqNeg, rNeg},
        hqNeg = ASSUME[leftAt[qBig]];
        rNeg = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[qBig,
                 HOL`Bool`SPEC[rSmall, ratLtTransThm]]], hLt], hqNeg];
        EQMP[HOL`Equal`SYM[betaAt[rSmall]], HOL`Bool`DISJ1[rNeg, exPartAt[rSmall]]]
      ];
      caseR = Module[{hEx, hConj, memXp, t1, memYq, t2, hpp, t3, hqq, hltQ, rLtPq,
                      newConj, innerEx, outerEx, nnR, chQ},
        hEx = ASSUME[exPartAt[qBig]];
        hConj = ASSUME[prodCondAt[qBig, pV, qV]];
        memXp = HOL`Bool`CONJUNCT1[hConj];
        t1 = HOL`Bool`CONJUNCT2[hConj]; memYq = HOL`Bool`CONJUNCT1[t1];
        t2 = HOL`Bool`CONJUNCT2[t1]; hpp = HOL`Bool`CONJUNCT1[t2];
        t3 = HOL`Bool`CONJUNCT2[t2]; hqq = HOL`Bool`CONJUNCT1[t3]; hltQ = HOL`Bool`CONJUNCT2[t3];
        rLtPq = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[pV, qV], HOL`Bool`SPEC[qBig,
                  HOL`Bool`SPEC[rSmall, ratLtTransThm]]], hLt], hltQ];
        newConj = HOL`Bool`CONJ[memXp, HOL`Bool`CONJ[memYq, HOL`Bool`CONJ[hpp,
                    HOL`Bool`CONJ[hqq, rLtPq]]]];
        innerEx = HOL`Bool`EXISTS[innerExAt[rSmall, pV], qV, newConj];
        outerEx = HOL`Bool`EXISTS[exPartAt[rSmall], pV, innerEx];
        nnR = EQMP[HOL`Equal`SYM[betaAt[rSmall]], HOL`Bool`DISJ2[outerEx, leftAt[rSmall]]];
        chQ = HOL`Bool`CHOOSE[qV, ASSUME[innerExAt[qBig, pV]], nnR];
        HOL`Bool`CHOOSE[pV, hEx, chQ]
      ];
      result = HOL`Bool`DISJCASES[redBig, caseL, caseR];
      HOL`Bool`GEN[qBig, HOL`Bool`GEN[rSmall,
        HOL`Bool`DISCH[mkComb[nnBody, qBig], HOL`Bool`DISCH[ratLtTm[rSmall, qBig], result]]]]
    ];

    (* --- c4 no greatest: strict ⟹ pure ratDense midpoint --- *)
    c4Thm = Module[{qBig, hBig, redBig, caseL, caseR, result},
      qBig = mkVar["a", ratTy];
      hBig = ASSUME[mkComb[nnBody, qBig]];
      redBig = EQMP[betaAt[qBig], hBig];
      caseL = Module[{hqNeg, dense, qLtMid, midLt0, midTm, nnMid, conjMid},
        hqNeg = ASSUME[leftAt[qBig]];
        dense = HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[qBig, ratDenseThm]], hqNeg];
        qLtMid = HOL`Bool`CONJUNCT1[dense]; midLt0 = HOL`Bool`CONJUNCT2[dense];
        midTm = concl[qLtMid][[2]];
        nnMid = EQMP[HOL`Equal`SYM[betaAt[midTm]], HOL`Bool`DISJ1[midLt0, exPartAt[midTm]]];
        conjMid = HOL`Bool`CONJ[nnMid, qLtMid];
        HOL`Bool`EXISTS[c4ExTerm[qBig], midTm, conjMid]
      ];
      caseR = Module[{hEx, aP, aQ, hConj, memXp, t1, memYq, t2, hpp, t3, hqq, hltQ,
                      dense, qLtMid, midLtPq, midTm, newConj, innerEx, outerEx, nnMid,
                      conjMid, exR, chQ},
        hEx = ASSUME[exPartAt[qBig]];
        aP = mkVar["pp", ratTy]; aQ = mkVar["qq", ratTy];   (* fresh: midTm contains pV,qV *)
        hConj = ASSUME[prodCondAt[qBig, pV, qV]];
        memXp = HOL`Bool`CONJUNCT1[hConj];
        t1 = HOL`Bool`CONJUNCT2[hConj]; memYq = HOL`Bool`CONJUNCT1[t1];
        t2 = HOL`Bool`CONJUNCT2[t1]; hpp = HOL`Bool`CONJUNCT1[t2];
        t3 = HOL`Bool`CONJUNCT2[t2]; hqq = HOL`Bool`CONJUNCT1[t3]; hltQ = HOL`Bool`CONJUNCT2[t3];
        dense = HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[pV, qV], HOL`Bool`SPEC[qBig, ratDenseThm]], hltQ];
        qLtMid = HOL`Bool`CONJUNCT1[dense]; midLtPq = HOL`Bool`CONJUNCT2[dense];
        midTm = concl[qLtMid][[2]];
        newConj = HOL`Bool`CONJ[memXp, HOL`Bool`CONJ[memYq, HOL`Bool`CONJ[hpp,
                    HOL`Bool`CONJ[hqq, midLtPq]]]];
        innerEx = HOL`Bool`EXISTS[existsTm[aQ, prodCondAt[midTm, pV, aQ]], qV, newConj];
        outerEx = HOL`Bool`EXISTS[existsTm[aP, existsTm[aQ, prodCondAt[midTm, aP, aQ]]], pV, innerEx];
        nnMid = EQMP[HOL`Equal`SYM[betaAt[midTm]], HOL`Bool`DISJ2[outerEx, leftAt[midTm]]];
        conjMid = HOL`Bool`CONJ[nnMid, qLtMid];
        exR = HOL`Bool`EXISTS[c4ExTerm[qBig], midTm, conjMid];
        chQ = HOL`Bool`CHOOSE[qV, ASSUME[innerExAt[qBig, pV]], exR];
        HOL`Bool`CHOOSE[pV, hEx, chQ]
      ];
      result = HOL`Bool`DISJCASES[redBig, caseL, caseR];
      HOL`Bool`GEN[qBig, HOL`Bool`DISCH[mkComb[nnBody, qBig], result]]
    ];

    conjAll = HOL`Bool`CONJ[c1Thm, HOL`Bool`CONJ[c2Thm, HOL`Bool`CONJ[c3Thm, c4Thm]]];
    isCutXY = EQMP[HOL`Equal`SYM[unfold], conjAll];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[concl[hNX], HOL`Bool`DISCH[concl[hNY], isCutXY]]]]
  ];

(* ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ REP_real (realNnMul x y) = nnMulBody x y *)
repRealNnMulThm =
  Module[{xV, yV, nnBody, isCutXY, lVar, repAbsInst, repAbsNn, apRep},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    nnBody = nnMulBodyTm[xV, yV];
    isCutXY = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, nnMulCutIsCutThm]],
                ASSUME[nonnegTm[xV]]], ASSUME[nonnegTm[yV]]];
    lVar = concl[repAbsRealThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{lVar -> nnBody}, repAbsRealThm];
    repAbsNn = EQMP[repAbsInst, isCutXY];
    apRep = HOL`Equal`APTERM[repRealConst[], unfoldRealNnMul[xV, yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV], TRANS[apRep, repAbsNn]]]]]
  ];

(* ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ ∀r. REP_real (realNnMul x y) r = (nnMulBody x y) r *)
realNnMulMemThm =
  Module[{xV, yV, rV, repEq, apAtR},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; rV = mkVar["r", ratTy];
    repEq = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, repRealNnMulThm]],
              ASSUME[nonnegTm[xV]]], ASSUME[nonnegTm[yV]]];
    apAtR = HOL`Equal`APTHM[repEq, rV];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV],
        HOL`Bool`GEN[rV, TRANS[apAtR, BETACONV[concl[apAtR][[2]]]]]]]]]
  ];

(* ============================================================ *)
(* realNnMul membership — extraction-based helpers (HYGIENE).   *)
(* All ∃-terms come from the kernel (realNnMulMemThm RHS / BETACONV), *)
(* never hand-rebuilt — so a witness term that shares the binder *)
(* names (e.g. a midpoint containing p,q) can't be captured.    *)
(* Require hNx:0≤x, hNy:0≤y. Private (proof scaffolding).        *)
(* ============================================================ *)

(* ⊢ REP_real (realNnMul x y) r = (r<0 ∨ ∃p q. …)  [under hNx, hNy] *)
nnMemEq[xT_, yT_, rT_, hNx_, hNy_] :=
  HOL`Bool`SPEC[rT, HOL`Bool`MP[HOL`Bool`MP[
    HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realNnMulMemThm]], hNx], hNy]];

(* membership via the left disjunct, from ltPf : ratLt rT 0 *)
nnMemIntroL[xT_, yT_, rT_, ltPf_, hNx_, hNy_] :=
  Module[{eqAt, exPart},
    eqAt = nnMemEq[xT, yT, rT, hNx, hNy];
    exPart = concl[eqAt][[2, 2]];
    EQMP[HOL`Equal`SYM[eqAt], HOL`Bool`DISJ1[ltPf, exPart]]
  ];

(* membership via the right disjunct, from condProof : prodCond[rT,pW,qW].
   innerTerm/exPart are EXTRACTED (BETACONV / membership RHS) — no rebuild. *)
nnMemIntroR[xT_, yT_, rT_, pW_, qW_, condProof_, hNx_, hNy_] :=
  Module[{eqAt, disjD, leftD, exPart, innerTerm, innerEx, outerEx},
    eqAt = nnMemEq[xT, yT, rT, hNx, hNy];
    disjD = concl[eqAt][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
    innerTerm = concl[BETACONV[mkComb[exPart[[2]], pW]]][[2]];
    innerEx = HOL`Bool`EXISTS[innerTerm, qW, condProof];
    outerEx = HOL`Bool`EXISTS[exPart, pW, innerEx];
    EQMP[HOL`Equal`SYM[eqAt], HOL`Bool`DISJ2[outerEx, leftD]]
  ];

(* destructure a POSITIVE membership: from hMemP : REP(a·b) P and hPosP : 0<P,
   produce ⊢ ∃p q. REP a p ∧ REP b q ∧ 0<p ∧ 0<q ∧ P<p·q (left disjunct P<0
   is killed by 0<P).  Caller CHOOSEs p,q. *)
nnMemPosThm[aT_, bT_, PT_, hMemP_, hPosP_, hNa_, hNb_] :=
  Module[{eqAt, disjD, leftD, exPart, redMem, caseL},
    eqAt = nnMemEq[aT, bT, PT, hNa, hNb];
    disjD = concl[eqAt][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
    redMem = EQMP[eqAt, hMemP];
    caseL = HOL`Bool`CONTR[exPart,
              HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[PT, ratLtIrreflThm]],
                HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[PT, HOL`Bool`SPEC[zeroQ[],
                  HOL`Bool`SPEC[PT, ratLtTransThm]]], ASSUME[leftD]], hPosP]]];
    HOL`Bool`DISJCASES[redMem, caseL, ASSUME[exPart]]
  ];

(* the product of two members is in the product cut: from s∈a, t∈b, 0<s, 0<t,
   produce ⊢ REP(a·b)(s·t).  STRICT < ⇒ bump s→s'>s, t→t'>t (openness) so
   s·t < s'·t' is a strict product.  Distinctive binders sPr/tPr (sT,tT may
   carry common names). *)
nnMemProdThm[aT_, bT_, sT_, tT_, hMemS_, hMemT_, hPosS_, hPosT_, hNa_, hNb_] :=
  Module[{opnA, opnB, sP, tP, hOpA, mAsP, sLtsP, hOpB, mBtP, tLttP, sPpos, tPpos,
          st1, st2c, st2, stLt, cond, intro},
    opnA = HOL`Bool`MP[HOL`Bool`SPEC[sT, HOL`Bool`SPEC[aT, realOpenThm]], hMemS];
    opnB = HOL`Bool`MP[HOL`Bool`SPEC[tT, HOL`Bool`SPEC[bT, realOpenThm]], hMemT];
    sP = mkVar["sPr", ratTy]; tP = mkVar["tPr", ratTy];
    hOpA = ASSUME[conjTm[repApp[aT, sP], ratLtTm[sT, sP]]];
    mAsP = HOL`Bool`CONJUNCT1[hOpA]; sLtsP = HOL`Bool`CONJUNCT2[hOpA];
    hOpB = ASSUME[conjTm[repApp[bT, tP], ratLtTm[tT, tP]]];
    mBtP = HOL`Bool`CONJUNCT1[hOpB]; tLttP = HOL`Bool`CONJUNCT2[hOpB];
    sPpos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[sP, HOL`Bool`SPEC[sT,
              HOL`Bool`SPEC[zeroQ[], ratLtTransThm]]], hPosS], sLtsP];   (* 0<s' *)
    tPpos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[tP, HOL`Bool`SPEC[tT,
              HOL`Bool`SPEC[zeroQ[], ratLtTransThm]]], hPosT], tLttP];   (* 0<t' *)
    st1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[sP, HOL`Bool`SPEC[sT,
            HOL`Bool`SPEC[tT, ratLtMulPosThm]]], hPosT], sLtsP];   (* s·t < s'·t *)
    st2c = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[tP, HOL`Bool`SPEC[tT,
             HOL`Bool`SPEC[sP, ratLtMulPosThm]]], sPpos], tLttP];   (* t·s' < t'·s' *)
    st2 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[],
            HOL`Bool`SPEC[sP, HOL`Bool`SPEC[tT, HOL`Stdlib`Rat`ratMulCommThm]]],
            HOL`Bool`SPEC[sP, HOL`Bool`SPEC[tP, HOL`Stdlib`Rat`ratMulCommThm]]], st2c];
            (* s'·t < s'·t' *)
    stLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[sP, tP],
             HOL`Bool`SPEC[ratMulTm[sP, tT], HOL`Bool`SPEC[ratMulTm[sT, tT],
               ratLtTransThm]]], st1], st2];   (* s·t < s'·t' *)
    cond = HOL`Bool`CONJ[mAsP, HOL`Bool`CONJ[mBtP, HOL`Bool`CONJ[sPpos,
             HOL`Bool`CONJ[tPpos, stLt]]]];
    intro = nnMemIntroR[aT, bT, ratMulTm[sT, tT], sP, tP, cond, hNa, hNb];
    HOL`Bool`CHOOSE[tP, opnB, HOL`Bool`CHOOSE[sP, opnA, intro]]
  ];

(* ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ realNnMul x y = realNnMul y x.
   First consumer of the membership helpers; the right-disjunct case
   destructs via extracted inner terms and rebuilds swapped via nnMemIntroR. *)
realNnMulCommThm =
  Module[{xV, yV, hNx, hNy, rV, pV, qV, dir, fwd, bwd, perR, eqXY},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hNx = ASSUME[nonnegTm[xV]]; hNy = ASSUME[nonnegTm[yV]];
    rV = mkVar["r", ratTy]; pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy];
    dir[aV_, bV_, hNa_, hNb_] :=
      Module[{eqAB, disjD, leftD, exPart, hMem, redMem, caseL, caseR, cases},
        eqAB = nnMemEq[aV, bV, rV, hNa, hNb];
        disjD = concl[eqAB][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
        hMem = ASSUME[repApp[realNnMulTm[aV, bV], rV]];
        redMem = EQMP[eqAB, hMem];
        caseL = nnMemIntroL[bV, aV, rV, ASSUME[leftD], hNb, hNa];
        caseR = Module[{innerTerm, condTerm, hCond, mX, t1, mY, t2, hpp, t3, hqq,
                        hltpq, commPq, hltqp, swCond, introBA, chQ},
          innerTerm = concl[BETACONV[mkComb[exPart[[2]], pV]]][[2]];
          condTerm = concl[BETACONV[mkComb[innerTerm[[2]], qV]]][[2]];
          hCond = ASSUME[condTerm];
          mX = HOL`Bool`CONJUNCT1[hCond];
          t1 = HOL`Bool`CONJUNCT2[hCond]; mY = HOL`Bool`CONJUNCT1[t1];
          t2 = HOL`Bool`CONJUNCT2[t1]; hpp = HOL`Bool`CONJUNCT1[t2];
          t3 = HOL`Bool`CONJUNCT2[t2]; hqq = HOL`Bool`CONJUNCT1[t3]; hltpq = HOL`Bool`CONJUNCT2[t3];
          commPq = HOL`Bool`SPEC[pV, HOL`Bool`SPEC[qV, HOL`Stdlib`Rat`ratMulCommThm]];   (* qV·pV = pV·qV *)
          hltqp = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[rV]],
                    HOL`Equal`SYM[commPq]], hltpq];   (* r < qV·pV *)
          swCond = HOL`Bool`CONJ[mY, HOL`Bool`CONJ[mX, HOL`Bool`CONJ[hqq, HOL`Bool`CONJ[hpp, hltqp]]]];
          introBA = nnMemIntroR[bV, aV, rV, qV, pV, swCond, hNb, hNa];
          chQ = HOL`Bool`CHOOSE[qV, ASSUME[innerTerm], introBA];
          HOL`Bool`CHOOSE[pV, ASSUME[exPart], chQ]
        ];
        cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
        HOL`Bool`DISCH[concl[hMem], cases]
      ];
    fwd = dir[xV, yV, hNx, hNy];   (* REP(nnMul x y) r ⇒ REP(nnMul y x) r *)
    bwd = dir[yV, xV, hNy, hNx];   (* REP(nnMul y x) r ⇒ REP(nnMul x y) r *)
    perR = HOL`Bool`GEN[rV, HOL`Kernel`DEDUCTANTISYM[
             HOL`Bool`UNDISCH[bwd], HOL`Bool`UNDISCH[fwd]]];
    eqXY = realEqFromRepEq[realNnMulTm[xV, yV], realNnMulTm[yV, xV], perR];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV], eqXY]]]]
  ];

(* ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒ realLe (&ℝ 0) (realNnMul x y).
   realLe (&ℝ0) z unfolds to ∀r. r<0 ⇒ REP z r — exactly the left disjunct. *)
realNnMulNonnegThm =
  Module[{xV, yV, hNx, hNy, rV, hMem0, memEq0r, ltR, memProd, impl, allImpl, leThm},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hNx = ASSUME[nonnegTm[xV]]; hNy = ASSUME[nonnegTm[yV]];
    rV = mkVar["r", ratTy];
    hMem0 = ASSUME[repApp[zeroRealTm[], rV]];
    memEq0r = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];   (* REP(&ℝ0) r = r<0 *)
    ltR = EQMP[memEq0r, hMem0];
    memProd = nnMemIntroL[xV, yV, rV, ltR, hNx, hNy];
    impl = HOL`Bool`DISCH[concl[hMem0], memProd];
    allImpl = HOL`Bool`GEN[rV, impl];
    leThm = EQMP[HOL`Equal`SYM[unfoldRealLe[zeroRealTm[], realNnMulTm[xV, yV]]], allImpl];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV], leThm]]]]
  ];

(* ⊢ ∀x. 0≤x ⇒ realNnMul x 0 = 0.  The positive branch needs 0<q with
   q ∈ cut(0) ⇒ q<0 — impossible; only r<0 survives = the cut of 0. *)
realNnMulZeroThm =
  Module[{xV, hNx, zR, hN0, rV, pV, qV, memEq0, fwd, bwd, perR, eqThm},
    xV = mkVar["x", realTy]; hNx = ASSUME[nonnegTm[xV]];
    zR = zeroRealTm[];
    hN0 = HOL`Bool`SPEC[zR, realLeReflThm];   (* 0 ≤ &ℝ0 *)
    rV = mkVar["r", ratTy]; pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy];
    memEq0[tT_] := HOL`Bool`SPEC[tT, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];   (* REP(&ℝ0) t = t<0 *)
    fwd = Module[{eqM, disjD, leftD, exPart, hMem, redMem, caseL, caseR, cases},
      eqM = nnMemEq[xV, zR, rV, hNx, hN0];
      disjD = concl[eqM][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
      hMem = ASSUME[repApp[realNnMulTm[xV, zR], rV]];
      redMem = EQMP[eqM, hMem];
      caseL = EQMP[HOL`Equal`SYM[memEq0[rV]], ASSUME[leftD]];   (* REP(&ℝ0) r from r<0 *)
      caseR = Module[{innerTerm, condTerm, hCond, t1, mY0, t2, t3, hqq, qLt0,
                      zeroLtZero, falseT, chQ},
        innerTerm = concl[BETACONV[mkComb[exPart[[2]], pV]]][[2]];
        condTerm = concl[BETACONV[mkComb[innerTerm[[2]], qV]]][[2]];
        hCond = ASSUME[condTerm];
        t1 = HOL`Bool`CONJUNCT2[hCond]; mY0 = HOL`Bool`CONJUNCT1[t1];
        t2 = HOL`Bool`CONJUNCT2[t1]; t3 = HOL`Bool`CONJUNCT2[t2]; hqq = HOL`Bool`CONJUNCT1[t3];
        qLt0 = EQMP[memEq0[qV], mY0];   (* q<0 from REP(&ℝ0) q *)
        zeroLtZero = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[qV,
                       HOL`Bool`SPEC[zeroQ[], ratLtTransThm]]], hqq], qLt0];   (* 0<0 *)
        falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[zeroQ[], ratLtIrreflThm]], zeroLtZero];
        chQ = HOL`Bool`CHOOSE[qV, ASSUME[innerTerm], HOL`Bool`CONTR[repApp[zR, rV], falseT]];
        HOL`Bool`CHOOSE[pV, ASSUME[exPart], chQ]
      ];
      cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
      HOL`Bool`DISCH[concl[hMem], cases]
    ];
    bwd = Module[{hM0, ltR, memP},
      hM0 = ASSUME[repApp[zR, rV]];
      ltR = EQMP[memEq0[rV], hM0];
      memP = nnMemIntroL[xV, zR, rV, ltR, hNx, hN0];
      HOL`Bool`DISCH[concl[hM0], memP]
    ];
    perR = HOL`Bool`GEN[rV, HOL`Kernel`DEDUCTANTISYM[HOL`Bool`UNDISCH[bwd], HOL`Bool`UNDISCH[fwd]]];
    eqThm = realEqFromRepEq[realNnMulTm[xV, zR], zR, perR];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[nonnegTm[xV], eqThm]]
  ];

(* ⊢ ∀x. 0≤x ⇒ realNnMul x 1 = x.  Hardest nonneg law (cf. Lean mul_nonneg_one).
   fwd: p·q < p·1 = p ⇒ downward-closed.  bwd ¬(r<0): openness gives p∈x, r<p;
   q = midpoint(r/p, 1) gives 0<q<1 and r = p·(r/p) < p·q. *)
realNnMulOneThm =
  Module[{xV, hNx, oneR, hN1, ratLe01, rV, pV, qV, ratMulC, leUnfX, memEq0, memEq1,
          fwd, bwd, perR, eqThm},
    xV = mkVar["x", realTy]; hNx = ASSUME[nonnegTm[xV]];
    oneR = realOfRatTm[oneQ[]];
    rV = mkVar["r", ratTy]; pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy];
    ratMulC[] := HOL`Stdlib`Rat`ratMulConst[];
    leUnfX = EQMP[unfoldRealLe[zeroRealTm[], xV], hNx];   (* ∀q. REP(&ℝ0) q ⇒ REP x q *)
    memEq0[tT_] := HOL`Bool`SPEC[tT, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];
    memEq1[tT_] := HOL`Bool`SPEC[tT, HOL`Bool`SPEC[oneQ[], realOfRatMemThm]];
    ratLe01 = HOL`Bool`DISJCASES[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[], ratLeTotalThm]],
                ASSUME[ratLeTm[zeroQ[], oneQ[]]],
                HOL`Bool`CONTR[ratLeTm[zeroQ[], oneQ[]],
                  HOL`Bool`MP[HOL`Bool`NOTELIM[EQMP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[],
                    HOL`Stdlib`Rat`ratLtNotLeThm]], ratZeroLtOneThm]], ASSUME[ratLeTm[oneQ[], zeroQ[]]]]]];
    hN1 = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[], realOfRatLeThm]]], ratLe01];

    fwd = Module[{eqM, disjD, leftD, exPart, hMem, redMem, caseL, caseR, cases},
      eqM = nnMemEq[xV, oneR, rV, hNx, hN1];
      disjD = concl[eqM][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
      hMem = ASSUME[repApp[realNnMulTm[xV, oneR], rV]];
      redMem = EQMP[eqM, hMem];
      caseL = HOL`Bool`MP[HOL`Bool`SPEC[rV, leUnfX], EQMP[HOL`Equal`SYM[memEq0[rV]], ASSUME[leftD]]];
      caseR = Module[{innerTerm, condTerm, hCond, mX, t1, mQ1, t2, hpp, t3, hqq, hltpq,
                      q1, mulStep, rwL, rwR, pqLtP, rLtP, dcX, chQ},
        innerTerm = concl[BETACONV[mkComb[exPart[[2]], pV]]][[2]];
        condTerm = concl[BETACONV[mkComb[innerTerm[[2]], qV]]][[2]];
        hCond = ASSUME[condTerm];
        mX = HOL`Bool`CONJUNCT1[hCond]; t1 = HOL`Bool`CONJUNCT2[hCond]; mQ1 = HOL`Bool`CONJUNCT1[t1];
        t2 = HOL`Bool`CONJUNCT2[t1]; hpp = HOL`Bool`CONJUNCT1[t2]; t3 = HOL`Bool`CONJUNCT2[t2];
        hqq = HOL`Bool`CONJUNCT1[t3]; hltpq = HOL`Bool`CONJUNCT2[t3];
        q1 = EQMP[memEq1[qV], mQ1];   (* q<1 *)
        mulStep = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[qV,
                    HOL`Bool`SPEC[pV, ratLtMulPosThm]]], hpp], q1];   (* ratLt (q·p)(1·p) *)
        rwL = HOL`Bool`SPEC[pV, HOL`Bool`SPEC[qV, HOL`Stdlib`Rat`ratMulCommThm]];   (* q·p = p·q *)
        rwR = TRANS[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratMulOneThm]];   (* 1·p = p·1 = p *)
        pqLtP = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], rwL], rwR], mulStep];   (* p·q < p *)
        rLtP = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[ratMulTm[pV, qV],
                 HOL`Bool`SPEC[rV, ratLtTransThm]]], hltpq], pqLtP];   (* r<p *)
        dcX = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rV, HOL`Bool`SPEC[pV,
                HOL`Bool`SPEC[xV, realDownClosedThm]]], mX], rLtP];   (* REP x r *)
        chQ = HOL`Bool`CHOOSE[qV, ASSUME[innerTerm], dcX];
        HOL`Bool`CHOOSE[pV, ASSUME[exPart], chQ]
      ];
      cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
      HOL`Bool`DISCH[concl[hMem], cases]
    ];

    bwd = Module[{hX, em, caseNeg, casePos, result},
      hX = ASSUME[repApp[xV, rV]];
      em = HOL`Bool`EXCLUDEDMIDDLE[ratLtTm[rV, zeroQ[]]];
      caseNeg = nnMemIntroL[xV, oneR, rV, ASSUME[ratLtTm[rV, zeroQ[]]], hNx, hN1];
      casePos = Module[{hNotNeg, le0r, opn, inner},
        hNotNeg = ASSUME[notTm[ratLtTm[rV, zeroQ[]]]];
        le0r = HOL`Bool`CCONTR[ratLeTm[zeroQ[], rV],
                 HOL`Bool`MP[HOL`Bool`NOTELIM[hNotNeg],
                   EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[rV,
                     HOL`Stdlib`Rat`ratLtNotLeThm]]], ASSUME[notTm[ratLeTm[zeroQ[], rV]]]]]];
        opn = HOL`Bool`MP[HOL`Bool`SPEC[rV, HOL`Bool`SPEC[xV, realOpenThm]], hX];
        inner = Module[{hOpenP, mXp, rLtP, pPos, pNe0, invP, invPos, le0inv, tT, pInvEq1,
                        tLt1, tNonneg, dense, tLtQ, qLt1, qMid, qPos, tpEqR, ptEqR,
                        ptLtPq, rLtPq, mQ1, condProof, introOne},
          hOpenP = ASSUME[conjTm[repApp[xV, pV], ratLtTm[rV, pV]]];
          mXp = HOL`Bool`CONJUNCT1[hOpenP]; rLtP = HOL`Bool`CONJUNCT2[hOpenP];
          pPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[rV,
                   HOL`Bool`SPEC[zeroQ[], ratLeLtTransThm]]], le0r], rLtP];   (* 0<p *)
          pNe0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[pV, zeroQ[]],
                   HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[zeroQ[], ratLtIrreflThm]],
                     EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[zeroQ[]]],
                       ASSUME[mkEq[pV, zeroQ[]]]], pPos]]]];   (* ¬(p=0) *)
          invP = ratInvTm[pV];
          invPos = HOL`Bool`MP[HOL`Bool`SPEC[pV, ratInvPosThm], pPos];   (* 0<p⁻¹ *)
          le0inv = HOL`Bool`MP[HOL`Bool`SPEC[invP, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], invPos];   (* 0≤p⁻¹ *)
          pInvEq1 = HOL`Bool`MP[HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratMulInvThm], pNe0];   (* p·p⁻¹=1 *)
          tT = ratMulTm[rV, invP];   (* t = r·p⁻¹ *)
          tLt1 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[tT]], pInvEq1],
                   HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[rV,
                     HOL`Bool`SPEC[invP, ratLtMulPosThm]]], invPos], rLtP]];   (* t<1 *)
          tNonneg = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[],
                      HOL`Bool`SPEC[invP, HOL`Stdlib`Rat`ratMulZeroThm]],
                      HOL`Bool`SPEC[rV, HOL`Bool`SPEC[invP, HOL`Stdlib`Rat`ratMulCommThm]]],
                      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rV, HOL`Bool`SPEC[zeroQ[],
                        HOL`Bool`SPEC[invP, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], le0inv], le0r]];   (* 0≤t *)
          dense = HOL`Bool`MP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[tT, ratDenseThm]], tLt1];
          tLtQ = HOL`Bool`CONJUNCT1[dense]; qLt1 = HOL`Bool`CONJUNCT2[dense];
          qMid = concl[tLtQ][[2]];   (* q = ½(t+1) *)
          qPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[qMid, HOL`Bool`SPEC[tT,
                   HOL`Bool`SPEC[zeroQ[], ratLeLtTransThm]]], tNonneg], tLtQ];   (* 0<q *)
          tpEqR = TRANS[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[invP, HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulAssocThm]]],
                    TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], REFL[rV]],
                      TRANS[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[invP, HOL`Stdlib`Rat`ratMulCommThm]], pInvEq1]],
                      HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulOneThm]]];   (* (r·p⁻¹)·p = r *)
          ptEqR = TRANS[HOL`Bool`SPEC[tT, HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratMulCommThm]], tpEqR];   (* p·t = r *)
          ptLtPq = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[],
                     HOL`Bool`SPEC[pV, HOL`Bool`SPEC[tT, HOL`Stdlib`Rat`ratMulCommThm]]],
                     HOL`Bool`SPEC[pV, HOL`Bool`SPEC[qMid, HOL`Stdlib`Rat`ratMulCommThm]]],
                     HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[qMid, HOL`Bool`SPEC[tT,
                       HOL`Bool`SPEC[pV, ratLtMulPosThm]]], pPos], tLtQ]];   (* p·t < p·q *)
          rLtPq = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], ptEqR],
                    REFL[ratMulTm[pV, qMid]]], ptLtPq];   (* r < p·q *)
          mQ1 = EQMP[HOL`Equal`SYM[memEq1[qMid]], qLt1];   (* REP(&ℝ1) q *)
          condProof = HOL`Bool`CONJ[mXp, HOL`Bool`CONJ[mQ1, HOL`Bool`CONJ[pPos,
                        HOL`Bool`CONJ[qPos, rLtPq]]]];
          introOne = nnMemIntroR[xV, oneR, rV, pV, qMid, condProof, hNx, hN1];   (* REP(nnMul x 1) r *)
          introOne
        ];
        HOL`Bool`CHOOSE[pV, opn, inner]
      ];
      result = HOL`Bool`DISJCASES[em, caseNeg, casePos];
      HOL`Bool`DISCH[concl[hX], result]
    ];

    perR = HOL`Bool`GEN[rV, HOL`Kernel`DEDUCTANTISYM[HOL`Bool`UNDISCH[bwd], HOL`Bool`UNDISCH[fwd]]];
    eqThm = realEqFromRepEq[realNnMulTm[xV, oneR], xV, perR];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[nonnegTm[xV], eqThm]]
  ];

(* ⊢ ∀x y z. 0≤x ⇒ 0≤y ⇒ 0≤z ⇒ (x·y)·z = x·(y·z).
   Each direction: destructure the outer positive membership (nnMemPos),
   then the inner one, regroup the rational product (ratMulAssoc), and
   rebuild via nnMemProd (the regrouped pair) + nnMemIntroR. *)
realNnMulAssocNonnegThm =
  Module[{xV, yV, zV, hNx, hNy, hNz, hNxy, hNyz, xy, yz, rV, fwd, bwd, perR, eqThm},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hNx = ASSUME[nonnegTm[xV]]; hNy = ASSUME[nonnegTm[yV]]; hNz = ASSUME[nonnegTm[zV]];
    hNxy = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realNnMulNonnegThm]], hNx], hNy];
    hNyz = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realNnMulNonnegThm]], hNy], hNz];
    xy = realNnMulTm[xV, yV]; yz = realNnMulTm[yV, zV];
    rV = mkVar["r", ratTy];

    fwd = Module[{eqM, disjD, leftD, exPart, hMem, redMem, caseL, caseR, cases},
      eqM = nnMemEq[xy, zV, rV, hNxy, hNz];
      disjD = concl[eqM][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
      hMem = ASSUME[repApp[realNnMulTm[xy, zV], rV]];
      redMem = EQMP[eqM, hMem];
      caseL = nnMemIntroL[xV, yz, rV, ASSUME[leftD], hNx, hNyz];
      caseR = Module[{Pv, qv, innerTerm, condTerm, hCond, mXYP, c1, mZq, c2, hPp, c3,
                      hqp, hrPq, exP1, p1, q1, iT2, cT2, hC2, mXp1, d1, mYq1, d2, hp1,
                      d3, hq1, hPlt, memYZ, q1qPos, PqLt1, assocEq, PqLtRHS, rLt, cond, intro},
        Pv = mkVar["Pp", ratTy]; qv = mkVar["qp", ratTy];
        innerTerm = concl[BETACONV[mkComb[exPart[[2]], Pv]]][[2]];
        condTerm = concl[BETACONV[mkComb[innerTerm[[2]], qv]]][[2]];
        hCond = ASSUME[condTerm];
        mXYP = HOL`Bool`CONJUNCT1[hCond]; c1 = HOL`Bool`CONJUNCT2[hCond]; mZq = HOL`Bool`CONJUNCT1[c1];
        c2 = HOL`Bool`CONJUNCT2[c1]; hPp = HOL`Bool`CONJUNCT1[c2]; c3 = HOL`Bool`CONJUNCT2[c2];
        hqp = HOL`Bool`CONJUNCT1[c3]; hrPq = HOL`Bool`CONJUNCT2[c3];
        exP1 = nnMemPosThm[xV, yV, Pv, mXYP, hPp, hNx, hNy];
        p1 = mkVar["p1", ratTy]; q1 = mkVar["q1", ratTy];
        iT2 = concl[BETACONV[mkComb[concl[exP1][[2]], p1]]][[2]];
        cT2 = concl[BETACONV[mkComb[iT2[[2]], q1]]][[2]];
        hC2 = ASSUME[cT2];
        mXp1 = HOL`Bool`CONJUNCT1[hC2]; d1 = HOL`Bool`CONJUNCT2[hC2]; mYq1 = HOL`Bool`CONJUNCT1[d1];
        d2 = HOL`Bool`CONJUNCT2[d1]; hp1 = HOL`Bool`CONJUNCT1[d2]; d3 = HOL`Bool`CONJUNCT2[d2];
        hq1 = HOL`Bool`CONJUNCT1[d3]; hPlt = HOL`Bool`CONJUNCT2[d3];
        memYZ = nnMemProdThm[yV, zV, q1, qv, mYq1, mZq, hq1, hqp, hNy, hNz];   (* REP(y·z)(q₁·q) *)
        q1qPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[qv, HOL`Bool`SPEC[q1, ratMulPosThm]], hq1], hqp];
        PqLt1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[p1, q1], HOL`Bool`SPEC[Pv,
                  HOL`Bool`SPEC[qv, ratLtMulPosThm]]], hqp], hPlt];   (* P·q < (p₁·q₁)·q *)
        assocEq = HOL`Bool`SPEC[qv, HOL`Bool`SPEC[q1, HOL`Bool`SPEC[p1, HOL`Stdlib`Rat`ratMulAssocThm]]];
        PqLtRHS = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[ratMulTm[Pv, qv]]], assocEq], PqLt1];
        rLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[p1, ratMulTm[q1, qv]],
                HOL`Bool`SPEC[ratMulTm[Pv, qv], HOL`Bool`SPEC[rV, ratLtTransThm]]], hrPq], PqLtRHS];
        cond = HOL`Bool`CONJ[mXp1, HOL`Bool`CONJ[memYZ, HOL`Bool`CONJ[hp1,
                 HOL`Bool`CONJ[q1qPos, rLt]]]];
        intro = nnMemIntroR[xV, yz, rV, p1, ratMulTm[q1, qv], cond, hNx, hNyz];
        HOL`Bool`CHOOSE[Pv, ASSUME[exPart], HOL`Bool`CHOOSE[qv, ASSUME[innerTerm],
          HOL`Bool`CHOOSE[p1, exP1, HOL`Bool`CHOOSE[q1, ASSUME[iT2], intro]]]]
      ];
      cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
      HOL`Bool`DISCH[concl[hMem], cases]
    ];

    bwd = Module[{eqM, disjD, leftD, exPart, hMem, redMem, caseL, caseR, cases},
      eqM = nnMemEq[xV, yz, rV, hNx, hNyz];
      disjD = concl[eqM][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
      hMem = ASSUME[repApp[realNnMulTm[xV, yz], rV]];
      redMem = EQMP[eqM, hMem];
      caseL = nnMemIntroL[xy, zV, rV, ASSUME[leftD], hNxy, hNz];
      caseR = Module[{pv, Qv, innerTerm, condTerm, hCond, mXp, c1, mYZQ, c2, hpp, c3,
                      hQp, hrpQ, exQ1, q1, q2, iT2, cT2, hC2, mYq1, d1, mZq2, d2, hq1,
                      d3, hq2, hQlt, memXY, pq1Pos, pQLt1, assocEq, pQLtRHS, rLt, cond, intro},
        pv = mkVar["pp", ratTy]; Qv = mkVar["Qq", ratTy];
        innerTerm = concl[BETACONV[mkComb[exPart[[2]], pv]]][[2]];
        condTerm = concl[BETACONV[mkComb[innerTerm[[2]], Qv]]][[2]];
        hCond = ASSUME[condTerm];
        mXp = HOL`Bool`CONJUNCT1[hCond]; c1 = HOL`Bool`CONJUNCT2[hCond]; mYZQ = HOL`Bool`CONJUNCT1[c1];
        c2 = HOL`Bool`CONJUNCT2[c1]; hpp = HOL`Bool`CONJUNCT1[c2]; c3 = HOL`Bool`CONJUNCT2[c2];
        hQp = HOL`Bool`CONJUNCT1[c3]; hrpQ = HOL`Bool`CONJUNCT2[c3];
        exQ1 = nnMemPosThm[yV, zV, Qv, mYZQ, hQp, hNy, hNz];
        q1 = mkVar["q1", ratTy]; q2 = mkVar["q2", ratTy];
        iT2 = concl[BETACONV[mkComb[concl[exQ1][[2]], q1]]][[2]];
        cT2 = concl[BETACONV[mkComb[iT2[[2]], q2]]][[2]];
        hC2 = ASSUME[cT2];
        mYq1 = HOL`Bool`CONJUNCT1[hC2]; d1 = HOL`Bool`CONJUNCT2[hC2]; mZq2 = HOL`Bool`CONJUNCT1[d1];
        d2 = HOL`Bool`CONJUNCT2[d1]; hq1 = HOL`Bool`CONJUNCT1[d2]; d3 = HOL`Bool`CONJUNCT2[d2];
        hq2 = HOL`Bool`CONJUNCT1[d3]; hQlt = HOL`Bool`CONJUNCT2[d3];
        memXY = nnMemProdThm[xV, yV, pv, q1, mXp, mYq1, hpp, hq1, hNx, hNy];   (* REP(x·y)(p·q₁) *)
        pq1Pos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[q1, HOL`Bool`SPEC[pv, ratMulPosThm]], hpp], hq1];
        pQLt1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[q1, q2], HOL`Bool`SPEC[Qv,
                  HOL`Bool`SPEC[pv, ratLtMulPosThm]]], hpp], hQlt];   (* Q·p < (q₁·q₂)·p *)
        (* commute both sides: Q·p→p·Q, (q₁·q₂)·p→p·(q₁·q₂), then assoc→(p·q₁)·q₂ *)
        assocEq = HOL`Equal`SYM[HOL`Bool`SPEC[q2, HOL`Bool`SPEC[q1, HOL`Bool`SPEC[pv, HOL`Stdlib`Rat`ratMulAssocThm]]]];
        (* p·(q₁·q₂) = (p·q₁)·q₂ *)
        pQLtRHS = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[],
                    HOL`Bool`SPEC[pv, HOL`Bool`SPEC[Qv, HOL`Stdlib`Rat`ratMulCommThm]]],
                    TRANS[HOL`Bool`SPEC[pv, HOL`Bool`SPEC[ratMulTm[q1, q2], HOL`Stdlib`Rat`ratMulCommThm]], assocEq]], pQLt1];
        (* p·Q < (p·q₁)·q₂ *)
        rLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[ratMulTm[pv, q1], q2],
                HOL`Bool`SPEC[ratMulTm[pv, Qv], HOL`Bool`SPEC[rV, ratLtTransThm]]], hrpQ], pQLtRHS];
        cond = HOL`Bool`CONJ[memXY, HOL`Bool`CONJ[mZq2, HOL`Bool`CONJ[pq1Pos,
                 HOL`Bool`CONJ[hq2, rLt]]]];
        intro = nnMemIntroR[xy, zV, rV, ratMulTm[pv, q1], q2, cond, hNxy, hNz];
        HOL`Bool`CHOOSE[pv, ASSUME[exPart], HOL`Bool`CHOOSE[Qv, ASSUME[innerTerm],
          HOL`Bool`CHOOSE[q1, exQ1, HOL`Bool`CHOOSE[q2, ASSUME[iT2], intro]]]]
      ];
      cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
      HOL`Bool`DISCH[concl[hMem], cases]
    ];

    perR = HOL`Bool`GEN[rV, HOL`Kernel`DEDUCTANTISYM[HOL`Bool`UNDISCH[bwd], HOL`Bool`UNDISCH[fwd]]];
    eqThm = realEqFromRepEq[realNnMulTm[xy, zV], realNnMulTm[xV, yz], perR];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV], HOL`Bool`DISCH[nonnegTm[zV], eqThm]]]]]]
  ];

(* ============================================================ *)
(* Stage D Layer 1 (final): non-negative distributivity.        *)
(*   realNnMul x (y+z) = realNnMul x y + realNnMul x z          *)
(* under 0≤x ∧ 0≤y ∧ 0≤z.  Blueprint: ../archive/tautology      *)
(* Cut/MulDistrib.lean (mul_nonneg_add); STRICT < lets ⊆ use one *)
(* density split + per-summand sign test (no Lean no_max bump),  *)
(* ⊇ uses the Rudin aux (build a negative q' extending p₃·M).    *)
(* ============================================================ *)

(* endpoint-extracting ℚ micro-helpers (cut the SPEC bookkeeping). *)
ratLtA[pf_] := concl[pf][[1, 2]];
ratLtB[pf_] := concl[pf][[2]];
(* a<b, b<c ⊢ a<c *)
ltLt2[ab_, bc_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratLtB[bc],
  HOL`Bool`SPEC[ratLtB[ab], HOL`Bool`SPEC[ratLtA[ab], ratLtTransThm]]], ab], bc];
(* a<b, b≤c ⊢ a<c *)
ltLe2[ab_, bc_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratLtB[bc],
  HOL`Bool`SPEC[ratLtB[ab], HOL`Bool`SPEC[ratLtA[ab], ratLtLeTransThm]]], ab], bc];
(* a≤b, b<c ⊢ a<c *)
leLt2[ab_, bc_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratLtB[bc],
  HOL`Bool`SPEC[ratLtB[ab], HOL`Bool`SPEC[ratLtA[ab], ratLeLtTransThm]]], ab], bc];
(* a<b ⊢ (a+c)<(b+c) *)
ltAddR[ab_, cT_] := HOL`Bool`MP[HOL`Bool`SPEC[cT, HOL`Bool`SPEC[ratLtB[ab],
  HOL`Bool`SPEC[ratLtA[ab], HOL`Stdlib`Rat`ratLtAddMonoThm]]], ab];
(* a<b, 0<w ⊢ (a·w)<(b·w) *)
ltMulR[ab_, wpos_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratLtB[ab],
  HOL`Bool`SPEC[ratLtA[ab], HOL`Bool`SPEC[ratLtB[wpos], ratLtMulPosThm]]], wpos], ab];
(* a<b, ⊢ a=a', ⊢ b=b' → a'<b' *)
rwLt[ltPf_, lEq_, rEq_] := EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lEq], rEq], ltPf];
(* ⊢ ¬(0<t) → ⊢ ratLe t 0 *)
notPosToLe0[hNot_, tT_] :=
  EQMP[TRANS[HOL`Equal`APTERM[notC[], HOL`Bool`SPEC[tT, HOL`Bool`SPEC[zeroQ[],
    HOL`Stdlib`Rat`ratLtNotLeThm]]],
    HOL`Auto`PropTaut`propTaut[mkEq[notTm[notTm[ratLeTm[tT, zeroQ[]]]],
      ratLeTm[tT, zeroQ[]]]]], hNot];
(* ⊢ ¬(r<0) → ⊢ ratLe 0 r *)
notNegToGe0[hNot_, rT_] :=
  EQMP[TRANS[HOL`Equal`APTERM[notC[], HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[rT,
    HOL`Stdlib`Rat`ratLtNotLeThm]]],
    HOL`Auto`PropTaut`propTaut[mkEq[notTm[notTm[ratLeTm[zeroQ[], rT]]],
      ratLeTm[zeroQ[], rT]]]], hNot];
(* 0<a ⊢ ¬(a=0) *)
posToNe0[apos_] := HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[ratLtB[apos], zeroQ[]],
  HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[zeroQ[], ratLtIrreflThm]],
    rwLt[apos, REFL[zeroQ[]], ASSUME[mkEq[ratLtB[apos], zeroQ[]]]]]]];

(* ⊢ ∀y z. 0≤y ⇒ 0≤z ⇒ realLe (&ℝ0) (realAdd y z)  [private interface helper]. *)
realAddNonnegThm =
  Module[{yV, zV, hNy, hNz, leUnfY, leUnfZ, memEq0, rV, hMem0, rLt0, dense, rLtM,
          mLt0, midTm, memYm, negLt, memZsub, inner, memAddEq, addBody, exS,
          memAdd0, impl, allImpl, leThm},
    yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hNy = ASSUME[nonnegTm[yV]]; hNz = ASSUME[nonnegTm[zV]];
    leUnfY = EQMP[unfoldRealLe[zeroRealTm[], yV], hNy];
    leUnfZ = EQMP[unfoldRealLe[zeroRealTm[], zV], hNz];
    memEq0[tT_] := HOL`Bool`SPEC[tT, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];
    rV = mkVar["r", ratTy];
    hMem0 = ASSUME[repApp[zeroRealTm[], rV]];
    rLt0 = EQMP[memEq0[rV], hMem0];   (* r<0 *)
    dense = HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[rV, ratDenseThm]], rLt0];
    rLtM = HOL`Bool`CONJUNCT1[dense]; mLt0 = HOL`Bool`CONJUNCT2[dense];
    midTm = concl[rLtM][[2]];   (* m = ½(r+0) *)
    memYm = HOL`Bool`MP[HOL`Bool`SPEC[midTm, leUnfY], EQMP[HOL`Equal`SYM[memEq0[midTm]], mLt0]];
    negLt = rwLt[ltAddR[rLtM, ratNegTm[midTm]], REFL[ratSubTm[rV, midTm]],
              HOL`Bool`SPEC[midTm, HOL`Stdlib`Rat`ratAddNegThm]];   (* r−m<0 *)
    memZsub = HOL`Bool`MP[HOL`Bool`SPEC[ratSubTm[rV, midTm], leUnfZ],
                EQMP[HOL`Equal`SYM[memEq0[ratSubTm[rV, midTm]]], negLt]];
    inner = HOL`Bool`CONJ[memYm, memZsub];
    memAddEq = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddMemThm]]];
    addBody = concl[memAddEq][[2]];
    exS = HOL`Bool`EXISTS[addBody, midTm, inner];
    memAdd0 = EQMP[HOL`Equal`SYM[memAddEq], exS];
    impl = HOL`Bool`DISCH[concl[hMem0], memAdd0];
    allImpl = HOL`Bool`GEN[rV, impl];
    leThm = EQMP[HOL`Equal`SYM[unfoldRealLe[zeroRealTm[], realAddTm[yV, zV]]], allImpl];
    HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[nonnegTm[yV], HOL`Bool`DISCH[nonnegTm[zV], leThm]]]]
  ];

(* Rudin aux for the ⊇ half: given nonneg cut bCut (hNb), 0<p3 (hp3), 0<M (hM)
   and r<p3·M (hrLt, r = ratLtA[hrLt]), build a NEGATIVE g ∈ bCut with
   0<(g+M) ∧ r<p3·(g+M).  ⊢ ∃g. REP bCut g ∧ 0<(g+M) ∧ r<p3·(g+M).
   by_cases r<0: near-0 midpoint (product>0>r is free); else g = D·p3⁻¹ − M
   with D the (r, p3·M) midpoint.  Blueprint: MulDistrib.lean mul_nonneg_add_ge_aux. *)
distribAux[bCut_, hNb_, p3T_, MT_, hp3_, hM_, hrLt_] :=
  Module[{rA, leUnfB, memEq0B, memBneg, gV, gExTerm, em, caseNeg, casePos},
    rA = ratLtA[hrLt];
    leUnfB = EQMP[unfoldRealLe[zeroRealTm[], bCut], hNb];
    memEq0B[tT_] := HOL`Bool`SPEC[tT, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];
    memBneg[tT_, ltPf_] := HOL`Bool`MP[HOL`Bool`SPEC[tT, leUnfB],
      EQMP[HOL`Equal`SYM[memEq0B[tT]], ltPf]];   (* REP bCut t  from t<0 *)
    gV = mkVar["gg", ratTy];
    gExTerm = existsTm[gV, conjTm[repApp[bCut, gV],
      conjTm[ratLtTm[zeroQ[], ratAddTm[gV, MT]],
        ratLtTm[rA, ratMulTm[p3T, ratAddTm[gV, MT]]]]]];
    em = HOL`Bool`EXCLUDEDMIDDLE[ratLtTm[rA, zeroQ[]]];

    caseNeg = Module[{hrNeg, negMlt0, denseG, negMltG, gLt0, gTm, memBg, zeroLtGM,
                      prodPos, rLtProd, conj},
      hrNeg = ASSUME[ratLtTm[rA, zeroQ[]]];
      negMlt0 = rwLt[ltAddR[hM, ratNegTm[MT]],
        TRANS[HOL`Bool`SPEC[ratNegTm[MT], HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
              HOL`Bool`SPEC[ratNegTm[MT], HOL`Stdlib`Rat`ratAddZeroThm]],
        HOL`Bool`SPEC[MT, HOL`Stdlib`Rat`ratAddNegThm]];   (* −M<0 *)
      denseG = HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[ratNegTm[MT], ratDenseThm]], negMlt0];
      negMltG = HOL`Bool`CONJUNCT1[denseG]; gLt0 = HOL`Bool`CONJUNCT2[denseG];
      gTm = concl[negMltG][[2]];
      memBg = memBneg[gTm, gLt0];
      zeroLtGM = rwLt[ltAddR[negMltG, MT],
        TRANS[HOL`Bool`SPEC[MT, HOL`Bool`SPEC[ratNegTm[MT], HOL`Stdlib`Rat`ratAddCommThm]],
              HOL`Bool`SPEC[MT, HOL`Stdlib`Rat`ratAddNegThm]],
        REFL[ratAddTm[gTm, MT]]];   (* 0<g+M *)
      prodPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratAddTm[gTm, MT],
                  HOL`Bool`SPEC[p3T, ratMulPosThm]], hp3], zeroLtGM];   (* 0<p3·(g+M) *)
      rLtProd = ltLt2[hrNeg, prodPos];   (* r<0<p3·(g+M) *)
      conj = HOL`Bool`CONJ[memBg, HOL`Bool`CONJ[zeroLtGM, rLtProd]];
      HOL`Bool`EXISTS[gExTerm, gTm, conj]
    ];

    casePos = Module[{hrNN, rGe0, denseD, rLtD, DLtPM, DTm, zeroLtD, p3ne0, p3InvEq1,
                      invP3, VTm, zeroLtV, p3V, p3VltP3M, Vp3, Mp3, Vp3LtMp3, le0p3,
                      VltM, gTm, gLt0, memBg, gAddMeqV, zeroLtGM, pGMeqD, rLtPGM, conj},
      hrNN = ASSUME[notTm[ratLtTm[rA, zeroQ[]]]];
      rGe0 = notNegToGe0[hrNN, rA];   (* 0≤r *)
      denseD = HOL`Bool`MP[HOL`Bool`SPEC[ratLtB[hrLt], HOL`Bool`SPEC[rA, ratDenseThm]], hrLt];
      rLtD = HOL`Bool`CONJUNCT1[denseD]; DLtPM = HOL`Bool`CONJUNCT2[denseD];
      DTm = concl[rLtD][[2]];   (* D *)
      zeroLtD = leLt2[rGe0, rLtD];   (* 0<D *)
      p3ne0 = posToNe0[hp3];
      p3InvEq1 = HOL`Bool`MP[HOL`Bool`SPEC[p3T, HOL`Stdlib`Rat`ratMulInvThm], p3ne0];   (* p3·p3⁻¹=1 *)
      invP3 = ratInvTm[p3T];
      invPos = HOL`Bool`MP[HOL`Bool`SPEC[p3T, ratInvPosThm], hp3];   (* 0<p3⁻¹ *)
      VTm = ratMulTm[DTm, invP3];   (* V=D·p3⁻¹ *)
      zeroLtV = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[invP3, HOL`Bool`SPEC[DTm, ratMulPosThm]],
                  zeroLtD], invPos];   (* 0<V *)
      p3V = TRANS[HOL`Bool`SPEC[VTm, HOL`Bool`SPEC[p3T, HOL`Stdlib`Rat`ratMulCommThm]],   (* p3·V=V·p3 *)
        TRANS[HOL`Bool`SPEC[p3T, HOL`Bool`SPEC[invP3, HOL`Bool`SPEC[DTm, HOL`Stdlib`Rat`ratMulAssocThm]]],
          TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], REFL[DTm]],
            TRANS[HOL`Bool`SPEC[p3T, HOL`Bool`SPEC[invP3, HOL`Stdlib`Rat`ratMulCommThm]], p3InvEq1]],
            HOL`Bool`SPEC[DTm, HOL`Stdlib`Rat`ratMulOneThm]]]];   (* p3·V = D *)
      p3VltP3M = rwLt[DLtPM, HOL`Equal`SYM[p3V], REFL[ratMulTm[p3T, MT]]];   (* p3·V<p3·M *)
      Vp3 = HOL`Bool`SPEC[VTm, HOL`Bool`SPEC[p3T, HOL`Stdlib`Rat`ratMulCommThm]];   (* p3·V=V·p3 *)
      Mp3 = HOL`Bool`SPEC[MT, HOL`Bool`SPEC[p3T, HOL`Stdlib`Rat`ratMulCommThm]];   (* p3·M=M·p3 *)
      Vp3LtMp3 = rwLt[p3VltP3M, Vp3, Mp3];   (* V·p3<M·p3 *)
      le0p3 = HOL`Bool`MP[HOL`Bool`SPEC[p3T, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], hp3];   (* 0≤p3 *)
      VltM = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[p3T, HOL`Bool`SPEC[MT,
               HOL`Bool`SPEC[VTm, HOL`Stdlib`Rat`ratLtMulPosCancelThm]]], le0p3], Vp3LtMp3];   (* V<M *)
      gTm = ratSubTm[VTm, MT];   (* g=V−M *)
      gLt0 = rwLt[ltAddR[VltM, ratNegTm[MT]], REFL[ratSubTm[VTm, MT]],
               HOL`Bool`SPEC[MT, HOL`Stdlib`Rat`ratAddNegThm]];   (* V−M<0 *)
      memBg = memBneg[gTm, gLt0];
      gAddMeqV = HOL`Bool`SPEC[MT, HOL`Bool`SPEC[VTm, ratSubAddThm]];   (* (V−M)+M=V *)
      zeroLtGM = rwLt[zeroLtV, REFL[zeroQ[]], HOL`Equal`SYM[gAddMeqV]];   (* 0<(V−M)+M *)
      pGMeqD = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], REFL[p3T]], gAddMeqV], p3V];
      rLtPGM = rwLt[rLtD, REFL[rA], HOL`Equal`SYM[pGMeqD]];   (* r<p3·(g+M) *)
      conj = HOL`Bool`CONJ[memBg, HOL`Bool`CONJ[zeroLtGM, rLtPGM]];
      HOL`Bool`EXISTS[gExTerm, gTm, conj]
    ];

    HOL`Bool`DISJCASES[em, caseNeg, casePos]
  ];

(* ⊢ ∀x y z. 0≤x ⇒ 0≤y ⇒ 0≤z ⇒ realNnMul x (realAdd y z)
                               = realAdd (realNnMul x y) (realNnMul x z). *)
realNnMulDistribNonnegThm =
  Module[{xV, yV, zV, hNx, hNy, hNz, hNyz, hNxy, hNxz, xy, xz, yz, lhs, rhs, rV,
          fwd, bwd, perR},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hNx = ASSUME[nonnegTm[xV]]; hNy = ASSUME[nonnegTm[yV]]; hNz = ASSUME[nonnegTm[zV]];
    hNyz = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddNonnegThm]], hNy], hNz];
    hNxy = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realNnMulNonnegThm]], hNx], hNy];
    hNxz = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zV, HOL`Bool`SPEC[xV, realNnMulNonnegThm]], hNx], hNz];
    xy = realNnMulTm[xV, yV]; xz = realNnMulTm[xV, zV]; yz = realAddTm[yV, zV];
    lhs = realNnMulTm[xV, yz]; rhs = realAddTm[xy, xz];
    rV = mkVar["r", ratTy];

    (* ----- fwd : REP(lhs) r ⇒ REP(rhs) r   (split a product by summand signs) ----- *)
    fwd = Module[{eqM, disjD, leftD, exPart, hMem, redMem, addBodyEq, addBody, mkRHS,
                  caseL, caseR, cases},
      eqM = nnMemEq[xV, yz, rV, hNx, hNyz];
      disjD = concl[eqM][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
      hMem = ASSUME[repApp[lhs, rV]];
      redMem = EQMP[eqM, hMem];
      addBodyEq = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[xz, HOL`Bool`SPEC[xy, realAddMemThm]]];
      addBody = concl[addBodyEq][[2]];
      mkRHS[sWit_, mXY_, mXZ_] := EQMP[HOL`Equal`SYM[addBodyEq],
        HOL`Bool`EXISTS[addBody, sWit, HOL`Bool`CONJ[mXY, mXZ]]];

      caseL = Module[{hL, dense, rLtM, mLt0, midTm, sxy, rmLt0, rsxz},
        hL = ASSUME[leftD];
        dense = HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[rV, ratDenseThm]], hL];
        rLtM = HOL`Bool`CONJUNCT1[dense]; mLt0 = HOL`Bool`CONJUNCT2[dense];
        midTm = concl[rLtM][[2]];
        sxy = nnMemIntroL[xV, yV, midTm, mLt0, hNx, hNy];
        rmLt0 = rwLt[ltAddR[rLtM, ratNegTm[midTm]], REFL[ratSubTm[rV, midTm]],
                  HOL`Bool`SPEC[midTm, HOL`Stdlib`Rat`ratAddNegThm]];   (* r−m<0 *)
        rsxz = nnMemIntroL[xV, zV, ratSubTm[rV, midTm], rmLt0, hNx, hNz];
        mkRHS[midTm, sxy, rsxz]
      ];

      caseR = Module[{pV, qV, innerTerm, condTerm, hCond, mXp, c1, mYZq, c2, hPp, c3,
                      hQp, hrpq, qMemEq, qExBody, qEx, tV, tCondTerm, hTCond, mYt, mZw,
                      wTm, tPlusWeqQ, pqEq, rLtSum, AT, BT, rSubB, rSubBLtA, denseS,
                      rSubBLtS, sLtA, sTm, rSubS, rLtSB, rSubSLtB, memSxy, memRSxz, finalRHS},
        pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy];
        innerTerm = concl[BETACONV[mkComb[exPart[[2]], pV]]][[2]];
        condTerm = concl[BETACONV[mkComb[innerTerm[[2]], qV]]][[2]];
        hCond = ASSUME[condTerm];
        mXp = HOL`Bool`CONJUNCT1[hCond]; c1 = HOL`Bool`CONJUNCT2[hCond]; mYZq = HOL`Bool`CONJUNCT1[c1];
        c2 = HOL`Bool`CONJUNCT2[c1]; hPp = HOL`Bool`CONJUNCT1[c2]; c3 = HOL`Bool`CONJUNCT2[c2];
        hQp = HOL`Bool`CONJUNCT1[c3]; hrpq = HOL`Bool`CONJUNCT2[c3];
        qMemEq = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddMemThm]]];
        qExBody = concl[qMemEq][[2]];
        qEx = EQMP[qMemEq, mYZq];
        tV = mkVar["t", ratTy];
        tCondTerm = concl[BETACONV[mkComb[qExBody[[2]], tV]]][[2]];
        hTCond = ASSUME[tCondTerm];
        mYt = HOL`Bool`CONJUNCT1[hTCond]; mZw = HOL`Bool`CONJUNCT2[hTCond];
        wTm = ratSubTm[qV, tV];
        tPlusWeqQ = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[tV, ratAddSubLeftThm]];   (* t+(q−t)=q *)
        pqEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], REFL[pV]], HOL`Equal`SYM[tPlusWeqQ]],
                 HOL`Bool`SPEC[wTm, HOL`Bool`SPEC[tV, HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratMulDistribThm]]]];
        (* p·q = p·(t+w) = p·t+p·w *)
        rLtSum = rwLt[hrpq, REFL[rV], pqEq];   (* r < p·t+p·w *)
        AT = ratMulTm[pV, tV]; BT = ratMulTm[pV, wTm]; rSubB = ratSubTm[rV, BT];
        rSubBLtA = rwLt[ltAddR[rLtSum, ratNegTm[BT]], REFL[rSubB],
                     HOL`Bool`SPEC[BT, HOL`Bool`SPEC[AT, HOL`Stdlib`Rat`ratAddSubCancelThm]]];   (* r−B<A *)
        denseS = HOL`Bool`MP[HOL`Bool`SPEC[AT, HOL`Bool`SPEC[rSubB, ratDenseThm]], rSubBLtA];
        rSubBLtS = HOL`Bool`CONJUNCT1[denseS]; sLtA = HOL`Bool`CONJUNCT2[denseS];
        sTm = concl[rSubBLtS][[2]]; rSubS = ratSubTm[rV, sTm];
        rLtSB = rwLt[ltAddR[rSubBLtS, BT], HOL`Bool`SPEC[BT, HOL`Bool`SPEC[rV, ratSubAddThm]],
                  REFL[ratAddTm[sTm, BT]]];   (* r<s+B *)
        rSubSLtB = rwLt[ltAddR[rLtSB, ratNegTm[sTm]], REFL[rSubS],
                     HOL`Bool`SPEC[BT, HOL`Bool`SPEC[sTm, ratAddSubCancelLeftThm]]];   (* r−s<B *)
        memSxy = Module[{emT, posT, negT},
          emT = HOL`Bool`EXCLUDEDMIDDLE[ratLtTm[zeroQ[], tV]];
          posT = nnMemIntroR[xV, yV, sTm, pV, tV,
            HOL`Bool`CONJ[mXp, HOL`Bool`CONJ[mYt, HOL`Bool`CONJ[hPp,
              HOL`Bool`CONJ[ASSUME[ratLtTm[zeroQ[], tV]], sLtA]]]], hNx, hNy];
          negT = Module[{hNotPos, tLe0, le0p, ptLe0, sLt0},
            hNotPos = ASSUME[notTm[ratLtTm[zeroQ[], tV]]];
            tLe0 = notPosToLe0[hNotPos, tV];
            le0p = HOL`Bool`MP[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], hPp];
            ptLe0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], REFL[AT]],
                      HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratMulZeroThm]],
                      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[tV,
                        HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], le0p], tLe0]];   (* p·t≤0 *)
            sLt0 = ltLe2[sLtA, ptLe0];
            nnMemIntroL[xV, yV, sTm, sLt0, hNx, hNy]
          ];
          HOL`Bool`DISJCASES[emT, posT, negT]
        ];
        memRSxz = Module[{emW, posW, negW},
          emW = HOL`Bool`EXCLUDEDMIDDLE[ratLtTm[zeroQ[], wTm]];
          posW = nnMemIntroR[xV, zV, rSubS, pV, wTm,
            HOL`Bool`CONJ[mXp, HOL`Bool`CONJ[mZw, HOL`Bool`CONJ[hPp,
              HOL`Bool`CONJ[ASSUME[ratLtTm[zeroQ[], wTm]], rSubSLtB]]]], hNx, hNz];
          negW = Module[{hNotPos, wLe0, le0p, pwLe0, rsLt0},
            hNotPos = ASSUME[notTm[ratLtTm[zeroQ[], wTm]]];
            wLe0 = notPosToLe0[hNotPos, wTm];
            le0p = HOL`Bool`MP[HOL`Bool`SPEC[pV, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], hPp];
            pwLe0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], REFL[BT]],
                      HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratMulZeroThm]],
                      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[wTm,
                        HOL`Bool`SPEC[pV, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], le0p], wLe0]];   (* p·w≤0 *)
            rsLt0 = ltLe2[rSubSLtB, pwLe0];
            nnMemIntroL[xV, zV, rSubS, rsLt0, hNx, hNz]
          ];
          HOL`Bool`DISJCASES[emW, posW, negW]
        ];
        finalRHS = mkRHS[sTm, memSxy, memRSxz];
        HOL`Bool`CHOOSE[pV, ASSUME[exPart], HOL`Bool`CHOOSE[qV, ASSUME[innerTerm],
          HOL`Bool`CHOOSE[tV, qEx, finalRHS]]]
      ];
      cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
      HOL`Bool`DISCH[concl[hMem], cases]
    ];

    (* ----- bwd : REP(rhs) r ⇒ REP(lhs) r   (4 cases; Rudin aux on the mixed two) ----- *)
    bwd = Module[{addEq, hMem, redMem, sV, sBody, sCondTerm, hSCond, memXYs, memXZrs,
                  uT, vT, uvEqR, redU, redV, uLt0Tm, uExTerm, vLt0Tm, vExTerm,
                  uvLtVfromUneg, bothNeg, uNegVpos, uPosVneg, bothPos, result},
      addEq = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[xz, HOL`Bool`SPEC[xy, realAddMemThm]]];
      hMem = ASSUME[repApp[rhs, rV]];
      redMem = EQMP[addEq, hMem];
      sV = mkVar["s", ratTy];
      sBody = concl[addEq][[2]];
      sCondTerm = concl[BETACONV[mkComb[sBody[[2]], sV]]][[2]];
      hSCond = ASSUME[sCondTerm];
      memXYs = HOL`Bool`CONJUNCT1[hSCond]; memXZrs = HOL`Bool`CONJUNCT2[hSCond];
      uT = sV; vT = ratSubTm[rV, sV];
      uvEqR = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[sV, ratAddSubLeftThm]];   (* u+v = r *)
      redU = EQMP[nnMemEq[xV, yV, uT, hNx, hNy], memXYs];
      redV = EQMP[nnMemEq[xV, zV, vT, hNx, hNz], memXZrs];
      uLt0Tm = concl[redU][[1, 2]]; uExTerm = concl[redU][[2]];
      vLt0Tm = concl[redV][[1, 2]]; vExTerm = concl[redV][[2]];
      (* u<0 ⊢ u+v<v *)
      uvLtVfromUneg[hUneg_] := rwLt[ltAddR[hUneg, vT], REFL[ratAddTm[uT, vT]],
        TRANS[HOL`Bool`SPEC[vT, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
              HOL`Bool`SPEC[vT, HOL`Stdlib`Rat`ratAddZeroThm]]];

      bothNeg = Module[{hUneg, hVneg, uvLtV, uvLt0, rLt0},
        hUneg = ASSUME[uLt0Tm]; hVneg = ASSUME[vLt0Tm];
        uvLtV = uvLtVfromUneg[hUneg];
        uvLt0 = ltLt2[uvLtV, hVneg];
        rLt0 = rwLt[uvLt0, uvEqR, REFL[zeroQ[]]];   (* r<0 *)
        nnMemIntroL[xV, yz, rV, rLt0, hNx, hNyz]
      ];

      uNegVpos = Module[{hUneg, p2V, w2V, vInner, vCondTerm, hVC, mXp2, e1, mZw2, e2,
                         hp2, e3, hw2, hvLt, openX2, p3V, hOC, mXp3, p2Ltp3, hp3,
                         vLtP3w2, uvLtP3w2, rLtP3w2, auxThm, gV, gAbs, gCondTerm, hGC,
                         memYg, g1, zeroLtGM, rLtProd, qTm, qSubGeqW2, memZqSubG,
                         sumInner, yzMemEq, yzBody, exYZ, memYZq, condProof, memLHS},
        hUneg = ASSUME[uLt0Tm];
        p2V = mkVar["pb", ratTy]; w2V = mkVar["wb", ratTy];
        vInner = concl[BETACONV[mkComb[vExTerm[[2]], p2V]]][[2]];
        vCondTerm = concl[BETACONV[mkComb[vInner[[2]], w2V]]][[2]];
        hVC = ASSUME[vCondTerm];
        mXp2 = HOL`Bool`CONJUNCT1[hVC]; e1 = HOL`Bool`CONJUNCT2[hVC]; mZw2 = HOL`Bool`CONJUNCT1[e1];
        e2 = HOL`Bool`CONJUNCT2[e1]; hp2 = HOL`Bool`CONJUNCT1[e2]; e3 = HOL`Bool`CONJUNCT2[e2];
        hw2 = HOL`Bool`CONJUNCT1[e3]; hvLt = HOL`Bool`CONJUNCT2[e3];
        openX2 = HOL`Bool`MP[HOL`Bool`SPEC[p2V, HOL`Bool`SPEC[xV, realOpenThm]], mXp2];
        p3V = mkVar["pc", ratTy];
        hOC = ASSUME[conjTm[repApp[xV, p3V], ratLtTm[p2V, p3V]]];
        mXp3 = HOL`Bool`CONJUNCT1[hOC]; p2Ltp3 = HOL`Bool`CONJUNCT2[hOC];
        hp3 = ltLt2[hp2, p2Ltp3];
        vLtP3w2 = ltLt2[hvLt, ltMulR[p2Ltp3, hw2]];   (* v<p2·w2<p3·w2 *)
        uvLtP3w2 = ltLt2[uvLtVfromUneg[hUneg], vLtP3w2];   (* u+v<p3·w2 *)
        rLtP3w2 = rwLt[uvLtP3w2, uvEqR, REFL[ratMulTm[p3V, w2V]]];   (* r<p3·w2 *)
        auxThm = distribAux[yV, hNy, p3V, w2V, hp3, hw2, rLtP3w2];
        gV = mkVar["gg", ratTy]; gAbs = concl[auxThm][[2]];
        gCondTerm = concl[BETACONV[mkComb[gAbs, gV]]][[2]];
        hGC = ASSUME[gCondTerm];
        memYg = HOL`Bool`CONJUNCT1[hGC]; g1 = HOL`Bool`CONJUNCT2[hGC];
        zeroLtGM = HOL`Bool`CONJUNCT1[g1]; rLtProd = HOL`Bool`CONJUNCT2[g1];
        qTm = ratAddTm[gV, w2V];
        qSubGeqW2 = HOL`Bool`SPEC[w2V, HOL`Bool`SPEC[gV, ratAddSubCancelLeftThm]];   (* (g+w2)−g=w2 *)
        memZqSubG = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[zV], qSubGeqW2]], mZw2];
        sumInner = HOL`Bool`CONJ[memYg, memZqSubG];
        yzMemEq = HOL`Bool`SPEC[qTm, HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddMemThm]]];
        yzBody = concl[yzMemEq][[2]];
        exYZ = HOL`Bool`EXISTS[yzBody, gV, sumInner];
        memYZq = EQMP[HOL`Equal`SYM[yzMemEq], exYZ];
        condProof = HOL`Bool`CONJ[mXp3, HOL`Bool`CONJ[memYZq, HOL`Bool`CONJ[hp3,
          HOL`Bool`CONJ[zeroLtGM, rLtProd]]]];
        memLHS = nnMemIntroR[xV, yz, rV, p3V, qTm, condProof, hNx, hNyz];
        HOL`Bool`CHOOSE[p2V, ASSUME[vExTerm], HOL`Bool`CHOOSE[w2V, ASSUME[vInner],
          HOL`Bool`CHOOSE[p3V, openX2, HOL`Bool`CHOOSE[gV, auxThm, memLHS]]]]
      ];

      uPosVneg = Module[{hVneg, p1V, t1V, uInner, uCondTerm, hUC, mXp1, e1, mYt1, e2,
                         hp1, e3, ht1, huLt, openX1, p3V, hOC, mXp3, p1Ltp3, hp3,
                         uLtP3t1, uvLtU, uvLtP3t1, rLtP3t1, auxThm, gV, gAbs, gCondTerm,
                         hGC, memZg, g1, zeroLtGM, rLtProd, qTm, qSubT1eqG, memZqSubT1,
                         sumInner, yzMemEq, yzBody, exYZ, memYZq, condProof, memLHS},
        hVneg = ASSUME[vLt0Tm];
        p1V = mkVar["pa", ratTy]; t1V = mkVar["ta", ratTy];
        uInner = concl[BETACONV[mkComb[uExTerm[[2]], p1V]]][[2]];
        uCondTerm = concl[BETACONV[mkComb[uInner[[2]], t1V]]][[2]];
        hUC = ASSUME[uCondTerm];
        mXp1 = HOL`Bool`CONJUNCT1[hUC]; e1 = HOL`Bool`CONJUNCT2[hUC]; mYt1 = HOL`Bool`CONJUNCT1[e1];
        e2 = HOL`Bool`CONJUNCT2[e1]; hp1 = HOL`Bool`CONJUNCT1[e2]; e3 = HOL`Bool`CONJUNCT2[e2];
        ht1 = HOL`Bool`CONJUNCT1[e3]; huLt = HOL`Bool`CONJUNCT2[e3];
        openX1 = HOL`Bool`MP[HOL`Bool`SPEC[p1V, HOL`Bool`SPEC[xV, realOpenThm]], mXp1];
        p3V = mkVar["pc", ratTy];
        hOC = ASSUME[conjTm[repApp[xV, p3V], ratLtTm[p1V, p3V]]];
        mXp3 = HOL`Bool`CONJUNCT1[hOC]; p1Ltp3 = HOL`Bool`CONJUNCT2[hOC];
        hp3 = ltLt2[hp1, p1Ltp3];
        uLtP3t1 = ltLt2[huLt, ltMulR[p1Ltp3, ht1]];   (* u<p1·t1<p3·t1 *)
        uvLtU = rwLt[ltAddR[hVneg, uT], HOL`Bool`SPEC[uT, HOL`Bool`SPEC[vT, HOL`Stdlib`Rat`ratAddCommThm]],
          TRANS[HOL`Bool`SPEC[uT, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
                HOL`Bool`SPEC[uT, HOL`Stdlib`Rat`ratAddZeroThm]]];   (* u+v<u *)
        uvLtP3t1 = ltLt2[uvLtU, uLtP3t1];
        rLtP3t1 = rwLt[uvLtP3t1, uvEqR, REFL[ratMulTm[p3V, t1V]]];
        auxThm = distribAux[zV, hNz, p3V, t1V, hp3, ht1, rLtP3t1];
        gV = mkVar["gg", ratTy]; gAbs = concl[auxThm][[2]];
        gCondTerm = concl[BETACONV[mkComb[gAbs, gV]]][[2]];
        hGC = ASSUME[gCondTerm];
        memZg = HOL`Bool`CONJUNCT1[hGC]; g1 = HOL`Bool`CONJUNCT2[hGC];
        zeroLtGM = HOL`Bool`CONJUNCT1[g1]; rLtProd = HOL`Bool`CONJUNCT2[g1];
        qTm = ratAddTm[gV, t1V];
        qSubT1eqG = HOL`Bool`SPEC[t1V, HOL`Bool`SPEC[gV, HOL`Stdlib`Rat`ratAddSubCancelThm]];   (* (g+t1)−t1=g *)
        memZqSubT1 = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[zV], qSubT1eqG]], memZg];
        sumInner = HOL`Bool`CONJ[mYt1, memZqSubT1];
        yzMemEq = HOL`Bool`SPEC[qTm, HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddMemThm]]];
        yzBody = concl[yzMemEq][[2]];
        exYZ = HOL`Bool`EXISTS[yzBody, t1V, sumInner];
        memYZq = EQMP[HOL`Equal`SYM[yzMemEq], exYZ];
        condProof = HOL`Bool`CONJ[mXp3, HOL`Bool`CONJ[memYZq, HOL`Bool`CONJ[hp3,
          HOL`Bool`CONJ[zeroLtGM, rLtProd]]]];
        memLHS = nnMemIntroR[xV, yz, rV, p3V, qTm, condProof, hNx, hNyz];
        HOL`Bool`CHOOSE[p1V, ASSUME[uExTerm], HOL`Bool`CHOOSE[t1V, ASSUME[uInner],
          HOL`Bool`CHOOSE[p3V, openX1, HOL`Bool`CHOOSE[gV, auxThm, memLHS]]]]
      ];

      bothPos = Module[{p1V, t1V, uInner, uCondTerm, hUC, mXp1, e1, mYt1, e2, hp1, e3,
                        ht1, huLt, p2V, w2V, vInner, vCondTerm, hVC, mXp2, f1, mZw2, f2,
                        hp2, f3, hw2, hvLt, buildFromP3, leTotal, caseP1leP2, caseP2leP1},
        p1V = mkVar["pa", ratTy]; t1V = mkVar["ta", ratTy];
        uInner = concl[BETACONV[mkComb[uExTerm[[2]], p1V]]][[2]];
        uCondTerm = concl[BETACONV[mkComb[uInner[[2]], t1V]]][[2]];
        hUC = ASSUME[uCondTerm];
        mXp1 = HOL`Bool`CONJUNCT1[hUC]; e1 = HOL`Bool`CONJUNCT2[hUC]; mYt1 = HOL`Bool`CONJUNCT1[e1];
        e2 = HOL`Bool`CONJUNCT2[e1]; hp1 = HOL`Bool`CONJUNCT1[e2]; e3 = HOL`Bool`CONJUNCT2[e2];
        ht1 = HOL`Bool`CONJUNCT1[e3]; huLt = HOL`Bool`CONJUNCT2[e3];
        p2V = mkVar["pb", ratTy]; w2V = mkVar["wb", ratTy];
        vInner = concl[BETACONV[mkComb[vExTerm[[2]], p2V]]][[2]];
        vCondTerm = concl[BETACONV[mkComb[vInner[[2]], w2V]]][[2]];
        hVC = ASSUME[vCondTerm];
        mXp2 = HOL`Bool`CONJUNCT1[hVC]; f1 = HOL`Bool`CONJUNCT2[hVC]; mZw2 = HOL`Bool`CONJUNCT1[f1];
        f2 = HOL`Bool`CONJUNCT2[f1]; hp2 = HOL`Bool`CONJUNCT1[f2]; f3 = HOL`Bool`CONJUNCT2[f2];
        hw2 = HOL`Bool`CONJUNCT1[f3]; hvLt = HOL`Bool`CONJUNCT2[f3];

        buildFromP3[p3V_, mXp3_, p1Ltp3_, p2Ltp3_, hp3_] :=
          Module[{uLtP3t1, vLtP3w2, s1, s2c, s2, uvLtSum, qTm, distribEq, rLtP3q,
                  w2LtSum, qPos, qSubT1eqW2, memZqSub, sumInner, yzMemEq, yzBody,
                  exYZ, memYZq, condProof},
            uLtP3t1 = ltLt2[huLt, ltMulR[p1Ltp3, ht1]];
            vLtP3w2 = ltLt2[hvLt, ltMulR[p2Ltp3, hw2]];
            s1 = ltAddR[uLtP3t1, vT];   (* u+v<(p3·t1)+v *)
            s2c = ltAddR[vLtP3w2, ratMulTm[p3V, t1V]];   (* v+(p3t1)<(p3w2)+(p3t1) *)
            s2 = rwLt[s2c,
              HOL`Bool`SPEC[ratMulTm[p3V, t1V], HOL`Bool`SPEC[vT, HOL`Stdlib`Rat`ratAddCommThm]],
              HOL`Bool`SPEC[ratMulTm[p3V, t1V], HOL`Bool`SPEC[ratMulTm[p3V, w2V], HOL`Stdlib`Rat`ratAddCommThm]]];
            (* (p3t1)+v < (p3t1)+(p3w2) *)
            uvLtSum = ltLt2[s1, s2];   (* u+v<(p3t1)+(p3w2) *)
            qTm = ratAddTm[t1V, w2V];
            distribEq = HOL`Bool`SPEC[w2V, HOL`Bool`SPEC[t1V, HOL`Bool`SPEC[p3V, HOL`Stdlib`Rat`ratMulDistribThm]]];
            rLtP3q = rwLt[uvLtSum, uvEqR, HOL`Equal`SYM[distribEq]];   (* r<p3·(t1+w2) *)
            w2LtSum = rwLt[ltAddR[ht1, w2V],
              TRANS[HOL`Bool`SPEC[w2V, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
                    HOL`Bool`SPEC[w2V, HOL`Stdlib`Rat`ratAddZeroThm]], REFL[ratAddTm[t1V, w2V]]];   (* w2<t1+w2 *)
            qPos = ltLt2[hw2, w2LtSum];   (* 0<t1+w2 *)
            qSubT1eqW2 = HOL`Bool`SPEC[w2V, HOL`Bool`SPEC[t1V, ratAddSubCancelLeftThm]];   (* (t1+w2)−t1=w2 *)
            memZqSub = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[zV], qSubT1eqW2]], mZw2];
            sumInner = HOL`Bool`CONJ[mYt1, memZqSub];
            yzMemEq = HOL`Bool`SPEC[qTm, HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddMemThm]]];
            yzBody = concl[yzMemEq][[2]];
            exYZ = HOL`Bool`EXISTS[yzBody, t1V, sumInner];
            memYZq = EQMP[HOL`Equal`SYM[yzMemEq], exYZ];
            condProof = HOL`Bool`CONJ[mXp3, HOL`Bool`CONJ[memYZq, HOL`Bool`CONJ[hp3,
              HOL`Bool`CONJ[qPos, rLtP3q]]]];
            nnMemIntroR[xV, yz, rV, p3V, qTm, condProof, hNx, hNyz]
          ];

        leTotal = HOL`Bool`SPEC[p2V, HOL`Bool`SPEC[p1V, HOL`Stdlib`Rat`ratLeTotalThm]];   (* p1≤p2 ∨ p2≤p1 *)
        caseP1leP2 = Module[{hLe, openX2, p3V, hOC, mXp3, p2Ltp3, p1Ltp3, hp3},
          hLe = ASSUME[ratLeTm[p1V, p2V]];
          openX2 = HOL`Bool`MP[HOL`Bool`SPEC[p2V, HOL`Bool`SPEC[xV, realOpenThm]], mXp2];
          p3V = mkVar["pc", ratTy];
          hOC = ASSUME[conjTm[repApp[xV, p3V], ratLtTm[p2V, p3V]]];
          mXp3 = HOL`Bool`CONJUNCT1[hOC]; p2Ltp3 = HOL`Bool`CONJUNCT2[hOC];
          p1Ltp3 = leLt2[hLe, p2Ltp3]; hp3 = ltLt2[hp2, p2Ltp3];
          HOL`Bool`CHOOSE[p3V, openX2, buildFromP3[p3V, mXp3, p1Ltp3, p2Ltp3, hp3]]
        ];
        caseP2leP1 = Module[{hLe, openX1, p3V, hOC, mXp3, p1Ltp3, p2Ltp3, hp3},
          hLe = ASSUME[ratLeTm[p2V, p1V]];
          openX1 = HOL`Bool`MP[HOL`Bool`SPEC[p1V, HOL`Bool`SPEC[xV, realOpenThm]], mXp1];
          p3V = mkVar["pc", ratTy];
          hOC = ASSUME[conjTm[repApp[xV, p3V], ratLtTm[p1V, p3V]]];
          mXp3 = HOL`Bool`CONJUNCT1[hOC]; p1Ltp3 = HOL`Bool`CONJUNCT2[hOC];
          p2Ltp3 = leLt2[hLe, p1Ltp3]; hp3 = ltLt2[hp1, p1Ltp3];
          HOL`Bool`CHOOSE[p3V, openX1, buildFromP3[p3V, mXp3, p1Ltp3, p2Ltp3, hp3]]
        ];
        HOL`Bool`CHOOSE[p1V, ASSUME[uExTerm], HOL`Bool`CHOOSE[t1V, ASSUME[uInner],
          HOL`Bool`CHOOSE[p2V, ASSUME[vExTerm], HOL`Bool`CHOOSE[w2V, ASSUME[vInner],
            HOL`Bool`DISJCASES[leTotal, caseP1leP2, caseP2leP1]]]]]
      ];

      result = HOL`Bool`DISJCASES[redU,
        HOL`Bool`DISJCASES[redV, bothNeg, uNegVpos],
        HOL`Bool`DISJCASES[redV, uPosVneg, bothPos]];
      HOL`Bool`DISCH[concl[hMem], HOL`Bool`CHOOSE[sV, redMem, result]]
    ];

    perR = HOL`Bool`GEN[rV, HOL`Kernel`DEDUCTANTISYM[HOL`Bool`UNDISCH[bwd], HOL`Bool`UNDISCH[fwd]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV], HOL`Bool`DISCH[nonnegTm[zV],
        realEqFromRepEq[lhs, rhs, perR]]]]]]]
  ];

(* ============================================================ *)
(* Layer 2 — signed multiplication  realMul.                    *)
(* Binary COND split on 0≤x / 0≤y (zero folds into nonneg);     *)
(* all sign cases reduce to the Layer-1 nonneg laws via the     *)
(* realNeg sign homomorphism.  Blueprint: ../archive/tautology  *)
(* Cut/Mul.lean + MulComm.lean (ternary→binary; signed distrib  *)
(* is the one no-reference step).                                *)
(* ============================================================ *)

(* ---- real additive-group micro-helpers (abelian; concise chains) ---- *)
rNeg[a_] := realNegTm[a];
rAdd[a_, b_] := realAddTm[a, b];
rZ[] := zeroRealTm[];
rAddZeroR[a_] := HOL`Bool`SPEC[a, realAddZeroThm];                       (* a+0 = a *)
rComm[a_, b_] := HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, realAddCommThm]];     (* a+b = b+a *)
rAddZeroL[a_] := TRANS[rComm[rZ[], a], rAddZeroR[a]];                    (* 0+a = a *)
rAddNegR[a_] := HOL`Bool`SPEC[a, realAddNegThm];                         (* a+(−a) = 0 *)
rAddNegL[a_] := TRANS[rComm[rNeg[a], a], rAddNegR[a]];                   (* (−a)+a = 0 *)
rAssoc[a_, b_, c_] := HOL`Bool`SPEC[c, HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, realAddAssocThm]]];   (* (a+b)+c = a+(b+c) *)
rAddCongL[eq_, c_] := HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], eq], REFL[c]];  (* a=b → a+c = b+c *)
rAddCongR[c_, eq_] := HOL`Equal`APTERM[mkComb[realAddConst[], c], eq];   (* a=b → c+a = c+b *)
rNegCong[eq_] := HOL`Equal`APTERM[realNegConst[], eq];                   (* a=b → −a = −b *)

(* ⊢ ∀a b c. realAdd a b = realAdd a c ⇒ b = c  (left cancellation). *)
realAddCancelLeftThm =
  Module[{aV, bV, cV, h, naTm, apL, chain},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; cV = mkVar["c", realTy];
    h = ASSUME[mkEq[rAdd[aV, bV], rAdd[aV, cV]]];
    naTm = rNeg[aV];
    apL = HOL`Equal`APTERM[mkComb[realAddConst[], naTm], h];   (* na+(a+b) = na+(a+c) *)
    chain[tT_] := TRANS[HOL`Equal`SYM[rAssoc[naTm, aV, tT]],
                    TRANS[rAddCongL[rAddNegL[aV], tT], rAddZeroL[tT]]];   (* na+(a+t) = t *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[concl[h], TRANS[HOL`Equal`SYM[chain[bV]], TRANS[apL, chain[cV]]]]]]]
  ];

(* ⊢ realNeg (&ℝ 0) = &ℝ 0. *)
realNegZeroThm =
  Module[{nz},
    nz = rNeg[rZ[]];
    TRANS[HOL`Equal`SYM[rAddZeroR[nz]], TRANS[rComm[nz, rZ[]], rAddNegR[rZ[]]]]
  ];

(* ⊢ ∀x. realNeg (realNeg x) = x  (group: inverse of inverse). *)
realNegNegThm =
  Module[{xV, nx, e1, e2, eqAdd, cancel},
    xV = mkVar["x", realTy]; nx = rNeg[xV];
    e1 = rAddNegL[xV];                 (* (−x)+x = 0 *)
    e2 = rAddNegR[nx];                 (* (−x)+(−−x) = 0 *)
    eqAdd = TRANS[e1, HOL`Equal`SYM[e2]];   (* (−x)+x = (−x)+(−−x) *)
    cancel = HOL`Bool`MP[HOL`Bool`SPEC[rNeg[nx], HOL`Bool`SPEC[xV, HOL`Bool`SPEC[nx, realAddCancelLeftThm]]], eqAdd];
    HOL`Bool`GEN[xV, HOL`Equal`SYM[cancel]]   (* x = −−x  ⟹  −−x = x *)
  ];

(* ⊢ ∀x y. realLe x y ⇒ realLe (realNeg y) (realNeg x).
   Pure cut: if t ∉ y then t ∉ x (x⊆y), so the same witness r serves −x. *)
realLeNegThm =
  Module[{xV, yV, h, leUnf, qV, rV, memNegY, memNegX, hMem, redMem, bodyX,
          innerBodyY, hConj, posR, notY, tArg, notX, condX, exX, memNegXq, chR,
          impl, allQ, leNeg},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    h = ASSUME[realLeTm[xV, yV]];
    leUnf = EQMP[unfoldRealLe[xV, yV], h];   (* ∀p. REP x p ⇒ REP y p *)
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    memNegY = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[yV, realNegMemThm]];
    memNegX = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[xV, realNegMemThm]];
    hMem = ASSUME[repApp[rNeg[yV], qV]];
    redMem = EQMP[memNegY, hMem];            (* ∃r. 0<r ∧ ¬REP y(−(q+r)) *)
    bodyX = concl[memNegX][[2]];
    innerBodyY = concl[BETACONV[mkComb[concl[memNegY][[2, 2]], rV]]][[2]];
    hConj = ASSUME[innerBodyY];
    posR = HOL`Bool`CONJUNCT1[hConj]; notY = HOL`Bool`CONJUNCT2[hConj];
    tArg = ratNegTm[ratAddTm[qV, rV]];
    notX = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[repApp[xV, tArg],
             HOL`Bool`MP[HOL`Bool`NOTELIM[notY],
               HOL`Bool`MP[HOL`Bool`SPEC[tArg, leUnf], ASSUME[repApp[xV, tArg]]]]]];
    condX = HOL`Bool`CONJ[posR, notX];
    exX = HOL`Bool`EXISTS[bodyX, rV, condX];
    memNegXq = EQMP[HOL`Equal`SYM[memNegX], exX];
    chR = HOL`Bool`CHOOSE[rV, redMem, memNegXq];
    impl = HOL`Bool`DISCH[concl[hMem], chR];
    allQ = HOL`Bool`GEN[qV, impl];
    leNeg = EQMP[HOL`Equal`SYM[unfoldRealLe[rNeg[yV], rNeg[xV]]], allQ];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[concl[h], leNeg]]]
  ];

(* ⊢ ∀x. realLe x 0 ⇒ realLe 0 (realNeg x).  (from realLeNeg + realNegZero) *)
realNegNonnegThm =
  Module[{xV, h, ln},
    xV = mkVar["x", realTy];
    h = ASSUME[realLeTm[xV, rZ[]]];
    ln = HOL`Bool`MP[HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[xV, realLeNegThm]], h];   (* realLe(−0)(−x) *)
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[h],
      EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], realNegZeroThm], REFL[rNeg[xV]]], ln]]]
  ];

(* ⊢ ∀x. realLe 0 x ⇒ realLe (realNeg x) 0.  (from realLeNeg + realNegZero) *)
realNegNonposThm =
  Module[{xV, h, ln},
    xV = mkVar["x", realTy];
    h = ASSUME[realLeTm[rZ[], xV]];
    ln = HOL`Bool`MP[HOL`Bool`SPEC[xV, HOL`Bool`SPEC[rZ[], realLeNegThm]], h];   (* realLe(−x)(−0) *)
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[h],
      EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], REFL[rNeg[xV]]], realNegZeroThm], ln]]]
  ];

(* ⊢ ∀x. ¬(realLe 0 x) ⇒ realLe x 0.  (totality) *)
notNonnegToLeZeroThm =
  Module[{xV, hN, total, xLe0},
    xV = mkVar["x", realTy];
    hN = ASSUME[notTm[realLeTm[rZ[], xV]]];
    total = HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[xV, realLeTotalThm]];   (* realLe x 0 ∨ realLe 0 x *)
    xLe0 = HOL`Bool`DISJCASES[total, ASSUME[realLeTm[xV, rZ[]]],
             HOL`Bool`CONTR[realLeTm[xV, rZ[]], HOL`Bool`MP[HOL`Bool`NOTELIM[hN], ASSUME[realLeTm[rZ[], xV]]]]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[hN], xLe0]]
  ];

(* ⊢ ∀x. ¬(realLe 0 x) ⇒ realLe 0 (realNeg x). *)
notNonnegNegThm =
  Module[{xV, hN},
    xV = mkVar["x", realTy];
    hN = ASSUME[notTm[realLeTm[rZ[], xV]]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[hN],
      HOL`Bool`MP[HOL`Bool`SPEC[xV, realNegNonnegThm],
        HOL`Bool`MP[HOL`Bool`SPEC[xV, notNonnegToLeZeroThm], hN]]]]
  ];

(* ⊢ ∀x y. realNeg (realAdd x y) = realAdd (realNeg x) (realNeg y). *)
realNegAddThm =
  Module[{xV, yV, nx, ny, inner, sumZero, e2, eqAdd, cancel},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; nx = rNeg[xV]; ny = rNeg[yV];
    (* inner : y+(−y) within  b+((−a)+(−b)) reduction  — compute (x+y)+((−x)+(−y)) = 0 *)
    inner = TRANS[rAddCongR[yV, rComm[nx, ny]],            (* y+((−x)+(−y)) = y+((−y)+(−x)) *)
              TRANS[HOL`Equal`SYM[rAssoc[yV, ny, nx]],     (*   = (y+(−y))+(−x) *)
                TRANS[rAddCongL[rAddNegR[yV], nx], rAddZeroL[nx]]]];   (*   = 0+(−x) = (−x) *)
    sumZero = TRANS[rAssoc[xV, yV, rAdd[nx, ny]],          (* (x+y)+((−x)+(−y)) = x+(y+((−x)+(−y))) *)
                TRANS[rAddCongR[xV, inner], rAddNegR[xV]]];   (*   = x+(−x) = 0 *)
    e2 = rAddNegR[rAdd[xV, yV]];                           (* (x+y)+(−(x+y)) = 0 *)
    eqAdd = TRANS[e2, HOL`Equal`SYM[sumZero]];             (* (x+y)+(−(x+y)) = (x+y)+((−x)+(−y)) *)
    cancel = HOL`Bool`MP[HOL`Bool`SPEC[rAdd[nx, ny], HOL`Bool`SPEC[rNeg[rAdd[xV, yV]],
               HOL`Bool`SPEC[rAdd[xV, yV], realAddCancelLeftThm]]], eqAdd];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, cancel]]
  ];

(* ---- realMul definition (nested COND, binary sign split) ---- *)
realMulTyL2 = tyFun[realTy, tyFun[realTy, realTy]];
condTm[cT_, aT_, bT_] := mkComb[mkComb[mkComb[HOL`Bool`condConst[realTy], cT], aT], bT];

(* the four branch values *)
brPP[xT_, yT_] := realNnMulTm[xT, yT];
brPN[xT_, yT_] := rNeg[realNnMulTm[xT, rNeg[yT]]];
brNP[xT_, yT_] := rNeg[realNnMulTm[rNeg[xT], yT]];
brNN[xT_, yT_] := realNnMulTm[rNeg[xT], rNeg[yT]];
innerPosTm[xT_, yT_] := condTm[nonnegTm[yT], brPP[xT, yT], brPN[xT, yT]];
innerNegTm[xT_, yT_] := condTm[nonnegTm[yT], brNP[xT, yT], brNN[xT, yT]];
realMulBodyTm[xT_, yT_] := condTm[nonnegTm[xT], innerPosTm[xT, yT], innerNegTm[xT, yT]];

realMulDefThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = mkAbs[xV, mkAbs[yV, realMulBodyTm[xV, yV]]];
    newDefinition[mkEq[mkVar["realMul", realMulTyL2], body]]
  ];

realMulConst[] := mkConst["realMul", realMulTyL2];
realMulTm[xT_, yT_] := mkComb[mkComb[realMulConst[], xT], yT];

unfoldRealMul[xT_, yT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[realMulDefThm, xT];
    s1b = TRANS[s1, BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, yT];
    TRANS[s2, BETACONV[concl[s2][[2]]]]
  ];

(* local EQF intro (HOL`Auto`PropTaut`eqfIntro is Private — unreachable here). *)
falseTm[] := mkConst["F", boolTy];
eqfIntroL[thNotP_] :=
  Module[{p, pToF, fToP},
    p = concl[thNotP][[2]];
    pToF = HOL`Bool`MP[HOL`Bool`NOTELIM[thNotP], ASSUME[p]];
    fToP = HOL`Bool`CONTR[p, ASSUME[falseTm[]]];
    HOL`Kernel`DEDUCTANTISYM[fToP, pToF]];

(* COND condition rewriters: condProof ⊢ c gives COND c a b = a; ¬c gives = b. *)
condReduceT[condProof_, aT_, bT_] :=
  TRANS[HOL`Equal`APTHM[HOL`Equal`APTHM[
          HOL`Equal`APTERM[HOL`Bool`condConst[realTy], HOL`Bool`EQTINTRO[condProof]], aT], bT],
        HOL`Bool`ISPEC[bT, HOL`Bool`ISPEC[aT, HOL`Bool`condTThm]]];
condReduceF[notCondProof_, aT_, bT_] :=
  TRANS[HOL`Equal`APTHM[HOL`Equal`APTHM[
          HOL`Equal`APTERM[HOL`Bool`condConst[realTy], eqfIntroL[notCondProof]], aT], bT],
        HOL`Bool`ISPEC[bT, HOL`Bool`ISPEC[aT, HOL`Bool`condFThm]]];

(* the four case-reduction theorems *)
realMulCasePPThm =
  Module[{xV, yV, hPx, hPy, unfold, outer, inner},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hPx = ASSUME[nonnegTm[xV]]; hPy = ASSUME[nonnegTm[yV]];
    unfold = unfoldRealMul[xV, yV];
    outer = condReduceT[hPx, innerPosTm[xV, yV], innerNegTm[xV, yV]];
    inner = condReduceT[hPy, brPP[xV, yV], brPN[xV, yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV],
      TRANS[unfold, TRANS[outer, inner]]]]]]
  ];
realMulCasePNThm =
  Module[{xV, yV, hPx, hNy, unfold, outer, inner},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hPx = ASSUME[nonnegTm[xV]]; hNy = ASSUME[notTm[nonnegTm[yV]]];
    unfold = unfoldRealMul[xV, yV];
    outer = condReduceT[hPx, innerPosTm[xV, yV], innerNegTm[xV, yV]];
    inner = condReduceF[hNy, brPP[xV, yV], brPN[xV, yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[notTm[nonnegTm[yV]],
      TRANS[unfold, TRANS[outer, inner]]]]]]
  ];
realMulCaseNPThm =
  Module[{xV, yV, hNx, hPy, unfold, outer, inner},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hNx = ASSUME[notTm[nonnegTm[xV]]]; hPy = ASSUME[nonnegTm[yV]];
    unfold = unfoldRealMul[xV, yV];
    outer = condReduceF[hNx, innerPosTm[xV, yV], innerNegTm[xV, yV]];
    inner = condReduceT[hPy, brNP[xV, yV], brNN[xV, yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[notTm[nonnegTm[xV]], HOL`Bool`DISCH[nonnegTm[yV],
      TRANS[unfold, TRANS[outer, inner]]]]]]
  ];
realMulCaseNNThm =
  Module[{xV, yV, hNx, hNy, unfold, outer, inner},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hNx = ASSUME[notTm[nonnegTm[xV]]]; hNy = ASSUME[notTm[nonnegTm[yV]]];
    unfold = unfoldRealMul[xV, yV];
    outer = condReduceF[hNx, innerPosTm[xV, yV], innerNegTm[xV, yV]];
    inner = condReduceF[hNy, brNP[xV, yV], brNN[xV, yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[notTm[nonnegTm[xV]], HOL`Bool`DISCH[notTm[nonnegTm[yV]],
      TRANS[unfold, TRANS[outer, inner]]]]]]
  ];

(* binary sign-case combinator: posFn[hPos], negFn[hNeg] prove the same G. *)
splitSign[tT_, posFn_, negFn_] :=
  HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[nonnegTm[tT]],
    posFn[ASSUME[nonnegTm[tT]]], negFn[ASSUME[notTm[nonnegTm[tT]]]]];

(* per-factor: apply a case reduction at concrete terms (SPEC + MP twice). *)
casePP[xT_, yT_, hPx_, hPy_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMulCasePPThm]], hPx], hPy];
casePN[xT_, yT_, hPx_, hNy_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMulCasePNThm]], hPx], hNy];
caseNP[xT_, yT_, hNx_, hPy_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMulCaseNPThm]], hNx], hPy];
caseNN[xT_, yT_, hNx_, hNy_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realMulCaseNNThm]], hNx], hNy];

(* sign / nonneg-law shorthands *)
posNeg[tT_, hNt_] := HOL`Bool`MP[HOL`Bool`SPEC[tT, notNonnegNegThm], hNt];        (* ¬0≤t ⊢ 0≤(−t) *)
nnComm[aT_, bT_, hNa_, hNb_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[bT, HOL`Bool`SPEC[aT, realNnMulCommThm]], hNa], hNb];
nnZeroR[aT_, hNa_] := HOL`Bool`MP[HOL`Bool`SPEC[aT, realNnMulZeroThm], hNa];       (* 0≤a ⊢ a·0 = 0 *)
nnOneR[aT_, hNa_]  := HOL`Bool`MP[HOL`Bool`SPEC[aT, realNnMulOneThm], hNa];        (* 0≤a ⊢ a·1 = a *)
nnNonneg[aT_, bT_, hNa_, hNb_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[bT, HOL`Bool`SPEC[aT, realNnMulNonnegThm]], hNa], hNb];

(* ⊢ realLe (&ℝ0) (&ℝ1) *)
oneNonneg[] :=
  Module[{ratLe01},
    ratLe01 = HOL`Bool`DISJCASES[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[], ratLeTotalThm]],
      ASSUME[ratLeTm[zeroQ[], oneQ[]]],
      HOL`Bool`CONTR[ratLeTm[zeroQ[], oneQ[]],
        HOL`Bool`MP[HOL`Bool`NOTELIM[EQMP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[],
          HOL`Stdlib`Rat`ratLtNotLeThm]], ratZeroLtOneThm]], ASSUME[ratLeTm[oneQ[], zeroQ[]]]]]];
    EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[], realOfRatLeThm]]], ratLe01]
  ];

(* ============================================================ *)
(* Signed laws: zero, one, comm — clean binary split (no product *)
(* sign needed; zero folds into the nonneg branch).             *)
(* ============================================================ *)

(* ⊢ ∀x. realMul x (&ℝ0) = &ℝ0. *)
realMulZeroThm =
  Module[{xV, h00, posF, negF},
    xV = mkVar["x", realTy];
    h00 = HOL`Bool`SPEC[rZ[], realLeReflThm];   (* 0≤0 *)
    posF = Function[{hPx},
      TRANS[casePP[xV, rZ[], hPx, h00], nnZeroR[xV, hPx]]];
    negF = Function[{hNx},
      TRANS[caseNP[xV, rZ[], hNx, h00],
        TRANS[rNegCong[nnZeroR[rNeg[xV], posNeg[xV, hNx]]], realNegZeroThm]]];
    HOL`Bool`GEN[xV, splitSign[xV, posF, negF]]
  ];

(* ⊢ ∀x. realMul x (&ℝ1) = x. *)
realMulOneThm =
  Module[{xV, oneR, h1, posF, negF},
    xV = mkVar["x", realTy];
    oneR = realOfRatTm[oneQ[]]; h1 = oneNonneg[];
    posF = Function[{hPx},
      TRANS[casePP[xV, oneR, hPx, h1], nnOneR[xV, hPx]]];
    negF = Function[{hNx},
      TRANS[caseNP[xV, oneR, hNx, h1],
        TRANS[rNegCong[nnOneR[rNeg[xV], posNeg[xV, hNx]]], HOL`Bool`SPEC[xV, realNegNegThm]]]];
    HOL`Bool`GEN[xV, splitSign[xV, posF, negF]]
  ];

(* ⊢ ∀x y. realMul x y = realMul y x. *)
realMulCommThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = splitSign[xV,
      Function[{hPx},
        splitSign[yV,
          Function[{hPy},   (* PP *)
            TRANS[casePP[xV, yV, hPx, hPy],
              TRANS[nnComm[xV, yV, hPx, hPy], HOL`Equal`SYM[casePP[yV, xV, hPy, hPx]]]]],
          Function[{hNy},   (* PN: x≥0,y<0 → y·x is NP *)
            TRANS[casePN[xV, yV, hPx, hNy],
              TRANS[rNegCong[nnComm[xV, rNeg[yV], hPx, posNeg[yV, hNy]]],
                HOL`Equal`SYM[caseNP[yV, xV, hNy, hPx]]]]]]],
      Function[{hNx},
        splitSign[yV,
          Function[{hPy},   (* NP: x<0,y≥0 → y·x is PN *)
            TRANS[caseNP[xV, yV, hNx, hPy],
              TRANS[rNegCong[nnComm[rNeg[xV], yV, posNeg[xV, hNx], hPy]],
                HOL`Equal`SYM[casePN[yV, xV, hPy, hNx]]]]],
          Function[{hNy},   (* NN *)
            TRANS[caseNN[xV, yV, hNx, hNy],
              TRANS[nnComm[rNeg[xV], rNeg[yV], posNeg[xV, hNx], posNeg[yV, hNy]],
                HOL`Equal`SYM[caseNN[yV, xV, hNy, hNx]]]]]]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

(* ============================================================ *)
(* Sign homomorphism: realMul x (−y) = −(realMul x y) and the    *)
(* left version.  These pull all signs out, reducing assoc and   *)
(* distrib to the Layer-1 nonneg laws.                           *)
(* ============================================================ *)

nnNegNeg[tT_] := HOL`Bool`SPEC[tT, realNegNegThm];          (* −(−t) = t *)
mulCongR[xT_, eq_] := HOL`Equal`APTERM[mkComb[realMulConst[], xT], eq];   (* a=b → x·a = x·b *)
nnCongR[xT_, eq_] := HOL`Equal`APTERM[mkComb[realNnMulConst[], xT], eq];  (* a=b → x·a = x·b (nn) *)

(* ⊢ ∀x y. realMul x (realNeg y) = realNeg (realMul x y). *)
realMulNegRightThm =
  Module[{xV, yV, ny, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; ny = rNeg[yV];
    body = splitSign[yV,
      (* y≥0 *)
      Function[{hPy},
        splitSign[ny,
          (* 0≤(−y): boundary y=0 *)
          Function[{hPny},
            Module[{yLe0, yEq, yEqR, lhsChain, rhsChain},
              yLe0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], nnNegNeg[yV]], REFL[rZ[]]],
                       HOL`Bool`MP[HOL`Bool`SPEC[ny, realNegNonposThm], hPny]];   (* realLe y 0 *)
              yEq = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yV, HOL`Bool`SPEC[rZ[], realLeAntisymThm]], hPy], yLe0];   (* 0 = y *)
              yEqR = HOL`Equal`SYM[yEq];   (* y = 0 *)
              lhsChain = TRANS[mulCongR[xV, rNegCong[yEqR]],
                           TRANS[mulCongR[xV, realNegZeroThm], HOL`Bool`SPEC[xV, realMulZeroThm]]];
              rhsChain = TRANS[rNegCong[mulCongR[xV, yEqR]],
                           TRANS[rNegCong[HOL`Bool`SPEC[xV, realMulZeroThm]], realNegZeroThm]];
              TRANS[lhsChain, HOL`Equal`SYM[rhsChain]]]],
          (* ¬0≤(−y): −y<0 *)
          Function[{hNny},
            splitSign[xV,
              Function[{hPx},   (* x≥0 *)
                TRANS[TRANS[casePN[xV, ny, hPx, hNny], rNegCong[nnCongR[xV, nnNegNeg[yV]]]],
                  HOL`Equal`SYM[rNegCong[casePP[xV, yV, hPx, hPy]]]]],
              Function[{hNx},   (* x<0 *)
                TRANS[TRANS[caseNN[xV, ny, hNx, hNny], nnCongR[rNeg[xV], nnNegNeg[yV]]],
                  HOL`Equal`SYM[TRANS[rNegCong[caseNP[xV, yV, hNx, hPy]],
                    nnNegNeg[realNnMulTm[rNeg[xV], yV]]]]]]]]]],
      (* y<0 *)
      Function[{hNy},
        splitSign[xV,
          Function[{hPx},   (* x≥0 *)
            TRANS[casePP[xV, ny, hPx, posNeg[yV, hNy]],
              HOL`Equal`SYM[TRANS[rNegCong[casePN[xV, yV, hPx, hNy]],
                nnNegNeg[realNnMulTm[xV, ny]]]]]],
          Function[{hNx},   (* x<0 *)
            TRANS[caseNP[xV, ny, hNx, posNeg[yV, hNy]],
              HOL`Equal`SYM[rNegCong[caseNN[xV, yV, hNx, hNy]]]]]]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, body]]
  ];

(* ⊢ ∀x y. realMul (realNeg x) y = realNeg (realMul x y).  (comm + NegRight) *)
realMulNegLeftThm =
  Module[{xV, yV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      TRANS[HOL`Bool`SPEC[yV, HOL`Bool`SPEC[rNeg[xV], realMulCommThm]],
        TRANS[HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realMulNegRightThm]],
          rNegCong[HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realMulCommThm]]]]]]]
  ];

(* ⊢ ∀x y. realLe 0 x ⇒ realLe 0 y ⇒ realLe 0 (realMul x y). *)
realMulNonnegThm =
  Module[{xV, yV, hPx, hPy},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hPx = ASSUME[nonnegTm[xV]]; hPy = ASSUME[nonnegTm[yV]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISCH[nonnegTm[xV], HOL`Bool`DISCH[nonnegTm[yV],
      EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], REFL[rZ[]]],
             HOL`Equal`SYM[casePP[xV, yV, hPx, hPy]]], nnNonneg[xV, yV, hPx, hPy]]]]]]
  ];
realLeMulNonnegThm = realMulNonnegThm;

(* ============================================================ *)
(* Associativity — nested sign-peel reduction to the all-nonneg  *)
(* base assocCore, pulling each negative factor out with the     *)
(* mulNeg homomorphism (binary, 3 peels deep).                   *)
(* ============================================================ *)

mulCongL[eq_, cT_] := HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realMulConst[], eq], REFL[cT]];   (* a=b → a·c = b·c *)
mnegR[xT_, wT_] := HOL`Bool`SPEC[wT, HOL`Bool`SPEC[xT, realMulNegRightThm]];  (* x·(−w) = −(x·w) *)
mnegL[xT_, wT_] := HOL`Bool`SPEC[wT, HOL`Bool`SPEC[xT, realMulNegLeftThm]];   (* (−x)·w = −(x·w) *)

(* all-nonneg base: realMul(realMul x y) z = realMul x (realMul y z). *)
assocCore[xT_, yT_, zT_, hPx_, hPy_, hPz_] :=
  Module[{xy, yz, redL, redR, assocNN},
    xy = realNnMulTm[xT, yT]; yz = realNnMulTm[yT, zT];
    redL = TRANS[mulCongL[casePP[xT, yT, hPx, hPy], zT],
             casePP[xy, zT, nnNonneg[xT, yT, hPx, hPy], hPz]];   (* (x·y)·z = nn(nn x y) z *)
    redR = TRANS[mulCongR[xT, casePP[yT, zT, hPy, hPz]],
             casePP[xT, yz, hPx, nnNonneg[yT, zT, hPy, hPz]]];   (* x·(y·z) = nn x (nn y z) *)
    assocNN = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zT, HOL`Bool`SPEC[yT,
                HOL`Bool`SPEC[xT, realNnMulAssocNonnegThm]]], hPx], hPy], hPz];
    TRANS[redL, TRANS[assocNN, HOL`Equal`SYM[redR]]]
  ];

assocGenZ[xT_, yT_, zT_, hPx_, hPy_] :=
  splitSign[zT,
    Function[{hPz}, assocCore[xT, yT, zT, hPx, hPy, hPz]],
    Function[{hNz},
      Module[{nz, hPnz, xRw, lhsTot, yzRed, rhsTot, sub},
        nz = rNeg[zT]; hPnz = posNeg[zT, hNz];
        xRw = HOL`Equal`SYM[nnNegNeg[zT]];   (* z = −(−z) *)
        lhsTot = TRANS[mulCongR[realMulTm[xT, yT], xRw],
                   mnegR[realMulTm[xT, yT], nz]];   (* (x·y)·z = −((x·y)·nz) *)
        yzRed = TRANS[mulCongR[yT, xRw], mnegR[yT, nz]];   (* y·z = −(y·nz) *)
        rhsTot = TRANS[mulCongR[xT, yzRed], mnegR[xT, realMulTm[yT, nz]]];   (* x·(y·z) = −(x·(y·nz)) *)
        sub = assocCore[xT, yT, nz, hPx, hPy, hPnz];
        TRANS[lhsTot, TRANS[rNegCong[sub], HOL`Equal`SYM[rhsTot]]]]]];

assocGenY[xT_, yT_, zT_, hPx_] :=
  splitSign[yT,
    Function[{hPy}, assocGenZ[xT, yT, zT, hPx, hPy]],
    Function[{hNy},
      Module[{ny, hPny, yRw, xyRed, lhsTot, yzRed, rhsTot, sub},
        ny = rNeg[yT]; hPny = posNeg[yT, hNy];
        yRw = HOL`Equal`SYM[nnNegNeg[yT]];   (* y = −(−y) *)
        xyRed = TRANS[mulCongR[xT, yRw], mnegR[xT, ny]];   (* x·y = −(x·ny) *)
        lhsTot = TRANS[mulCongL[xyRed, zT], mnegL[realMulTm[xT, ny], zT]];   (* (x·y)·z = −((x·ny)·z) *)
        yzRed = TRANS[mulCongL[yRw, zT], mnegL[ny, zT]];   (* y·z = −(ny·z) *)
        rhsTot = TRANS[mulCongR[xT, yzRed], mnegR[xT, realMulTm[ny, zT]]];   (* x·(y·z) = −(x·(ny·z)) *)
        sub = assocGenZ[xT, ny, zT, hPx, hPny];
        TRANS[lhsTot, TRANS[rNegCong[sub], HOL`Equal`SYM[rhsTot]]]]]];

assocGen[xT_, yT_, zT_] :=
  splitSign[xT,
    Function[{hPx}, assocGenY[xT, yT, zT, hPx]],
    Function[{hNx},
      Module[{nx, hPnx, xRw, xyRed, lhsTot, rhsTot, sub},
        nx = rNeg[xT]; hPnx = posNeg[xT, hNx];
        xRw = HOL`Equal`SYM[nnNegNeg[xT]];   (* x = −(−x) *)
        xyRed = TRANS[mulCongL[xRw, yT], mnegL[nx, yT]];   (* x·y = −(nx·y) *)
        lhsTot = TRANS[mulCongL[xyRed, zT], mnegL[realMulTm[nx, yT], zT]];   (* (x·y)·z = −((nx·y)·z) *)
        rhsTot = TRANS[mulCongL[xRw, realMulTm[yT, zT]], mnegL[nx, realMulTm[yT, zT]]];   (* x·(y·z) = −(nx·(y·z)) *)
        sub = assocGenY[nx, yT, zT, hPnx];
        TRANS[lhsTot, TRANS[rNegCong[sub], HOL`Equal`SYM[rhsTot]]]]]];

realMulAssocThm =
  Module[{xV, yV, zV},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV, assocGen[xV, yV, zV]]]]
  ];

(* ============================================================ *)
(* Signed left distributivity — the no-reference Stage D step.   *)
(*   realMul x (y+z) = realMul x y + realMul x z.                *)
(* Core: prove for 0≤x and all y,z (sign-case on y,z,(y+z)),     *)
(* reusing realNnMulDistribNonneg + the real additive group;     *)
(* then peel x<0 with mulNegLeft + realNegAdd.                   *)
(* ============================================================ *)

nnDistrib[xT_, uT_, vT_, hx_, hu_, hv_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
  HOL`Bool`SPEC[vT, HOL`Bool`SPEC[uT, HOL`Bool`SPEC[xT, realNnMulDistribNonnegThm]]], hx], hu], hv];
realAddNN[aT_, bT_, hNa_, hNb_] := HOL`Bool`MP[HOL`Bool`MP[
  HOL`Bool`SPEC[bT, HOL`Bool`SPEC[aT, realAddNonnegThm]], hNa], hNb];
rNegAddSplit[aT_, bT_] := HOL`Bool`SPEC[bT, HOL`Bool`SPEC[aT, realNegAddThm]];   (* −(a+b)=(−a)+(−b) *)

(* 0≤x, 0≤a, b<0 ⊢ realMul x (a+b) = realMul x a + realMul x b. *)
mixedCase[xT_, aT_, bT_, hPx_, hPa_, hNb_] :=
  Module[{nb, hPnb, abTm, rhsRed},
    nb = rNeg[bT]; hPnb = posNeg[bT, hNb]; abTm = rAdd[aT, bT];
    rhsRed = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], casePP[xT, aT, hPx, hPa]],
               casePN[xT, bT, hPx, hNb]];   (* x·a + x·b = (nn x a) + (−(nn x nb)) *)
    splitSign[abTm,
      Function[{hPab},
        Module[{P, R, abnbEqA, aSplit, step, lhsPos},
          P = realNnMulTm[xT, abTm]; R = realNnMulTm[xT, nb];
          abnbEqA = TRANS[rAssoc[aT, bT, nb], TRANS[rAddCongR[aT, rAddNegR[bT]], rAddZeroR[aT]]];
          aSplit = TRANS[nnCongR[xT, HOL`Equal`SYM[abnbEqA]], nnDistrib[xT, abTm, nb, hPx, hPab, hPnb]];
          step = TRANS[rAddCongL[aSplit, rNeg[R]],
                   TRANS[rAssoc[P, R, rNeg[R]], TRANS[rAddCongR[P, rAddNegR[R]], rAddZeroR[P]]]];
          lhsPos = TRANS[casePP[xT, abTm, hPx, hPab], HOL`Equal`SYM[step]];
          TRANS[lhsPos, HOL`Equal`SYM[rhsRed]]]],
      Function[{hNab},
        Module[{nab, hPnab, A, N, S, negAddAB, aNabEqNb, nbSplit, negS, step, lhsNeg},
          nab = rNeg[abTm]; hPnab = posNeg[abTm, hNab];
          A = realNnMulTm[xT, aT]; N = realNnMulTm[xT, nab]; S = realNnMulTm[xT, nb];
          negAddAB = rNegAddSplit[aT, bT];
          aNabEqNb = TRANS[rAddCongR[aT, negAddAB],
                       TRANS[HOL`Equal`SYM[rAssoc[aT, rNeg[aT], rNeg[bT]]],
                         TRANS[rAddCongL[rAddNegR[aT], rNeg[bT]], rAddZeroL[rNeg[bT]]]]];
          nbSplit = TRANS[nnCongR[xT, HOL`Equal`SYM[aNabEqNb]], nnDistrib[xT, aT, nab, hPx, hPa, hPnab]];
          negS = TRANS[rNegCong[nbSplit], HOL`Bool`SPEC[N, HOL`Bool`SPEC[A, realNegAddThm]]];
          step = TRANS[rAddCongR[A, negS],
                   TRANS[HOL`Equal`SYM[rAssoc[A, rNeg[A], rNeg[N]]],
                     TRANS[rAddCongL[rAddNegR[A], rNeg[N]], rAddZeroL[rNeg[N]]]]];   (* A + (−S) = (−N) *)
          lhsNeg = casePN[xT, abTm, hPx, hNab];   (* x·(a+b) = −(nn x nab) *)
          TRANS[lhsNeg, TRANS[HOL`Equal`SYM[step], HOL`Equal`SYM[rhsRed]]]]]]
  ];

(* 0≤x, y<0, z<0 ⊢ realMul x (y+z) = realMul x y + realMul x z. *)
nnNegCase[xT_, yT_, zT_, hPx_, hNy_, hNz_] :=
  Module[{ny, nz, hPny, hPnz, sTm, hPs, yzTm, sEqNegYZ, yzEqNegS, lhsRed2,
          distribS, negDistribS, rhsRed},
    ny = rNeg[yT]; nz = rNeg[zT]; hPny = posNeg[yT, hNy]; hPnz = posNeg[zT, hNz];
    sTm = rAdd[ny, nz]; hPs = realAddNN[ny, nz, hPny, hPnz]; yzTm = rAdd[yT, zT];
    sEqNegYZ = HOL`Equal`SYM[rNegAddSplit[yT, zT]];   (* (−y)+(−z) = −(y+z) *)
    yzEqNegS = HOL`Equal`SYM[TRANS[rNegCong[sEqNegYZ], nnNegNeg[yzTm]]];   (* y+z = −s *)
    lhsRed2 = TRANS[TRANS[mulCongR[xT, yzEqNegS], mnegR[xT, sTm]],
                rNegCong[casePP[xT, sTm, hPx, hPs]]];   (* x·(y+z) = −(nn x s) *)
    distribS = nnDistrib[xT, ny, nz, hPx, hPny, hPnz];   (* nn x s = nn x ny + nn x nz *)
    negDistribS = TRANS[rNegCong[distribS],
                    HOL`Bool`SPEC[realNnMulTm[xT, nz], HOL`Bool`SPEC[realNnMulTm[xT, ny], realNegAddThm]]];
    rhsRed = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], casePN[xT, yT, hPx, hNy]],
               casePN[xT, zT, hPx, hNz]];   (* x·y + x·z = (−(nn x ny)) + (−(nn x nz)) *)
    TRANS[lhsRed2, TRANS[negDistribS, HOL`Equal`SYM[rhsRed]]]
  ];

(* 0≤x ⊢ realMul x (y+z) = realMul x y + realMul x z  (all y,z). *)
distribNonnegX[xT_, yT_, zT_, hPx_] :=
  splitSign[yT,
    Function[{hPy},
      splitSign[zT,
        Function[{hPz},
          Module[{yzN, lhs, nnD, rhsRed},
            yzN = realAddNN[yT, zT, hPy, hPz];
            lhs = casePP[xT, rAdd[yT, zT], hPx, yzN];
            nnD = nnDistrib[xT, yT, zT, hPx, hPy, hPz];
            rhsRed = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], casePP[xT, yT, hPx, hPy]],
                       casePP[xT, zT, hPx, hPz]];
            TRANS[lhs, TRANS[nnD, HOL`Equal`SYM[rhsRed]]]]],
        Function[{hNz}, mixedCase[xT, yT, zT, hPx, hPy, hNz]]]],
    Function[{hNy},
      splitSign[zT,
        Function[{hPz},   (* y<0, z≥0: commute to mixedCase[x,z,y] *)
          TRANS[mulCongR[xT, rComm[yT, zT]],
            TRANS[mixedCase[xT, zT, yT, hPx, hPz, hNy],
              rComm[realMulTm[xT, zT], realMulTm[xT, yT]]]]],
        Function[{hNz}, nnNegCase[xT, yT, zT, hPx, hNy, hNz]]]]];

realMulDistribThm =
  Module[{xV, yV, zV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    body = splitSign[xV,
      Function[{hPx}, distribNonnegX[xV, yV, zV, hPx]],
      Function[{hNx},
        Module[{nx, hPnx, xRw, yzTm, lhs1, distribNx, lhs2, negAdd, lhs3, xyEq, xzEq, rhsRed},
          nx = rNeg[xV]; hPnx = posNeg[xV, hNx]; yzTm = rAdd[yV, zV];
          xRw = HOL`Equal`SYM[nnNegNeg[xV]];   (* x = −(−x) *)
          lhs1 = TRANS[mulCongL[xRw, yzTm], mnegL[nx, yzTm]];   (* x·(y+z) = −(nx·(y+z)) *)
          distribNx = distribNonnegX[nx, yV, zV, hPnx];
          lhs2 = TRANS[lhs1, rNegCong[distribNx]];   (* = −(nx·y + nx·z) *)
          negAdd = HOL`Bool`SPEC[realMulTm[nx, zV], HOL`Bool`SPEC[realMulTm[nx, yV], realNegAddThm]];
          lhs3 = TRANS[lhs2, negAdd];   (* = −(nx·y) + −(nx·z) *)
          xyEq = TRANS[mulCongL[xRw, yV], mnegL[nx, yV]];   (* x·y = −(nx·y) *)
          xzEq = TRANS[mulCongL[xRw, zV], mnegL[nx, zV]];   (* x·z = −(nx·z) *)
          rhsRed = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realAddConst[], xyEq], xzEq];
          TRANS[lhs3, HOL`Equal`SYM[rhsRed]]]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV, body]]]
  ];

(* ============================================================ *)
(* Order surface: strict positivity of a product of positives.  *)
(* ============================================================ *)

realLtTm[aT_, bT_] := mkComb[mkComb[realLtConst[], aT], bT];

(* ⊢ ∀a b. ¬(realLe a b) ⇒ ∃q. REP a q ∧ ¬(REP b q). *)
notLeWitnessThm =
  Module[{aV, bV, hNotLe, qV, exTerm, hNoEx, hRaq, hNRbq, ex, fls, repBq, impl,
          allImpl, leAB, flsTop, exThm},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy];
    hNotLe = ASSUME[notTm[realLeTm[aV, bV]]];
    qV = mkVar["q", ratTy];
    exTerm = existsTm[qV, conjTm[repApp[aV, qV], notTm[repApp[bV, qV]]]];
    hNoEx = ASSUME[notTm[exTerm]];
    hRaq = ASSUME[repApp[aV, qV]]; hNRbq = ASSUME[notTm[repApp[bV, qV]]];
    ex = HOL`Bool`EXISTS[exTerm, qV, HOL`Bool`CONJ[hRaq, hNRbq]];
    fls = HOL`Bool`MP[HOL`Bool`NOTELIM[hNoEx], ex];
    repBq = HOL`Bool`CCONTR[repApp[bV, qV], fls];
    impl = HOL`Bool`DISCH[repApp[aV, qV], repBq];
    allImpl = HOL`Bool`GEN[qV, impl];
    leAB = EQMP[HOL`Equal`SYM[unfoldRealLe[aV, bV]], allImpl];
    flsTop = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotLe], leAB];
    exThm = HOL`Bool`CCONTR[exTerm, flsTop];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[notTm[realLeTm[aV, bV]], exThm]]]
  ];

(* ⊢ ∀x. realLt 0 x ⇒ ∃p. REP x p ∧ 0<p. *)
realPosHasPosMemThm =
  Module[{xV, h, hNotLe, wit, qV, rV, posBody, hConj, mXq, nNeg, memEq0, nLt, ge0q,
          open, hOpen, mXr, qLtr, posr, posMem, exP, chR, chQ},
    xV = mkVar["x", realTy];
    h = ASSUME[realLtTm[rZ[], xV]];
    hNotLe = EQMP[HOL`Bool`SPEC[xV, HOL`Bool`SPEC[rZ[], realLtNotLeThm]], h];   (* ¬realLe x 0 *)
    wit = HOL`Bool`MP[HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[xV, notLeWitnessThm]], hNotLe];
    qV = mkVar["q", ratTy]; rV = mkVar["r", ratTy];
    posBody = existsTm[rV, conjTm[repApp[xV, rV], ratLtTm[zeroQ[], rV]]];
    hConj = ASSUME[conjTm[repApp[xV, qV], notTm[repApp[zeroRealTm[], qV]]]];
    mXq = HOL`Bool`CONJUNCT1[hConj]; nNeg = HOL`Bool`CONJUNCT2[hConj];
    memEq0 = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];   (* REP(&ℝ0) q = q<0 *)
    nLt = EQMP[HOL`Equal`APTERM[notC[], memEq0], nNeg];   (* ¬(q<0) *)
    ge0q = notNegToGe0[nLt, qV];   (* 0≤q *)
    open = HOL`Bool`MP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[xV, realOpenThm]], mXq];
    hOpen = ASSUME[conjTm[repApp[xV, rV], ratLtTm[qV, rV]]];
    mXr = HOL`Bool`CONJUNCT1[hOpen]; qLtr = HOL`Bool`CONJUNCT2[hOpen];
    posr = leLt2[ge0q, qLtr];   (* 0<r *)
    posMem = HOL`Bool`CONJ[mXr, posr];
    exP = HOL`Bool`EXISTS[posBody, rV, posMem];
    chR = HOL`Bool`CHOOSE[rV, open, exP];
    chQ = HOL`Bool`CHOOSE[qV, wit, chR];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLtTm[rZ[], xV], chQ]]
  ];

(* realLt 0 t ⊢ realLe 0 t  (totality). *)
realLtLeReal[tT_, htLt_] :=
  Module[{hNotLe, total},
    hNotLe = EQMP[HOL`Bool`SPEC[tT, HOL`Bool`SPEC[rZ[], realLtNotLeThm]], htLt];
    total = HOL`Bool`SPEC[tT, HOL`Bool`SPEC[rZ[], realLeTotalThm]];
    HOL`Bool`DISJCASES[total, ASSUME[realLeTm[rZ[], tT]],
      HOL`Bool`CONTR[realLeTm[rZ[], tT], HOL`Bool`MP[HOL`Bool`NOTELIM[hNotLe], ASSUME[realLeTm[tT, rZ[]]]]]]
  ];

(* ⊢ ∀x y. realLt 0 x ⇒ realLt 0 y ⇒ realLt 0 (realMul x y). *)
realLtMulPosThm =
  Module[{xV, yV, hx, hy, hx0, hy0, posMemX, posMemY, pV, qV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hx = ASSUME[realLtTm[rZ[], xV]]; hy = ASSUME[realLtTm[rZ[], yV]];
    hx0 = realLtLeReal[xV, hx]; hy0 = realLtLeReal[yV, hy];
    posMemX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realPosHasPosMemThm], hx];
    posMemY = HOL`Bool`MP[HOL`Bool`SPEC[yV, realPosHasPosMemThm], hy];
    pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy];
    body = Module[{hPx2, mXp, pPos, hQy, mYq, qPos, pqPos, mem0, hLe, leUnf, at0,
                   lt00, fls, notLe, ltNn, ltMul, chQ, chP},
      hPx2 = ASSUME[conjTm[repApp[xV, pV], ratLtTm[zeroQ[], pV]]];
      mXp = HOL`Bool`CONJUNCT1[hPx2]; pPos = HOL`Bool`CONJUNCT2[hPx2];
      hQy = ASSUME[conjTm[repApp[yV, qV], ratLtTm[zeroQ[], qV]]];
      mYq = HOL`Bool`CONJUNCT1[hQy]; qPos = HOL`Bool`CONJUNCT2[hQy];
      pqPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[pV, ratMulPosThm]], pPos], qPos];
      mem0 = nnMemIntroR[xV, yV, zeroQ[], pV, qV,
               HOL`Bool`CONJ[mXp, HOL`Bool`CONJ[mYq, HOL`Bool`CONJ[pPos, HOL`Bool`CONJ[qPos, pqPos]]]],
               hx0, hy0];
      hLe = ASSUME[realLeTm[realNnMulTm[xV, yV], rZ[]]];
      leUnf = EQMP[unfoldRealLe[realNnMulTm[xV, yV], rZ[]], hLe];
      at0 = HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], leUnf], mem0];
      lt00 = EQMP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]], at0];
      fls = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[zeroQ[], ratLtIrreflThm]], lt00];
      notLe = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[concl[hLe], fls]];
      ltNn = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[realNnMulTm[xV, yV], HOL`Bool`SPEC[rZ[], realLtNotLeThm]]], notLe];
      ltMul = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], REFL[rZ[]]],
                 HOL`Equal`SYM[casePP[xV, yV, hx0, hy0]]], ltNn];
      chQ = HOL`Bool`CHOOSE[qV, posMemY, ltMul];
      chP = HOL`Bool`CHOOSE[pV, posMemX, chQ];
      chP];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[realLtTm[rZ[], xV], HOL`Bool`DISCH[realLtTm[rZ[], yV], body]]]]
  ];

(* ============================================================ *)
(* Ordered-field: additive-order compatibility (+ ↔ ≤/<).       *)
(* Reuses the rAdd group helpers above. realLeAddMono is a pure  *)
(* cut-inclusion proof (a⊆b ⟹ (a+c)⊆(b+c)).                     *)
(* ============================================================ *)

(* (x+c)+(−c) = x ;  (b+(−a))+a = b *)
gCancelR[xT_, cT_] := TRANS[rAssoc[xT, cT, rNeg[cT]],
  TRANS[rAddCongR[xT, rAddNegR[cT]], rAddZeroR[xT]]];
gSubAddR[bT_, aT_] := TRANS[rAssoc[bT, rNeg[aT], aT],
  TRANS[rAddCongR[bT, rAddNegL[aT]], rAddZeroR[bT]]];

(* ⊢ ∀a b c. realLe a b ⇒ realLe (realAdd a c) (realAdd b c). *)
realLeAddMonoThm =
  Module[{aV, bV, cV, h, leUnf, rV, sV, memAC, memBC, hMem, redMem, bodyBC, innerA,
          hConj, mAs, mCrs, mBs, newConj, exBC, memBCr, chS, impl, allR, leRes},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; cV = mkVar["c", realTy];
    h = ASSUME[realLeTm[aV, bV]];
    leUnf = EQMP[unfoldRealLe[aV, bV], h];   (* ∀p. REP a p ⇒ REP b p *)
    rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy];
    memAC = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[cV, HOL`Bool`SPEC[aV, realAddMemThm]]];
    memBC = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[cV, HOL`Bool`SPEC[bV, realAddMemThm]]];
    hMem = ASSUME[repApp[realAddTm[aV, cV], rV]];
    redMem = EQMP[memAC, hMem];   (* ∃s. REP a s ∧ REP c (r−s) *)
    bodyBC = concl[memBC][[2]];
    innerA = concl[BETACONV[mkComb[concl[memAC][[2, 2]], sV]]][[2]];   (* REP a s ∧ REP c (r−s) *)
    hConj = ASSUME[innerA];
    mAs = HOL`Bool`CONJUNCT1[hConj]; mCrs = HOL`Bool`CONJUNCT2[hConj];
    mBs = HOL`Bool`MP[HOL`Bool`SPEC[sV, leUnf], mAs];   (* REP b s *)
    newConj = HOL`Bool`CONJ[mBs, mCrs];
    exBC = HOL`Bool`EXISTS[bodyBC, sV, newConj];
    memBCr = EQMP[HOL`Equal`SYM[memBC], exBC];   (* REP (b+c) r *)
    chS = HOL`Bool`CHOOSE[sV, redMem, memBCr];
    impl = HOL`Bool`DISCH[concl[hMem], chS];
    allR = HOL`Bool`GEN[rV, impl];
    leRes = EQMP[HOL`Equal`SYM[unfoldRealLe[realAddTm[aV, cV], realAddTm[bV, cV]]], allR];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`DISCH[concl[h], leRes]]]]
  ];

leAddMono[abLe_, cT_] := Module[{a, b},
  a = concl[abLe][[1, 2]]; b = concl[abLe][[2]];
  HOL`Bool`MP[HOL`Bool`SPEC[cT, HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, realLeAddMonoThm]]], abLe]];

(* ⊢ ∀a b c. realLt a b ⇒ realLt (realAdd a c) (realAdd b c). *)
realLtAddMonoThm =
  Module[{aV, bV, cV, h, notLeBA, hLe, monoBack, leBA, fls, notLeRes, ltRes},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; cV = mkVar["c", realTy];
    h = ASSUME[realLtTm[aV, bV]];
    notLeBA = EQMP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, realLtNotLeThm]], h];   (* ¬realLe b a *)
    hLe = ASSUME[realLeTm[realAddTm[bV, cV], realAddTm[aV, cV]]];
    monoBack = leAddMono[hLe, rNeg[cV]];   (* realLe ((b+c)+(−c)) ((a+c)+(−c)) *)
    leBA = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], gCancelR[bV, cV]],
             gCancelR[aV, cV]], monoBack];   (* realLe b a *)
    fls = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeBA], leBA];
    notLeRes = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[concl[hLe], fls]];   (* ¬realLe (b+c)(a+c) *)
    ltRes = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[realAddTm[bV, cV],
              HOL`Bool`SPEC[realAddTm[aV, cV], realLtNotLeThm]]], notLeRes];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, HOL`Bool`DISCH[concl[h], ltRes]]]]
  ];

(* ⊢ ∀a b. realLe a b = realLe (&ℝ0) (realAdd b (realNeg a)).  (a≤b ⟺ 0≤b−a) *)
realLeSubNonnegThm =
  Module[{aV, bV, sub, hF, fMono, fwd, hB, bMono, zeroAddA, bwd},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; sub = rAdd[bV, rNeg[aV]];
    hF = ASSUME[realLeTm[aV, bV]];
    fMono = leAddMono[hF, rNeg[aV]];   (* realLe (a+(−a)) (b+(−a)) *)
    fwd = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], rAddNegR[aV]], REFL[sub]], fMono];   (* realLe 0 (b−a) *)
    hB = ASSUME[realLeTm[rZ[], sub]];
    bMono = leAddMono[hB, aV];   (* realLe (0+a) ((b−a)+a) *)
    zeroAddA = rAddZeroL[aV];   (* 0+a = a *)
    bwd = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], zeroAddA], gSubAddR[bV, aV]], bMono];   (* realLe a b *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Equal`SYM[HOL`Kernel`DEDUCTANTISYM[fwd, bwd]]]]
  ];

(* ⊢ ∀a b. realLt a b = realLt (&ℝ0) (realAdd b (realNeg a)).  (a<b ⟺ 0<b−a) *)
realLtSubPosThm =
  Module[{aV, bV, sub, ltAddMono, hF, fMono, fwd, hB, bMono, zeroAddA, bwd},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; sub = rAdd[bV, rNeg[aV]];
    ltAddMono[abLt_, cT_] := Module[{a, b},
      a = concl[abLt][[1, 2]]; b = concl[abLt][[2]];   (* realLt a b = ¬…; concl[[1,2]]/[[2]] = a,b *)
      HOL`Bool`MP[HOL`Bool`SPEC[cT, HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, realLtAddMonoThm]]], abLt]];
    hF = ASSUME[realLtTm[aV, bV]];
    fMono = ltAddMono[hF, rNeg[aV]];   (* realLt (a+(−a)) (b+(−a)) *)
    fwd = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], rAddNegR[aV]], REFL[sub]], fMono];
    hB = ASSUME[realLtTm[rZ[], sub]];
    bMono = ltAddMono[hB, aV];   (* realLt (0+a) ((b−a)+a) *)
    zeroAddA = rAddZeroL[aV];
    bwd = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], zeroAddA], gSubAddR[bV, aV]], bMono];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Equal`SYM[HOL`Kernel`DEDUCTANTISYM[fwd, bwd]]]]
  ];

(* ============================================================ *)
(* Ordered-field: multiplicative-order compatibility (× ↔ ≤/<). *)
(* a≤b ∧ 0≤c ⟹ c·a≤c·b, via the bridge + distrib + sign-product. *)
(* ============================================================ *)

(* realMul c (b−a) = (c·b) + (−(c·a)) *)
mulSubEq[cT_, aT_, bT_] := TRANS[
  HOL`Bool`SPEC[rNeg[aT], HOL`Bool`SPEC[bT, HOL`Bool`SPEC[cT, realMulDistribThm]]],
  rAddCongR[realMulTm[cT, bT], HOL`Bool`SPEC[aT, HOL`Bool`SPEC[cT, realMulNegRightThm]]]];

(* ⊢ ∀a b c. realLe 0 c ⇒ realLe a b ⇒ realLe (realMul c a) (realMul c b). *)
realLeMulMonoThm =
  Module[{aV, bV, cV, h0c, hab, sub0, nn, subEq, nnSub, res},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; cV = mkVar["c", realTy];
    h0c = ASSUME[nonnegTm[cV]]; hab = ASSUME[realLeTm[aV, bV]];
    sub0 = EQMP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, realLeSubNonnegThm]], hab];   (* 0 ≤ b−a *)
    nn = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rAdd[bV, rNeg[aV]], HOL`Bool`SPEC[cV, realMulNonnegThm]], h0c], sub0];   (* 0 ≤ c·(b−a) *)
    subEq = mulSubEq[cV, aV, bV];
    nnSub = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], REFL[rZ[]]], subEq], nn];   (* 0 ≤ (c·b)−(c·a) *)
    res = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[realMulTm[cV, bV], HOL`Bool`SPEC[realMulTm[cV, aV], realLeSubNonnegThm]]], nnSub];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[nonnegTm[cV], HOL`Bool`DISCH[realLeTm[aV, bV], res]]]]]
  ];

(* ⊢ ∀a b c. realLt 0 c ⇒ realLt a b ⇒ realLt (realMul c a) (realMul c b). *)
realLtMulMonoThm =
  Module[{aV, bV, cV, h0c, hab, sub0, pos, subEq, posSub, res},
    aV = mkVar["a", realTy]; bV = mkVar["b", realTy]; cV = mkVar["c", realTy];
    h0c = ASSUME[realLtTm[rZ[], cV]]; hab = ASSUME[realLtTm[aV, bV]];
    sub0 = EQMP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, realLtSubPosThm]], hab];   (* 0 < b−a *)
    pos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rAdd[bV, rNeg[aV]], HOL`Bool`SPEC[cV, realLtMulPosThm]], h0c], sub0];   (* 0 < c·(b−a) *)
    subEq = mulSubEq[cV, aV, bV];
    posSub = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLtConst[], REFL[rZ[]]], subEq], pos];   (* 0 < (c·b)−(c·a) *)
    res = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[realMulTm[cV, bV], HOL`Bool`SPEC[realMulTm[cV, aV], realLtSubPosThm]]], posSub];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[realLtTm[rZ[], cV], HOL`Bool`DISCH[realLtTm[aV, bV], res]]]]]
  ];

(* ============================================================ *)
(* Stage E — &ℝ : rat → real is a ring/order homomorphism.      *)
(* realOfRatLe already in Field; here Add / Neg / Mul.          *)
(* ============================================================ *)

memOR[qT_, pT_] := HOL`Bool`SPEC[pT, HOL`Bool`SPEC[qT, realOfRatMemThm]];   (* REP(&ℝq) p = p<q *)
ratComm[xT_, yT_] := HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, HOL`Stdlib`Rat`ratAddCommThm]];   (* x+y = y+x *)

(* ⊢ ∀a b. &ℝ (a+b) = realAdd (&ℝ a) (&ℝ b). *)
realOfRatAddThm =
  Module[{aV, bV, rV, sV, abQ, lhs, rhs, memL, addEq, addBody, fwdImp, bwdImp, exEq, perR},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy]; rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy];
    abQ = ratAddTm[aV, bV];
    lhs = realOfRatTm[abQ]; rhs = realAddTm[realOfRatTm[aV], realOfRatTm[bV]];
    memL = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[abQ, realOfRatMemThm]];   (* REP(&ℝ(a+b)) r = r<(a+b) *)
    addEq = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[realOfRatTm[bV], HOL`Bool`SPEC[realOfRatTm[aV], realAddMemThm]]];
    addBody = concl[addEq][[2]];   (* ∃s. REP(&ℝa)s ∧ REP(&ℝb)(r−s) *)
    fwdImp = Module[{innerBody, hConj, mAs, mBrs, sLtA, rsLtB, i1, i2c, i2, chain, rsSub, rLtAB},
      innerBody = concl[BETACONV[mkComb[addBody[[2]], sV]]][[2]];
      hConj = ASSUME[innerBody];
      mAs = HOL`Bool`CONJUNCT1[hConj]; mBrs = HOL`Bool`CONJUNCT2[hConj];
      sLtA = EQMP[memOR[aV, sV], mAs];   (* s<a *)
      rsLtB = EQMP[memOR[bV, ratSubTm[rV, sV]], mBrs];   (* (r−s)<b *)
      i1 = ltAddR[rsLtB, sV];   (* (r−s)+s < b+s *)
      i2c = ltAddR[sLtA, bV];   (* s+b < a+b *)
      i2 = rwLt[i2c, ratComm[sV, bV], REFL[abQ]];   (* b+s < a+b *)
      chain = ltLt2[i1, i2];   (* (r−s)+s < a+b *)
      rsSub = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[rV, ratSubAddThm]];   (* (r−s)+s = r *)
      rLtAB = rwLt[chain, rsSub, REFL[abQ]];   (* r < a+b *)
      HOL`Bool`CHOOSE[sV, ASSUME[addBody], rLtAB]
    ];
    bwdImp = Module[{hLt, monoH, rmbLtA, dense, rmbLtMid, midLtA, midTm, step1, rbbEqR,
                     rLtMidB, step2, midbSubMid, rMidLtB, mMidA, mRmidB, conjB},
      hLt = ASSUME[ratLtTm[rV, abQ]];
      monoH = ltAddR[hLt, ratNegTm[bV]];   (* (r+(−b)) < ((a+b)+(−b)) *)
      rmbLtA = rwLt[monoH, REFL[ratSubTm[rV, bV]],
                 HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, ratAddSubCancelThm]]];   (* (r−b)<a *)
      dense = HOL`Bool`MP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[ratSubTm[rV, bV], ratDenseThm]], rmbLtA];
      rmbLtMid = HOL`Bool`CONJUNCT1[dense]; midLtA = HOL`Bool`CONJUNCT2[dense];
      midTm = concl[rmbLtMid][[2]];
      step1 = ltAddR[rmbLtMid, bV];   (* (r−b)+b < mid+b *)
      rbbEqR = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[rV, ratSubAddThm]];   (* (r−b)+b = r *)
      rLtMidB = rwLt[step1, rbbEqR, REFL[ratAddTm[midTm, bV]]];   (* r < mid+b *)
      step2 = ltAddR[rLtMidB, ratNegTm[midTm]];   (* (r+(−mid)) < ((mid+b)+(−mid)) *)
      midbSubMid = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
                     ratComm[midTm, bV]], REFL[ratNegTm[midTm]]],
                     HOL`Bool`SPEC[midTm, HOL`Bool`SPEC[bV, ratAddSubCancelThm]]];   (* (mid+b)+(−mid) = b *)
      rMidLtB = rwLt[step2, REFL[ratSubTm[rV, midTm]], midbSubMid];   (* (r−mid)<b *)
      mMidA = EQMP[HOL`Equal`SYM[memOR[aV, midTm]], midLtA];   (* REP(&ℝa) mid *)
      mRmidB = EQMP[HOL`Equal`SYM[memOR[bV, ratSubTm[rV, midTm]]], rMidLtB];   (* REP(&ℝb)(r−mid) *)
      conjB = HOL`Bool`CONJ[mMidA, mRmidB];
      HOL`Bool`EXISTS[addBody, midTm, conjB]
    ];
    exEq = HOL`Kernel`DEDUCTANTISYM[fwdImp, bwdImp];   (* (r<a+b) = addBody *)
    perR = HOL`Bool`GEN[rV, TRANS[memL, TRANS[exEq, HOL`Equal`SYM[addEq]]]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, realEqFromRepEq[lhs, rhs, perR]]]
  ];

(* ⊢ ∀a. &ℝ (ratNeg a) = realNeg (&ℝ a).  (via additive inverse cancellation) *)
realOfRatNegThm =
  Module[{aV, e1, e2, e2p, cancel},
    aV = mkVar["a", ratTy];
    e1 = HOL`Bool`SPEC[realOfRatTm[aV], realAddNegThm];   (* &ℝa + (−&ℝa) = &ℝ0 *)
    e2 = HOL`Bool`SPEC[ratNegTm[aV], HOL`Bool`SPEC[aV, realOfRatAddThm]];   (* &ℝ(a+(−a)) = &ℝa + &ℝ(−a) *)
    e2p = TRANS[HOL`Equal`SYM[e2], HOL`Equal`APTERM[realOfRatConst[], HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddNegThm]]];
       (* &ℝa + &ℝ(−a) = &ℝ(a+(−a)) = &ℝ0 *)
    cancel = HOL`Bool`MP[HOL`Bool`SPEC[realOfRatTm[ratNegTm[aV]], HOL`Bool`SPEC[realNegTm[realOfRatTm[aV]],
               HOL`Bool`SPEC[realOfRatTm[aV], realAddCancelLeftThm]]], TRANS[e1, HOL`Equal`SYM[e2p]]];
       (* realNeg(&ℝa) = &ℝ(−a) *)
    HOL`Bool`GEN[aV, HOL`Equal`SYM[cancel]]
  ];

(* ℚ multiplicative cancellation helpers (0<y ⟹ y≠0) *)
rmC[xT_, yT_] := HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, HOL`Stdlib`Rat`ratMulCommThm]];   (* x·y = y·x *)
mulCancelRgt[xT_, yT_, yPos_] :=                                              (* (x·y)·(1/y) = x *)
  TRANS[HOL`Bool`SPEC[ratInvTm[yT], HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, HOL`Stdlib`Rat`ratMulAssocThm]]],
    TRANS[HOL`Equal`APTERM[mkComb[ratMulC[], xT], HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Stdlib`Rat`ratMulInvThm], posToNe0[yPos]]],
      HOL`Bool`SPEC[xT, HOL`Stdlib`Rat`ratMulOneThm]]];
invCancelRgt[xT_, yT_, yPos_] :=                                              (* (x·(1/y))·y = x *)
  TRANS[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[ratInvTm[yT], HOL`Bool`SPEC[xT, HOL`Stdlib`Rat`ratMulAssocThm]]],
    TRANS[HOL`Equal`APTERM[mkComb[ratMulC[], xT],
        TRANS[rmC[ratInvTm[yT], yT], HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Stdlib`Rat`ratMulInvThm], posToNe0[yPos]]]],
      HOL`Bool`SPEC[xT, HOL`Stdlib`Rat`ratMulOneThm]]];
fstCancel[pT_, bT_, pPos_] :=                                                 (* (p·b)·(1/p) = b *)
  TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], rmC[pT, bT]], REFL[ratInvTm[pT]]],
    mulCancelRgt[bT, pT, pPos]];
(* 0≤r ⟹ 0 ≤ r·(1/y)  (y>0) *)
le0RInv[rT_, yT_, yPos_, rGe0_] :=
  Module[{yi = ratInvTm[yT], invPos2 = HOL`Bool`MP[HOL`Bool`SPEC[yT, ratInvPosThm], yPos]},
    EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], HOL`Bool`SPEC[rT, HOL`Stdlib`Rat`ratMulZeroThm]], REFL[ratMulTm[rT, yi]]],
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yi, HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[rT, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], rGe0],
        HOL`Bool`MP[HOL`Bool`SPEC[yi, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], invPos2]]]];

(* ⊢ ∀a b. 0≤a ⇒ 0≤b ⇒ realNnMul (&ℝ a) (&ℝ b) = &ℝ (a·b). *)
realOfRatNnMulThm =
  Module[{aV, bV, hRa, hRb, hNa, hNb, ipa, ipb, abQ, rV, prod, memEq, memProd,
          zeroLeAB, posOfLeMul, fwd, bwd, perR},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    hRa = ASSUME[ratLeTm[zeroQ[], aV]]; hRb = ASSUME[ratLeTm[zeroQ[], bV]];
    hNa = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[zeroQ[], realOfRatLeThm]]], hRa];
    hNb = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[zeroQ[], realOfRatLeThm]]], hRb];
    ipa = realOfRatTm[aV]; ipb = realOfRatTm[bV]; abQ = ratMulTm[aV, bV];
    rV = mkVar["r", ratTy]; prod = realNnMulTm[ipa, ipb];
    memEq[rT_] := nnMemEq[ipa, ipb, rT, hNa, hNb];
    memProd[rT_] := HOL`Bool`SPEC[rT, HOL`Bool`SPEC[abQ, realOfRatMemThm]];
    zeroLeAB = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratMulZeroThm]], REFL[abQ]],
                 HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], hRa], hRb]];   (* 0 ≤ a·b *)
    (* 0<a·b ∧ 0≤a ⟹ 0<a  (kill the a=0 case) *)
    posOfLeMul[xT_, yT_, hx_, abPos_] := HOL`Bool`DISJCASES[
      HOL`Bool`MP[HOL`Bool`SPEC[xT, HOL`Bool`SPEC[zeroQ[], ratLeCasesThm]], hx],
      ASSUME[ratLtTm[zeroQ[], xT]],
      HOL`Bool`CONTR[ratLtTm[zeroQ[], xT],
        HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[zeroQ[], ratLtIrreflThm]],
          rwLt[abPos, REFL[zeroQ[]],
            TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], HOL`Equal`SYM[ASSUME[mkEq[zeroQ[], xT]]]], REFL[yT]],
              TRANS[rmC[zeroQ[], yT], HOL`Bool`SPEC[yT, HOL`Stdlib`Rat`ratMulZeroThm]]]]]]];   (* x·y → 0·... wait: rewrite a·b with a=0 *)

    fwd = Module[{hMem, redMem, leftD, exPart, caseL, caseR, cases},
      hMem = ASSUME[repApp[prod, rV]];
      redMem = EQMP[memEq[rV], hMem];
      leftD = concl[memEq[rV]][[2, 1, 2]]; exPart = concl[memEq[rV]][[2, 2]];
      caseL = EQMP[HOL`Equal`SYM[memProd[rV]], ltLe2[ASSUME[leftD], zeroLeAB]];
      caseR = Module[{pV, qV, innerP, condT, hC, mAp, c1, mBq, c2, pPos, c3, qPos,
                      rLtpq, pLtA, qLtB, aPos, pqLtaq, qaLtba, aqLtab, pqLtab, rLtab},
        pV = mkVar["p", ratTy]; qV = mkVar["q", ratTy];
        innerP = concl[BETACONV[mkComb[exPart[[2]], pV]]][[2]];
        condT = concl[BETACONV[mkComb[innerP[[2]], qV]]][[2]];
        hC = ASSUME[condT];
        mAp = HOL`Bool`CONJUNCT1[hC]; c1 = HOL`Bool`CONJUNCT2[hC];
        mBq = HOL`Bool`CONJUNCT1[c1]; c2 = HOL`Bool`CONJUNCT2[c1];
        pPos = HOL`Bool`CONJUNCT1[c2]; c3 = HOL`Bool`CONJUNCT2[c2];
        qPos = HOL`Bool`CONJUNCT1[c3]; rLtpq = HOL`Bool`CONJUNCT2[c3];
        pLtA = EQMP[memOR[aV, pV], mAp]; qLtB = EQMP[memOR[bV, qV], mBq];
        aPos = ltLt2[pPos, pLtA];
        pqLtaq = ltMulR[pLtA, qPos];   (* p·q < a·q *)
        qaLtba = ltMulR[qLtB, aPos];   (* q·a < b·a *)
        aqLtab = rwLt[qaLtba, rmC[qV, aV], rmC[bV, aV]];   (* a·q < a·b *)
        pqLtab = ltLt2[pqLtaq, aqLtab];
        rLtab = ltLt2[rLtpq, pqLtab];
        HOL`Bool`CHOOSE[pV, ASSUME[exPart], HOL`Bool`CHOOSE[qV, ASSUME[innerP],
          EQMP[HOL`Equal`SYM[memProd[rV]], rLtab]]]
      ];
      cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
      HOL`Bool`DISCH[concl[hMem], cases]
    ];

    bwd = Module[{hMemP, rLtab, em, caseNeg, casePos, result},
      hMemP = ASSUME[repApp[realOfRatTm[abQ], rV]];
      rLtab = EQMP[memProd[rV], hMemP];
      em = HOL`Bool`EXCLUDEDMIDDLE[ratLtTm[rV, zeroQ[]]];
      caseNeg = nnMemIntroL[ipa, ipb, rV, ASSUME[ratLtTm[rV, zeroQ[]]], hNa, hNb];
      casePos = Module[{hNotNeg, rGe0, abPos, aPos, bPos, invB, invBpos, rDivB,
                        rDivBLtA, denseP, rDivBLtP, pLtA, pPos, pTm, invP, invPpos,
                        pbGtR, rDivPLtB, denseQ, rDivPLtQ, qLtB, qPos, qTm, rLtpq,
                        mAp, mBq, cond},
        hNotNeg = ASSUME[notTm[ratLtTm[rV, zeroQ[]]]];
        rGe0 = notNegToGe0[hNotNeg, rV];
        abPos = leLt2[rGe0, rLtab];   (* 0 < a·b *)
        aPos = posOfLeMul[aV, bV, hRa, abPos];   (* 0<a *)
        bPos = posOfLeMul[bV, aV, hRb, rwLt[abPos, REFL[zeroQ[]], rmC[aV, bV]]];   (* 0<b (from 0<b·a) *)
        invB = ratInvTm[bV]; invBpos = HOL`Bool`MP[HOL`Bool`SPEC[bV, ratInvPosThm], bPos];
        rDivB = ratMulTm[rV, invB];
        rDivBLtA = rwLt[ltMulR[rLtab, invBpos], REFL[rDivB], mulCancelRgt[aV, bV, bPos]];   (* r·(1/b) < a *)
        denseP = HOL`Bool`MP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[rDivB, ratDenseThm]], rDivBLtA];
        rDivBLtP = HOL`Bool`CONJUNCT1[denseP]; pLtA = HOL`Bool`CONJUNCT2[denseP];
        pTm = concl[rDivBLtP][[2]];
        pPos = leLt2[le0RInv[rV, bV, bPos, rGe0], rDivBLtP];   (* 0<p *)
        pbGtR = rwLt[ltMulR[rDivBLtP, bPos], invCancelRgt[rV, bV, bPos], REFL[ratMulTm[pTm, bV]]];   (* r < p·b *)
        invP = ratInvTm[pTm]; invPpos = HOL`Bool`MP[HOL`Bool`SPEC[pTm, ratInvPosThm], pPos];
        rDivPLtB = rwLt[ltMulR[pbGtR, invPpos], REFL[ratMulTm[rV, invP]], fstCancel[pTm, bV, pPos]];   (* r·(1/p) < b *)
        denseQ = HOL`Bool`MP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[ratMulTm[rV, invP], ratDenseThm]], rDivPLtB];
        rDivPLtQ = HOL`Bool`CONJUNCT1[denseQ]; qLtB = HOL`Bool`CONJUNCT2[denseQ];
        qTm = concl[rDivPLtQ][[2]];
        qPos = leLt2[le0RInv[rV, pTm, pPos, rGe0], rDivPLtQ];   (* 0<q *)
        rLtpq = rwLt[ltMulR[rDivPLtQ, pPos], invCancelRgt[rV, pTm, pPos], rmC[qTm, pTm]];   (* r < p·q *)
        mAp = EQMP[HOL`Equal`SYM[memOR[aV, pTm]], pLtA];
        mBq = EQMP[HOL`Equal`SYM[memOR[bV, qTm]], qLtB];
        cond = HOL`Bool`CONJ[mAp, HOL`Bool`CONJ[mBq, HOL`Bool`CONJ[pPos, HOL`Bool`CONJ[qPos, rLtpq]]]];
        nnMemIntroR[ipa, ipb, rV, pTm, qTm, cond, hNa, hNb]
      ];
      result = HOL`Bool`DISJCASES[em, caseNeg, casePos];
      HOL`Bool`DISCH[concl[hMemP], result]
    ];

    perR = HOL`Bool`GEN[rV, HOL`Kernel`DEDUCTANTISYM[HOL`Bool`UNDISCH[bwd], HOL`Bool`UNDISCH[fwd]]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[concl[hRa], HOL`Bool`DISCH[concl[hRb],
        realEqFromRepEq[prod, realOfRatTm[abQ], perR]]]]]
  ];

(* ℚ multiplicative-negation facts (not in Rat) — for the signed homomorphism. *)
ratNegC[] := HOL`Stdlib`Rat`ratNegConst[];
ratMulNegR[aT_, bT_] :=   (* a·(−b) = ratNeg(a·b) *)
  Module[{ab = ratMulTm[aT, bT], anb = ratMulTm[aT, ratNegTm[bT]], sumZero, eqC},
    sumZero = TRANS[HOL`Equal`SYM[HOL`Bool`SPEC[bT, HOL`Bool`SPEC[ratNegTm[bT], HOL`Bool`SPEC[aT, HOL`Stdlib`Rat`ratMulDistribThm]]]],
                TRANS[HOL`Equal`APTERM[mkComb[ratMulC[], aT],
                    TRANS[ratComm[ratNegTm[bT], bT], HOL`Bool`SPEC[bT, HOL`Stdlib`Rat`ratAddNegThm]]],
                  HOL`Bool`SPEC[aT, HOL`Stdlib`Rat`ratMulZeroThm]]];   (* a·(−b)+a·b = 0 *)
    eqC = TRANS[TRANS[ratComm[ab, anb], sumZero], HOL`Equal`SYM[HOL`Bool`SPEC[ab, HOL`Stdlib`Rat`ratAddNegThm]]];
       (* (a·b)+(a·(−b)) = (a·b)+ratNeg(a·b) *)
    HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[ab], HOL`Bool`SPEC[anb, HOL`Bool`SPEC[ab, ratAddLeftCancelThm]]], eqC]
  ];
ratMulNegL[aT_, bT_] :=   (* (−a)·b = ratNeg(a·b) *)
  TRANS[rmC[ratNegTm[aT], bT],
    TRANS[ratMulNegR[bT, aT], HOL`Equal`APTERM[ratNegC[], rmC[bT, aT]]]];
ratMulNegNeg[aT_, bT_] :=   (* (−a)·(−b) = a·b *)
  TRANS[ratMulNegL[aT, ratNegTm[bT]],
    TRANS[HOL`Equal`APTERM[ratNegC[], ratMulNegR[aT, bT]], HOL`Bool`SPEC[ratMulTm[aT, bT], ratNegNegThm]]];

(* sign-hyp bridges: rat sign ↔ real sign of &ℝ; 0≤−q from ¬(0≤q). *)
realNonnegOfRat[qT_, hq_] := EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[qT, HOL`Bool`SPEC[zeroQ[], realOfRatLeThm]]], hq];
realNegOfRat[qT_, hnq_] := EQMP[HOL`Equal`APTERM[notC[], HOL`Equal`SYM[HOL`Bool`SPEC[qT, HOL`Bool`SPEC[zeroQ[], realOfRatLeThm]]]], hnq];
ratNegNonneg[qT_, hnq_] := HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[qT], HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]],
  HOL`Bool`MP[HOL`Bool`SPEC[qT, ratNegPosThm],
    EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[qT, HOL`Stdlib`Rat`ratLtNotLeThm]]], hnq]]];

(* ⊢ ∀a b. &ℝ (a·b) = realMul (&ℝ a) (&ℝ b). *)
realOfRatMulThm =
  Module[{aV, bV, ipa, ipb, abQ, nnOR, mkPP, mkPN, mkNP, mkNN, hRaT, hRbT, hNRaT, hNRbT},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    ipa = realOfRatTm[aV]; ipb = realOfRatTm[bV]; abQ = ratMulTm[aV, bV];
    hRaT = ratLeTm[zeroQ[], aV]; hRbT = ratLeTm[zeroQ[], bV];
    hNRaT = notTm[hRaT]; hNRbT = notTm[hRbT];
    nnOR[xT_, yT_, hx_, hy_] := HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yT, HOL`Bool`SPEC[xT, realOfRatNnMulThm]], hx], hy];
    mkPP[hRa_, hRb_] := HOL`Equal`SYM[TRANS[casePP[ipa, ipb, realNonnegOfRat[aV, hRa], realNonnegOfRat[bV, hRb]],
      nnOR[aV, bV, hRa, hRb]]];
    mkPN[hRa_, hNotRb_] := Module[{hNa, e, e1, e2, argEq},
      hNa = realNonnegOfRat[aV, hRa];
      e = casePN[ipa, ipb, hNa, realNegOfRat[bV, hNotRb]];
      e1 = nnCongR[ipa, HOL`Equal`SYM[HOL`Bool`SPEC[bV, realOfRatNegThm]]];
      e2 = nnOR[aV, ratNegTm[bV], hRa, ratNegNonneg[bV, hNotRb]];
      argEq = HOL`Equal`APTERM[realOfRatConst[],
                TRANS[HOL`Equal`APTERM[ratNegC[], ratMulNegR[aV, bV]], HOL`Bool`SPEC[abQ, ratNegNegThm]]];
      HOL`Equal`SYM[TRANS[e, TRANS[rNegCong[TRANS[e1, e2]],
        TRANS[HOL`Equal`SYM[HOL`Bool`SPEC[ratMulTm[aV, ratNegTm[bV]], realOfRatNegThm]], argEq]]]]
    ];
    mkNP[hNotRa_, hRb_] := Module[{hNb, e, e1, e2, argEq},
      hNb = realNonnegOfRat[bV, hRb];
      e = caseNP[ipa, ipb, realNegOfRat[aV, hNotRa], hNb];
      e1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realNnMulConst[], HOL`Equal`SYM[HOL`Bool`SPEC[aV, realOfRatNegThm]]], REFL[ipb]];
      e2 = nnOR[ratNegTm[aV], bV, ratNegNonneg[aV, hNotRa], hRb];
      argEq = HOL`Equal`APTERM[realOfRatConst[],
                TRANS[HOL`Equal`APTERM[ratNegC[], ratMulNegL[aV, bV]], HOL`Bool`SPEC[abQ, ratNegNegThm]]];
      HOL`Equal`SYM[TRANS[e, TRANS[rNegCong[TRANS[e1, e2]],
        TRANS[HOL`Equal`SYM[HOL`Bool`SPEC[ratMulTm[ratNegTm[aV], bV], realOfRatNegThm]], argEq]]]]
    ];
    mkNN[hNotRa_, hNotRb_] := Module[{e, e1, e2, argEq},
      e = caseNN[ipa, ipb, realNegOfRat[aV, hNotRa], realNegOfRat[bV, hNotRb]];
      e1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realNnMulConst[], HOL`Equal`SYM[HOL`Bool`SPEC[aV, realOfRatNegThm]]],
             HOL`Equal`SYM[HOL`Bool`SPEC[bV, realOfRatNegThm]]];
      e2 = nnOR[ratNegTm[aV], ratNegTm[bV], ratNegNonneg[aV, hNotRa], ratNegNonneg[bV, hNotRb]];
      argEq = HOL`Equal`APTERM[realOfRatConst[], ratMulNegNeg[aV, bV]];
      HOL`Equal`SYM[TRANS[e, TRANS[e1, TRANS[e2, argEq]]]]
    ];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[hRaT],
        HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[hRbT],
          mkPP[ASSUME[hRaT], ASSUME[hRbT]], mkPN[ASSUME[hRaT], ASSUME[hNRbT]]],
        HOL`Bool`DISJCASES[HOL`Bool`EXCLUDEDMIDDLE[hRbT],
          mkNP[ASSUME[hNRaT], ASSUME[hRbT]], mkNN[ASSUME[hNRaT], ASSUME[hNRbT]]]]]]
  ];

End[];

EndPackage[];
