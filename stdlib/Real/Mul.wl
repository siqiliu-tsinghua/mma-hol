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

   STATUS: shell — implementation begins with the non-negative core. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

(* Exports added as Stage D theorems are built (realNnMul…, realMul…). *)

Begin["`Private`"];

(* === Layer 1: non-negative multiplication core (realNnMul) begins here. === *)

End[];

EndPackage[];
