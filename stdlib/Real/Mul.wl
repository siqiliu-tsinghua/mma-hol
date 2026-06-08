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

End[];

EndPackage[];
