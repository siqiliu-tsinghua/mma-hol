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

End[];

EndPackage[];
