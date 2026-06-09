(* M7-7 / stdlib/Real/Inv.wl — multiplicative inverse on ℝ (Rudin reciprocal).

   Part of the stdlib/Real/ folder (PLAN §8.1): shares context HOL`Stdlib`Real`
   with Cut.wl / RatAux.wl / Field.wl / Mul.wl.  Loads LAST in the folder
   (Cut → RatAux → Field → Mul → Inv); consumes realMul + the sign
   homomorphism (realMulNeg{Left,Right}, realNegNeg, realLtMulPos, casePP,
   realPosHasPosMem) from Mul, the additive group + memNotMemLt from Field,
   the cut vocabulary from Cut, and the ℚ mul-order/inverse layer from RatAux.

   ============================================================================
   NO LEAN BLUEPRINT.  The sibling Dedekind dev (../archive/tautology) never
   built the reciprocal (Cut/ has Add/Mul/MulComm/MulDistrib/Sup, no Inv).
   This is a from-scratch translation of Rudin "Principles" Step 8.
   ============================================================================

   Design (mirrors realMul: positive core + binary-COND sign extension):

   (1) POSITIVE CORE  invPos x  (semantics only for 0 < x)
         cut body  { p | ∃w. ¬REP_x w ∧ 0<w ∧ ratLt (p·w) 1 }
       "∃ a positive non-member w of x with p < 1/w" — exactly { p : p < 1/x }
       (p ≤ 0 falls in automatically; w's positivity is baked in so proofs
       don't re-derive it).  0<x is used to make every non-member positive
       (REP_x 0 holds, so a non-member w ⟹ 0<w) and to supply a positive
       member (realPosHasPosMem) for the proper/bounded condition.

   (2) SIGNED WRAPPER  realInv x  via COND on  realLt 0 x  (binary):
         0 < x →  invPos x
         else  →  realNeg (invPos (realNeg x))     [x<0 → −(1/(−x)); x=0 junk]
       realInv (&ℝ0) is junk (total but unspecified) — mirrors ℚ's ratInv;
       the field law realMulInvThm conditions on x ≠ 0.

   (3) FIELD LAW  realMulInvThm : ∀x. ¬(x=&ℝ0) ⇒ realMul x (realInv x) = &ℝ1.
       Core  invPosMulThm : 0<x ⇒ realNnMul x (invPos x) = 1  (the hard
       Rudin step, Archimedean ⊇ half); signed cases via realMulNeg lemmas.

   STATUS: increment 1 — invBody/invPos/realInv defs + invPosCutIsCutThm
   (4 conds) + rep/mem.  NEXT: invPosMulThm, then realMulInvThm. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

invPosConst::usage = "invPosConst[] — invPos : real → real, the reciprocal of a POSITIVE real (Rudin). Cut body { p | ∃w. ¬REP_x w ∧ 0<w ∧ ratLt (p·w) 1 }. Semantics only contracted under realLt 0 x.";
invPosDefThm::usage = "invPosDefThm — ⊢ invPos = (λx. ABS_real (λp. ∃w. ¬ (REP_real x w) ∧ ratLt 0 w ∧ ratLt (ratMul p w) (&ℚ(&ℤ(SUC 0))))).";
invPosCutIsCutThm::usage = "invPosCutIsCutThm — ⊢ ∀x. realLt (&ℝ 0) x ⇒ IS_CUT (λp. ∃w. ¬ (REP_real x w) ∧ ratLt 0 w ∧ ratLt (ratMul p w) 1). The reciprocal set of a positive cut is a cut.";
repInvPosThm::usage = "repInvPosThm — ⊢ ∀x. realLt (&ℝ 0) x ⇒ REP_real (invPos x) = (λp. ∃w. ¬ (REP_real x w) ∧ ratLt 0 w ∧ ratLt (ratMul p w) 1).";
invPosMemThm::usage = "invPosMemThm — ⊢ ∀x. realLt (&ℝ 0) x ⇒ ∀p. REP_real (invPos x) p = (∃w. ¬ (REP_real x w) ∧ ratLt 0 w ∧ ratLt (ratMul p w) 1).";
invPosNonnegThm::usage = "invPosNonnegThm — ⊢ ∀x. realLt (&ℝ 0) x ⇒ realLe (&ℝ 0) (invPos x). The reciprocal of a positive real is non-negative.";
invPosMulThm::usage = "invPosMulThm — ⊢ ∀x. realLt (&ℝ 0) x ⇒ realNnMul x (invPos x) = &ℝ (&ℚ (&ℤ (SUC 0))). x · (1/x) = 1 for x > 0 (the Rudin reciprocal law).";
realInvConst::usage = "realInvConst[] — realInv : real → real, the signed multiplicative inverse. COND on realLt 0 x: positive → invPos x; else → realNeg (invPos (realNeg x)). realInv (&ℝ0) is junk.";
realInvDefThm::usage = "realInvDefThm — ⊢ realInv = (λx. COND (realLt (&ℝ0) x) (invPos x) (realNeg (invPos (realNeg x)))).";

Begin["`Private`"];

(* ---- shared Real-folder private vocab is visible here (same package    ---- *)
(* ---- context HOL`Stdlib`Real`Private`, loaded after Cut/RatAux/Field/Mul). ---- *)

invPosTy = tyFun[realTy, realTy];

(* cut body: λp. ∃w. ¬REP_x w ∧ 0<w ∧ (p·w) < 1 *)
invBodyTm[xT_] :=
  Module[{pV, wV},
    pV = mkVar["p", ratTy]; wV = mkVar["w", ratTy];
    mkAbs[pV, existsTm[wV, conjTm[notTm[repApp[xT, wV]],
      conjTm[ratLtTm[zeroQ[], wV], ratLtTm[ratMulTm[pV, wV], oneQ[]]]]]]
  ];

invPosDefThm =
  Module[{xV, body},
    xV = mkVar["x", realTy];
    body = mkAbs[xV, mkComb[absRealConst[], invBodyTm[xV]]];
    newDefinition[mkEq[mkVar["invPos", invPosTy], body]]
  ];

invPosConst[] := mkConst["invPos", invPosTy];
invPosTm[xT_] := mkComb[invPosConst[], xT];

(* ⊢ invPos x = ABS_real (invBody x) *)
unfoldInvPos[xT_] :=
  Module[{s1}, s1 = HOL`Equal`APTHM[invPosDefThm, xT];
    TRANS[s1, BETACONV[concl[s1][[2]]]]];

(* ⊢ ∀x. realLt 0 x ⇒ IS_CUT (invBody x). *)
invPosCutIsCutThm =
  Module[{xV, h0, posMemX, sV, sConj, hS, mXs, sPos, sNe0, rep0, invBody, betaAt,
          rhsAt, invExAt, exBodyAt, unfold, rhsConj, c1Tm, rest1, c2Tm, rest2,
          c3Tm, c4Tm, c1Thm, c2Thm, c3Thm, c4Thm, conjAll, isCutXY, chS},
    xV = mkVar["x", realTy];
    h0 = ASSUME[realLtTm[rZ[], xV]];
    posMemX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realPosHasPosMemThm], h0];   (* ∃s. REP x s ∧ 0<s *)
    sV = mkVar["s", ratTy];
    sConj = conjTm[repApp[xV, sV], ratLtTm[zeroQ[], sV]];
    hS = ASSUME[sConj]; mXs = HOL`Bool`CONJUNCT1[hS]; sPos = HOL`Bool`CONJUNCT2[hS];
    sNe0 = posToNe0[sPos];                                    (* ¬(s=0) *)
    rep0 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[sV,
             HOL`Bool`SPEC[xV, realDownClosedThm]]], mXs], sPos];   (* REP x 0 *)
    invBody = invBodyTm[xV];
    betaAt[pT_] := BETACONV[mkComb[invBody, pT]];
    rhsAt[pT_]  := concl[betaAt[pT]][[2]];
    exBodyAt[pT_, wT_] := conjTm[notTm[repApp[xV, wT]],
      conjTm[ratLtTm[zeroQ[], wT], ratLtTm[ratMulTm[pT, wT], oneQ[]]]];

    unfold = unfoldIsCut[invBody];
    rhsConj = concl[unfold][[2]];
    c1Tm = rhsConj[[1, 2]]; rest1 = rhsConj[[2]];
    c2Tm = rest1[[1, 2]]; rest2 = rest1[[2]];
    c3Tm = rest2[[1, 2]]; c4Tm = rest2[[2]];

    (* --- c1 nonempty: witness p=0, with any non-member c (positive) --- *)
    c1Thm = Module[{prX, cV, hNM, cPos, zeroMulC, lt0c, conj0, ex0, atZero},
      prX = HOL`Bool`SPEC[xV, realProperThm];   (* ∃w. ¬REP x w *)
      cV = mkVar["c", ratTy];
      hNM = ASSUME[notTm[repApp[xV, cV]]];
      cPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[zeroQ[],
               HOL`Bool`SPEC[xV, memNotMemLtThm]]], rep0], hNM];   (* 0<c *)
      zeroMulC = TRANS[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                   HOL`Bool`SPEC[cV, HOL`Stdlib`Rat`ratMulZeroThm]];   (* 0·c = 0 *)
      lt0c = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], HOL`Equal`SYM[zeroMulC]],
               REFL[oneQ[]]], ratZeroLtOneThm];   (* (0·c) < 1 *)
      conj0 = HOL`Bool`CONJ[hNM, HOL`Bool`CONJ[cPos, lt0c]];
      ex0 = HOL`Bool`EXISTS[rhsAt[zeroQ[]], cV, conj0];
      atZero = EQMP[HOL`Equal`SYM[betaAt[zeroQ[]]], ex0];
      HOL`Bool`CHOOSE[cV, prX, HOL`Bool`EXISTS[c1Tm, zeroQ[], atZero]]
    ];

    (* --- c2 proper: witness 1/s; any body-witness d gives s<d ∧ d<s --- *)
    c2Thm = Module[{invS, dV, hEx, hConj, hNMd, t1, hPosd, hLtd, sLtd, mulS, assocA,
                    congComm, assocB, invSs1, congInv, oneMulD, lhsEq, oneMulS, dLts,
                    ltTrans, fls, notEx, notBody},
      invS = ratInvTm[sV];
      dV = mkVar["d", ratTy];
      hEx = ASSUME[existsTm[dV, exBodyAt[invS, dV]]];   (* the ∃w body at p=1/s, bound→d *)
      hConj = ASSUME[exBodyAt[invS, dV]];
      hNMd = HOL`Bool`CONJUNCT1[hConj]; t1 = HOL`Bool`CONJUNCT2[hConj];
      hPosd = HOL`Bool`CONJUNCT1[t1]; hLtd = HOL`Bool`CONJUNCT2[t1];   (* (1/s·d)<1 *)
      sLtd = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[dV, HOL`Bool`SPEC[sV,
               HOL`Bool`SPEC[xV, memNotMemLtThm]]], mXs], hNMd];   (* s<d *)
      mulS = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[ratMulTm[invS, dV],
               HOL`Bool`SPEC[sV, ratLtMulPosThm]]], sPos], hLtd];   (* (1/s·d)·s < 1·s *)
      (* (1/s·d)·s = d : assoc, comm d·s→s·d, assoc back, (1/s·s)=1, 1·d=d *)
      assocA = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[dV, HOL`Bool`SPEC[invS, HOL`Stdlib`Rat`ratMulAssocThm]]];   (* (1/s·d)·s = 1/s·(d·s) *)
      congComm = HOL`Equal`APTERM[mkComb[ratMulC[], invS],
                   HOL`Bool`SPEC[sV, HOL`Bool`SPEC[dV, HOL`Stdlib`Rat`ratMulCommThm]]];   (* 1/s·(d·s) = 1/s·(s·d) *)
      assocB = HOL`Equal`SYM[HOL`Bool`SPEC[dV, HOL`Bool`SPEC[sV, HOL`Bool`SPEC[invS, HOL`Stdlib`Rat`ratMulAssocThm]]]];   (* 1/s·(s·d) = (1/s·s)·d *)
      invSs1 = TRANS[HOL`Bool`SPEC[sV, HOL`Bool`SPEC[invS, HOL`Stdlib`Rat`ratMulCommThm]],
                 HOL`Bool`MP[HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratMulInvThm], sNe0]];   (* 1/s·s = s·1/s = 1 *)
      congInv = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], invSs1], REFL[dV]];   (* (1/s·s)·d = 1·d *)
      oneMulD = TRANS[HOL`Bool`SPEC[dV, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                  HOL`Bool`SPEC[dV, HOL`Stdlib`Rat`ratMulOneThm]];   (* 1·d = d *)
      lhsEq = TRANS[assocA, TRANS[congComm, TRANS[assocB, TRANS[congInv, oneMulD]]]];   (* (1/s·d)·s = d *)
      oneMulS = TRANS[HOL`Bool`SPEC[sV, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                  HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratMulOneThm]];   (* 1·s = s *)
      dLts = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsEq], oneMulS], mulS];   (* d < s *)
      ltTrans = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[sV, HOL`Bool`SPEC[dV,
                  HOL`Bool`SPEC[sV, ratLtTransThm]]], sLtd], dLts];   (* s<s *)
      fls = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[sV, ratLtIrreflThm]], ltTrans];
      notEx = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[existsTm[dV, exBodyAt[invS, dV]],
                HOL`Bool`CHOOSE[dV, hEx, fls]]];
      notBody = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[], betaAt[invS]]], notEx];
      HOL`Bool`EXISTS[c2Tm, invS, notBody]
    ];

    (* --- c3 downward closed --- *)
    c3Thm = Module[{aV, bV, hBig, hLt, redBig, eV, hC, mNM, t1, ePos, aeLt, beLt,
                    beLt1, newConj, exB, invBb},
      aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
      hBig = ASSUME[mkComb[invBody, aV]]; hLt = ASSUME[ratLtTm[bV, aV]];
      redBig = EQMP[betaAt[aV], hBig];
      eV = mkVar["e", ratTy];
      hC = ASSUME[exBodyAt[aV, eV]];
      mNM = HOL`Bool`CONJUNCT1[hC]; t1 = HOL`Bool`CONJUNCT2[hC];
      ePos = HOL`Bool`CONJUNCT1[t1]; aeLt = HOL`Bool`CONJUNCT2[t1];   (* (a·e)<1 *)
      beLt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV,
               HOL`Bool`SPEC[eV, ratLtMulPosThm]]], ePos], hLt];   (* (b·e)<(a·e) *)
      beLt1 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[ratMulTm[aV, eV],
                HOL`Bool`SPEC[ratMulTm[bV, eV], ratLtTransThm]]], beLt], aeLt];   (* (b·e)<1 *)
      newConj = HOL`Bool`CONJ[mNM, HOL`Bool`CONJ[ePos, beLt1]];
      exB = HOL`Bool`EXISTS[rhsAt[bV], eV, newConj];
      invBb = EQMP[HOL`Equal`SYM[betaAt[bV]], exB];
      HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
        HOL`Bool`DISCH[mkComb[invBody, aV], HOL`Bool`DISCH[ratLtTm[bV, aV],
          HOL`Bool`CHOOSE[eV, redBig, invBb]]]]]
    ];

    (* --- c4 no greatest: midpoint of (a, 1/e) via ratDense --- *)
    c4Thm = Module[{aV, rV, hBig, redBig, eV, hC, mNM, t1, ePos, aeLt, eNe0, invE,
                    invEpos, eInv1, aeInvEq, oneInvEq, mulStep, aLtInvE, dense, aLtMid,
                    midLtInvE, midTm, invEe1, midELt, midE1, newConj, invMid, c4ExTerm, exR},
      aV = mkVar["a", ratTy]; rV = mkVar["r", ratTy];
      hBig = ASSUME[mkComb[invBody, aV]];
      redBig = EQMP[betaAt[aV], hBig];
      eV = mkVar["e", ratTy];
      hC = ASSUME[exBodyAt[aV, eV]];
      mNM = HOL`Bool`CONJUNCT1[hC]; t1 = HOL`Bool`CONJUNCT2[hC];
      ePos = HOL`Bool`CONJUNCT1[t1]; aeLt = HOL`Bool`CONJUNCT2[t1];
      eNe0 = posToNe0[ePos]; invE = ratInvTm[eV];
      invEpos = HOL`Bool`MP[HOL`Bool`SPEC[eV, ratInvPosThm], ePos];   (* 0<1/e *)
      (* a < 1/e from (a·e)<1: multiply by 1/e>0, then (a·e)·(1/e)=a, 1·(1/e)=1/e *)
      eInv1 = HOL`Bool`MP[HOL`Bool`SPEC[eV, HOL`Stdlib`Rat`ratMulInvThm], eNe0];   (* e·(1/e) = 1 *)
      aeInvEq = TRANS[HOL`Bool`SPEC[invE, HOL`Bool`SPEC[eV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratMulAssocThm]]],
                  TRANS[HOL`Equal`APTERM[mkComb[ratMulC[], aV], eInv1],
                    HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratMulOneThm]]];   (* (a·e)·(1/e) = a *)
      oneInvEq = TRANS[HOL`Bool`SPEC[invE, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                   HOL`Bool`SPEC[invE, HOL`Stdlib`Rat`ratMulOneThm]];   (* 1·(1/e) = 1/e *)
      mulStep = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[ratMulTm[aV, eV],
                  HOL`Bool`SPEC[invE, ratLtMulPosThm]]], invEpos], aeLt];   (* (a·e)·(1/e) < 1·(1/e) *)
      aLtInvE = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], aeInvEq], oneInvEq], mulStep];   (* a < 1/e *)
      dense = HOL`Bool`MP[HOL`Bool`SPEC[invE, HOL`Bool`SPEC[aV, ratDenseThm]], aLtInvE];
      aLtMid = HOL`Bool`CONJUNCT1[dense]; midLtInvE = HOL`Bool`CONJUNCT2[dense];
      midTm = concl[aLtMid][[2]];
      invEe1 = TRANS[HOL`Bool`SPEC[eV, HOL`Bool`SPEC[invE, HOL`Stdlib`Rat`ratMulCommThm]],
                 HOL`Bool`MP[HOL`Bool`SPEC[eV, HOL`Stdlib`Rat`ratMulInvThm], eNe0]];   (* (1/e)·e = 1 *)
      midELt = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[invE, HOL`Bool`SPEC[midTm,
                 HOL`Bool`SPEC[eV, ratLtMulPosThm]]], ePos], midLtInvE];   (* (mid·e)<((1/e)·e) *)
      midE1 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[ratMulTm[midTm, eV]]], invEe1], midELt];   (* (mid·e)<1 *)
      newConj = HOL`Bool`CONJ[mNM, HOL`Bool`CONJ[ePos, midE1]];
      invMid = EQMP[HOL`Equal`SYM[betaAt[midTm]], HOL`Bool`EXISTS[rhsAt[midTm], eV, newConj]];
      c4ExTerm = existsTm[rV, conjTm[mkComb[invBody, rV], ratLtTm[aV, rV]]];
      exR = HOL`Bool`EXISTS[c4ExTerm, midTm, HOL`Bool`CONJ[invMid, aLtMid]];
      HOL`Bool`GEN[aV, HOL`Bool`DISCH[mkComb[invBody, aV], HOL`Bool`CHOOSE[eV, redBig, exR]]]
    ];

    conjAll = HOL`Bool`CONJ[c1Thm, HOL`Bool`CONJ[c2Thm, HOL`Bool`CONJ[c3Thm, c4Thm]]];
    isCutXY = EQMP[HOL`Equal`SYM[unfold], conjAll];
    chS = HOL`Bool`CHOOSE[sV, posMemX, isCutXY];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[h0], chS]]
  ];

(* ⊢ ∀x. realLt 0 x ⇒ REP_real (invPos x) = invBody x *)
repInvPosThm =
  Module[{xV, invBody, isCutX, lVar, repAbsInst, repAbs, apRep},
    xV = mkVar["x", realTy]; invBody = invBodyTm[xV];
    isCutX = HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosCutIsCutThm], ASSUME[realLtTm[rZ[], xV]]];
    lVar = concl[repAbsRealThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{lVar -> invBody}, repAbsRealThm];
    repAbs = EQMP[repAbsInst, isCutX];
    apRep = HOL`Equal`APTERM[repRealConst[], unfoldInvPos[xV]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLtTm[rZ[], xV], TRANS[apRep, repAbs]]]
  ];

(* ⊢ ∀x. realLt 0 x ⇒ ∀p. REP_real (invPos x) p = (invBody x) p *)
invPosMemThm =
  Module[{xV, pV, repEq, apAtP},
    xV = mkVar["x", realTy]; pV = mkVar["p", ratTy];
    repEq = HOL`Bool`MP[HOL`Bool`SPEC[xV, repInvPosThm], ASSUME[realLtTm[rZ[], xV]]];
    apAtP = HOL`Equal`APTHM[repEq, pV];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLtTm[rZ[], xV],
      HOL`Bool`GEN[pV, TRANS[apAtP, BETACONV[concl[apAtP][[2]]]]]]]
  ];

(* ⊢ ∀x. realLt 0 x ⇒ realLe (&ℝ0) (invPos x).  Every p<0 is in the cut:
   take any non-member c (positive, since 0<x), then p·c<0<1. *)
invPosNonnegThm =
  Module[{xV, h0, posMemX, sV, hS0c, mXs0, s0Pos, rep0, prX, cV, hNM, cPos, pV2,
          hMem0, pLt0, zeroMulC, pcLt0, pcLt1, memEqInv, exBody, cond, exW, repInvP,
          chC, chS, impl, allImpl, leThm},
    xV = mkVar["x", realTy]; h0 = ASSUME[realLtTm[rZ[], xV]];
    posMemX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realPosHasPosMemThm], h0];
    sV = mkVar["s", ratTy];
    hS0c = ASSUME[conjTm[repApp[xV, sV], ratLtTm[zeroQ[], sV]]];
    mXs0 = HOL`Bool`CONJUNCT1[hS0c]; s0Pos = HOL`Bool`CONJUNCT2[hS0c];
    rep0 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[sV,
             HOL`Bool`SPEC[xV, realDownClosedThm]]], mXs0], s0Pos];   (* REP x 0 *)
    prX = HOL`Bool`SPEC[xV, realProperThm];
    cV = mkVar["c", ratTy]; hNM = ASSUME[notTm[repApp[xV, cV]]];
    cPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[zeroQ[],
             HOL`Bool`SPEC[xV, memNotMemLtThm]]], rep0], hNM];   (* 0<c *)
    pV2 = mkVar["p", ratTy];
    hMem0 = ASSUME[repApp[zeroRealTm[], pV2]];
    pLt0 = EQMP[HOL`Bool`SPEC[pV2, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]], hMem0];   (* p<0 *)
    zeroMulC = TRANS[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                 HOL`Bool`SPEC[cV, HOL`Stdlib`Rat`ratMulZeroThm]];   (* 0·c = 0 *)
    pcLt0 = rwLt[ltMulR[pLt0, cPos], REFL[ratMulTm[pV2, cV]], zeroMulC];   (* p·c < 0 *)
    pcLt1 = ltLt2[pcLt0, ratZeroLtOneThm];   (* p·c < 1 *)
    memEqInv = HOL`Bool`SPEC[pV2, HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosMemThm], h0]];
    exBody = concl[memEqInv][[2]];
    cond = HOL`Bool`CONJ[hNM, HOL`Bool`CONJ[cPos, pcLt1]];
    exW = HOL`Bool`EXISTS[exBody, cV, cond];
    repInvP = EQMP[HOL`Equal`SYM[memEqInv], exW];
    chC = HOL`Bool`CHOOSE[cV, prX, repInvP];
    chS = HOL`Bool`CHOOSE[sV, posMemX, chC];
    impl = HOL`Bool`DISCH[concl[hMem0], chS];
    allImpl = HOL`Bool`GEN[pV2, impl];
    leThm = EQMP[HOL`Equal`SYM[unfoldRealLe[zeroRealTm[], invPosTm[xV]]], allImpl];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[h0], leThm]]
  ];

(* ---- signed wrapper realInv (def only; field law in increment 3) ---- *)
realInvTy = tyFun[realTy, realTy];
realInvDefThm =
  Module[{xV, body},
    xV = mkVar["x", realTy];
    body = mkAbs[xV, condTm[realLtTm[rZ[], xV], invPosTm[xV],
             realNegTm[invPosTm[realNegTm[xV]]]]];
    newDefinition[mkEq[mkVar["realInv", realInvTy], body]]
  ];
realInvConst[] := mkConst["realInv", realInvTy];
realInvTm[xT_] := mkComb[realInvConst[], xT];

End[];

EndPackage[];
