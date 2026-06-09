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
realInvPosThm::usage = "realInvPosThm — ⊢ ∀x. realLt (&ℝ 0) x ⇒ realInv x = invPos x.";
realInvNegThm::usage = "realInvNegThm — ⊢ ∀x. ¬(realLt (&ℝ 0) x) ⇒ realInv x = realNeg (invPos (realNeg x)).";
realNegPosThm::usage = "realNegPosThm — ⊢ ∀x. realLt x (&ℝ 0) ⇒ realLt (&ℝ 0) (realNeg x). Negation sends negatives to positives.";
realMulInvThm::usage = "realMulInvThm — ⊢ ∀x. ¬(x = &ℝ 0) ⇒ realMul x (realInv x) = &ℝ (&ℚ (&ℤ (SUC 0))). x · (1/x) = 1 — ℝ is a FIELD.";

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

(* ⊢ ∀x. realLt 0 x ⇒ realNnMul x (invPos x) = &ℝ1.  The Rudin reciprocal law.
   fwd (⊆ 1): any product member r satisfies r<1 (s<w ⟹ s·t<w·t=t·w<1).
   bwd (⊇ 1, hard): for 0≤r<1, straddle x with a gap < s0·(1−r) so the
   boundary member y and non-member y+gap have y/(y+gap) > r, then pick
   t ∈ (r/y, 1/(y+gap)); (y,t) is the product witness. *)
invPosMulThm =
  Module[{xV, h0, hNx, hNyNN, ip, oneR, rV, prod, memEq, oneMem, invMem, fwd, bwd, perR},
    xV = mkVar["x", realTy]; h0 = ASSUME[realLtTm[rZ[], xV]];
    hNx = realLtLeReal[xV, h0];                                   (* 0≤x *)
    hNyNN = HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosNonnegThm], h0];  (* 0≤invPos x *)
    ip = invPosTm[xV]; oneR = realOfRatTm[oneQ[]]; rV = mkVar["r", ratTy];
    prod = realNnMulTm[xV, ip];
    memEq = nnMemEq[xV, ip, rV, hNx, hNyNN];                      (* REP(x·ip) r = (r<0 ∨ ∃p q…) *)
    oneMem[tT_] := HOL`Bool`SPEC[tT, HOL`Bool`SPEC[oneQ[], realOfRatMemThm]];   (* REP(&ℝ1) t = t<1 *)
    invMem[tT_] := HOL`Bool`SPEC[tT, HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosMemThm], h0]];

    fwd = Module[{disjD, leftD, exPart, hMem, redMem, caseL, caseR, cases},
      disjD = concl[memEq][[2]]; leftD = disjD[[1, 2]]; exPart = disjD[[2]];
      hMem = ASSUME[repApp[prod, rV]];
      redMem = EQMP[memEq, hMem];
      caseL = EQMP[HOL`Equal`SYM[oneMem[rV]], ltLt2[ASSUME[leftD], ratZeroLtOneThm]];
      caseR = Module[{sV, tV, innerS, condT, hCond, mXs, c1, mIpT, c2, sPos, c3, tPos,
                      rLtst, invTred, wV3, hWbody, hW, mNMw, e1, wPos, twLt1, sLtw,
                      stLtwt, wtLt1, stLt1, rLt1, repOne},
        sV = mkVar["s", ratTy]; tV = mkVar["t", ratTy];
        innerS = concl[BETACONV[mkComb[exPart[[2]], sV]]][[2]];
        condT = concl[BETACONV[mkComb[innerS[[2]], tV]]][[2]];
        hCond = ASSUME[condT];
        mXs = HOL`Bool`CONJUNCT1[hCond]; c1 = HOL`Bool`CONJUNCT2[hCond];
        mIpT = HOL`Bool`CONJUNCT1[c1]; c2 = HOL`Bool`CONJUNCT2[c1];
        sPos = HOL`Bool`CONJUNCT1[c2]; c3 = HOL`Bool`CONJUNCT2[c2];
        tPos = HOL`Bool`CONJUNCT1[c3]; rLtst = HOL`Bool`CONJUNCT2[c3];
        invTred = EQMP[invMem[tV], mIpT];   (* ∃w. ¬REP_x w ∧ 0<w ∧ (t·w)<1 *)
        wV3 = mkVar["w", ratTy];
        hWbody = concl[BETACONV[mkComb[concl[invMem[tV]][[2, 2]], wV3]]][[2]];
        hW = ASSUME[hWbody];
        mNMw = HOL`Bool`CONJUNCT1[hW]; e1 = HOL`Bool`CONJUNCT2[hW];
        wPos = HOL`Bool`CONJUNCT1[e1]; twLt1 = HOL`Bool`CONJUNCT2[e1];   (* (t·w)<1 *)
        sLtw = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[wV3, HOL`Bool`SPEC[sV,
                 HOL`Bool`SPEC[xV, memNotMemLtThm]]], mXs], mNMw];   (* s<w *)
        stLtwt = ltMulR[sLtw, tPos];   (* s·t < w·t *)
        wtLt1 = rwLt[twLt1, HOL`Bool`SPEC[wV3, HOL`Bool`SPEC[tV, HOL`Stdlib`Rat`ratMulCommThm]], REFL[oneQ[]]];   (* w·t<1 *)
        stLt1 = ltLt2[stLtwt, wtLt1];   (* s·t<1 *)
        rLt1 = ltLt2[rLtst, stLt1];   (* r<1 *)
        repOne = EQMP[HOL`Equal`SYM[oneMem[rV]], rLt1];
        HOL`Bool`CHOOSE[sV, ASSUME[exPart], HOL`Bool`CHOOSE[tV, ASSUME[innerS],
          HOL`Bool`CHOOSE[wV3, invTred, repOne]]]
      ];
      cases = HOL`Bool`DISJCASES[redMem, caseL, caseR];
      HOL`Bool`DISCH[concl[hMem], cases]
    ];

    bwd = Module[{hMem1, rLt1, em, caseNeg, casePos, result},
      hMem1 = ASSUME[repApp[oneR, rV]];
      rLt1 = EQMP[oneMem[rV], hMem1];   (* r<1 *)
      em = HOL`Bool`EXCLUDEDMIDDLE[ratLtTm[rV, zeroQ[]]];
      caseNeg = nnMemIntroL[xV, ip, rV, ASSUME[ratLtTm[rV, zeroQ[]]], hNx, hNyNN];
      casePos = Module[{hNotNeg, rGe0, posMemX, sV, hS0c, mXs0, s0Pos, omr, omrPos,
                        s0omr, s0omrPos, dense0, gapPos, gapLt, gapTm, properX, uV, hU,
                        nV, hN, monoU, lhsU, rhsU, uLtSum, sumNW, hRepSum, sumLtU,
                        falseSum, notRepSum, straddleAll, straddle, MV, hM, hYin,
                        hSucMout, yTm, sucMulEq, yPlusWeq, wpTm, hYWout, le0Mnat, intLeEq,
                        int0M, ratLeEq, rat0M, le0gap, monoMul, mulZ, mqNN, addMonoY,
                        zeroAddY, commMQ, sLeY, yPos, yNe0, addMono0gap, zeroAddYe,
                        commGapY, yLeYgap, wpPos, wpNe0, invY, invW, invYpos, le0invY,
                        invYy1, invWwp1, rDistrib, oneMulGap, rGapLtGap, le0omr, monoLR,
                        commLs, commLy, s0omrLeYomr, rGapLtS0omr, rGapLtYomr, a1, a2, a3,
                        a4, a5, rPlusOmr, commRY, distBack, yTimesSum, yEq, addRy,
                        commLhs, commRhs, sumLtY, keyIneq, p1, p2, p3, p4, lhsP, q1, q2,
                        q3, q4, rhsP, le0y, le0wp, monoYW, mulZy, le0yw, ltU, rInvYltInvW,
                        denseT, tLow, tHigh, tTm, mulZr, monoRInvY, le0rInvY, ttPos, assocRIY,
                        invYyComm, congIY, rOne, rInvYyEqR, mulY, commTY, ytGtR, mulWp,
                        twpLt1, condInv, repIpT, nnCond, repProd, chM, chN, chU, chS0},
        hNotNeg = ASSUME[notTm[ratLtTm[rV, zeroQ[]]]];
        rGe0 = notNegToGe0[hNotNeg, rV];   (* 0≤r *)
        posMemX = HOL`Bool`MP[HOL`Bool`SPEC[xV, realPosHasPosMemThm], h0];
        sV = mkVar["s0", ratTy];
        hS0c = ASSUME[conjTm[repApp[xV, sV], ratLtTm[zeroQ[], sV]]];
        mXs0 = HOL`Bool`CONJUNCT1[hS0c]; s0Pos = HOL`Bool`CONJUNCT2[hS0c];
        omr = ratSubTm[oneQ[], rV];   (* 1−r *)
        omrPos = HOL`Bool`MP[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[rV, ratLtSubPosThm]], rLt1];   (* 0<1−r *)
        s0omr = ratMulTm[sV, omr];
        s0omrPos = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[omr, HOL`Bool`SPEC[sV, ratMulPosThm]], s0Pos], omrPos];
        dense0 = HOL`Bool`MP[HOL`Bool`SPEC[s0omr, HOL`Bool`SPEC[zeroQ[], ratDenseThm]], s0omrPos];
        gapPos = HOL`Bool`CONJUNCT1[dense0]; gapLt = HOL`Bool`CONJUNCT2[dense0];
        gapTm = concl[gapPos][[2]];   (* gap = ½(0+s0·(1−r)) *)
        properX = HOL`Bool`SPEC[xV, realProperThm];
        uV = mkVar["u0", ratTy]; hU = ASSUME[notTm[repApp[xV, uV]]];
        nV = mkVar["n", numTy];
        hN = ASSUME[ratLtTm[ratSubTm[uV, sV], natMulQ[nV, gapTm]]];
        monoU = HOL`Bool`MP[HOL`Bool`SPEC[sV, HOL`Bool`SPEC[natMulQ[nV, gapTm],
                  HOL`Bool`SPEC[ratSubTm[uV, sV], HOL`Stdlib`Rat`ratLtAddMonoThm]]], hN];
        lhsU = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[uV, ratSubAddThm]];   (* (u−s0)+s0 = u *)
        rhsU = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[natMulQ[nV, gapTm], HOL`Stdlib`Rat`ratAddCommThm]];
        uLtSum = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsU], rhsU], monoU];   (* u < s0+n·gap *)
        sumNW = ratAddTm[sV, natMulQ[nV, gapTm]];
        hRepSum = ASSUME[repApp[xV, sumNW]];
        sumLtU = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uV, HOL`Bool`SPEC[sumNW,
                   HOL`Bool`SPEC[xV, memNotMemLtThm]]], hRepSum], hU];
        falseSum = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[sumNW, ratLtIrreflThm]],
                     HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[sumNW, HOL`Bool`SPEC[uV,
                       HOL`Bool`SPEC[sumNW, ratLtTransThm]]], sumLtU], uLtSum]];
        notRepSum = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[repApp[xV, sumNW], falseSum]];
        straddleAll = HOL`Bool`SPEC[nV, HOL`Bool`MP[HOL`Bool`SPEC[gapTm,
                        HOL`Bool`SPEC[sV, HOL`Bool`SPEC[xV, cutStraddleThm]]], mXs0]];
        straddle = HOL`Bool`MP[straddleAll, notRepSum];
        MV = mkVar["MM", numTy];
        hM = ASSUME[conjTm[repApp[xV, ratAddTm[sV, natMulQ[MV, gapTm]]],
               notTm[repApp[xV, ratAddTm[sV, natMulQ[sucT[MV], gapTm]]]]]];
        hYin = HOL`Bool`CONJUNCT1[hM]; hSucMout = HOL`Bool`CONJUNCT2[hM];
        yTm = ratAddTm[sV, natMulQ[MV, gapTm]];   (* y = s0 + M·gap *)
        sucMulEq = HOL`Bool`SPEC[MV, HOL`Bool`SPEC[gapTm, ratNatSucMulThm]];   (* (SUC M)·gap = M·gap+gap *)
        yPlusWeq = TRANS[
          HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[sV]], sucMulEq],
          HOL`Equal`SYM[HOL`Bool`SPEC[gapTm, HOL`Bool`SPEC[natMulQ[MV, gapTm],
            HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratAddAssocThm]]]]];   (* s0+(SUC M)·gap = y+gap *)
        wpTm = ratAddTm[yTm, gapTm];   (* y+gap *)
        hYWout = EQMP[HOL`Equal`APTERM[notC[], HOL`Equal`APTERM[repRealTm[xV], yPlusWeq]], hSucMout];
        (* 0 < y :  0 ≤ M·gap ⟹ s0 ≤ y, with 0<s0 *)
        le0Mnat = HOL`Bool`SPEC[MV, HOL`Stdlib`Num`leqZeroThm];   (* 0≤M (nat) *)
        intLeEq = HOL`Bool`SPEC[MV, HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Int`intOfNumLeThm]];
        int0M = EQMP[HOL`Equal`SYM[intLeEq], le0Mnat];
        ratLeEq = HOL`Bool`SPEC[intOfNumTm[MV], HOL`Bool`SPEC[zeroInt[], HOL`Stdlib`Rat`ratOfIntLeThm]];
        rat0M = EQMP[HOL`Equal`SYM[ratLeEq], int0M];   (* 0 ≤ &ℚ(&ℤ M) *)
        le0gap = HOL`Bool`MP[HOL`Bool`SPEC[gapTm, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], gapPos];
        monoMul = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[gapTm, HOL`Bool`SPEC[zeroQ[],
                    HOL`Bool`SPEC[ratOfIntTm[intOfNumTm[MV]], HOL`Stdlib`Rat`ratLeMulNonnegThm]]], rat0M], le0gap];
        mulZ = HOL`Bool`SPEC[ratOfIntTm[intOfNumTm[MV]], HOL`Stdlib`Rat`ratMulZeroThm];   (* (&ℚ(&ℤM))·0 = 0 *)
        mqNN = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], mulZ], REFL[natMulQ[MV, gapTm]]], monoMul];   (* 0 ≤ M·gap *)
        addMonoY = HOL`Bool`MP[HOL`Bool`SPEC[sV, HOL`Bool`SPEC[natMulQ[MV, gapTm],
                     HOL`Bool`SPEC[zeroQ[], ratLeAddMonoThm]]], mqNN];   (* (0+s0) ≤ (M·gap+s0) *)
        zeroAddY = TRANS[HOL`Bool`SPEC[sV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
                     HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+s0 = s0 *)
        commMQ = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[natMulQ[MV, gapTm], HOL`Stdlib`Rat`ratAddCommThm]];   (* M·gap+s0 = s0+M·gap = y *)
        sLeY = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], zeroAddY], commMQ], addMonoY];   (* s0 ≤ y *)
        yPos = ltLe2[s0Pos, sLeY];   (* 0<y *)
        yNe0 = posToNe0[yPos];
        (* y ≤ y+gap, then 0 < y+gap *)
        addMono0gap = HOL`Bool`MP[HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[gapTm,
                        HOL`Bool`SPEC[zeroQ[], ratLeAddMonoThm]]], le0gap];   (* (0+y) ≤ (gap+y) *)
        zeroAddYe = TRANS[HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
                      HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+y = y *)
        commGapY = HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[gapTm, HOL`Stdlib`Rat`ratAddCommThm]];   (* gap+y = y+gap *)
        yLeYgap = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], zeroAddYe], commGapY], addMono0gap];   (* y ≤ y+gap *)
        wpPos = ltLe2[yPos, yLeYgap];   (* 0 < y+gap *)
        wpNe0 = posToNe0[wpPos];
        invY = ratInvTm[yTm]; invW = ratInvTm[wpTm];
        invYpos = HOL`Bool`MP[HOL`Bool`SPEC[yTm, ratInvPosThm], yPos];
        le0invY = HOL`Bool`MP[HOL`Bool`SPEC[invY, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], invYpos];
        invYy1 = TRANS[HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[invY, HOL`Stdlib`Rat`ratMulCommThm]],
                   HOL`Bool`MP[HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratMulInvThm], yNe0]];   (* invY·y = 1 *)
        invWwp1 = TRANS[HOL`Bool`SPEC[wpTm, HOL`Bool`SPEC[invW, HOL`Stdlib`Rat`ratMulCommThm]],
                    HOL`Bool`MP[HOL`Bool`SPEC[wpTm, HOL`Stdlib`Rat`ratMulInvThm], wpNe0]];   (* invW·(y+gap) = 1 *)
        (* key inequality  r·(y+gap) < y *)
        rDistrib = HOL`Bool`SPEC[gapTm, HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulDistribThm]]];   (* r·(y+gap)=r·y+r·gap *)
        oneMulGap = TRANS[HOL`Bool`SPEC[gapTm, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                      HOL`Bool`SPEC[gapTm, HOL`Stdlib`Rat`ratMulOneThm]];   (* 1·gap = gap *)
        rGapLtGap = rwLt[ltMulR[rLt1, gapPos], REFL[ratMulTm[rV, gapTm]], oneMulGap];   (* r·gap < gap *)
        le0omr = HOL`Bool`MP[HOL`Bool`SPEC[omr, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], omrPos];   (* 0≤1−r *)
        monoLR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[sV,
                   HOL`Bool`SPEC[omr, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], le0omr], sLeY];   (* (1−r)·s0 ≤ (1−r)·y *)
        commLs = HOL`Bool`SPEC[omr, HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratMulCommThm]];   (* s0·(1−r)=(1−r)·s0 *)
        commLy = HOL`Bool`SPEC[omr, HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratMulCommThm]];   (* y·(1−r)=(1−r)·y *)
        s0omrLeYomr = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], HOL`Equal`SYM[commLs]],
                        HOL`Equal`SYM[commLy]], monoLR];   (* s0·(1−r) ≤ y·(1−r) *)
        rGapLtS0omr = ltLt2[rGapLtGap, gapLt];   (* r·gap < s0·(1−r) *)
        rGapLtYomr = ltLe2[rGapLtS0omr, s0omrLeYomr];   (* r·gap < y·(1−r) *)
        a1 = HOL`Equal`SYM[HOL`Bool`SPEC[ratNegTm[rV], HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratAddAssocThm]]]];   (* r+(1+(−r)) = (r+1)+(−r) *)
        a2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
               HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratAddCommThm]]], REFL[ratNegTm[rV]]];   (* (r+1)+(−r) = (1+r)+(−r) *)
        a3 = HOL`Bool`SPEC[ratNegTm[rV], HOL`Bool`SPEC[rV, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratAddAssocThm]]];   (* (1+r)+(−r) = 1+(r+(−r)) *)
        a4 = HOL`Equal`APTERM[mkComb[HOL`Stdlib`Rat`ratAddConst[], oneQ[]], HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratAddNegThm]];   (* 1+(r+(−r)) = 1+0 *)
        a5 = HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratAddZeroThm];   (* 1+0 = 1 *)
        rPlusOmr = TRANS[a1, TRANS[a2, TRANS[a3, TRANS[a4, a5]]]];   (* r+(1−r) = 1 *)
        commRY = HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulCommThm]];   (* r·y = y·r *)
        distBack = HOL`Equal`SYM[HOL`Bool`SPEC[omr, HOL`Bool`SPEC[rV, HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratMulDistribThm]]]];   (* y·r+y·(1−r) = y·(r+(1−r)) *)
        yTimesSum = TRANS[distBack, TRANS[HOL`Equal`APTERM[mkComb[ratMulC[], yTm], rPlusOmr],
                      HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratMulOneThm]]];   (* y·r+y·(1−r) = y *)
        yEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], commRY],
                REFL[ratMulTm[yTm, omr]]], yTimesSum];   (* r·y+y·(1−r) = y *)
        addRy = ltAddR[rGapLtYomr, ratMulTm[rV, yTm]];   (* (r·gap+r·y) < (y·(1−r)+r·y) *)
        commLhs = HOL`Bool`SPEC[ratMulTm[rV, yTm], HOL`Bool`SPEC[ratMulTm[rV, gapTm], HOL`Stdlib`Rat`ratAddCommThm]];   (* r·gap+r·y = r·y+r·gap *)
        commRhs = HOL`Bool`SPEC[ratMulTm[rV, yTm], HOL`Bool`SPEC[ratMulTm[yTm, omr], HOL`Stdlib`Rat`ratAddCommThm]];   (* y·(1−r)+r·y = r·y+y·(1−r) *)
        sumLtY = rwLt[rwLt[addRy, commLhs, commRhs], HOL`Equal`SYM[rDistrib], yEq];   (* r·(y+gap) < y *)
        keyIneq = sumLtY;
        (* r·invY < invW  via cancel of u = y·(y+gap) ≥ 0 *)
        p1 = HOL`Bool`SPEC[ratMulTm[yTm, wpTm], HOL`Bool`SPEC[invY, HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulAssocThm]]];   (* (r·invY)·(y·wp) = r·(invY·(y·wp)) *)
        p2 = HOL`Equal`APTERM[mkComb[ratMulC[], rV],
               HOL`Equal`SYM[HOL`Bool`SPEC[wpTm, HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[invY, HOL`Stdlib`Rat`ratMulAssocThm]]]]];   (* r·(invY·(y·wp)) = r·((invY·y)·wp) *)
        p3 = HOL`Equal`APTERM[mkComb[ratMulC[], rV],
               HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], invYy1], REFL[wpTm]]];   (* r·((invY·y)·wp) = r·(1·wp) *)
        p4 = HOL`Equal`APTERM[mkComb[ratMulC[], rV],
               TRANS[HOL`Bool`SPEC[wpTm, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratMulCommThm]],
                 HOL`Bool`SPEC[wpTm, HOL`Stdlib`Rat`ratMulOneThm]]];   (* r·(1·wp) = r·wp *)
        lhsP = TRANS[p1, TRANS[p2, TRANS[p3, p4]]];   (* (r·invY)·(y·wp) = r·wp *)
        q1 = HOL`Equal`APTERM[mkComb[ratMulC[], invW],
               HOL`Bool`SPEC[wpTm, HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratMulCommThm]]];   (* invW·(y·wp) = invW·(wp·y) *)
        q2 = HOL`Equal`SYM[HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[wpTm, HOL`Bool`SPEC[invW, HOL`Stdlib`Rat`ratMulAssocThm]]]];   (* invW·(wp·y) = (invW·wp)·y *)
        q3 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], invWwp1], REFL[yTm]];   (* (invW·wp)·y = 1·y *)
        q4 = TRANS[HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratMulCommThm]],
               HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratMulOneThm]];   (* 1·y = y *)
        rhsP = TRANS[q1, TRANS[q2, TRANS[q3, q4]]];   (* invW·(y·wp) = y *)
        le0y = HOL`Bool`MP[HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], yPos];
        le0wp = HOL`Bool`MP[HOL`Bool`SPEC[wpTm, HOL`Bool`SPEC[zeroQ[], ratLtImpLeThm]], wpPos];
        monoYW = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[wpTm, HOL`Bool`SPEC[zeroQ[],
                   HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], le0y], le0wp];   (* y·0 ≤ y·wp *)
        mulZy = HOL`Bool`SPEC[yTm, HOL`Stdlib`Rat`ratMulZeroThm];   (* y·0 = 0 *)
        le0yw = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], mulZy], REFL[ratMulTm[yTm, wpTm]]], monoYW];   (* 0 ≤ y·wp *)
        ltU = rwLt[keyIneq, HOL`Equal`SYM[lhsP], HOL`Equal`SYM[rhsP]];   (* (r·invY)·(y·wp) < invW·(y·wp) *)
        rInvYltInvW = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[ratMulTm[yTm, wpTm],
                        HOL`Bool`SPEC[invW, HOL`Bool`SPEC[ratMulTm[rV, invY], HOL`Stdlib`Rat`ratLtMulPosCancelThm]]], le0yw], ltU];   (* r·invY < invW *)
        denseT = HOL`Bool`MP[HOL`Bool`SPEC[invW, HOL`Bool`SPEC[ratMulTm[rV, invY], ratDenseThm]], rInvYltInvW];
        tLow = HOL`Bool`CONJUNCT1[denseT]; tHigh = HOL`Bool`CONJUNCT2[denseT];   (* r·invY < t ;  t < invW *)
        tTm = concl[tLow][[2]];
        (* 0 < t *)
        mulZr = HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulZeroThm];   (* r·0 = 0 *)
        monoRInvY = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[invY, HOL`Bool`SPEC[zeroQ[],
                      HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratLeMulNonnegThm]]], rGe0], le0invY];   (* r·0 ≤ r·invY *)
        le0rInvY = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLeC[], mulZr], REFL[ratMulTm[rV, invY]]], monoRInvY];   (* 0 ≤ r·invY *)
        ttPos = leLt2[le0rInvY, tLow];   (* 0 < t *)
        (* r < y·t *)
        assocRIY = HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[invY, HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulAssocThm]]];   (* (r·invY)·y = r·(invY·y) *)
        congIY = HOL`Equal`APTERM[mkComb[ratMulC[], rV], invYy1];   (* r·(invY·y) = r·1 *)
        rOne = HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulOneThm];   (* r·1 = r *)
        rInvYyEqR = TRANS[assocRIY, TRANS[congIY, rOne]];   (* (r·invY)·y = r *)
        mulY = ltMulR[tLow, yPos];   (* (r·invY)·y < t·y *)
        commTY = HOL`Bool`SPEC[yTm, HOL`Bool`SPEC[tTm, HOL`Stdlib`Rat`ratMulCommThm]];   (* t·y = y·t *)
        ytGtR = rwLt[mulY, rInvYyEqR, commTY];   (* r < y·t *)
        (* t·(y+gap) < 1 *)
        mulWp = ltMulR[tHigh, wpPos];   (* t·wp < invW·wp *)
        twpLt1 = rwLt[mulWp, REFL[ratMulTm[tTm, wpTm]], invWwp1];   (* t·wp < 1 *)
        condInv = HOL`Bool`CONJ[hYWout, HOL`Bool`CONJ[wpPos, twpLt1]];
        repIpT = EQMP[HOL`Equal`SYM[invMem[tTm]], HOL`Bool`EXISTS[concl[invMem[tTm]][[2]], wpTm, condInv]];
        nnCond = HOL`Bool`CONJ[hYin, HOL`Bool`CONJ[repIpT, HOL`Bool`CONJ[yPos, HOL`Bool`CONJ[ttPos, ytGtR]]]];
        repProd = nnMemIntroR[xV, ip, rV, yTm, tTm, nnCond, hNx, hNyNN];
        chM = HOL`Bool`CHOOSE[MV, straddle, repProd];
        chN = HOL`Bool`CHOOSE[nV, HOL`Bool`MP[HOL`Bool`SPEC[ratSubTm[uV, sV],
                HOL`Bool`SPEC[gapTm, ratNatMulGtThm]], gapPos], chM];
        chU = HOL`Bool`CHOOSE[uV, properX, chN];
        chS0 = HOL`Bool`CHOOSE[sV, posMemX, chU];
        chS0
      ];
      result = HOL`Bool`DISJCASES[em, caseNeg, casePos];
      HOL`Bool`DISCH[concl[hMem1], result]
    ];

    perR = HOL`Bool`GEN[rV, HOL`Kernel`DEDUCTANTISYM[HOL`Bool`UNDISCH[bwd], HOL`Bool`UNDISCH[fwd]]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[h0], realEqFromRepEq[prod, oneR, perR]]]
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

(* ⊢ realInv x = COND (realLt 0 x) (invPos x) (realNeg (invPos (realNeg x))) *)
unfoldRealInv[xT_] :=
  Module[{s1}, s1 = HOL`Equal`APTHM[realInvDefThm, xT];
    TRANS[s1, BETACONV[concl[s1][[2]]]]];

(* ⊢ ∀x. realLt 0 x ⇒ realInv x = invPos x. *)
realInvPosThm =
  Module[{xV, hPos},
    xV = mkVar["x", realTy]; hPos = ASSUME[realLtTm[rZ[], xV]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLtTm[rZ[], xV],
      TRANS[unfoldRealInv[xV],
        condReduceT[hPos, invPosTm[xV], realNegTm[invPosTm[realNegTm[xV]]]]]]]
  ];

(* ⊢ ∀x. ¬(realLt 0 x) ⇒ realInv x = realNeg (invPos (realNeg x)). *)
realInvNegThm =
  Module[{xV, hNotPos},
    xV = mkVar["x", realTy]; hNotPos = ASSUME[notTm[realLtTm[rZ[], xV]]];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[notTm[realLtTm[rZ[], xV]],
      TRANS[unfoldRealInv[xV],
        condReduceF[hNotPos, invPosTm[xV], realNegTm[invPosTm[realNegTm[xV]]]]]]]
  ];

(* ⊢ ∀x. realLt x 0 ⇒ realLt 0 (realNeg x).  (negation reverses around 0) *)
realNegPosThm =
  Module[{xV, hLt, nx, leNegX0, viaNeg, le0x, notLeNegX0, ltNeg},
    xV = mkVar["x", realTy]; nx = realNegTm[xV];
    hLt = ASSUME[realLtTm[xV, rZ[]]];   (* x<0 = ¬realLe 0 x *)
    leNegX0 = ASSUME[realLeTm[nx, rZ[]]];
    viaNeg = HOL`Bool`MP[HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[nx, realLeNegThm]], leNegX0];   (* realLe(−0)(−−x) *)
    le0x = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[realLeConst[], realNegZeroThm],
             HOL`Bool`SPEC[xV, realNegNegThm]], viaNeg];   (* realLe 0 x *)
    notLeNegX0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[nx, rZ[]],
                   HOL`Bool`MP[HOL`Bool`NOTELIM[EQMP[HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[xV, realLtNotLeThm]], hLt]], le0x]]];
    ltNeg = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[nx, HOL`Bool`SPEC[rZ[], realLtNotLeThm]]], notLeNegX0];   (* realLt 0 (−x) *)
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[realLtTm[xV, rZ[]], ltNeg]]
  ];

(* ⊢ ∀x. ¬(x = &ℝ0) ⇒ realMul x (realInv x) = &ℝ1.  ℝ is a FIELD. *)
realMulInvThm =
  Module[{xV, hNe, oneR, em, casePosX, caseNegX},
    xV = mkVar["x", realTy]; hNe = ASSUME[notTm[mkEq[xV, rZ[]]]];
    oneR = realOfRatTm[oneQ[]];
    em = HOL`Bool`EXCLUDEDMIDDLE[realLtTm[rZ[], xV]];
    casePosX = Module[{hPos, hNx, hNyInv, e1, e2, e3},
      hPos = ASSUME[realLtTm[rZ[], xV]];
      hNx = realLtLeReal[xV, hPos];
      hNyInv = HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosNonnegThm], hPos];
      e1 = mulCongR[xV, HOL`Bool`MP[HOL`Bool`SPEC[xV, realInvPosThm], hPos]];   (* x·invX = x·invPos x *)
      e2 = casePP[xV, invPosTm[xV], hNx, hNyInv];   (* x·invPos x = nn x (invPos x) *)
      e3 = HOL`Bool`MP[HOL`Bool`SPEC[xV, invPosMulThm], hPos];   (* = &ℝ1 *)
      TRANS[e1, TRANS[e2, e3]]
    ];
    caseNegX = Module[{hNotPos, eqLt, notNotLe, xLe0, notLe0x, antis, eqX0, fls, xLt0,
                       negXpos, nx, ipnx, hNnx, hNyInvNx, eN1, xeqNegNx, eN3a, eN3,
                       eN2, eN4, eN5, eN6, eN7},
      hNotPos = ASSUME[notTm[realLtTm[rZ[], xV]]];
      eqLt = HOL`Bool`SPEC[xV, HOL`Bool`SPEC[rZ[], realLtNotLeThm]];   (* realLt 0 x = ¬realLe x 0 *)
      notNotLe = EQMP[HOL`Equal`APTERM[notC[], eqLt], hNotPos];   (* ¬¬realLe x 0 *)
      xLe0 = HOL`Bool`CCONTR[realLeTm[xV, rZ[]],
               HOL`Bool`MP[HOL`Bool`NOTELIM[notNotLe], ASSUME[notTm[realLeTm[xV, rZ[]]]]]];   (* realLe x 0 *)
      antis = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[xV, HOL`Bool`SPEC[rZ[], realLeAntisymThm]],
                ASSUME[realLeTm[rZ[], xV]]], xLe0];   (* &ℝ0 = x *)
      eqX0 = HOL`Equal`SYM[antis];   (* x = &ℝ0 *)
      fls = HOL`Bool`MP[HOL`Bool`NOTELIM[hNe], eqX0];
      notLe0x = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[rZ[], xV], fls]];   (* ¬realLe 0 x *)
      xLt0 = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[rZ[], HOL`Bool`SPEC[xV, realLtNotLeThm]]], notLe0x];   (* realLt x 0 *)
      negXpos = HOL`Bool`MP[HOL`Bool`SPEC[xV, realNegPosThm], xLt0];   (* realLt 0 (−x) *)
      nx = realNegTm[xV]; ipnx = invPosTm[nx];
      hNnx = realLtLeReal[nx, negXpos];
      hNyInvNx = HOL`Bool`MP[HOL`Bool`SPEC[nx, invPosNonnegThm], negXpos];
      eN1 = mulCongR[xV, HOL`Bool`MP[HOL`Bool`SPEC[xV, realInvNegThm], hNotPos]];   (* x·invX = x·(−ipnx) *)
      eN2 = HOL`Bool`SPEC[ipnx, HOL`Bool`SPEC[xV, realMulNegRightThm]];   (* x·(−ipnx) = −(x·ipnx) *)
      xeqNegNx = HOL`Equal`SYM[HOL`Bool`SPEC[xV, realNegNegThm]];   (* x = −(−x) = −nx *)
      eN3a = mulCongL[xeqNegNx, ipnx];   (* x·ipnx = (−nx)·ipnx *)
      eN3 = TRANS[eN3a, HOL`Bool`SPEC[ipnx, HOL`Bool`SPEC[nx, realMulNegLeftThm]]];   (* x·ipnx = −(nx·ipnx) *)
      eN4 = rNegCong[eN3];   (* −(x·ipnx) = −(−(nx·ipnx)) *)
      eN5 = HOL`Bool`SPEC[realMulTm[nx, ipnx], realNegNegThm];   (* −(−(nx·ipnx)) = nx·ipnx *)
      eN6 = casePP[nx, ipnx, hNnx, hNyInvNx];   (* nx·ipnx = nn nx ipnx *)
      eN7 = HOL`Bool`MP[HOL`Bool`SPEC[nx, invPosMulThm], negXpos];   (* = &ℝ1 *)
      TRANS[eN1, TRANS[eN2, TRANS[eN4, TRANS[eN5, TRANS[eN6, eN7]]]]]
    ];
    HOL`Bool`GEN[xV, HOL`Bool`DISCH[concl[hNe], HOL`Bool`DISJCASES[em, casePosX, caseNegX]]]
  ];

End[];

EndPackage[];
