(* M7-7 / stdlib/Real/RatAux.wl — ℚ/ℤ Archimedean + ℚ multiplicative-order
   layer serving Real's multiplication (Mul.wl) and completeness (Complete.wl).

   Part of the stdlib/Real/ folder (PLAN §8.1): shares context HOL`Stdlib`Real`
   with Cut.wl / Field.wl, so Cut.wl's shared term-builder vocabulary
   (ratLtTm, ratOfIntTm, intOfNumTm, zeroN, sucT, zeroQ, existsTm, …) and its
   parked strict-order lemmas (intOfNumLtThm, ratLtIrreflThm, ratLtTransThm,
   ratLeCasesThm) are reused here for free.  Loads AFTER Cut.wl, BEFORE Field.wl.

   Extracted verbatim from Field.wl 2026-06-07 (pre-mul cleanup — PLAN Phase-3
   "Stage D realMul 架构"): the integer/rational Archimedean property and the ℚ
   positive-multiplication order layer the Dedekind product proof consumes.
   Pure ℚ/ℤ — no REP_real / IS_CUT.  (natMulQ / ratNatZeroMulThm are the
   straddle helpers Field's cutStraddleThm consumes from here.)
   Blueprint: ../archive/tautology Cut/Arch.lean (their exists_nat_gt used
   Rat.ceil; we build it from ℤ). *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

intLtLeTransThm::usage = "intLtLeTransThm — ⊢ ∀a b c. intLt a b ⇒ intLe b c ⇒ intLt a c.";
intLeLtTransThm::usage = "intLeLtTransThm — ⊢ ∀a b c. intLe a b ⇒ intLt b c ⇒ intLt a c.";
intArchThm::usage = "intArchThm — ⊢ ∀z. ∃n:num. intLt z (&ℤ n). ℤ is Archimedean (every integer is below some natural).";
ratArchThm::usage = "ratArchThm — ⊢ ∀q. ∃n:num. ratLt q (&ℚ (&ℤ n)). ℚ is Archimedean (every rational is below some natural). Lifts intArchThm via cross-multiplication.";
ratMulRightCancelThm::usage = "ratMulRightCancelThm — ⊢ ∀w a b. ¬(w = &ℚ(&ℤ0)) ⇒ ratMul a w = ratMul b w ⇒ a = b.";
ratLtMulPosThm::usage = "ratLtMulPosThm — ⊢ ∀w a b. ratLt (&ℚ(&ℤ0)) w ⇒ ratLt a b ⇒ ratLt (ratMul a w) (ratMul b w). Strict monotonicity of ·w for w>0.";
ratNatMulGtThm::usage = "ratNatMulGtThm — ⊢ ∀w r. ratLt (&ℚ(&ℤ0)) w ⇒ ∃n:num. ratLt r (ratMul (&ℚ(&ℤ n)) w).";
ratNatSucMulThm::usage = "ratNatSucMulThm — ⊢ ∀w k. ratMul (&ℚ(&ℤ(SUC k))) w = ratAdd (ratMul (&ℚ(&ℤ k)) w) w.";

ratAddRightCancelThm::usage = "ratAddRightCancelThm — ⊢ ∀a b c. ratAdd a c = ratAdd b c ⇒ a = b. Right additive cancellation in ℚ.";
ratNegNegThm::usage = "ratNegNegThm — ⊢ ∀q. ratNeg (ratNeg q) = q.";
ratAddLeftCancelThm::usage = "ratAddLeftCancelThm — ⊢ ∀a x y. ratAdd a x = ratAdd a y ⇒ x = y. Left additive cancellation in ℚ.";
ratNegAddThm::usage = "ratNegAddThm — ⊢ ∀a b. ratNeg (ratAdd a b) = ratAdd (ratNeg a) (ratNeg b).";
ratSubLtSelfThm::usage = "ratSubLtSelfThm — ⊢ ∀v r. ratLt (&ℚ (&ℤ 0)) r ⇒ ratLt (ratAdd v (ratNeg r)) v. (0<r ⇒ v−r < v.)";
ratLtSubPosThm::usage = "ratLtSubPosThm — ⊢ ∀a b. ratLt a b ⇒ ratLt (&ℚ (&ℤ 0)) (ratAdd b (ratNeg a)). (a<b ⇒ 0 < b−a.)";

Begin["`Private`"];

(* ============================================================ *)
(* Stage C (cont.): ℚ-Archimedean (for the additive inverse).    *)
(* Blueprint: ../tautology Lean (Cut/Arch.lean, Cut/Add.lean);   *)
(* their exists_nat_gt used Rat.ceil — we build it from ℤ.       *)
(* ============================================================ *)

intTyF = mkType["int", {}];
intLtC[] := HOL`Stdlib`Int`intLtConst[];
intLeC[] := HOL`Stdlib`Int`intLeConst[];
intLtTmF[a_, b_] := mkComb[mkComb[intLtC[], a], b];
intLeTmF[a_, b_] := mkComb[mkComb[intLeC[], a], b];
intNegTmF[z_] := mkComb[HOL`Stdlib`Int`intNegConst[], z];

(* ⊢ ∀a b c. intLt a b ⇒ intLe b c ⇒ intLt a c *)
intLtLeTransThm =
  Module[{aV, bV, cV, hab, hbc, abNL, notLeBA, hca, leBA, falseT, acNL, notLeCA, ltAC},
    aV = mkVar["a", intTyF]; bV = mkVar["b", intTyF]; cV = mkVar["c", intTyF];
    hab = ASSUME[intLtTmF[aV, bV]]; hbc = ASSUME[intLeTmF[bV, cV]];
    abNL = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Int`intLtNotLeThm]];   (* a<b = ¬(b≤a) *)
    notLeBA = EQMP[abNL, hab];
    hca = ASSUME[intLeTmF[cV, aV]];
    leBA = HOL`Bool`MP[HOL`Bool`MP[
             HOL`Bool`SPEC[aV, HOL`Bool`SPEC[cV, HOL`Bool`SPEC[bV, HOL`Stdlib`Int`intLeTransThm]]],
             hbc], hca];   (* b≤a *)
    falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeBA], leBA];
    acNL = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[aV, HOL`Stdlib`Int`intLtNotLeThm]];   (* a<c = ¬(c≤a) *)
    notLeCA = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[intLeTmF[cV, aV], falseT]];
    ltAC = EQMP[HOL`Equal`SYM[acNL], notLeCA];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[concl[hab], HOL`Bool`DISCH[concl[hbc], ltAC]]]]]
  ];

(* ⊢ ∀a b c. intLe a b ⇒ intLt b c ⇒ intLt a c *)
intLeLtTransThm =
  Module[{aV, bV, cV, hab, hbc, bcNL, notLeCB, hca, leCB, falseT, acNL, notLeCA, ltAC},
    aV = mkVar["a", intTyF]; bV = mkVar["b", intTyF]; cV = mkVar["c", intTyF];
    hab = ASSUME[intLeTmF[aV, bV]]; hbc = ASSUME[intLtTmF[bV, cV]];
    bcNL = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[bV, HOL`Stdlib`Int`intLtNotLeThm]];   (* b<c = ¬(c≤b) *)
    notLeCB = EQMP[bcNL, hbc];
    hca = ASSUME[intLeTmF[cV, aV]];
    leCB = HOL`Bool`MP[HOL`Bool`MP[
             HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[cV, HOL`Stdlib`Int`intLeTransThm]]],
             hca], hab];   (* c≤b *)
    falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeCB], leCB];
    acNL = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[aV, HOL`Stdlib`Int`intLtNotLeThm]];   (* a<c = ¬(c≤a) *)
    notLeCA = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[intLeTmF[cV, aV], falseT]];
    ltAC = EQMP[HOL`Equal`SYM[acNL], notLeCA];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[concl[hab], HOL`Bool`DISCH[concl[hbc], ltAC]]]]]
  ];

(* ⊢ ∀z. ∃n:num. intLt z (&ℤ n) *)
intArchThm =
  Module[{zV, nV, mV, cases, posTm, negTm, posBranch, negBranch},
    zV = mkVar["z", intTyF]; nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    cases = HOL`Bool`SPEC[zV, HOL`Stdlib`Int`intCasesThm];   (* (∃n. z=&ℤn) ∨ (∃n. z=intNeg(&ℤn)) *)
    posTm = existsTm[nV, mkEq[zV, intOfNumTm[nV]]];        (* ∃n. z = &ℤ n *)
    negTm = existsTm[nV, mkEq[zV, intNegTmF[intOfNumTm[nV]]]];   (* ∃n. z = intNeg (&ℤ n) *)

    (* pos: z=&ℤm ⟹ z < &ℤ(SUC m) *)
    posBranch = Module[{hEx, hzm, ltEq, ltMS, zLt, ex},
      hEx = ASSUME[posTm];
      hzm = ASSUME[mkEq[zV, intOfNumTm[mV]]];   (* z = &ℤ m *)
      ltEq = HOL`Bool`SPEC[sucT[mV], HOL`Bool`SPEC[mV, intOfNumLtThm]];   (* intLt(&ℤm)(&ℤ(SUC m)) = (m<SUC m) *)
      ltMS = HOL`Bool`SPEC[mV, HOL`Stdlib`Num`ltSucThm];   (* m < SUC m *)
      zLt = EQMP[HOL`Equal`SYM[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLtC[], hzm],
              REFL[intOfNumTm[sucT[mV]]]]], EQMP[HOL`Equal`SYM[ltEq], ltMS]];
      (* intLt(&ℤm)(&ℤ(SUC m)) [from m<SUC m], then rewrite &ℤm → z via hzm⁻¹ → intLt z (&ℤ(SUC m)) *)
      ex = HOL`Bool`EXISTS[existsTm[nV, intLtTmF[zV, intOfNumTm[nV]]], sucT[mV], zLt];
      HOL`Bool`CHOOSE[mV, hEx, ex]
    ];

    (* neg: z=intNeg(&ℤm) ⟹ z < &ℤ(SUC 0) (via z ≤ &ℤ0 < &ℤ1) *)
    negBranch = Module[{hEx, hzm, zeroLeM, le0M, leNegM, negZ, zLe0Raw, zLe0,
                        lt01Eq, lt01, zLtSuc0, zLt, ex},
      hEx = ASSUME[negTm];
      hzm = ASSUME[mkEq[zV, intNegTmF[intOfNumTm[mV]]]];   (* z = intNeg(&ℤ m) *)
      zeroLeM = HOL`Bool`SPEC[mV, HOL`Stdlib`Num`leqZeroThm];   (* 0 ≤ m *)
      le0M = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[mV, HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Int`intOfNumLeThm]]], zeroLeM];
      (* intLe(&ℤ0)(&ℤm) *)
      leNegM = HOL`Bool`MP[HOL`Bool`SPEC[intOfNumTm[mV], HOL`Bool`SPEC[intOfNumTm[zeroN[]],
                 HOL`Stdlib`Int`intLeNegThm]], le0M];   (* intLe(intNeg(&ℤm))(intNeg(&ℤ0)) *)
      negZ = HOL`Stdlib`Int`intNegZeroThm;   (* intNeg(&ℤ0) = &ℤ0 *)
      zLe0Raw = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC[], REFL[intNegTmF[intOfNumTm[mV]]]], negZ],
                  leNegM];   (* intLe(intNeg(&ℤm))(&ℤ0) *)
      zLe0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLeC[], HOL`Equal`SYM[hzm]],
               REFL[intOfNumTm[zeroN[]]]], zLe0Raw];   (* intLe z (&ℤ0) *)
      lt01Eq = HOL`Bool`SPEC[sucT[zeroN[]], HOL`Bool`SPEC[zeroN[], intOfNumLtThm]];   (* intLt(&ℤ0)(&ℤ(SUC0)) = (0<SUC0) *)
      lt01 = EQMP[HOL`Equal`SYM[lt01Eq], HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`ltSucThm]];   (* intLt(&ℤ0)(&ℤ(SUC0)) *)
      zLtSuc0 = HOL`Bool`MP[HOL`Bool`MP[
                  HOL`Bool`SPEC[intOfNumTm[sucT[zeroN[]]], HOL`Bool`SPEC[intOfNumTm[zeroN[]],
                    HOL`Bool`SPEC[zV, intLeLtTransThm]]], zLe0], lt01];   (* intLt z (&ℤ(SUC0)) *)
      ex = HOL`Bool`EXISTS[existsTm[nV, intLtTmF[zV, intOfNumTm[nV]]], sucT[zeroN[]], zLtSuc0];
      HOL`Bool`CHOOSE[mV, hEx, ex]
    ];

    HOL`Bool`GEN[zV, HOL`Bool`DISJCASES[cases, posBranch, negBranch]]
  ];

(* ⊢ ∀q. ∃n:num. ratLt q (&ℚ (&ℤ n)) *)
intNumPairTy = HOL`Stdlib`Pair`prodTy[intTyF, numTy];
repRatTm[q_] := mkComb[HOL`Stdlib`Rat`repRatConst[], q];
fstIN[p_] := mkComb[mkConst["FST", tyFun[intNumPairTy, intTyF]], p];
sndIN[p_] := mkComb[mkConst["SND", tyFun[intNumPairTy, numTy]], p];
intMulTmF[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
intOfNumC[] := HOL`Stdlib`Int`intOfNumConst[];
leqC[] := HOL`Stdlib`Num`leqConst[];

(* ⊢ FST (a, b) = a  at int × num *)
fstINeq[aT_, bT_] :=
  HOL`Kernel`INST[{mkVar["a", intTyF] -> aT, mkVar["b", numTy] -> bT},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTyF, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`fstPairEqThm]];
sndINeq[aT_, bT_] :=
  HOL`Kernel`INST[{mkVar["a", intTyF] -> aT, mkVar["b", numTy] -> bT},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> intTyF, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`sndPairEqThm]];

ratArchThm =
  Module[{qV, aTm, bTm, redEq, bNeq0, lt0b, ltUnf, suc0LeB, archA, kV, hArchK,
          kbThm, kSUC0, kbTm, kSUC0eqK, kLeKb, kLeKbInt, aLtKb, ratLtQk, ex},
    qV = mkVar["q", ratTy];
    aTm = fstIN[repRatTm[qV]];   (* FST (REP q) : int *)
    bTm = sndIN[repRatTm[qV]];   (* SND (REP q) : num *)

    (* redEq[n] : ratLt q (&ℚ(&ℤ n)) = intLt aTm (&ℤ (n · bTm)) *)
    redEq[nTm_] := Module[{ap1, ap1b, ap2, unf, freeROI, repQOI, fstE, sndE,
                           leftRw, rightRw, ofnMul},
      ap1 = HOL`Equal`APTHM[HOL`Stdlib`Rat`ratLtDefThm, qV];
      ap1b = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
      ap2 = HOL`Equal`APTHM[ap1b, ratOfIntTm[intOfNumTm[nTm]]];
      unf = TRANS[ap2, BETACONV[concl[ap2][[2]]]];
      (* ratLt q (&ℚ&ℤn) = intLt (intMul aTm (&ℤ(SND(REP(&ℚ&ℤn))))) (intMul (FST(REP(&ℚ&ℤn))) (&ℤ bTm)) *)
      freeROI = concl[HOL`Stdlib`Rat`repRatOfIntThm][[1, 2, 2, 2]];   (* the free int var in REP_rat(&ℚ ·) *)
      repQOI = HOL`Kernel`INST[{freeROI -> intOfNumTm[nTm]}, HOL`Stdlib`Rat`repRatOfIntThm];
      (* REP(&ℚ&ℤn) = (&ℤn, SUC 0) *)
      fstE = TRANS[HOL`Equal`APTERM[mkConst["FST", tyFun[intNumPairTy, intTyF]], repQOI],
               fstINeq[intOfNumTm[nTm], sucT[zeroN[]]]];   (* FST(REP(&ℚ&ℤn)) = &ℤn *)
      sndE = TRANS[HOL`Equal`APTERM[mkConst["SND", tyFun[intNumPairTy, numTy]], repQOI],
               sndINeq[intOfNumTm[nTm], sucT[zeroN[]]]];   (* SND(REP(&ℚ&ℤn)) = SUC 0 *)
      leftRw = TRANS[
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Int`intMulConst[], REFL[aTm]],
          HOL`Equal`APTERM[intOfNumC[], sndE]],
        HOL`Bool`SPEC[aTm, HOL`Stdlib`Int`intMulOneThm]];
      (* intMul aTm (&ℤ(SND(REP(&ℚ&ℤn)))) = intMul aTm (&ℤ(SUC0)) = aTm *)
      ofnMul = HOL`Bool`SPEC[bTm, HOL`Bool`SPEC[nTm, HOL`Stdlib`Int`intOfNumMulThm]];   (* &ℤ(n·b) = intMul(&ℤn)(&ℤb) *)
      rightRw = TRANS[
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Int`intMulConst[], fstE], REFL[intOfNumTm[bTm]]],
        HOL`Equal`SYM[ofnMul]];
      (* intMul (FST(REP(&ℚ&ℤn))) (&ℤ b) = intMul (&ℤn)(&ℤb) = &ℤ(n·b) *)
      TRANS[unf, HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intLtC[], leftRw], rightRw]]
    ];

    (* bTm ≠ 0 from RAT_REP(REP q) *)
    bNeq0 = Module[{rrUnf, freeRR, rrAtQ, conds},
      rrUnf = HOL`Equal`APTHM[HOL`Stdlib`Rat`ratRepDefThm, repRatTm[qV]];
      freeRR = concl[HOL`Stdlib`Rat`ratRepRepThm][[2, 2]];   (* the free rat var q0 in RAT_REP(REP q0) *)
      rrAtQ = HOL`Kernel`INST[{freeRR -> qV}, HOL`Stdlib`Rat`ratRepRepThm];   (* RAT_REP(REP q) *)
      conds = EQMP[TRANS[rrUnf, BETACONV[concl[rrUnf][[2]]]], rrAtQ];   (* ¬(SND(REP q)=0) ∧ gcd…=SUC0 *)
      HOL`Bool`CONJUNCT1[conds]   (* ¬(SND(REP q) = 0) *)
    ];

    (* SUC 0 ≤ bTm *)
    lt0b = HOL`Bool`MP[HOL`Bool`SPEC[bTm, HOL`Stdlib`Num`ltZeroNotZeroThm], bNeq0];   (* 0 < b *)
    ltUnf = Module[{a1, a1b, a2},
      a1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, zeroN[]];
      a1b = TRANS[a1, BETACONV[concl[a1][[2]]]];
      a2 = HOL`Equal`APTHM[a1b, bTm];
      TRANS[a2, BETACONV[concl[a2][[2]]]]   (* (0 < b) = (SUC 0 ≤ b) *)
    ];
    suc0LeB = EQMP[ltUnf, lt0b];   (* SUC 0 ≤ b *)

    archA = HOL`Bool`SPEC[aTm, intArchThm];   (* ∃n. intLt aTm (&ℤ n) *)
    kV = mkVar["k", numTy];
    hArchK = ASSUME[intLtTmF[aTm, intOfNumTm[kV]]];   (* intLt aTm (&ℤ k) *)

    kbThm = HOL`Bool`MP[HOL`Bool`SPEC[bTm, HOL`Bool`SPEC[sucT[zeroN[]],
              HOL`Bool`SPEC[kV, HOL`Stdlib`Num`leqMultLeftThm]]], suc0LeB];   (* k·SUC0 ≤ k·b *)
    kSUC0 = concl[kbThm][[1, 2]];   (* k · SUC 0 *)
    kbTm = concl[kbThm][[2]];        (* k · b *)
    kSUC0eqK = TRANS[HOL`Bool`SPEC[sucT[zeroN[]], HOL`Bool`SPEC[kV, HOL`Stdlib`Num`timesCommThm]],
                 HOL`Bool`SPEC[kV, HOL`Stdlib`Num`oneTimesEqThm]];   (* k·SUC0 = SUC0·k = k *)
    kLeKb = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[leqC[], kSUC0eqK], REFL[kbTm]], kbThm];   (* k ≤ k·b *)
    kLeKbInt = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[kbTm, HOL`Bool`SPEC[kV, HOL`Stdlib`Int`intOfNumLeThm]]], kLeKb];
    (* intLe (&ℤ k) (&ℤ (k·b)) *)
    aLtKb = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[intOfNumTm[kbTm], HOL`Bool`SPEC[intOfNumTm[kV],
                HOL`Bool`SPEC[aTm, intLtLeTransThm]]], hArchK], kLeKbInt];   (* intLt aTm (&ℤ(k·b)) *)
    ratLtQk = EQMP[HOL`Equal`SYM[redEq[kV]], aLtKb];   (* ratLt q (&ℚ(&ℤ k)) *)
    ex = HOL`Bool`EXISTS[
      existsTm[kV, ratLtTm[qV, ratOfIntTm[intOfNumTm[kV]]]], kV, ratLtQk];
    HOL`Bool`GEN[qV, HOL`Bool`CHOOSE[kV, archA, ex]]
  ];

(* ============================================================ *)
(* ℚ multiplicative-order layer (for exists_nat_mul_gt).         *)
(* ============================================================ *)

ratMulC[] := HOL`Stdlib`Rat`ratMulConst[];
ratInvC[] := HOL`Stdlib`Rat`ratInvConst[];
ratMulTm[a_, b_] := mkComb[mkComb[ratMulC[], a], b];
ratInvTm[w_] := mkComb[ratInvC[], w];
oneQR[] := ratOfIntTm[intOfNumTm[sucT[zeroN[]]]];   (* &ℚ(&ℤ(SUC 0)) = 1 *)

(* ⊢ ∀w a b. ¬(w=0) ⇒ a·w = b·w ⇒ a = b *)
ratMulRightCancelThm =
  Module[{wV, aV, bV, hwne, heq, wInvW, aMulOne, bMulOne, st1, st2, st3, st4, st5, st6, aEqB},
    wV = mkVar["w", ratTy]; aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    hwne = ASSUME[notTm[mkEq[wV, zeroQ[]]]];
    heq = ASSUME[mkEq[ratMulTm[aV, wV], ratMulTm[bV, wV]]];
    wInvW = HOL`Bool`MP[HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulInvThm], hwne];   (* w·w⁻¹ = 1 *)
    aMulOne = HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratMulOneThm];   (* a·1 = a *)
    bMulOne = HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratMulOneThm];   (* b·1 = b *)
    st1 = HOL`Equal`SYM[aMulOne];   (* a = a·1 *)
    st2 = HOL`Equal`SYM[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], REFL[aV]], wInvW]];   (* a·1 = a·(w·w⁻¹) *)
    st3 = HOL`Equal`SYM[HOL`Bool`SPEC[ratInvTm[wV], HOL`Bool`SPEC[wV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratMulAssocThm]]]];
    (* a·(w·w⁻¹) = (a·w)·w⁻¹ *)
    st4 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], heq], REFL[ratInvTm[wV]]];   (* (a·w)·w⁻¹ = (b·w)·w⁻¹ *)
    st5 = HOL`Bool`SPEC[ratInvTm[wV], HOL`Bool`SPEC[wV, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratMulAssocThm]]];
    (* (b·w)·w⁻¹ = b·(w·w⁻¹) *)
    st6 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], REFL[bV]], wInvW];   (* b·(w·w⁻¹) = b·1 *)
    aEqB = TRANS[st1, TRANS[st2, TRANS[st3, TRANS[st4, TRANS[st5, TRANS[st6, bMulOne]]]]]];
    HOL`Bool`GEN[wV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[concl[hwne], HOL`Bool`DISCH[concl[heq], aEqB]]]]]
  ];

(* ⊢ ∀w a b. 0<w ⇒ a<b ⇒ ratLt (a·w)(b·w) *)
ratLtMulPosThm =
  Module[{wV, aV, bV, h0w, hab, notLeW0, le0w, wne0, awTm, bwTm, hLe, cases,
          ltCase, eqCase, falseFromCases, notLeBwAw, result},
    wV = mkVar["w", ratTy]; aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    h0w = ASSUME[ratLtTm[zeroQ[], wV]];   (* 0<w *)
    hab = ASSUME[ratLtTm[aV, bV]];        (* a<b *)
    notLeW0 = EQMP[HOL`Bool`SPEC[wV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratLtNotLeThm]], h0w];   (* ¬(ratLe w 0) *)
    le0w = HOL`Bool`DISJCASES[HOL`Bool`SPEC[wV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratLeTotalThm]],
             ASSUME[ratLeTm[zeroQ[], wV]],
             HOL`Bool`CONTR[ratLeTm[zeroQ[], wV],
               HOL`Bool`MP[HOL`Bool`NOTELIM[notLeW0], ASSUME[ratLeTm[wV, zeroQ[]]]]]];   (* ratLe 0 w *)
    wne0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[wV, zeroQ[]],
             HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[zeroQ[], ratLtIrreflThm]],
               EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[zeroQ[]]],
                 ASSUME[mkEq[wV, zeroQ[]]]], h0w]]]];   (* ¬(w=0) *)
    awTm = ratMulTm[aV, wV]; bwTm = ratMulTm[bV, wV];
    hLe = ASSUME[ratLeTm[bwTm, awTm]];   (* b·w ≤ a·w *)
    cases = HOL`Bool`MP[HOL`Bool`SPEC[awTm, HOL`Bool`SPEC[bwTm, ratLeCasesThm]], hLe];   (* b·w<a·w ∨ b·w=a·w *)
    ltCase = Module[{hlt, bLtA, aLtA},
      hlt = ASSUME[ratLtTm[bwTm, awTm]];
      bLtA = HOL`Bool`MP[HOL`Bool`MP[
               HOL`Bool`SPEC[wV, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratLtMulPosCancelThm]]],
               le0w], hlt];   (* b<a *)
      aLtA = HOL`Bool`MP[HOL`Bool`MP[
               HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, ratLtTransThm]]], hab], bLtA];   (* a<a *)
      HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[aV, ratLtIrreflThm]], aLtA]   (* F *)
    ];
    eqCase = Module[{heqc, aEqB, bLtB},
      heqc = ASSUME[mkEq[bwTm, awTm]];
      aEqB = HOL`Bool`MP[HOL`Bool`MP[
               HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[wV, ratMulRightCancelThm]]], wne0],
               HOL`Equal`SYM[heqc]];   (* a = b *)
      bLtB = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], aEqB], REFL[bV]], hab];   (* b<b *)
      HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[bV, ratLtIrreflThm]], bLtB]   (* F *)
    ];
    falseFromCases = HOL`Bool`DISJCASES[cases, ltCase, eqCase];
    notLeBwAw = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[concl[hLe], falseFromCases]];   (* ¬(b·w ≤ a·w) *)
    result = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[bwTm, HOL`Bool`SPEC[awTm, HOL`Stdlib`Rat`ratLtNotLeThm]]], notLeBwAw];
    (* ratLt (a·w)(b·w) *)
    HOL`Bool`GEN[wV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[concl[h0w], HOL`Bool`DISCH[concl[hab], result]]]]]
  ];

(* ⊢ ∀w r. 0<w ⇒ ∃n. ratLt r (ratMul (&ℚ(&ℤ n)) w) *)
ratNatMulGtThm =
  Module[{wV, rV, h0w, tTm, archT, nV, hArchN, wne0, twLtNw, assoc1, comm1,
          invW, twEqR, rLtNw, ex},
    wV = mkVar["w", ratTy]; rV = mkVar["r", ratTy];
    h0w = ASSUME[ratLtTm[zeroQ[], wV]];
    tTm = ratMulTm[rV, ratInvTm[wV]];   (* t = r·w⁻¹ = r/w *)
    archT = HOL`Bool`SPEC[tTm, ratArchThm];   (* ∃n. ratLt t (&ℚ&ℤn) *)
    nV = mkVar["n", numTy];
    hArchN = ASSUME[ratLtTm[tTm, ratOfIntTm[intOfNumTm[nV]]]];   (* ratLt t (&ℚ&ℤn) *)
    wne0 = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[wV, zeroQ[]],
             HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[zeroQ[], ratLtIrreflThm]],
               EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[zeroQ[]]],
                 ASSUME[mkEq[wV, zeroQ[]]]], h0w]]]];   (* ¬(w=0) *)
    twLtNw = HOL`Bool`MP[HOL`Bool`MP[
               HOL`Bool`SPEC[ratOfIntTm[intOfNumTm[nV]], HOL`Bool`SPEC[tTm,
                 HOL`Bool`SPEC[wV, ratLtMulPosThm]]], h0w], hArchN];   (* ratLt (t·w) ((&ℚ&ℤn)·w) *)
    (* t·w = r:  (r·w⁻¹)·w = r·(w⁻¹·w) = r·(w·w⁻¹) = r·1 = r *)
    assoc1 = HOL`Bool`SPEC[wV, HOL`Bool`SPEC[ratInvTm[wV], HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulAssocThm]]];
    (* (r·w⁻¹)·w = r·(w⁻¹·w) *)
    comm1 = HOL`Bool`SPEC[ratInvTm[wV], HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulCommThm]];   (* w·w⁻¹ = w⁻¹·w *)
    invW = HOL`Bool`MP[HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulInvThm], wne0];   (* w·w⁻¹ = 1 *)
    twEqR = TRANS[assoc1, TRANS[
              HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], REFL[rV]],
                TRANS[HOL`Equal`SYM[comm1], invW]],
              HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratMulOneThm]]];
    (* (r·w⁻¹)·w = r·(w⁻¹·w) = r·1 = r ; uses w⁻¹·w = w·w⁻¹ = 1 *)
    rLtNw = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], twEqR],
              REFL[ratMulTm[ratOfIntTm[intOfNumTm[nV]], wV]]], twLtNw];   (* ratLt r ((&ℚ&ℤn)·w) *)
    ex = HOL`Bool`EXISTS[
      existsTm[nV, ratLtTm[rV, ratMulTm[ratOfIntTm[intOfNumTm[nV]], wV]]], nV, rLtNw];
    HOL`Bool`GEN[wV, HOL`Bool`GEN[rV,
      HOL`Bool`DISCH[concl[h0w], HOL`Bool`CHOOSE[nV, archT, ex]]]]
  ];

(* natMulQ n w = (&ℚ(&ℤ n)) · w *)
natMulQ[nT_, wT_] := ratMulTm[ratOfIntTm[intOfNumTm[nT]], wT];

(* ⊢ ∀w. ratMul (&ℚ(&ℤ 0)) w = &ℚ(&ℤ 0) *)
ratNatZeroMulThm =
  Module[{wV},
    wV = mkVar["w", ratTy];
    HOL`Bool`GEN[wV, TRANS[
      HOL`Bool`SPEC[wV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratMulCommThm]],   (* 0·w = w·0 *)
      HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulZeroThm]]]   (* w·0 = 0 *)
  ];

(* ⊢ ∀w k. ratMul (&ℚ(&ℤ(SUC k))) w = ratAdd (ratMul (&ℚ(&ℤ k)) w) w *)
ratNatSucMulThm =
  Module[{wV, kV, sucKnatEq, sucZeq, distrib, commK, mulOneW, sucQeq, lhsCong, rhs},
    wV = mkVar["w", ratTy]; kV = mkVar["k", numTy];
    sucKnatEq = HOL`Equal`SYM[TRANS[
      HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[kV, HOL`Stdlib`Num`plusSucEqThm]],   (* k+SUC0 = SUC(k+0) *)
      HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], HOL`Bool`SPEC[kV, HOL`Stdlib`Num`plusZeroEqThm]]]];
    (* SUC k = k + SUC 0 *)
    sucZeq = TRANS[
      HOL`Equal`APTERM[intOfNumC[], sucKnatEq],   (* &ℤ(SUC k) = &ℤ(k+SUC0) *)
      HOL`Bool`SPEC[sucT[zeroN[]], HOL`Bool`SPEC[kV, HOL`Stdlib`Int`intOfNumAddThm]]];   (* &ℤ(k+SUC0) = intAdd(&ℤk)(&ℤSUC0) *)
    (* &ℤ(SUC k) = intAdd (&ℤ k) (&ℤ(SUC 0)) *)
    sucQeq = TRANS[
      HOL`Equal`APTERM[HOL`Stdlib`Rat`ratOfIntConst[], sucZeq],   (* &ℚ(&ℤ(SUC k)) = &ℚ(intAdd(&ℤk)(&ℤSUC0)) *)
      HOL`Bool`SPEC[intOfNumTm[sucT[zeroN[]]], HOL`Bool`SPEC[intOfNumTm[kV], HOL`Stdlib`Rat`ratOfIntAddThm]]];
    (* &ℚ(&ℤ(SUC k)) = ratAdd (&ℚ&ℤk) (&ℚ&ℤSUC0) = ratAdd (&ℚ&ℤk) 1 *)
    lhsCong = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratMulC[], sucQeq], REFL[wV]];
    (* ratMul (&ℚ&ℤ(SUC k)) w = ratMul (ratAdd(&ℚ&ℤk) 1) w *)
    commK = HOL`Bool`SPEC[ratAddTm[ratOfIntTm[intOfNumTm[kV]], oneQR[]],
              HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulCommThm]];
    (* ratMul (ratAdd(&ℚ&ℤk) 1) w  ... actually ratMulComm w (..) : w·(..) = (..)·w ; want (..)·w = w·(..), SYM *)
    distrib = HOL`Bool`SPEC[oneQR[], HOL`Bool`SPEC[ratOfIntTm[intOfNumTm[kV]],
                HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulDistribThm]]];
    (* w·(&ℚ&ℤk + 1) = (w·&ℚ&ℤk) + (w·1) *)
    mulOneW = HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulOneThm];   (* w·1 = w *)
    rhs = TRANS[HOL`Equal`SYM[commK],
            TRANS[distrib,
              HOL`Kernel`MKCOMB[
                HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
                  HOL`Bool`SPEC[ratOfIntTm[intOfNumTm[kV]], HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratMulCommThm]]],
                mulOneW]]];
    (* ratMul (ratAdd(&ℚ&ℤk) 1) w = w·(&ℚ&ℤk+1) = (w·&ℚ&ℤk)+(w·1) = (&ℚ&ℤk·w) + w *)
    HOL`Bool`GEN[wV, HOL`Bool`GEN[kV, TRANS[lhsCong, rhs]]]
  ];

(* ============================================================ *)
(* Additive ℚ algebra (cancellation / negation / subtraction).   *)
(* Pure ℚ — moved here from Field.wl 2026-06-07 with the rest of  *)
(* the rat* vocabulary; consumed by realAdd/realNeg/realAddNeg.   *)
(* ============================================================ *)

(* ⊢ ∀a b. ratAdd (ratAdd a b) (ratNeg a) = b   ((a+b)−a = b) *)
ratAddSubCancelLeftThm =
  Module[{aV, bV, commEq, cong, subCancel},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    commEq = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddCommThm]];   (* a+b = b+a *)
    cong = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], commEq],
             REFL[ratNegTm[aV]]];   (* (a+b)−a = (b+a)−a *)
    subCancel = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratAddSubCancelThm]];   (* (b+a)−a = b *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, TRANS[cong, subCancel]]]
  ];

ratSubTm[rT_, sT_] := ratAddTm[rT, ratNegTm[sT]];   (* r − s *)

(* ⊢ ∀a b. ratAdd a (ratAdd b (ratNeg a)) = b   (a+(b−a) = b) *)
ratAddSubLeftThm =
  Module[{aV, bV, innerComm, cong1, assocBack, negEq, cong2, zeroComm, zeroEq, lhs},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    innerComm = HOL`Bool`SPEC[ratNegTm[aV], HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratAddCommThm]];   (* b+(−a) = (−a)+b *)
    cong1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[aV]], innerComm];
    (* a+(b+(−a)) = a+((−a)+b) *)
    assocBack = HOL`Equal`SYM[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[ratNegTm[aV],
                  HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddAssocThm]]]];
    (* a+((−a)+b) = (a+(−a))+b *)
    negEq = HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddNegThm];   (* a+(−a) = 0 *)
    cong2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], negEq], REFL[bV]];
    (* (a+(−a))+b = 0+b *)
    zeroComm = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]];   (* 0+b = b+0 *)
    zeroEq = HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratAddZeroThm];   (* b+0 = b *)
    lhs = TRANS[cong1, TRANS[assocBack, TRANS[cong2, TRANS[zeroComm, zeroEq]]]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, lhs]]
  ];

(* ⊢ ∀r s. ratAdd (ratAdd r (ratNeg s)) s = r   ((r−s)+s = r) *)
ratSubAddThm =
  Module[{rV, sV, assocFwd, innerComm, negEq, cong1, cong2, zeroEq},
    rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy];
    assocFwd = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[ratNegTm[sV], HOL`Bool`SPEC[rV,
                 HOL`Stdlib`Rat`ratAddAssocThm]]];   (* (r+(−s))+s = r+((−s)+s) *)
    innerComm = HOL`Bool`SPEC[sV, HOL`Bool`SPEC[ratNegTm[sV], HOL`Stdlib`Rat`ratAddCommThm]];   (* (−s)+s = s+(−s) *)
    negEq = HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratAddNegThm];   (* s+(−s) = 0 *)
    cong1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[rV]], innerComm];
    (* r+((−s)+s) = r+(s+(−s)) *)
    cong2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[rV]], negEq];
    (* r+(s+(−s)) = r+0 *)
    zeroEq = HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratAddZeroThm];   (* r+0 = r *)
    HOL`Bool`GEN[rV, HOL`Bool`GEN[sV,
      TRANS[assocFwd, TRANS[cong1, TRANS[cong2, zeroEq]]]]]
  ];

(* ⊢ ∀r s. ratAdd r (ratNeg (ratAdd r (ratNeg s))) = s   (r−(r−s) = s) *)
ratSubSubThm =
  Module[{rV, sV, sp, eq1, congStep, cancelStep},
    rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy];
    sp = ratSubTm[rV, sV];   (* r − s *)
    eq1 = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[sV, ratAddSubLeftThm]];   (* s + (r−s) = r *)
    congStep = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], HOL`Equal`SYM[eq1]], REFL[ratNegTm[sp]]];
    (* r + (−(r−s)) = (s+(r−s)) + (−(r−s)) *)
    cancelStep = HOL`Bool`SPEC[sp, HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratAddSubCancelThm]];
    (* (s+(r−s)) + (−(r−s)) = s *)
    HOL`Bool`GEN[rV, HOL`Bool`GEN[sV, TRANS[congStep, cancelStep]]]
  ];

(* ⊢ ∀a b c. ratAdd a c = ratAdd b c ⇒ a = b *)
ratAddRightCancelThm =
  Module[{aV, bV, cV, hyp, apEq, cancA, cancB, aEqB},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy]; cV = mkVar["c", ratTy];
    hyp = ASSUME[mkEq[ratAddTm[aV, cV], ratAddTm[bV, cV]]];
    apEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], hyp], REFL[ratNegTm[cV]]];
    (* (a+c)+(−c) = (b+c)+(−c) *)
    cancA = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddSubCancelThm]];   (* (a+c)+(−c) = a *)
    cancB = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratAddSubCancelThm]];   (* (b+c)+(−c) = b *)
    aEqB = TRANS[TRANS[HOL`Equal`SYM[cancA], apEq], cancB];   (* a = b *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[concl[hyp], aEqB]]]]
  ];

(* ⊢ ∀r s t. (r−t)−(s−t) = r−s   (private helper for assoc fwd) *)
ratSubSubDistThm =
  Module[{rV, sV, tV, sMt, rMt, rMs, xPlus, assocStep, subAddCong, yPlus, bothEq},
    rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy]; tV = mkVar["t", ratTy];
    sMt = ratSubTm[sV, tV]; rMt = ratSubTm[rV, tV]; rMs = ratSubTm[rV, sV];
    xPlus = HOL`Bool`SPEC[sMt, HOL`Bool`SPEC[rMt, ratSubAddThm]];   (* ((r−t)−(s−t))+(s−t) = r−t *)
    assocStep = HOL`Equal`SYM[HOL`Bool`SPEC[ratNegTm[tV], HOL`Bool`SPEC[sV,
                  HOL`Bool`SPEC[rMs, HOL`Stdlib`Rat`ratAddAssocThm]]]];
    (* (r−s)+(s+(−t)) = ((r−s)+s)+(−t) *)
    subAddCong = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
                   HOL`Bool`SPEC[sV, HOL`Bool`SPEC[rV, ratSubAddThm]]], REFL[ratNegTm[tV]]];
    (* ((r−s)+s)+(−t) = r+(−t) *)
    yPlus = TRANS[assocStep, subAddCong];   (* (r−s)+(s−t) = r−t *)
    bothEq = TRANS[xPlus, HOL`Equal`SYM[yPlus]];   (* ((r−t)−(s−t))+(s−t) = (r−s)+(s−t) *)
    HOL`Bool`GEN[rV, HOL`Bool`GEN[sV, HOL`Bool`GEN[tV,
      HOL`Bool`MP[HOL`Bool`SPEC[sMt, HOL`Bool`SPEC[rMs,
        HOL`Bool`SPEC[ratSubTm[rMt, sMt], ratAddRightCancelThm]]], bothEq]]]]
  ];

(* ⊢ ∀r a b. r−(a+b) = (r−a)−b   (private helper for assoc bwd) *)
ratSubAddDistThm =
  Module[{rV, aV, bV, aPb, rMa, xPlus, commStep, assocStep, subBcong, subAddA, yPlus, bothEq},
    rV = mkVar["r", ratTy]; aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    aPb = ratAddTm[aV, bV]; rMa = ratSubTm[rV, aV];
    xPlus = HOL`Bool`SPEC[aPb, HOL`Bool`SPEC[rV, ratSubAddThm]];   (* (r−(a+b))+(a+b) = r *)
    commStep = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[ratSubTm[rMa, bV]]],
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddCommThm]]];
    (* ((r−a)−b)+(a+b) = ((r−a)−b)+(b+a) *)
    assocStep = HOL`Equal`SYM[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV,
                  HOL`Bool`SPEC[ratSubTm[rMa, bV], HOL`Stdlib`Rat`ratAddAssocThm]]]];
    (* ((r−a)−b)+(b+a) = (((r−a)−b)+b)+a *)
    subBcong = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
                 HOL`Bool`SPEC[bV, HOL`Bool`SPEC[rMa, ratSubAddThm]]], REFL[aV]];
    (* (((r−a)−b)+b)+a = (r−a)+a *)
    subAddA = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[rV, ratSubAddThm]];   (* (r−a)+a = r *)
    yPlus = TRANS[commStep, TRANS[assocStep, TRANS[subBcong, subAddA]]];   (* ((r−a)−b)+(a+b) = r *)
    bothEq = TRANS[xPlus, HOL`Equal`SYM[yPlus]];   (* (r−(a+b))+(a+b) = ((r−a)−b)+(a+b) *)
    HOL`Bool`GEN[rV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`MP[HOL`Bool`SPEC[aPb, HOL`Bool`SPEC[ratSubTm[rMa, bV],
        HOL`Bool`SPEC[ratSubTm[rV, aPb], ratAddRightCancelThm]]], bothEq]]]]
  ];

(* ⊢ ∀q. ratNeg (ratNeg q) = q *)
ratNegNegThm =
  Module[{qV, nq, nnq, e1, commEq, lhsZero, e2, bothEq},
    qV = mkVar["q", ratTy]; nq = ratNegTm[qV]; nnq = ratNegTm[nq];
    e1 = HOL`Bool`SPEC[nq, HOL`Stdlib`Rat`ratAddNegThm];   (* (−q)+(−(−q)) = 0 *)
    commEq = HOL`Bool`SPEC[nq, HOL`Bool`SPEC[nnq, HOL`Stdlib`Rat`ratAddCommThm]];   (* (−(−q))+(−q) = (−q)+(−(−q)) *)
    lhsZero = TRANS[commEq, e1];   (* (−(−q))+(−q) = 0 *)
    e2 = HOL`Bool`SPEC[qV, HOL`Stdlib`Rat`ratAddNegThm];   (* q+(−q) = 0 *)
    bothEq = TRANS[lhsZero, HOL`Equal`SYM[e2]];   (* (−(−q))+(−q) = q+(−q) *)
    HOL`Bool`GEN[qV,
      HOL`Bool`MP[HOL`Bool`SPEC[nq, HOL`Bool`SPEC[qV, HOL`Bool`SPEC[nnq, ratAddRightCancelThm]]], bothEq]]
  ];

(* ⊢ ∀a x y. ratAdd a x = ratAdd a y ⇒ x = y *)
ratAddLeftCancelThm =
  Module[{aV, xV, yV, hyp, commX, commY, xaEQya},
    aV = mkVar["a", ratTy]; xV = mkVar["x", ratTy]; yV = mkVar["y", ratTy];
    hyp = ASSUME[mkEq[ratAddTm[aV, xV], ratAddTm[aV, yV]]];
    commX = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[xV, HOL`Stdlib`Rat`ratAddCommThm]];   (* x+a = a+x *)
    commY = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[yV, HOL`Stdlib`Rat`ratAddCommThm]];   (* y+a = a+y *)
    xaEQya = TRANS[TRANS[commX, hyp], HOL`Equal`SYM[commY]];   (* x+a = y+a *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[concl[hyp],
        HOL`Bool`MP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, ratAddRightCancelThm]]], xaEQya]]]]]
  ];

(* ⊢ ∀a b. ratNeg (ratAdd a b) = ratAdd (ratNeg a) (ratNeg b) *)
ratNegAddThm =
  Module[{aV, bV, na, nb, aPb, s1, s2, s3, s4, s5, eClean, rn, bothEq, negBA, commBA},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    na = ratNegTm[aV]; nb = ratNegTm[bV]; aPb = ratAddTm[aV, bV];
    (* eClean: (a+b) + ((−b)+(−a)) = 0 *)
    s1 = HOL`Bool`SPEC[ratAddTm[nb, na], HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddAssocThm]]];
    (* (a+b)+((−b)+(−a)) = a+(b+((−b)+(−a))) *)
    s2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[aV]],
           HOL`Equal`SYM[HOL`Bool`SPEC[na, HOL`Bool`SPEC[nb, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratAddAssocThm]]]]];
    (* a+(b+((−b)+(−a))) = a+((b+(−b))+(−a)) *)
    s3 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[aV]],
           HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
             HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratAddNegThm]], REFL[na]]];
    (* a+((b+(−b))+(−a)) = a+(0+(−a)) *)
    s4 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[aV]],
           TRANS[HOL`Bool`SPEC[na, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
             HOL`Bool`SPEC[na, HOL`Stdlib`Rat`ratAddZeroThm]]];
    (* a+(0+(−a)) = a+(−a) *)
    s5 = HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddNegThm];   (* a+(−a) = 0 *)
    eClean = TRANS[s1, TRANS[s2, TRANS[s3, TRANS[s4, s5]]]];   (* (a+b)+((−b)+(−a)) = 0 *)
    rn = HOL`Bool`SPEC[aPb, HOL`Stdlib`Rat`ratAddNegThm];   (* (a+b)+(−(a+b)) = 0 *)
    bothEq = TRANS[rn, HOL`Equal`SYM[eClean]];   (* (a+b)+(−(a+b)) = (a+b)+((−b)+(−a)) *)
    negBA = HOL`Bool`MP[HOL`Bool`SPEC[ratAddTm[nb, na], HOL`Bool`SPEC[ratNegTm[aPb],
              HOL`Bool`SPEC[aPb, ratAddLeftCancelThm]]], bothEq];   (* −(a+b) = (−b)+(−a) *)
    commBA = HOL`Bool`SPEC[na, HOL`Bool`SPEC[nb, HOL`Stdlib`Rat`ratAddCommThm]];   (* (−b)+(−a) = (−a)+(−b) *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, TRANS[negBA, commBA]]]
  ];

(* ⊢ ∀v r. ratLt 0 r ⇒ ratLt (v−r) v *)
ratSubLtSelfThm =
  Module[{vV, rV, hyp, monoNeg, lhsE, rhsE, negRLt0, mono2, lhsE2, rhsE2, result},
    vV = mkVar["v", ratTy]; rV = mkVar["r", ratTy];
    hyp = ASSUME[ratLtTm[zeroQ[], rV]];   (* 0<r *)
    monoNeg = HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[rV], HOL`Bool`SPEC[rV,
                HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratLtAddMonoThm]]], hyp];   (* 0+(−r) < r+(−r) *)
    lhsE = TRANS[HOL`Bool`SPEC[ratNegTm[rV], HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
             HOL`Bool`SPEC[ratNegTm[rV], HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+(−r) = −r *)
    rhsE = HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratAddNegThm];   (* r+(−r) = 0 *)
    negRLt0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsE], rhsE], monoNeg];   (* −r < 0 *)
    mono2 = HOL`Bool`MP[HOL`Bool`SPEC[vV, HOL`Bool`SPEC[zeroQ[],
              HOL`Bool`SPEC[ratNegTm[rV], HOL`Stdlib`Rat`ratLtAddMonoThm]]], negRLt0];   (* (−r)+v < 0+v *)
    lhsE2 = HOL`Bool`SPEC[vV, HOL`Bool`SPEC[ratNegTm[rV], HOL`Stdlib`Rat`ratAddCommThm]];   (* (−r)+v = v+(−r) *)
    rhsE2 = TRANS[HOL`Bool`SPEC[vV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
              HOL`Bool`SPEC[vV, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+v = v *)
    result = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsE2], rhsE2], mono2];   (* v+(−r) < v *)
    HOL`Bool`GEN[vV, HOL`Bool`GEN[rV, HOL`Bool`DISCH[concl[hyp], result]]]
  ];

(* ⊢ ∀a b. ratLt a b ⇒ ratLt 0 (b−a) *)
ratLtSubPosThm =
  Module[{aV, bV, hyp, mono, lhsE, result},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    hyp = ASSUME[ratLtTm[aV, bV]];   (* a<b *)
    mono = HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[aV], HOL`Bool`SPEC[bV,
             HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLtAddMonoThm]]], hyp];   (* a+(−a) < b+(−a) *)
    lhsE = HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddNegThm];   (* a+(−a) = 0 *)
    result = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsE], REFL[ratSubTm[bV, aV]]], mono];   (* 0 < b−a *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[concl[hyp], result]]]
  ];

(* ⊢ ∀a. ratLt a 0 ⇒ ratLt 0 (ratNeg a) *)
ratNegPosThm =
  Module[{aV, ha, mono, lhsE, rhsE},
    aV = mkVar["a", ratTy];
    ha = ASSUME[ratLtTm[aV, zeroQ[]]];
    mono = HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[aV], HOL`Bool`SPEC[zeroQ[],
             HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLtAddMonoThm]]], ha];   (* a+(−a) < 0+(−a) *)
    lhsE = HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratAddNegThm];   (* a+(−a) = 0 *)
    rhsE = TRANS[HOL`Bool`SPEC[ratNegTm[aV], HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
             HOL`Bool`SPEC[ratNegTm[aV], HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+(−a) = −a *)
    HOL`Bool`GEN[aV, HOL`Bool`DISCH[concl[ha],
      EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsE], rhsE], mono]]]
  ];

End[];

EndPackage[];
