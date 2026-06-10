(* M7-7 / stdlib/Real/Complete.wl — Dedekind completeness + Archimedean + ℚ-density.

   Part of the stdlib/Real/ folder (PLAN §8.1): shares the package context
   HOL`Stdlib`Real` with Cut.wl/Field.wl/Mul.wl/Inv.wl, so the private
   term-builder / unfold vocabulary (forallTm, existsTm, ratLtTm, repApp,
   repRealTm, unfoldRealLe, unfoldIsCut, realOfRatTm, realLtTm, …) is reused
   here for free.

   Contents:
   - strict-order vocabulary: realLtImpLe / realLtLeTrans / realLeLtTrans /
     realLtTrans + the strict-order embedding realOfRatLt;
   - realSup: the least upper bound of a nonempty bounded-above set of
     reals, as the UNION of the member lower sets (Lean blueprint
     ../archive/tautology Cut/Sup.lean) — supCutIsCut, rep/mem, upper
     bound, least upper bound, and the packaged dedekindCompleteThm;
   - realRatBound (every real sits strictly below some rational),
     realArch (ℕ-form Archimedean property), realDense (ℚ dense in ℝ). *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

realLtImpLeThm::usage = "realLtImpLeThm — ⊢ ∀x y. realLt x y ⇒ realLe x y. Strict implies non-strict (via totality).";
realLtLeTransThm::usage = "realLtLeTransThm — ⊢ ∀x y z. realLt x y ⇒ realLe y z ⇒ realLt x z.";
realLeLtTransThm::usage = "realLeLtTransThm — ⊢ ∀x y z. realLe x y ⇒ realLt y z ⇒ realLt x z.";
realLtTransThm::usage = "realLtTransThm — ⊢ ∀x y z. realLt x y ⇒ realLt y z ⇒ realLt x z. Strict order is transitive.";
realOfRatLtThm::usage = "realOfRatLtThm — ⊢ ∀a b. realLt (&ℝ a) (&ℝ b) = ratLt a b. &ℝ is a strict-order embedding.";

realSupConst::usage = "realSupConst[] — realSup : (real → bool) → real, the supremum of a set of reals: realSup S = ABS_real (λq. ∃a. S a ∧ REP_real a q), the union of the member lower sets. Semantics only contracted when S is nonempty and bounded above.";
realSupDefThm::usage = "realSupDefThm — ⊢ realSup = (λS. ABS_real (λq. ∃a. S a ∧ REP_real a q)).";
supCutIsCutThm::usage = "supCutIsCutThm — ⊢ ∀S. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ IS_CUT (λq. ∃a. S a ∧ REP_real a q). The union of the lower sets of a nonempty bounded-above set is a cut.";
repRealSupThm::usage = "repRealSupThm — ⊢ ∀S. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ REP_real (realSup S) = (λq. ∃a. S a ∧ REP_real a q).";
realSupMemThm::usage = "realSupMemThm — ⊢ ∀S. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ ∀q. REP_real (realSup S) q = (∃a. S a ∧ REP_real a q). Membership in the sup cut is membership in some member's cut.";
realSupUpperThm::usage = "realSupUpperThm — ⊢ ∀S. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ ∀a. S a ⇒ realLe a (realSup S). realSup S is an upper bound.";
realSupLeastThm::usage = "realSupLeastThm — ⊢ ∀S v. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ (∀a. S a ⇒ realLe a v) ⇒ realLe (realSup S) v. realSup S is below every upper bound.";
dedekindCompleteThm::usage = "dedekindCompleteThm — ⊢ ∀S. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ (∀a. S a ⇒ realLe a (realSup S)) ∧ (∀v. (∀a. S a ⇒ realLe a v) ⇒ realLe (realSup S) v). ℝ is Dedekind-complete: every nonempty bounded-above set has a least upper bound.";

realRatBoundThm::usage = "realRatBoundThm — ⊢ ∀x. ∃q. realLt x (&ℝ q). Every real sits strictly below some rational.";
realArchThm::usage = "realArchThm — ⊢ ∀x. ∃n:num. realLt x (&ℝ (&ℚ (&ℤ n))). ℝ is Archimedean: every real is below some natural.";
realDenseThm::usage = "realDenseThm — ⊢ ∀x y. realLt x y ⇒ ∃q. realLt x (&ℝ q) ∧ realLt (&ℝ q) y. ℚ is dense in ℝ.";

Begin["`Private`"];

(* ============================================================ *)
(* Complete.wl vocabulary (on top of the folder-shared builders).*)
(* ============================================================ *)

setTy = tyFun[realTy, boolTy];          (* S : real → bool *)
supTy = tyFun[setTy, realTy];

(* the sup lower set: λq. ∃a. S a ∧ REP_real a q *)
supLTm[Stm_] :=
  Module[{qB, aB},
    qB = mkVar["q", ratTy]; aB = mkVar["a", realTy];
    mkAbs[qB, existsTm[aB, conjTm[mkComb[Stm, aB], repApp[aB, qB]]]]];

(* the two side conditions, with the final-statement canonical binders *)
hneTmOf[Stm_] :=
  Module[{aB}, aB = mkVar["a", realTy]; existsTm[aB, mkComb[Stm, aB]]];

hbndTmOf[Stm_] :=
  Module[{aB, uB},
    aB = mkVar["a", realTy]; uB = mkVar["u", realTy];
    existsTm[uB, forallTm[aB, impTm[mkComb[Stm, aB], realLeTm[aB, uB]]]]];

(* kernel-computed instance of an ∃-body at witness w — the exact term
   CHOOSE expects as the discharged hypothesis (extract, don't rebuild) *)
chooseBody[exTm_, w_] := concl[BETACONV[mkComb[exTm[[2]], w]]][[2]];

(* ⊢ realLt a b = ¬ (realLe b a)  (instantiated) *)
ltNotLeAt[a_, b_] := HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, realLtNotLeThm]];

(* ============================================================ *)
(* realLtImpLeThm — ⊢ ∀x y. realLt x y ⇒ realLe x y.             *)
(*   realLt x y = ¬(realLe y x); totality then forces realLe x y.*)
(* ============================================================ *)

realLtImpLeThm =
  Module[{xV, yV, hLt, notLeYX, tot, leXY},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    hLt = ASSUME[realLtTm[xV, yV]];
    notLeYX = EQMP[ltNotLeAt[xV, yV], hLt];        (* ¬(realLe y x) *)
    tot = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realLeTotalThm]];   (* realLe x y ∨ realLe y x *)
    leXY = HOL`Bool`DISJCASES[tot,
      ASSUME[realLeTm[xV, yV]],
      HOL`Bool`CONTR[realLeTm[xV, yV],
        HOL`Bool`MP[HOL`Bool`NOTELIM[notLeYX], ASSUME[realLeTm[yV, xV]]]]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[realLtTm[xV, yV], leXY]]]
  ];

(* ============================================================ *)
(* realLtLeTransThm — ⊢ ∀x y z. realLt x y ⇒ realLe y z ⇒ realLt x z. *)
(*   Suppose realLe z x; with realLe y z get realLe y x,          *)
(*   contradicting realLt x y.                                    *)
(* ============================================================ *)

realLtLeTransThm =
  Module[{xV, yV, zV, hLt, hLe, notLeYX, hZX, leYX, ff, notLeZX},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hLt = ASSUME[realLtTm[xV, yV]];
    hLe = ASSUME[realLeTm[yV, zV]];
    notLeYX = EQMP[ltNotLeAt[xV, yV], hLt];        (* ¬(realLe y x) *)
    hZX = ASSUME[realLeTm[zV, xV]];
    leYX = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[xV, HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realLeTransThm]]],
      hLe], hZX];                                   (* realLe y x *)
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeYX], leYX];
    notLeZX = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[zV, xV], ff]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[realLtTm[xV, yV], HOL`Bool`DISCH[realLeTm[yV, zV],
        EQMP[HOL`Equal`SYM[ltNotLeAt[xV, zV]], notLeZX]]]]]]
  ];

(* ============================================================ *)
(* realLeLtTransThm — ⊢ ∀x y z. realLe x y ⇒ realLt y z ⇒ realLt x z. *)
(* ============================================================ *)

realLeLtTransThm =
  Module[{xV, yV, zV, hLe, hLt, notLeZY, hZX, leZY, ff, notLeZX},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hLe = ASSUME[realLeTm[xV, yV]];
    hLt = ASSUME[realLtTm[yV, zV]];
    notLeZY = EQMP[ltNotLeAt[yV, zV], hLt];        (* ¬(realLe z y) *)
    hZX = ASSUME[realLeTm[zV, xV]];
    leZY = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[zV, realLeTransThm]]],
      hZX], hLe];                                   (* realLe z y *)
    ff = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeZY], leZY];
    notLeZX = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[zV, xV], ff]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[realLeTm[xV, yV], HOL`Bool`DISCH[realLtTm[yV, zV],
        EQMP[HOL`Equal`SYM[ltNotLeAt[xV, zV]], notLeZX]]]]]]
  ];

(* ============================================================ *)
(* realLtTransThm — ⊢ ∀x y z. realLt x y ⇒ realLt y z ⇒ realLt x z. *)
(* ============================================================ *)

realLtTransThm =
  Module[{xV, yV, zV, hLt1, hLt2, leYZ, ltXZ},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    hLt1 = ASSUME[realLtTm[xV, yV]];
    hLt2 = ASSUME[realLtTm[yV, zV]];
    leYZ = HOL`Bool`MP[HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realLtImpLeThm]], hLt2];
    ltXZ = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realLtLeTransThm]]],
      hLt1], leYZ];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      HOL`Bool`DISCH[realLtTm[xV, yV], HOL`Bool`DISCH[realLtTm[yV, zV], ltXZ]]]]]
  ];

(* ============================================================ *)
(* realOfRatLtThm — ⊢ ∀a b. realLt (&ℝ a) (&ℝ b) = ratLt a b.    *)
(*   Chain through ¬(realLe (&ℝ b)(&ℝ a)) = ¬(ratLe b a).         *)
(* ============================================================ *)

realOfRatLtThm =
  Module[{aV, bV, lhs, mid, rat},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    lhs = ltNotLeAt[realOfRatTm[aV], realOfRatTm[bV]];
    mid = HOL`Equal`APTERM[notC[],
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, realOfRatLeThm]]];   (* ¬(realLe (&ℝb)(&ℝa)) = ¬(ratLe b a) *)
    rat = HOL`Equal`SYM[
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLtNotLeThm]]];   (* ¬(ratLe b a) = ratLt a b *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, TRANS[TRANS[lhs, mid], rat]]]
  ];

(* ============================================================ *)
(* realSup — definition + unfold.                                *)
(* ============================================================ *)

realSupDefThm =
  Module[{SV},
    SV = mkVar["S", setTy];
    newDefinition[mkEq[mkVar["realSup", supTy],
      mkAbs[SV, mkComb[absRealConst[], supLTm[SV]]]]]];

realSupConst[] := mkConst["realSup", supTy];
realSupTm[Stm_] := mkComb[realSupConst[], Stm];

(* ⊢ realSup S = ABS_real (λq. ∃a. S a ∧ REP_real a q) *)
unfoldRealSup[Stm_] :=
  Module[{ap}, ap = HOL`Equal`APTHM[realSupDefThm, Stm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]];

(* ============================================================ *)
(* supCutIsCutThm — the union of the lower sets of a nonempty     *)
(* bounded-above set is a cut (Lean: Cut/Sup.lean sup).           *)
(*   c1 nonempty: a member's member.                              *)
(*   c2 proper:   a point outside the bound's cut.                *)
(*   c3 down-closed / c4 open: inherited from the chosen member.  *)
(* ============================================================ *)

supCutIsCutThm =
  Module[{SV, supL, betaAt, cutUnfold, rhsConj, c1Tm, rest1, c2Tm, rest2,
          c3Tm, c4Tm, hneTm, hbndTm, hne, hbnd,
          aN, qN, hSaN, neA, hRepN, exN, memQN, c1Body, c1Thm,
          uW, bW, aP, hUB, prU, hNotRepU, hSup, exMem, hPairP, leAPU,
          repUb, ffP, ffCh, notSup, c2Body, c2Thm,
          qD, rD, aD, hSupQ, hLtRQ, exQ, hPairD, repADr, exR, memR,
          memRCh, c3Thm,
          qO, aO, rO, hSupO, exO, hPairO, openA, hPairR, exRO, memRO,
          conjFin, c4At, exTarget, exFin, exFinCh2, c4Thm,
          conjAll, isCutSup},
    SV = mkVar["S", setTy];
    supL = supLTm[SV];
    betaAt[t_] := BETACONV[mkComb[supL, t]];        (* ⊢ supL t = ∃a. S a ∧ REP a t *)
    cutUnfold = unfoldIsCut[supL];
    rhsConj = concl[cutUnfold][[2]];
    c1Tm = rhsConj[[1, 2]]; rest1 = rhsConj[[2]];
    c2Tm = rest1[[1, 2]];   rest2 = rest1[[2]];
    c3Tm = rest2[[1, 2]];   c4Tm = rest2[[2]];
    hneTm = hneTmOf[SV]; hbndTm = hbndTmOf[SV];
    hne = ASSUME[hneTm]; hbnd = ASSUME[hbndTm];

    (* --- c1: ∃q. supL q --- *)
    aN = mkVar["aN", realTy]; qN = mkVar["qN", ratTy];
    hSaN = ASSUME[chooseBody[hneTm, aN]];           (* S aN *)
    neA = HOL`Bool`SPEC[aN, realNonemptyThm];       (* ∃q. REP aN q *)
    hRepN = ASSUME[chooseBody[concl[neA], qN]];     (* REP aN qN *)
    exN = HOL`Bool`EXISTS[concl[betaAt[qN]][[2]], aN, HOL`Bool`CONJ[hSaN, hRepN]];
    memQN = EQMP[HOL`Equal`SYM[betaAt[qN]], exN];   (* supL qN *)
    c1Body = HOL`Bool`EXISTS[c1Tm, qN, memQN];
    c1Thm = HOL`Bool`CHOOSE[aN, hne, HOL`Bool`CHOOSE[qN, neA, c1Body]];

    (* --- c2: ∃q. ¬ supL q --- *)
    uW = mkVar["uW", realTy]; bW = mkVar["bW", ratTy]; aP = mkVar["aP", realTy];
    hUB = ASSUME[chooseBody[hbndTm, uW]];           (* ∀a. S a ⇒ realLe a uW *)
    prU = HOL`Bool`SPEC[uW, realProperThm];         (* ∃q. ¬ REP uW q *)
    hNotRepU = ASSUME[chooseBody[concl[prU], bW]];  (* ¬ REP uW bW *)
    hSup = ASSUME[mkComb[supL, bW]];
    exMem = EQMP[betaAt[bW], hSup];                 (* ∃a. S a ∧ REP a bW *)
    hPairP = ASSUME[chooseBody[concl[exMem], aP]];  (* S aP ∧ REP aP bW *)
    leAPU = HOL`Bool`MP[HOL`Bool`SPEC[aP, hUB], HOL`Bool`CONJUNCT1[hPairP]];
    repUb = HOL`Bool`MP[
      HOL`Bool`SPEC[bW, EQMP[unfoldRealLe[aP, uW], leAPU]],
      HOL`Bool`CONJUNCT2[hPairP]];                  (* REP uW bW *)
    ffP = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotRepU], repUb];
    ffCh = HOL`Bool`CHOOSE[aP, exMem, ffP];
    notSup = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkComb[supL, bW], ffCh]];
    c2Body = HOL`Bool`EXISTS[c2Tm, bW, notSup];
    c2Thm = HOL`Bool`CHOOSE[uW, hbnd, HOL`Bool`CHOOSE[bW, prU, c2Body]];

    (* --- c3: down-closed --- *)
    qD = mkVar["qD", ratTy]; rD = mkVar["rD", ratTy]; aD = mkVar["aD", realTy];
    hSupQ = ASSUME[mkComb[supL, qD]];
    hLtRQ = ASSUME[ratLtTm[rD, qD]];
    exQ = EQMP[betaAt[qD], hSupQ];                  (* ∃a. S a ∧ REP a qD *)
    hPairD = ASSUME[chooseBody[concl[exQ], aD]];    (* S aD ∧ REP aD qD *)
    repADr = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[rD, HOL`Bool`SPEC[qD, HOL`Bool`SPEC[aD, realDownClosedThm]]],
      HOL`Bool`CONJUNCT2[hPairD]], hLtRQ];          (* REP aD rD *)
    exR = HOL`Bool`EXISTS[concl[betaAt[rD]][[2]], aD,
      HOL`Bool`CONJ[HOL`Bool`CONJUNCT1[hPairD], repADr]];
    memR = EQMP[HOL`Equal`SYM[betaAt[rD]], exR];    (* supL rD *)
    memRCh = HOL`Bool`CHOOSE[aD, exQ, memR];
    c3Thm = HOL`Bool`GEN[qD, HOL`Bool`GEN[rD,
      HOL`Bool`DISCH[mkComb[supL, qD], HOL`Bool`DISCH[ratLtTm[rD, qD], memRCh]]]];

    (* --- c4: open --- *)
    qO = mkVar["qO", ratTy]; aO = mkVar["aO", realTy]; rO = mkVar["rO", ratTy];
    hSupO = ASSUME[mkComb[supL, qO]];
    exO = EQMP[betaAt[qO], hSupO];                  (* ∃a. S a ∧ REP a qO *)
    hPairO = ASSUME[chooseBody[concl[exO], aO]];    (* S aO ∧ REP aO qO *)
    openA = HOL`Bool`MP[HOL`Bool`SPEC[qO, HOL`Bool`SPEC[aO, realOpenThm]],
      HOL`Bool`CONJUNCT2[hPairO]];                  (* ∃r. REP aO r ∧ ratLt qO r *)
    hPairR = ASSUME[chooseBody[concl[openA], rO]];  (* REP aO rO ∧ ratLt qO rO *)
    exRO = HOL`Bool`EXISTS[concl[betaAt[rO]][[2]], aO,
      HOL`Bool`CONJ[HOL`Bool`CONJUNCT1[hPairO], HOL`Bool`CONJUNCT1[hPairR]]];
    memRO = EQMP[HOL`Equal`SYM[betaAt[rO]], exRO];  (* supL rO *)
    conjFin = HOL`Bool`CONJ[memRO, HOL`Bool`CONJUNCT2[hPairR]];
    c4At = concl[BETACONV[mkComb[c4Tm[[2]], qO]]][[2]];   (* supL qO ⇒ ∃r. supL r ∧ qO<r *)
    exTarget = c4At[[2]];
    exFin = HOL`Bool`EXISTS[exTarget, rO, conjFin];
    exFinCh2 = HOL`Bool`CHOOSE[aO, exO, HOL`Bool`CHOOSE[rO, openA, exFin]];
    c4Thm = HOL`Bool`GEN[qO, HOL`Bool`DISCH[mkComb[supL, qO], exFinCh2]];

    (* --- assemble --- *)
    conjAll = HOL`Bool`CONJ[c1Thm,
      HOL`Bool`CONJ[c2Thm, HOL`Bool`CONJ[c3Thm, c4Thm]]];
    isCutSup = EQMP[HOL`Equal`SYM[cutUnfold], conjAll];   (* IS_CUT supL *)
    HOL`Bool`GEN[SV, HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm, isCutSup]]]
  ];

(* ============================================================ *)
(* repRealSupThm / realSupMemThm — the carve round-trip under     *)
(* the two side conditions.                                       *)
(* ============================================================ *)

repRealSupThm =
  Module[{SV, hneTm, hbndTm, isCutSup, supL, lVar, repAbsInst, repAbsCut,
          apRep},
    SV = mkVar["S", setTy];
    hneTm = hneTmOf[SV]; hbndTm = hbndTmOf[SV];
    isCutSup = HOL`Bool`UNDISCH[HOL`Bool`UNDISCH[
      HOL`Bool`SPEC[SV, supCutIsCutThm]]];          (* IS_CUT supL  [hne, hbnd] *)
    supL = concl[isCutSup][[2]];
    lVar = concl[repAbsRealThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{lVar -> supL}, repAbsRealThm];
    repAbsCut = EQMP[repAbsInst, isCutSup];         (* REP (ABS supL) = supL *)
    apRep = HOL`Equal`APTERM[repRealConst[], unfoldRealSup[SV]];
    HOL`Bool`GEN[SV, HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm,
      TRANS[apRep, repAbsCut]]]]
  ];

realSupMemThm =
  Module[{SV, qV, hneTm, hbndTm, repEq, apQ},
    SV = mkVar["S", setTy]; qV = mkVar["q", ratTy];
    hneTm = hneTmOf[SV]; hbndTm = hbndTmOf[SV];
    repEq = HOL`Bool`UNDISCH[HOL`Bool`UNDISCH[
      HOL`Bool`SPEC[SV, repRealSupThm]]];           (* REP (realSup S) = supL *)
    apQ = HOL`Equal`APTHM[repEq, qV];
    HOL`Bool`GEN[SV, HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm,
      HOL`Bool`GEN[qV, TRANS[apQ, BETACONV[concl[apQ][[2]]]]]]]]
  ];

(* ============================================================ *)
(* realSupUpperThm — sup is an upper bound: a ∈ S puts L_a       *)
(* inside the union.                                             *)
(* ============================================================ *)

realSupUpperThm =
  Module[{SV, aU, qU, hneTm, hbndTm, memEqAll, hSa, memEqQ, exU, repSupQ,
          allQ, leA},
    SV = mkVar["S", setTy];
    aU = mkVar["a", realTy]; qU = mkVar["qU", ratTy];
    hneTm = hneTmOf[SV]; hbndTm = hbndTmOf[SV];
    memEqAll = HOL`Bool`UNDISCH[HOL`Bool`UNDISCH[
      HOL`Bool`SPEC[SV, realSupMemThm]]];           (* ∀q. REP (realSup S) q = ∃a. … *)
    hSa = ASSUME[mkComb[SV, aU]];
    memEqQ = HOL`Bool`SPEC[qU, memEqAll];           (* REP (realSup S) qU = ∃a. S a ∧ REP a qU *)
    exU = HOL`Bool`EXISTS[concl[memEqQ][[2]], aU,
      HOL`Bool`CONJ[hSa, ASSUME[repApp[aU, qU]]]];
    repSupQ = EQMP[HOL`Equal`SYM[memEqQ], exU];     (* REP (realSup S) qU *)
    allQ = HOL`Bool`GEN[qU, HOL`Bool`DISCH[repApp[aU, qU], repSupQ]];
    leA = EQMP[HOL`Equal`SYM[unfoldRealLe[aU, realSupTm[SV]]], allQ];
    HOL`Bool`GEN[SV, HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm,
      HOL`Bool`GEN[aU, HOL`Bool`DISCH[mkComb[SV, aU], leA]]]]]
  ];

(* ============================================================ *)
(* realSupLeastThm — sup is below every upper bound: each point  *)
(* of the union lies in some L_a ⊆ L_v.                          *)
(* ============================================================ *)

realSupLeastThm =
  Module[{SV, vV, aB, aL, qL, hneTm, hbndTm, lubTm, hLub, memEqAll,
          hRepSup, exL, hPairL, leALv, repVq, repVqCh, allL, leSupV},
    SV = mkVar["S", setTy]; vV = mkVar["v", realTy];
    aB = mkVar["a", realTy];
    aL = mkVar["aL", realTy]; qL = mkVar["qL", ratTy];
    hneTm = hneTmOf[SV]; hbndTm = hbndTmOf[SV];
    lubTm = forallTm[aB, impTm[mkComb[SV, aB], realLeTm[aB, vV]]];
    hLub = ASSUME[lubTm];
    memEqAll = HOL`Bool`UNDISCH[HOL`Bool`UNDISCH[
      HOL`Bool`SPEC[SV, realSupMemThm]]];
    hRepSup = ASSUME[repApp[realSupTm[SV], qL]];
    exL = EQMP[HOL`Bool`SPEC[qL, memEqAll], hRepSup];   (* ∃a. S a ∧ REP a qL *)
    hPairL = ASSUME[chooseBody[concl[exL], aL]];        (* S aL ∧ REP aL qL *)
    leALv = HOL`Bool`MP[HOL`Bool`SPEC[aL, hLub], HOL`Bool`CONJUNCT1[hPairL]];
    repVq = HOL`Bool`MP[
      HOL`Bool`SPEC[qL, EQMP[unfoldRealLe[aL, vV], leALv]],
      HOL`Bool`CONJUNCT2[hPairL]];                      (* REP v qL *)
    repVqCh = HOL`Bool`CHOOSE[aL, exL, repVq];
    allL = HOL`Bool`GEN[qL,
      HOL`Bool`DISCH[repApp[realSupTm[SV], qL], repVqCh]];
    leSupV = EQMP[HOL`Equal`SYM[unfoldRealLe[realSupTm[SV], vV]], allL];
    HOL`Bool`GEN[SV, HOL`Bool`GEN[vV,
      HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm,
        HOL`Bool`DISCH[lubTm, leSupV]]]]]
  ];

(* ============================================================ *)
(* dedekindCompleteThm — the packaged least-upper-bound law.     *)
(* ============================================================ *)

dedekindCompleteThm =
  Module[{SV, vV, hneTm, hbndTm, upper, least},
    SV = mkVar["S", setTy]; vV = mkVar["v", realTy];
    hneTm = hneTmOf[SV]; hbndTm = hbndTmOf[SV];
    upper = HOL`Bool`UNDISCH[HOL`Bool`UNDISCH[
      HOL`Bool`SPEC[SV, realSupUpperThm]]];         (* ∀a. S a ⇒ realLe a (realSup S) *)
    least = HOL`Bool`UNDISCH[HOL`Bool`UNDISCH[
      HOL`Bool`SPEC[vV, HOL`Bool`SPEC[SV, realSupLeastThm]]]];
    HOL`Bool`GEN[SV, HOL`Bool`DISCH[hneTm, HOL`Bool`DISCH[hbndTm,
      HOL`Bool`CONJ[upper, HOL`Bool`GEN[vV, least]]]]]
  ];

(* ============================================================ *)
(* realRatBoundThm — ⊢ ∀x. ∃q. realLt x (&ℝ q).                  *)
(*   Take q0 ∉ L_x (properness); then &ℝ (1+q0) is strictly       *)
(*   above x: q0 itself witnesses non-inclusion of L_{&ℝ(1+q0)}.  *)
(* ============================================================ *)

realRatBoundThm =
  Module[{xV, qF, qB0, prX, hNotRepX, mono, leftEq, bnd, congLt, ltQB,
          hLe1, memBnd, repXq, ff1, notLe, ltX, exQ},
    xV = mkVar["x", realTy];
    qF = mkVar["q", ratTy]; qB0 = mkVar["qB0", ratTy];
    prX = HOL`Bool`SPEC[xV, realProperThm];         (* ∃q. ¬ REP x q *)
    hNotRepX = ASSUME[chooseBody[concl[prX], qB0]]; (* ¬ REP x qB0 *)
    (* ratLt qB0 (1 + qB0) *)
    mono = HOL`Bool`MP[
      HOL`Bool`SPEC[qB0, HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[],
        HOL`Stdlib`Rat`ratLtAddMonoThm]]],
      ratZeroLtOneThm];                             (* ratLt (0+qB0) (1+qB0) *)
    leftEq = TRANS[
      HOL`Bool`SPEC[qB0, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
      HOL`Bool`SPEC[qB0, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+qB0 = qB0 *)
    bnd = ratAddTm[oneQ[], qB0];
    congLt = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], leftEq], REFL[bnd]];
    ltQB = EQMP[congLt, mono];                      (* ratLt qB0 (1+qB0) *)
    (* realLe (&ℝ bnd) x would push qB0 into L_x *)
    hLe1 = ASSUME[realLeTm[realOfRatTm[bnd], xV]];
    memBnd = EQMP[HOL`Equal`SYM[
      HOL`Bool`SPEC[qB0, HOL`Bool`SPEC[bnd, realOfRatMemThm]]], ltQB];
    repXq = HOL`Bool`MP[
      HOL`Bool`SPEC[qB0, EQMP[unfoldRealLe[realOfRatTm[bnd], xV], hLe1]],
      memBnd];                                      (* REP x qB0 *)
    ff1 = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotRepX], repXq];
    notLe = HOL`Bool`NOTINTRO[
      HOL`Bool`DISCH[realLeTm[realOfRatTm[bnd], xV], ff1]];
    ltX = EQMP[HOL`Equal`SYM[ltNotLeAt[xV, realOfRatTm[bnd]]], notLe];
    exQ = HOL`Bool`EXISTS[
      existsTm[qF, realLtTm[xV, realOfRatTm[qF]]], bnd, ltX];
    HOL`Bool`GEN[xV, HOL`Bool`CHOOSE[qB0, prX, exQ]]
  ];

(* ============================================================ *)
(* realArchThm — ⊢ ∀x. ∃n. realLt x (&ℝ (&ℚ (&ℤ n))).            *)
(*   Rational bound + ℚ-Archimedean + strict transitivity.        *)
(* ============================================================ *)

realArchThm =
  Module[{xV, nB, qA, nA, bd, hLtQ, arch, hLtN, natQ, rLtRR, ltXN, exN},
    xV = mkVar["x", realTy]; nB = mkVar["n", numTy];
    qA = mkVar["qA", ratTy]; nA = mkVar["nA", numTy];
    bd = HOL`Bool`SPEC[xV, realRatBoundThm];        (* ∃q. realLt x (&ℝ q) *)
    hLtQ = ASSUME[chooseBody[concl[bd], qA]];       (* realLt x (&ℝ qA) *)
    arch = HOL`Bool`SPEC[qA, ratArchThm];           (* ∃n. ratLt qA (&ℚ (&ℤ n)) *)
    hLtN = ASSUME[chooseBody[concl[arch], nA]];     (* ratLt qA (&ℚ (&ℤ nA)) *)
    natQ = ratOfIntTm[intOfNumTm[nA]];
    rLtRR = EQMP[HOL`Equal`SYM[
      HOL`Bool`SPEC[natQ, HOL`Bool`SPEC[qA, realOfRatLtThm]]], hLtN];
    ltXN = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[realOfRatTm[natQ],
        HOL`Bool`SPEC[realOfRatTm[qA], HOL`Bool`SPEC[xV, realLtTransThm]]],
      hLtQ], rLtRR];                                (* realLt x (&ℝ (&ℚ (&ℤ nA))) *)
    exN = HOL`Bool`EXISTS[
      existsTm[nB, realLtTm[xV, realOfRatTm[ratOfIntTm[intOfNumTm[nB]]]]],
      nA, ltXN];
    HOL`Bool`GEN[xV,
      HOL`Bool`CHOOSE[qA, bd, HOL`Bool`CHOOSE[nA, arch, exN]]]
  ];

(* ============================================================ *)
(* realDenseThm — ⊢ ∀x y. realLt x y ⇒ ∃q. realLt x (&ℝ q) ∧      *)
(* realLt (&ℝ q) y.                                              *)
(*   Separating point qDe ∈ L_y \ L_x, bumped open to rDe ∈ L_y   *)
(*   with qDe < rDe. Then qDe witnesses x < &ℝ rDe, and rDe ∈ L_y *)
(*   kills realLe y (&ℝ rDe) by irreflexivity.                    *)
(* ============================================================ *)

realDenseThm =
  Module[{xV, yV, qF, qDe, rDe, hXY, notLeYX, wit, hPairDe, opn, hPairR,
          hLe1, memQinR, repXq, ff1, lt1, hLe2, repRR, ltRR, ff2, lt2,
          exTgt, exDe},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    qF = mkVar["q", ratTy];
    qDe = mkVar["qDe", ratTy]; rDe = mkVar["rDe", ratTy];
    hXY = ASSUME[realLtTm[xV, yV]];
    notLeYX = EQMP[ltNotLeAt[xV, yV], hXY];         (* ¬(realLe y x) *)
    wit = HOL`Bool`MP[
      HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, notLeWitnessThm]], notLeYX];
    hPairDe = ASSUME[chooseBody[concl[wit], qDe]];  (* REP y qDe ∧ ¬ REP x qDe *)
    opn = HOL`Bool`MP[HOL`Bool`SPEC[qDe, HOL`Bool`SPEC[yV, realOpenThm]],
      HOL`Bool`CONJUNCT1[hPairDe]];                 (* ∃r. REP y r ∧ ratLt qDe r *)
    hPairR = ASSUME[chooseBody[concl[opn], rDe]];   (* REP y rDe ∧ ratLt qDe rDe *)

    (* realLt x (&ℝ rDe): inclusion would push qDe into L_x *)
    hLe1 = ASSUME[realLeTm[realOfRatTm[rDe], xV]];
    memQinR = EQMP[HOL`Equal`SYM[
      HOL`Bool`SPEC[qDe, HOL`Bool`SPEC[rDe, realOfRatMemThm]]],
      HOL`Bool`CONJUNCT2[hPairR]];                  (* REP (&ℝ rDe) qDe *)
    repXq = HOL`Bool`MP[
      HOL`Bool`SPEC[qDe, EQMP[unfoldRealLe[realOfRatTm[rDe], xV], hLe1]],
      memQinR];                                     (* REP x qDe *)
    ff1 = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`CONJUNCT2[hPairDe]], repXq];
    lt1 = EQMP[HOL`Equal`SYM[ltNotLeAt[xV, realOfRatTm[rDe]]],
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[realOfRatTm[rDe], xV], ff1]]];

    (* realLt (&ℝ rDe) y: inclusion would give ratLt rDe rDe *)
    hLe2 = ASSUME[realLeTm[yV, realOfRatTm[rDe]]];
    repRR = HOL`Bool`MP[
      HOL`Bool`SPEC[rDe, EQMP[unfoldRealLe[yV, realOfRatTm[rDe]], hLe2]],
      HOL`Bool`CONJUNCT1[hPairR]];                  (* REP (&ℝ rDe) rDe *)
    ltRR = EQMP[HOL`Bool`SPEC[rDe, HOL`Bool`SPEC[rDe, realOfRatMemThm]],
      repRR];                                       (* ratLt rDe rDe *)
    ff2 = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[rDe, ratLtIrreflThm]], ltRR];
    lt2 = EQMP[HOL`Equal`SYM[ltNotLeAt[realOfRatTm[rDe], yV]],
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[realLeTm[yV, realOfRatTm[rDe]], ff2]]];

    exTgt = existsTm[qF, conjTm[
      realLtTm[xV, realOfRatTm[qF]], realLtTm[realOfRatTm[qF], yV]]];
    exDe = HOL`Bool`EXISTS[exTgt, rDe, HOL`Bool`CONJ[lt1, lt2]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      HOL`Bool`DISCH[realLtTm[xV, yV],
        HOL`Bool`CHOOSE[qDe, wit, HOL`Bool`CHOOSE[rDe, opn, exDe]]]]]
  ];

End[];
EndPackage[];
