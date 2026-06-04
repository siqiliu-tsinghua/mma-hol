(* M7-7 / stdlib/Real/Field.wl — ℝ algebraic structure + &ℝ embedding.

   Part of the stdlib/Real/ folder (PLAN §8.1): shares the package context
   HOL`Stdlib`Real` with Cut.wl, so Cut.wl's private term-builder / unfold
   vocabulary (forallTm, ratLtTm, repApp, repRealTm, absRealConst,
   unfoldRealLe, …) is reused here for free.

   Stage A (this commit): the embedding &ℝ : rat → real, q ↦ the principal
   cut { p : p < q } = ABS_real (λp. ratLt p q) (well-defined by Cut.wl's
   principalCutIsCutThm). Injective; an order embedding
   (realLe (&ℝ a) (&ℝ b) = ratLe a b). Later stages: realAdd / realNeg
   (additive group), realMul (Rudin sign-case), then &ℝ as a ring/order
   homomorphism. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

realOfRatConst::usage = "realOfRatConst[] — &ℝ : rat → real, the embedding q ↦ ABS_real (λp. ratLt p q) (the principal cut { p : p < q }).";
realOfRatDefThm::usage = "realOfRatDefThm — ⊢ &ℝ = (λq. ABS_real (λp. ratLt p q)).";
repRealOfRatThm::usage = "repRealOfRatThm — ⊢ REP_real (&ℝ q) = (λp. ratLt p q) (q free): the cut of &ℝ q is the principal cut of q.";
realOfRatMemThm::usage = "realOfRatMemThm — ⊢ ∀q p. REP_real (&ℝ q) p = ratLt p q. Membership in &ℝ q is being below q.";
realOfRatInjThm::usage = "realOfRatInjThm — ⊢ ∀a b. &ℝ a = &ℝ b ⇒ a = b. The embedding is injective.";
realOfRatLeThm::usage = "realOfRatLeThm — ⊢ ∀a b. realLe (&ℝ a) (&ℝ b) = ratLe a b. &ℝ is an order embedding.";

memNotMemLtThm::usage = "memNotMemLtThm — ⊢ ∀x a b. REP_real x a ⇒ ¬ (REP_real x b) ⇒ ratLt a b. Cut separation: a point in the cut precedes a point outside it.";

realAddConst::usage = "realAddConst[] — realAdd : real → real → real, cut addition. L_{x+y} = { r : ∃s. s ∈ L_x ∧ (r − s) ∈ L_y }.";
realAddDefThm::usage = "realAddDefThm — ⊢ realAdd = (λx y. ABS_real (λr. ∃s. REP_real x s ∧ REP_real y (ratAdd r (ratNeg s)))).";
sumCutIsCutThm::usage = "sumCutIsCutThm — ⊢ ∀x y. IS_CUT (λr. ∃s. REP_real x s ∧ REP_real y (ratAdd r (ratNeg s))). The sum-set of two cuts is a cut.";
repRealAddThm::usage = "repRealAddThm — ⊢ ∀x y. REP_real (realAdd x y) = (λr. ∃s. REP_real x s ∧ REP_real y (ratAdd r (ratNeg s))).";
realAddMemThm::usage = "realAddMemThm — ⊢ ∀x y r. REP_real (realAdd x y) r = (∃s. REP_real x s ∧ REP_real y (ratAdd r (ratNeg s))).";

sumMemSwapThm::usage = "sumMemSwapThm — ⊢ ∀x y r. (∃s. REP_real x s ∧ REP_real y (ratAdd r (ratNeg s))) ⇒ (∃s. REP_real y s ∧ REP_real x (ratAdd r (ratNeg s))). The sum-set is symmetric in x, y.";
realAddCommThm::usage = "realAddCommThm — ⊢ ∀x y. realAdd x y = realAdd y x.";
realAddZeroThm::usage = "realAddZeroThm — ⊢ ∀x. realAdd x (&ℝ (&ℚ (&ℤ 0))) = x. The real 0 is a right additive identity.";
ratAddRightCancelThm::usage = "ratAddRightCancelThm — ⊢ ∀a b c. ratAdd a c = ratAdd b c ⇒ a = b. Right additive cancellation in ℚ.";
realAddAssocThm::usage = "realAddAssocThm — ⊢ ∀x y z. realAdd (realAdd x y) z = realAdd x (realAdd y z). Closes the additive abelian group on ℝ.";
ratNegNegThm::usage = "ratNegNegThm — ⊢ ∀q. ratNeg (ratNeg q) = q.";
ratAddLeftCancelThm::usage = "ratAddLeftCancelThm — ⊢ ∀a x y. ratAdd a x = ratAdd a y ⇒ x = y. Left additive cancellation in ℚ.";
ratNegAddThm::usage = "ratNegAddThm — ⊢ ∀a b. ratNeg (ratAdd a b) = ratAdd (ratNeg a) (ratNeg b).";
ratSubLtSelfThm::usage = "ratSubLtSelfThm — ⊢ ∀v r. ratLt (&ℚ (&ℤ 0)) r ⇒ ratLt (ratAdd v (ratNeg r)) v. (0<r ⇒ v−r < v.)";
ratLtSubPosThm::usage = "ratLtSubPosThm — ⊢ ∀a b. ratLt a b ⇒ ratLt (&ℚ (&ℤ 0)) (ratAdd b (ratNeg a)). (a<b ⇒ 0 < b−a.)";

realNegConst::usage = "realNegConst[] — realNeg : real → real, cut negation (Rudin). L_{−x} = { p : ∃r. 0<r ∧ −(p+r) ∉ L_x }.";
realNegDefThm::usage = "realNegDefThm — ⊢ realNeg = (λx. ABS_real (λp. ∃r. ratLt (&ℚ(&ℤ0)) r ∧ ¬ (REP_real x (ratNeg (ratAdd p r))))).";
negCutIsCutThm::usage = "negCutIsCutThm — ⊢ ∀x. IS_CUT (λp. ∃r. ratLt (&ℚ(&ℤ0)) r ∧ ¬ (REP_real x (ratNeg (ratAdd p r)))). The Rudin negation set of a cut is a cut.";
repRealNegThm::usage = "repRealNegThm — ⊢ ∀x. REP_real (realNeg x) = (λp. ∃r. ratLt (&ℚ(&ℤ0)) r ∧ ¬ (REP_real x (ratNeg (ratAdd p r)))).";
realNegMemThm::usage = "realNegMemThm — ⊢ ∀x p. REP_real (realNeg x) p = (∃r. ratLt (&ℚ(&ℤ0)) r ∧ ¬ (REP_real x (ratNeg (ratAdd p r)))).";

intLtLeTransThm::usage = "intLtLeTransThm — ⊢ ∀a b c. intLt a b ⇒ intLe b c ⇒ intLt a c.";
intLeLtTransThm::usage = "intLeLtTransThm — ⊢ ∀a b c. intLe a b ⇒ intLt b c ⇒ intLt a c.";
intArchThm::usage = "intArchThm — ⊢ ∀z. ∃n:num. intLt z (&ℤ n). ℤ is Archimedean (every integer is below some natural).";
ratArchThm::usage = "ratArchThm — ⊢ ∀q. ∃n:num. ratLt q (&ℚ (&ℤ n)). ℚ is Archimedean (every rational is below some natural). Lifts intArchThm via cross-multiplication.";
ratMulRightCancelThm::usage = "ratMulRightCancelThm — ⊢ ∀w a b. ¬(w = &ℚ(&ℤ0)) ⇒ ratMul a w = ratMul b w ⇒ a = b.";
ratLtMulPosThm::usage = "ratLtMulPosThm — ⊢ ∀w a b. ratLt (&ℚ(&ℤ0)) w ⇒ ratLt a b ⇒ ratLt (ratMul a w) (ratMul b w). Strict monotonicity of ·w for w>0.";
ratNatMulGtThm::usage = "ratNatMulGtThm — ⊢ ∀w r. ratLt (&ℚ(&ℤ0)) w ⇒ ∃n:num. ratLt r (ratMul (&ℚ(&ℤ n)) w).";
ratNatSucMulThm::usage = "ratNatSucMulThm — ⊢ ∀w k. ratMul (&ℚ(&ℤ(SUC k))) w = ratAdd (ratMul (&ℚ(&ℤ k)) w) w.";
cutStraddleThm::usage = "cutStraddleThm — ⊢ ∀x s w. REP_real x s ⇒ ∀n. ¬(REP_real x (ratAdd s (ratMul (&ℚ(&ℤ n)) w))) ⇒ ∃M. REP_real x (ratAdd s (ratMul (&ℚ(&ℤ M)) w)) ∧ ¬(REP_real x (ratAdd s (ratMul (&ℚ(&ℤ(SUC M))) w))). Stepping s by multiples of w eventually leaves the cut; the last-in/first-out boundary M (Rudin straddle).";
realAddNegLeThm::usage = "realAddNegLeThm — ⊢ ∀x. realLe (realAdd x (realNeg x)) (&ℝ (&ℚ (&ℤ 0))). Easy half of the additive inverse.";
realAddNegGeThm::usage = "realAddNegGeThm — ⊢ ∀x. realLe (&ℝ (&ℚ (&ℤ 0))) (realAdd x (realNeg x)). Hard half (Archimedean straddle).";
realAddNegThm::usage = "realAddNegThm — ⊢ ∀x. realAdd x (realNeg x) = &ℝ (&ℚ (&ℤ 0)). Additive inverse — closes ℝ as an additive abelian GROUP.";

Begin["`Private`"];

(* &ℝ : rat → real.  Reuses Cut.wl's shared-context vocabulary
   (ratTy, ratLtTm, ratLeTm, notC, impC, absRealConst, repRealConst,
   realLeTm, unfoldRealLe, principalCutIsCutThm, repAbsRealThm,
   ratLtIrreflThm). *)

realOfRatTy = tyFun[ratTy, realTy];

realOfRatDefThm =
  Module[{qV, pV, body},
    qV = mkVar["q", ratTy]; pV = mkVar["p", ratTy];
    body = mkAbs[qV, mkComb[absRealConst[], mkAbs[pV, ratLtTm[pV, qV]]]];
    newDefinition[mkEq[mkVar["&ℝ", realOfRatTy], body]]
  ];

realOfRatConst[] := mkConst["&ℝ", realOfRatTy];
realOfRatTm[qTm_] := mkComb[realOfRatConst[], qTm];

(* ⊢ &ℝ q = ABS_real (λp. ratLt p q) *)
unfoldRealOfRat[qTm_] :=
  Module[{ap}, ap = HOL`Equal`APTHM[realOfRatDefThm, qTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]];

(* ⊢ REP_real (&ℝ q) = (λp. ratLt p q)  (q free) *)
repRealOfRatThm =
  Module[{qV, isCutQ, cutTerm, lVar, repAbsInst, repAbsCut, apRep},
    qV = mkVar["q", ratTy];
    isCutQ = HOL`Bool`SPEC[qV, principalCutIsCutThm];   (* IS_CUT (λp. ratLt p q) *)
    cutTerm = concl[isCutQ][[2]];                        (* λp. ratLt p q *)
    lVar = concl[repAbsRealThm][[1, 2, 2]];              (* the free L in IS_CUT L = (…) *)
    repAbsInst = HOL`Kernel`INST[{lVar -> cutTerm}, repAbsRealThm];
    repAbsCut = EQMP[repAbsInst, isCutQ];                (* REP_real (ABS_real cutTerm) = cutTerm *)
    apRep = HOL`Equal`APTERM[repRealConst[], unfoldRealOfRat[qV]];
    TRANS[apRep, repAbsCut]
  ];

(* ⊢ ∀q p. REP_real (&ℝ q) p = ratLt p q *)
realOfRatMemThm =
  Module[{qV, pV, apAtP},
    qV = mkVar["q", ratTy]; pV = mkVar["p", ratTy];
    apAtP = HOL`Equal`APTHM[repRealOfRatThm, pV];   (* REP_real (&ℝ q) p = (λp. ratLt p q) p *)
    HOL`Bool`GEN[qV, HOL`Bool`GEN[pV,
      TRANS[apAtP, BETACONV[concl[apAtP][[2]]]]]]
  ];

(* ⊢ REP_real (&ℝ a) p = ratLt p a  (instantiated) *)
memAt[aTm_, pTm_] :=
  HOL`Bool`SPEC[pTm, HOL`Bool`SPEC[aTm, realOfRatMemThm]];

(* from ⊢ (ratLt x y) = (ratLt x z) and ⊢ ¬(ratLt x y), derive ⊢ ¬(ratLt x z). *)
notLtFromEq[eqThm_, notLhsThm_] :=
  EQMP[HOL`Equal`APTERM[notC[], eqThm], notLhsThm];

(* ⊢ ¬(ratLt x y) = ratLe y x   (ratLt x y = ¬(ratLe y x), then double-neg) *)
ddNotLeFromNotLt[xV_, yV_] :=
  Module[{ltNL, apNeg, dd},
    ltNL = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, HOL`Stdlib`Rat`ratLtNotLeThm]];   (* ratLt x y = ¬(ratLe y x) *)
    apNeg = HOL`Equal`APTERM[notC[], ltNL];   (* ¬(ratLt x y) = ¬¬(ratLe y x) *)
    dd = HOL`Auto`PropTaut`propTaut[
      mkEq[notTm[notTm[ratLeTm[yV, xV]]], ratLeTm[yV, xV]]];
    TRANS[apNeg, dd]
  ];

(* ⊢ ∀a b. &ℝ a = &ℝ b ⇒ a = b *)
realOfRatInjThm =
  Module[{aV, bV, hEq, apRep, aMemA, aMemB, atA, bMemA, bMemB, atB,
          notALtA, notBLtB, leBA, leAB, aEqB},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    hEq = ASSUME[mkEq[realOfRatTm[aV], realOfRatTm[bV]]];   (* &ℝ a = &ℝ b *)
    apRep = HOL`Equal`APTERM[repRealConst[], hEq];          (* REP_real(&ℝa) = REP_real(&ℝb) *)
    aMemA = memAt[aV, aV];   (* REP_real(&ℝa) a = ratLt a a *)
    aMemB = memAt[bV, aV];   (* REP_real(&ℝb) a = ratLt a b *)
    atA = TRANS[TRANS[HOL`Equal`SYM[aMemA], HOL`Equal`APTHM[apRep, aV]], aMemB];
    (* ⊢ ratLt a a = ratLt a b *)
    bMemA = memAt[aV, bV];   (* REP_real(&ℝa) b = ratLt b a *)
    bMemB = memAt[bV, bV];   (* REP_real(&ℝb) b = ratLt b b *)
    atB = TRANS[TRANS[HOL`Equal`SYM[bMemA], HOL`Equal`APTHM[apRep, bV]], bMemB];
    (* ⊢ ratLt b a = ratLt b b *)
    notALtA = HOL`Bool`SPEC[aV, ratLtIrreflThm];   (* ¬(ratLt a a) *)
    notBLtB = HOL`Bool`SPEC[bV, ratLtIrreflThm];   (* ¬(ratLt b b) *)
    (* atA has the irreflexive term (ratLt a a) on its LHS, atB on its RHS
       (the two TRANS chains are built in mirror order) — so atB needs SYM
       to feed notLtFromEq, which expects ¬(LHS). *)
    leBA = EQMP[ddNotLeFromNotLt[aV, bV], notLtFromEq[atA, notALtA]];   (* ratLe b a *)
    leAB = EQMP[ddNotLeFromNotLt[bV, aV], notLtFromEq[HOL`Equal`SYM[atB], notBLtB]];   (* ratLe a b *)
    aEqB = HOL`Bool`MP[HOL`Bool`MP[
             HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLeAntisymThm]],
             leAB], leBA];   (* a = b *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[concl[hEq], aEqB]]]
  ];

(* ⊢ ∀a b. realLe (&ℝ a) (&ℝ b) = ratLe a b *)
realOfRatLeThm =
  Module[{aV, bV, fwd, bwd},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];

    (* forward: {realLe(&ℝa)(&ℝb)} ⊢ ratLe a b *)
    fwd = Module[{hLe, leUnf, specB, memBA, memBB, impl, hNotLe, bLtA,
                  bLtB, falseT},
      hLe = ASSUME[realLeTm[realOfRatTm[aV], realOfRatTm[bV]]];
      leUnf = EQMP[unfoldRealLe[realOfRatTm[aV], realOfRatTm[bV]], hLe];
      specB = HOL`Bool`SPEC[bV, leUnf];   (* REP(&ℝa) b ⇒ REP(&ℝb) b *)
      memBA = memAt[aV, bV];   (* REP(&ℝa) b = ratLt b a *)
      memBB = memAt[bV, bV];   (* REP(&ℝb) b = ratLt b b *)
      impl = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[impC[], memBA], memBB], specB];
      (* ⊢ ratLt b a ⇒ ratLt b b *)
      hNotLe = ASSUME[notTm[ratLeTm[aV, bV]]];   (* ¬(ratLe a b) *)
      bLtA = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV,
               HOL`Stdlib`Rat`ratLtNotLeThm]]], hNotLe];   (* ratLt b a *)
      bLtB = HOL`Bool`MP[impl, bLtA];   (* ratLt b b *)
      falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[bV, ratLtIrreflThm]], bLtB];
      HOL`Bool`CCONTR[ratLeTm[aV, bV], falseT]   (* ratLe a b  [realLe …] *)
    ];

    (* backward: {ratLe a b} ⊢ realLe(&ℝa)(&ℝb) *)
    bwd = Module[{hLeAB, qV, hQltA, notAleQ, hBleQ, aLeQ, qLtB, impl,
                  allImpl},
      hLeAB = ASSUME[ratLeTm[aV, bV]];   (* ratLe a b *)
      qV = mkVar["q", ratTy];
      hQltA = ASSUME[ratLtTm[qV, aV]];   (* ratLt q a *)
      notAleQ = EQMP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[qV,
                  HOL`Stdlib`Rat`ratLtNotLeThm]], hQltA];   (* ¬(ratLe a q) *)
      hBleQ = ASSUME[ratLeTm[bV, qV]];   (* ratLe b q *)
      aLeQ = HOL`Bool`MP[HOL`Bool`MP[
               HOL`Bool`SPEC[qV, HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV,
                 HOL`Stdlib`Rat`ratLeTransThm]]], hLeAB], hBleQ];   (* ratLe a q *)
      qLtB = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[qV,
               HOL`Stdlib`Rat`ratLtNotLeThm]]],
               HOL`Bool`NOTINTRO[HOL`Bool`DISCH[ratLeTm[bV, qV],
                 HOL`Bool`MP[HOL`Bool`NOTELIM[notAleQ], aLeQ]]]];   (* ratLt q b *)
      impl = EQMP[HOL`Kernel`MKCOMB[
               HOL`Equal`APTERM[impC[], HOL`Equal`SYM[memAt[aV, qV]]],
               HOL`Equal`SYM[memAt[bV, qV]]],
               HOL`Bool`DISCH[ratLtTm[qV, aV], qLtB]];
      (* ⊢ REP(&ℝa) q ⇒ REP(&ℝb) q *)
      allImpl = HOL`Bool`GEN[qV, impl];
      EQMP[HOL`Equal`SYM[unfoldRealLe[realOfRatTm[aV], realOfRatTm[bV]]], allImpl]
    ];

    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Kernel`DEDUCTANTISYM[bwd, fwd]]]
  ];

(* ============================================================ *)
(* Stage B: realAdd — cut addition.                              *)
(* ============================================================ *)

ratSubTm[rT_, sT_] := ratAddTm[rT, ratNegTm[sT]];   (* r − s *)

(* small reusable rat identities (logically Rat; parked in Real vocab) *)

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

(* ⊢ ∀x a b. REP_real x a ⇒ ¬(REP_real x b) ⇒ ratLt a b   (cut separation) *)
memNotMemLtThm =
  Module[{xV, aV, bV, hMemA, hNotMemB, hNotLt, ltNL, apN, dd, leBA, cases,
          dcX, caseLt, caseEq, falseFromCases, ltAB},
    xV = mkVar["x", realTy]; aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    hMemA = ASSUME[repApp[xV, aV]];                 (* REP x a *)
    hNotMemB = ASSUME[notTm[repApp[xV, bV]]];        (* ¬REP x b *)
    hNotLt = ASSUME[notTm[ratLtTm[aV, bV]]];         (* ¬(ratLt a b) *)
    ltNL = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLtNotLeThm]];   (* ratLt a b = ¬(ratLe b a) *)
    apN = HOL`Equal`APTERM[notC[], ltNL];            (* ¬(ratLt a b) = ¬¬(ratLe b a) *)
    dd = HOL`Auto`PropTaut`propTaut[
      mkEq[notTm[notTm[ratLeTm[bV, aV]]], ratLeTm[bV, aV]]];
    leBA = EQMP[TRANS[apN, dd], hNotLt];             (* ratLe b a *)
    cases = HOL`Bool`MP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, ratLeCasesThm]], leBA];   (* ratLt b a ∨ b=a *)
    dcX = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[xV, realDownClosedThm]]];   (* REP x a ⇒ ratLt b a ⇒ REP x b *)
    caseLt = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotMemB],
               HOL`Bool`MP[HOL`Bool`MP[dcX, hMemA], ASSUME[ratLtTm[bV, aV]]]];   (* F  [ratLt b a] *)
    caseEq = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotMemB],
               EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[xV], ASSUME[mkEq[bV, aV]]]], hMemA]];   (* F  [b=a] *)
    falseFromCases = HOL`Bool`DISJCASES[cases, caseLt, caseEq];   (* F  [¬(a<b), REP x a, ¬REP x b] *)
    ltAB = HOL`Bool`CCONTR[ratLtTm[aV, bV], falseFromCases];   (* ratLt a b *)
    HOL`Bool`GEN[xV, HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[repApp[xV, aV],
        HOL`Bool`DISCH[notTm[repApp[xV, bV]], ltAB]]]]]
  ];

(* realAdd = λx y. ABS_real (λr. ∃s. REP x s ∧ REP y (r − s)) *)
realAddTy = tyFun[realTy, tyFun[realTy, realTy]];

sumCutBodyTm[xT_, yT_] :=
  Module[{rV, sV},
    rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy];
    mkAbs[rV, existsTm[sV, conjTm[repApp[xT, sV], repApp[yT, ratSubTm[rV, sV]]]]]
  ];

realAddDefThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = mkAbs[xV, mkAbs[yV, mkComb[absRealConst[], sumCutBodyTm[xV, yV]]]];
    newDefinition[mkEq[mkVar["realAdd", realAddTy], body]]
  ];

realAddConst[] := mkConst["realAdd", realAddTy];
realAddTm[xT_, yT_] := mkComb[mkComb[realAddConst[], xT], yT];

(* ⊢ realAdd x y = ABS_real (sumCutBody x y) *)
unfoldRealAdd[xT_, yT_] :=
  Module[{s1, s1b, s2},
    s1 = HOL`Equal`APTHM[realAddDefThm, xT];
    s1b = TRANS[s1, BETACONV[concl[s1][[2]]]];
    s2 = HOL`Equal`APTHM[s1b, yT];
    TRANS[s2, BETACONV[concl[s2][[2]]]]
  ];

(* ⊢ ∀x y. IS_CUT (λr. ∃s. REP x s ∧ REP y (r − s)) *)
sumCutIsCutThm =
  Module[{xV, yV, sumBody, betaSum, sV, unfold, rhsConj, c1Tm, rest1, c2Tm,
          rest2, c3Tm, c4Tm, c1Thm, c2Thm, c3Thm, c4Thm, conjAll, isCutXY},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    sumBody = sumCutBodyTm[xV, yV];
    sV = mkVar["s", ratTy];
    betaSum[rT_] := BETACONV[mkComb[sumBody, rT]];   (* sumBody r = ∃s. REP x s ∧ REP y (r−s) *)

    unfold = unfoldIsCut[sumBody];
    rhsConj = concl[unfold][[2]];
    c1Tm = rhsConj[[1, 2]]; rest1 = rhsConj[[2]];
    c2Tm = rest1[[1, 2]]; rest2 = rest1[[2]];
    c3Tm = rest2[[1, 2]]; c4Tm = rest2[[2]];

    (* --- c1 nonempty: witness s0 + t0 --- *)
    c1Thm = Module[{neX, neY, s0, t0, r0, hX, hY, subEq, memYsub, innerWit, exS, sumAt, ex},
      neX = HOL`Bool`SPEC[xV, realNonemptyThm];
      neY = HOL`Bool`SPEC[yV, realNonemptyThm];
      s0 = mkVar["s0", ratTy]; t0 = mkVar["t0", ratTy];
      r0 = ratAddTm[s0, t0];
      hX = ASSUME[repApp[xV, s0]]; hY = ASSUME[repApp[yV, t0]];
      subEq = HOL`Bool`SPEC[t0, HOL`Bool`SPEC[s0, ratAddSubCancelLeftThm]];   (* (s0+t0)−s0 = t0 *)
      memYsub = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[yV], subEq]], hY];
      innerWit = HOL`Bool`CONJ[hX, memYsub];
      exS = HOL`Bool`EXISTS[
        existsTm[sV, conjTm[repApp[xV, sV], repApp[yV, ratSubTm[r0, sV]]]], s0, innerWit];
      sumAt = EQMP[HOL`Equal`SYM[betaSum[r0]], exS];
      ex = HOL`Bool`EXISTS[c1Tm, r0, sumAt];
      HOL`Bool`CHOOSE[t0, neY, HOL`Bool`CHOOSE[s0, neX, ex]]
    ];

    (* --- c2 proper: witness u0 + v0 with u0∉L_x, v0∉L_y --- *)
    c2Thm = Module[{prX, prY, u0, v0, r0p, hNX, hNY, s1, hP1, memX1, memYsub1,
                    sub1, ltS1U0, ltSubV0, step1, step2raw, commL, commR, step2,
                    ltSum, addId, ltR0p, falseFromP1, hEx, falseChosen, notEx, notSum, ex},
      prX = HOL`Bool`SPEC[xV, realProperThm];
      prY = HOL`Bool`SPEC[yV, realProperThm];
      u0 = mkVar["u0", ratTy]; v0 = mkVar["v0", ratTy];
      r0p = ratAddTm[u0, v0];
      hNX = ASSUME[notTm[repApp[xV, u0]]]; hNY = ASSUME[notTm[repApp[yV, v0]]];
      s1 = mkVar["s1", ratTy];
      sub1 = ratSubTm[r0p, s1];
      hP1 = ASSUME[conjTm[repApp[xV, s1], repApp[yV, sub1]]];
      memX1 = HOL`Bool`CONJUNCT1[hP1]; memYsub1 = HOL`Bool`CONJUNCT2[hP1];
      ltS1U0 = HOL`Bool`MP[HOL`Bool`MP[
                 HOL`Bool`SPEC[u0, HOL`Bool`SPEC[s1, HOL`Bool`SPEC[xV, memNotMemLtThm]]], memX1], hNX];   (* s1 < u0 *)
      ltSubV0 = HOL`Bool`MP[HOL`Bool`MP[
                  HOL`Bool`SPEC[v0, HOL`Bool`SPEC[sub1, HOL`Bool`SPEC[yV, memNotMemLtThm]]], memYsub1], hNY];   (* (r0p−s1) < v0 *)
      step1 = HOL`Bool`MP[HOL`Bool`SPEC[sub1, HOL`Bool`SPEC[u0, HOL`Bool`SPEC[s1,
                HOL`Stdlib`Rat`ratLtAddMonoThm]]], ltS1U0];   (* (s1+sub1) < (u0+sub1) *)
      step2raw = HOL`Bool`MP[HOL`Bool`SPEC[u0, HOL`Bool`SPEC[v0, HOL`Bool`SPEC[sub1,
                   HOL`Stdlib`Rat`ratLtAddMonoThm]]], ltSubV0];   (* (sub1+u0) < (v0+u0) *)
      commL = HOL`Bool`SPEC[sub1, HOL`Bool`SPEC[u0, HOL`Stdlib`Rat`ratAddCommThm]];   (* u0+sub1 = sub1+u0 *)
      commR = HOL`Bool`SPEC[u0, HOL`Bool`SPEC[v0, HOL`Stdlib`Rat`ratAddCommThm]];   (* v0+u0 = u0+v0 *)
      step2 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], HOL`Equal`SYM[commL]], commR], step2raw];
      (* (u0+sub1) < (u0+v0) *)
      ltSum = HOL`Bool`MP[HOL`Bool`MP[
                HOL`Bool`SPEC[ratAddTm[u0, v0], HOL`Bool`SPEC[ratAddTm[u0, sub1],
                  HOL`Bool`SPEC[ratAddTm[s1, sub1], ratLtTransThm]]], step1], step2];   (* (s1+sub1) < (u0+v0) *)
      addId = HOL`Bool`SPEC[r0p, HOL`Bool`SPEC[s1, ratAddSubLeftThm]];   (* s1 + (r0p−s1) = r0p *)
      ltR0p = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], addId], REFL[ratAddTm[u0, v0]]], ltSum];
      (* ratLt r0p (u0+v0) ≡ ratLt r0p r0p *)
      falseFromP1 = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[r0p, ratLtIrreflThm]], ltR0p];   (* F *)
      hEx = ASSUME[existsTm[sV, conjTm[repApp[xV, sV], repApp[yV, ratSubTm[r0p, sV]]]]];
      falseChosen = HOL`Bool`CHOOSE[s1, hEx, falseFromP1];   (* F  [∃s.P, ¬REP x u0, ¬REP y v0] *)
      notEx = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[concl[hEx], falseChosen]];   (* ¬(∃s.P) *)
      notSum = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[], betaSum[r0p]]], notEx];   (* ¬(sumBody r0p) *)
      ex = HOL`Bool`EXISTS[c2Tm, r0p, notSum];
      HOL`Bool`CHOOSE[v0, prY, HOL`Bool`CHOOSE[u0, prX, ex]]
    ];

    (* --- c3 downward closed: same witness, L_y downclosed --- *)
    c3Thm = Module[{uV, wV, hSum, exU, hLt, s2, hP2, memX2, memYsub2, ltSub,
                    dcY, memYsubW, innerW, exW, sumW, sumWChosen, disch},
      uV = mkVar["u", ratTy]; wV = mkVar["w", ratTy];
      hSum = ASSUME[mkComb[sumBody, uV]];
      exU = EQMP[betaSum[uV], hSum];   (* ∃s. REP x s ∧ REP y (u−s) *)
      hLt = ASSUME[ratLtTm[wV, uV]];
      s2 = mkVar["s2", ratTy];
      hP2 = ASSUME[conjTm[repApp[xV, s2], repApp[yV, ratSubTm[uV, s2]]]];
      memX2 = HOL`Bool`CONJUNCT1[hP2]; memYsub2 = HOL`Bool`CONJUNCT2[hP2];
      ltSub = HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[s2], HOL`Bool`SPEC[uV, HOL`Bool`SPEC[wV,
                HOL`Stdlib`Rat`ratLtAddMonoThm]]], hLt];   (* (w−s2) < (u−s2) *)
      dcY = HOL`Bool`SPEC[ratSubTm[wV, s2], HOL`Bool`SPEC[ratSubTm[uV, s2],
              HOL`Bool`SPEC[yV, realDownClosedThm]]];   (* REP y (u−s2) ⇒ ratLt (w−s2)(u−s2) ⇒ REP y (w−s2) *)
      memYsubW = HOL`Bool`MP[HOL`Bool`MP[dcY, memYsub2], ltSub];   (* REP y (w−s2) *)
      innerW = HOL`Bool`CONJ[memX2, memYsubW];
      exW = HOL`Bool`EXISTS[
        existsTm[sV, conjTm[repApp[xV, sV], repApp[yV, ratSubTm[wV, sV]]]], s2, innerW];
      sumW = EQMP[HOL`Equal`SYM[betaSum[wV]], exW];
      sumWChosen = HOL`Bool`CHOOSE[s2, exU, sumW];
      disch = HOL`Bool`DISCH[mkComb[sumBody, uV], HOL`Bool`DISCH[ratLtTm[wV, uV], sumWChosen]];
      HOL`Bool`GEN[uV, HOL`Bool`GEN[wV, disch]]
    ];

    (* --- c4 no greatest: L_y open above (u−s) --- *)
    c4Thm = Module[{uV, hSum, exU, s3, hP3, memX3, memYsub3, openY, t3, hOpen,
                    memYt3, ltSubT3, r2, subEq2, memYr2, innerR2, exR2, sumR2,
                    uId, monoT, commA, commB, ltCommed, ltUr2, bodyR2, exBody,
                    chosen1, chosen2, disch},
      uV = mkVar["u", ratTy];
      hSum = ASSUME[mkComb[sumBody, uV]];
      exU = EQMP[betaSum[uV], hSum];
      s3 = mkVar["s3", ratTy];
      hP3 = ASSUME[conjTm[repApp[xV, s3], repApp[yV, ratSubTm[uV, s3]]]];
      memX3 = HOL`Bool`CONJUNCT1[hP3]; memYsub3 = HOL`Bool`CONJUNCT2[hP3];
      openY = HOL`Bool`MP[HOL`Bool`SPEC[ratSubTm[uV, s3], HOL`Bool`SPEC[yV, realOpenThm]], memYsub3];
      (* ∃r. REP y r ∧ ratLt (u−s3) r *)
      t3 = mkVar["t3", ratTy];
      hOpen = ASSUME[conjTm[repApp[yV, t3], ratLtTm[ratSubTm[uV, s3], t3]]];
      memYt3 = HOL`Bool`CONJUNCT1[hOpen]; ltSubT3 = HOL`Bool`CONJUNCT2[hOpen];
      r2 = ratAddTm[s3, t3];
      subEq2 = HOL`Bool`SPEC[t3, HOL`Bool`SPEC[s3, ratAddSubCancelLeftThm]];   (* (s3+t3)−s3 = t3 *)
      memYr2 = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[yV], subEq2]], memYt3];   (* REP y (r2−s3) *)
      innerR2 = HOL`Bool`CONJ[memX3, memYr2];
      exR2 = HOL`Bool`EXISTS[
        existsTm[sV, conjTm[repApp[xV, sV], repApp[yV, ratSubTm[r2, sV]]]], s3, innerR2];
      sumR2 = EQMP[HOL`Equal`SYM[betaSum[r2]], exR2];   (* sumBody r2 *)
      uId = HOL`Bool`SPEC[uV, HOL`Bool`SPEC[s3, ratAddSubLeftThm]];   (* s3 + (u−s3) = u *)
      monoT = HOL`Bool`MP[HOL`Bool`SPEC[s3, HOL`Bool`SPEC[t3, HOL`Bool`SPEC[ratSubTm[uV, s3],
                HOL`Stdlib`Rat`ratLtAddMonoThm]]], ltSubT3];   (* ((u−s3)+s3) < (t3+s3) *)
      commA = HOL`Bool`SPEC[ratSubTm[uV, s3], HOL`Bool`SPEC[s3, HOL`Stdlib`Rat`ratAddCommThm]];   (* s3+(u−s3) = (u−s3)+s3 *)
      commB = HOL`Bool`SPEC[t3, HOL`Bool`SPEC[s3, HOL`Stdlib`Rat`ratAddCommThm]];   (* s3+t3 = t3+s3 *)
      ltCommed = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], HOL`Equal`SYM[commA]],
                   HOL`Equal`SYM[commB]], monoT];   (* (s3+(u−s3)) < (s3+t3) *)
      ltUr2 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], uId], REFL[r2]], ltCommed];   (* u < r2 *)
      bodyR2 = HOL`Bool`CONJ[sumR2, ltUr2];   (* sumBody r2 ∧ ratLt u r2 *)
      exBody = HOL`Bool`EXISTS[
        existsTm[mkVar["w", ratTy], conjTm[mkComb[sumBody, mkVar["w", ratTy]],
          ratLtTm[uV, mkVar["w", ratTy]]]], r2, bodyR2];
      chosen1 = HOL`Bool`CHOOSE[t3, openY, exBody];
      chosen2 = HOL`Bool`CHOOSE[s3, exU, chosen1];
      disch = HOL`Bool`DISCH[mkComb[sumBody, uV], chosen2];
      HOL`Bool`GEN[uV, disch]
    ];

    conjAll = HOL`Bool`CONJ[c1Thm, HOL`Bool`CONJ[c2Thm, HOL`Bool`CONJ[c3Thm, c4Thm]]];
    isCutXY = EQMP[HOL`Equal`SYM[unfold], conjAll];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, isCutXY]]
  ];

(* ⊢ ∀x y. REP_real (realAdd x y) = (λr. ∃s. REP x s ∧ REP y (r − s)) *)
repRealAddThm =
  Module[{xV, yV, sumBody, isCutXY, lVar, repAbsInst, repAbsSum, apRep},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    sumBody = sumCutBodyTm[xV, yV];
    isCutXY = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, sumCutIsCutThm]];   (* IS_CUT sumBody *)
    lVar = concl[repAbsRealThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{lVar -> sumBody}, repAbsRealThm];
    repAbsSum = EQMP[repAbsInst, isCutXY];   (* REP (ABS sumBody) = sumBody *)
    apRep = HOL`Equal`APTERM[repRealConst[], unfoldRealAdd[xV, yV]];   (* REP(realAdd x y) = REP(ABS sumBody) *)
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, TRANS[apRep, repAbsSum]]]
  ];

(* ⊢ ∀x y r. REP_real (realAdd x y) r = (∃s. REP x s ∧ REP y (r − s)) *)
realAddMemThm =
  Module[{xV, yV, rV, repEq, apAtR},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; rV = mkVar["r", ratTy];
    repEq = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, repRealAddThm]];   (* REP(realAdd x y) = sumBody *)
    apAtR = HOL`Equal`APTHM[repEq, rV];   (* REP(realAdd x y) r = sumBody r *)
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[rV,
      TRANS[apAtR, BETACONV[concl[apAtR][[2]]]]]]]
  ];

(* ============================================================ *)
(* Stage B.2: additive laws (comm, identity).                   *)
(* ============================================================ *)

(* helper: from ⊢ ∀r. REP_real lT r = REP_real rT r derive ⊢ lT = rT
   (funcExt on the cuts + ABS round-trip). *)
realEqFromRepEq[lT_, rT_, perR_] :=
  Module[{funcEq, apAbs, aVarAbs, absL, absR},
    funcEq = HOL`Stdlib`List`funcExtThm[repRealTm[lT], repRealTm[rT], perR];
    apAbs = HOL`Equal`APTERM[absRealConst[], funcEq];
    aVarAbs = concl[absRepRealThm][[2]];
    absL = HOL`Kernel`INST[{aVarAbs -> lT}, absRepRealThm];
    absR = HOL`Kernel`INST[{aVarAbs -> rT}, absRepRealThm];
    TRANS[TRANS[HOL`Equal`SYM[absL], apAbs], absR]
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

(* ⊢ ∀x y r. (∃s. REP x s ∧ REP y (r−s)) ⇒ (∃s. REP y s ∧ REP x (r−s)) *)
sumMemSwapThm =
  Module[{xV, yV, rV, sV, aTerm, bTerm, hEx, sW, hP, memX, memYsub, sp,
          subSub, memXrsp, innerSwap, exSwap, chosen},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; rV = mkVar["r", ratTy];
    sV = mkVar["s", ratTy];
    aTerm = existsTm[sV, conjTm[repApp[xV, sV], repApp[yV, ratSubTm[rV, sV]]]];
    bTerm = existsTm[sV, conjTm[repApp[yV, sV], repApp[xV, ratSubTm[rV, sV]]]];
    hEx = ASSUME[aTerm];
    sW = mkVar["sw", ratTy];
    hP = ASSUME[conjTm[repApp[xV, sW], repApp[yV, ratSubTm[rV, sW]]]];
    memX = HOL`Bool`CONJUNCT1[hP]; memYsub = HOL`Bool`CONJUNCT2[hP];
    sp = ratSubTm[rV, sW];   (* r − sw : the swapped witness *)
    subSub = HOL`Bool`SPEC[sW, HOL`Bool`SPEC[rV, ratSubSubThm]];   (* r − (r−sw) = sw *)
    memXrsp = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[xV], subSub]], memX];   (* REP x (r−sp) *)
    innerSwap = HOL`Bool`CONJ[memYsub, memXrsp];   (* REP y sp ∧ REP x (r−sp) *)
    exSwap = HOL`Bool`EXISTS[bTerm, sp, innerSwap];
    chosen = HOL`Bool`CHOOSE[sW, hEx, exSwap];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[rV, HOL`Bool`DISCH[aTerm, chosen]]]]
  ];

(* ⊢ ∀x y. realAdd x y = realAdd y x *)
realAddCommThm =
  Module[{xV, yV, rV, sV, aTerm, bTerm, swapImplXY, swapImplYX, dirFwd, dirBwd,
          memEqR, memXY, memYX, chain, perR},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; rV = mkVar["r", ratTy];
    sV = mkVar["s", ratTy];
    aTerm = existsTm[sV, conjTm[repApp[xV, sV], repApp[yV, ratSubTm[rV, sV]]]];
    bTerm = existsTm[sV, conjTm[repApp[yV, sV], repApp[xV, ratSubTm[rV, sV]]]];
    swapImplXY = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, sumMemSwapThm]]];   (* A ⇒ B *)
    swapImplYX = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, sumMemSwapThm]]];   (* B ⇒ A *)
    dirFwd = HOL`Bool`MP[swapImplXY, ASSUME[aTerm]];   (* A ⊢ B *)
    dirBwd = HOL`Bool`MP[swapImplYX, ASSUME[bTerm]];   (* B ⊢ A *)
    memEqR = HOL`Kernel`DEDUCTANTISYM[dirBwd, dirFwd];   (* ⊢ A = B *)
    memXY = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realAddMemThm]]];   (* REP(realAdd x y) r = A *)
    memYX = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV, realAddMemThm]]];   (* REP(realAdd y x) r = B *)
    chain = TRANS[TRANS[memXY, memEqR], HOL`Equal`SYM[memYX]];   (* REP(realAdd x y) r = REP(realAdd y x) r *)
    perR = HOL`Bool`GEN[rV, chain];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV,
      realEqFromRepEq[realAddTm[xV, yV], realAddTm[yV, xV], perR]]]
  ];

(* ⊢ ∀x. realAdd x (&ℝ (&ℚ (&ℤ 0))) = x *)
realAddZeroThm =
  Module[{xV, rV, sV, zeroR, a0Term, memZeroMem, fwd, bwd, memEqR, memAdd, chain, perR},
    xV = mkVar["x", realTy]; rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy];
    zeroR = realOfRatTm[zeroQ[]];   (* &ℝ 0 *)
    a0Term = existsTm[sV, conjTm[repApp[xV, sV], repApp[zeroR, ratSubTm[rV, sV]]]];
    memZeroMem[rT_, sT_] :=
      HOL`Bool`SPEC[ratSubTm[rT, sT], HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]];
      (* REP(&ℝ 0)(r−s) = ratLt (r−s) 0 *)

    fwd = Module[{hA0, sW, hP, memX, memZero, memZeroLt, monoStep, lhsEq, rhsEq,
                  rLtSw, dcX, memXr},
      hA0 = ASSUME[a0Term];
      sW = mkVar["sw", ratTy];
      hP = ASSUME[conjTm[repApp[xV, sW], repApp[zeroR, ratSubTm[rV, sW]]]];
      memX = HOL`Bool`CONJUNCT1[hP]; memZero = HOL`Bool`CONJUNCT2[hP];
      memZeroLt = EQMP[memZeroMem[rV, sW], memZero];   (* ratLt (r−sw) 0 *)
      monoStep = HOL`Bool`MP[HOL`Bool`SPEC[sW, HOL`Bool`SPEC[zeroQ[],
                   HOL`Bool`SPEC[ratSubTm[rV, sW], HOL`Stdlib`Rat`ratLtAddMonoThm]]], memZeroLt];
      (* ratLt ((r−sw)+sw) (0+sw) *)
      lhsEq = HOL`Bool`SPEC[sW, HOL`Bool`SPEC[rV, ratSubAddThm]];   (* (r−sw)+sw = r *)
      rhsEq = TRANS[HOL`Bool`SPEC[sW, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
                HOL`Bool`SPEC[sW, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+sw = sw *)
      rLtSw = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsEq], rhsEq], monoStep];   (* ratLt r sw *)
      dcX = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[sW, HOL`Bool`SPEC[xV, realDownClosedThm]]];
      (* REP x sw ⇒ ratLt r sw ⇒ REP x r *)
      memXr = HOL`Bool`MP[HOL`Bool`MP[dcX, memX], rLtSw];   (* REP x r *)
      HOL`Bool`CHOOSE[sW, hA0, memXr]   (* REP x r  [A0] *)
    ];

    bwd = Module[{hXr, openX, sW, hOpen, memX, rLtSw, monoStep, negEq, subLt,
                  memZero, innerA0, exA0},
      hXr = ASSUME[repApp[xV, rV]];
      openX = HOL`Bool`MP[HOL`Bool`SPEC[rV, HOL`Bool`SPEC[xV, realOpenThm]], hXr];
      (* ∃s. REP x s ∧ ratLt r s *)
      sW = mkVar["sw", ratTy];
      hOpen = ASSUME[conjTm[repApp[xV, sW], ratLtTm[rV, sW]]];
      memX = HOL`Bool`CONJUNCT1[hOpen]; rLtSw = HOL`Bool`CONJUNCT2[hOpen];
      monoStep = HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[sW], HOL`Bool`SPEC[sW,
                   HOL`Bool`SPEC[rV, HOL`Stdlib`Rat`ratLtAddMonoThm]]], rLtSw];
      (* ratLt (r+(−sw)) (sw+(−sw)) *)
      negEq = HOL`Bool`SPEC[sW, HOL`Stdlib`Rat`ratAddNegThm];   (* sw+(−sw) = 0 *)
      subLt = EQMP[HOL`Kernel`MKCOMB[
                HOL`Equal`APTERM[ratLtC[], REFL[ratSubTm[rV, sW]]], negEq], monoStep];   (* ratLt (r−sw) 0 *)
      memZero = EQMP[HOL`Equal`SYM[memZeroMem[rV, sW]], subLt];   (* REP(&ℝ 0)(r−sw) *)
      innerA0 = HOL`Bool`CONJ[memX, memZero];
      exA0 = HOL`Bool`EXISTS[a0Term, sW, innerA0];   (* A0 *)
      HOL`Bool`CHOOSE[sW, openX, exA0]   (* A0  [REP x r] *)
    ];

    memEqR = HOL`Kernel`DEDUCTANTISYM[bwd, fwd];   (* ⊢ A0 = REP x r *)
    memAdd = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[zeroR, HOL`Bool`SPEC[xV, realAddMemThm]]];
    (* REP(realAdd x 0ℝ) r = A0 *)
    chain = TRANS[memAdd, memEqR];   (* REP(realAdd x 0ℝ) r = REP x r *)
    perR = HOL`Bool`GEN[rV, chain];
    HOL`Bool`GEN[xV, realEqFromRepEq[realAddTm[xV, zeroR], xV, perR]]
  ];

(* ============================================================ *)
(* Stage B.2b: associativity.                                   *)
(* ============================================================ *)

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

(* ⊢ ∀x y z. realAdd (realAdd x y) z = realAdd x (realAdd y z) *)
realAddAssocThm =
  Module[{xV, yV, zV, rV, sV, xyTm, yzTm, lhsMemTerm, rhsMemTerm, fwd, bwd,
          memEqR, memLHS, memRHS, chain, perR},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    rV = mkVar["r", ratTy]; sV = mkVar["s", ratTy];
    xyTm = realAddTm[xV, yV]; yzTm = realAddTm[yV, zV];
    lhsMemTerm = existsTm[sV, conjTm[repApp[xyTm, sV], repApp[zV, ratSubTm[rV, sV]]]];
    rhsMemTerm = existsTm[sV, conjTm[repApp[xV, sV], repApp[yzTm, ratSubTm[rV, sV]]]];

    (* fwd: LHSmem ⊢ RHSmem *)
    fwd = Module[{hLHS, sA, hPs, memXYsA, memZ, exT, tA, hPt, memX, memYsub,
                  id1, memZinner, amYZ, exYZterm, exYZ, memYZ, innerRHS, exRHS,
                  chosenT},
      hLHS = ASSUME[lhsMemTerm];
      sA = mkVar["sA", ratTy];
      hPs = ASSUME[conjTm[repApp[xyTm, sA], repApp[zV, ratSubTm[rV, sA]]]];
      memXYsA = HOL`Bool`CONJUNCT1[hPs]; memZ = HOL`Bool`CONJUNCT2[hPs];   (* REP(x+y) sA ; REP z (r−sA) *)
      exT = EQMP[HOL`Bool`SPEC[sA, HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realAddMemThm]]], memXYsA];
      (* ∃s. REP x s ∧ REP y (sA−s) *)
      tA = mkVar["tA", ratTy];
      hPt = ASSUME[conjTm[repApp[xV, tA], repApp[yV, ratSubTm[sA, tA]]]];
      memX = HOL`Bool`CONJUNCT1[hPt]; memYsub = HOL`Bool`CONJUNCT2[hPt];   (* REP x tA ; REP y (sA−tA) *)
      id1 = HOL`Bool`SPEC[tA, HOL`Bool`SPEC[sA, HOL`Bool`SPEC[rV, ratSubSubDistThm]]];
      (* (r−tA)−(sA−tA) = r−sA *)
      memZinner = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[zV], id1]], memZ];
      (* REP z ((r−tA)−(sA−tA)) *)
      amYZ = HOL`Bool`SPEC[ratSubTm[rV, tA], HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddMemThm]]];
      (* REP(y+z)(r−tA) = ∃s. REP y s ∧ REP z ((r−tA)−s) *)
      exYZterm = concl[amYZ][[2]];
      exYZ = HOL`Bool`EXISTS[exYZterm, ratSubTm[sA, tA], HOL`Bool`CONJ[memYsub, memZinner]];
      memYZ = EQMP[HOL`Equal`SYM[amYZ], exYZ];   (* REP(y+z)(r−tA) *)
      innerRHS = HOL`Bool`CONJ[memX, memYZ];   (* REP x tA ∧ REP(y+z)(r−tA) *)
      exRHS = HOL`Bool`EXISTS[rhsMemTerm, tA, innerRHS];
      chosenT = HOL`Bool`CHOOSE[tA, exT, exRHS];
      HOL`Bool`CHOOSE[sA, hLHS, chosenT]
    ];

    (* bwd: RHSmem ⊢ LHSmem *)
    bwd = Module[{hRHS, sB, hPs, memX, memYZsub, exT, tB, hPt, memY, memZsub,
                  id2, memZinner, subEqB, memYinner, amXY, exXYterm, exXY, memXY,
                  innerLHS, exLHS, chosenT},
      hRHS = ASSUME[rhsMemTerm];
      sB = mkVar["sB", ratTy];
      hPs = ASSUME[conjTm[repApp[xV, sB], repApp[yzTm, ratSubTm[rV, sB]]]];
      memX = HOL`Bool`CONJUNCT1[hPs]; memYZsub = HOL`Bool`CONJUNCT2[hPs];   (* REP x sB ; REP(y+z)(r−sB) *)
      exT = EQMP[HOL`Bool`SPEC[ratSubTm[rV, sB], HOL`Bool`SPEC[zV, HOL`Bool`SPEC[yV, realAddMemThm]]], memYZsub];
      (* ∃s. REP y s ∧ REP z ((r−sB)−s) *)
      tB = mkVar["tB", ratTy];
      hPt = ASSUME[conjTm[repApp[yV, tB], repApp[zV, ratSubTm[ratSubTm[rV, sB], tB]]]];
      memY = HOL`Bool`CONJUNCT1[hPt]; memZsub = HOL`Bool`CONJUNCT2[hPt];   (* REP y tB ; REP z ((r−sB)−tB) *)
      id2 = HOL`Bool`SPEC[tB, HOL`Bool`SPEC[sB, HOL`Bool`SPEC[rV, ratSubAddDistThm]]];
      (* r−(sB+tB) = (r−sB)−tB *)
      memZinner = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[zV], id2]], memZsub];
      (* REP z (r−(sB+tB))  from REP z ((r−sB)−tB) *)
      subEqB = HOL`Bool`SPEC[tB, HOL`Bool`SPEC[sB, ratAddSubCancelLeftThm]];   (* (sB+tB)−sB = tB *)
      memYinner = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[yV], subEqB]], memY];
      (* REP y ((sB+tB)−sB)  from REP y tB *)
      amXY = HOL`Bool`SPEC[ratAddTm[sB, tB], HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV, realAddMemThm]]];
      (* REP(x+y)(sB+tB) = ∃s. REP x s ∧ REP y ((sB+tB)−s) *)
      exXYterm = concl[amXY][[2]];
      exXY = HOL`Bool`EXISTS[exXYterm, sB, HOL`Bool`CONJ[memX, memYinner]];
      memXY = EQMP[HOL`Equal`SYM[amXY], exXY];   (* REP(x+y)(sB+tB) *)
      innerLHS = HOL`Bool`CONJ[memXY, memZinner];   (* REP(x+y)(sB+tB) ∧ REP z (r−(sB+tB)) *)
      exLHS = HOL`Bool`EXISTS[lhsMemTerm, ratAddTm[sB, tB], innerLHS];
      chosenT = HOL`Bool`CHOOSE[tB, exT, exLHS];
      HOL`Bool`CHOOSE[sB, hRHS, chosenT]
    ];

    memEqR = HOL`Kernel`DEDUCTANTISYM[bwd, fwd];   (* ⊢ LHSmem = RHSmem *)
    memLHS = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[zV, HOL`Bool`SPEC[xyTm, realAddMemThm]]];
    (* REP((x+y)+z) r = LHSmem *)
    memRHS = HOL`Bool`SPEC[rV, HOL`Bool`SPEC[yzTm, HOL`Bool`SPEC[xV, realAddMemThm]]];
    (* REP(x+(y+z)) r = RHSmem *)
    chain = TRANS[TRANS[memLHS, memEqR], HOL`Equal`SYM[memRHS]];
    perR = HOL`Bool`GEN[rV, chain];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV,
      realEqFromRepEq[realAddTm[xyTm, zV], realAddTm[xV, yzTm], perR]]]]
  ];

(* ============================================================ *)
(* Stage C: realNeg — additive inverse. Reusable ℚ negation algebra. *)
(* ============================================================ *)

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

(* ============================================================ *)
(* negCut + realNeg.                                            *)
(* ============================================================ *)

realNegTy = tyFun[realTy, realTy];

(* the negation set { p : ∃r. 0<r ∧ ¬(REP x (−(p+r))) } as a rat→bool *)
negCutBodyTm[xT_] :=
  Module[{pV, rV},
    pV = mkVar["p", ratTy]; rV = mkVar["r", ratTy];
    mkAbs[pV, existsTm[rV, conjTm[ratLtTm[zeroQ[], rV],
      notTm[repApp[xT, ratNegTm[ratAddTm[pV, rV]]]]]]]
  ];

(* the ∃r-form (= negCutBody applied to pT, after β) *)
negExTerm[xT_, pT_] :=
  Module[{rV}, rV = mkVar["r", ratTy];
    existsTm[rV, conjTm[ratLtTm[zeroQ[], rV],
      notTm[repApp[xT, ratNegTm[ratAddTm[pT, rV]]]]]]];

realNegDefThm =
  Module[{xV, body},
    xV = mkVar["x", realTy];
    body = mkAbs[xV, mkComb[absRealConst[], negCutBodyTm[xV]]];
    newDefinition[mkEq[mkVar["realNeg", realNegTy], body]]
  ];

realNegConst[] := mkConst["realNeg", realNegTy];
realNegTm[xT_] := mkComb[realNegConst[], xT];

unfoldRealNeg[xT_] :=
  Module[{ap}, ap = HOL`Equal`APTHM[realNegDefThm, xT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]];

(* ⊢ ∀x. IS_CUT (negCutBody x) *)
negCutIsCutThm =
  Module[{xV, negBody, betaNeg, unfold, rhsConj, c1Tm, rest1, c2Tm, rest2,
          c3Tm, c4Tm, c1Thm, c2Thm, c3Thm, c4Thm, conjAll},
    xV = mkVar["x", realTy];
    negBody = negCutBodyTm[xV];
    betaNeg[pT_] := BETACONV[mkComb[negBody, pT]];

    unfold = unfoldIsCut[negBody];
    rhsConj = concl[unfold][[2]];
    c1Tm = rhsConj[[1, 2]]; rest1 = rhsConj[[2]];
    c2Tm = rest1[[1, 2]]; rest2 = rest1[[2]];
    c3Tm = rest2[[1, 2]]; c4Tm = rest2[[2]];

    (* --- c1 nonempty: u∉L, p0 = −(u+1), r=1 --- *)
    c1Thm = Module[{prX, u, hNotU, p0, eA, congA, assocB, eC, congC, zeroD,
                    p0Plus1Eq, negWitEq, notMemNeg, innerWit, exR, sumAt, ex},
      prX = HOL`Bool`SPEC[xV, realProperThm];
      u = mkVar["u0", ratTy];
      hNotU = ASSUME[notTm[repApp[xV, u]]];
      p0 = ratNegTm[ratAddTm[u, oneQ[]]];   (* −(u+1) *)
      eA = HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[u, ratNegAddThm]];   (* −(u+1) = (−u)+(−1) *)
      congA = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], eA], REFL[oneQ[]]];
      (* (−(u+1))+1 = ((−u)+(−1))+1 *)
      assocB = HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[ratNegTm[oneQ[]],
                 HOL`Bool`SPEC[ratNegTm[u], HOL`Stdlib`Rat`ratAddAssocThm]]];
      (* ((−u)+(−1))+1 = (−u)+((−1)+1) *)
      eC = TRANS[HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[ratNegTm[oneQ[]], HOL`Stdlib`Rat`ratAddCommThm]],
             HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratAddNegThm]];   (* (−1)+1 = 0 *)
      congC = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[ratNegTm[u]]], eC];
      (* (−u)+((−1)+1) = (−u)+0 *)
      zeroD = HOL`Bool`SPEC[ratNegTm[u], HOL`Stdlib`Rat`ratAddZeroThm];   (* (−u)+0 = −u *)
      p0Plus1Eq = TRANS[congA, TRANS[assocB, TRANS[congC, zeroD]]];   (* (−(u+1))+1 = −u *)
      negWitEq = TRANS[HOL`Equal`APTERM[ratNegConst[], p0Plus1Eq], HOL`Bool`SPEC[u, ratNegNegThm]];
      (* −(p0+1) = −(−u) = u *)
      notMemNeg = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[],
                    HOL`Equal`APTERM[repRealTm[xV], negWitEq]]], hNotU];   (* ¬(REP x (−(p0+1))) *)
      innerWit = HOL`Bool`CONJ[ratZeroLtOneThm, notMemNeg];   (* 0<1 ∧ ¬(REP x (−(p0+1))) *)
      exR = HOL`Bool`EXISTS[negExTerm[xV, p0], oneQ[], innerWit];
      sumAt = EQMP[HOL`Equal`SYM[betaNeg[p0]], exR];
      ex = HOL`Bool`EXISTS[c1Tm, p0, sumAt];
      HOL`Bool`CHOOSE[u, prX, ex]
    ];

    (* --- c2 proper: v∈L, witness −v --- *)
    c2Thm = Module[{neX, v, hMemV, nv, r1, hEx, hP1, h0Ltr1, hNotMem, negArgEq,
                    vSubR1LtV, dcX, memVsub, notMemVsub, falseT, falseChosen,
                    notExThm, notSum, ex},
      neX = HOL`Bool`SPEC[xV, realNonemptyThm];
      v = mkVar["v0", ratTy];
      hMemV = ASSUME[repApp[xV, v]];
      nv = ratNegTm[v];
      hEx = ASSUME[negExTerm[xV, nv]];   (* ∃r. 0<r ∧ ¬(REP x (−((−v)+r))) *)
      r1 = mkVar["r1", ratTy];
      hP1 = ASSUME[conjTm[ratLtTm[zeroQ[], r1], notTm[repApp[xV, ratNegTm[ratAddTm[nv, r1]]]]]];
      h0Ltr1 = HOL`Bool`CONJUNCT1[hP1]; hNotMem = HOL`Bool`CONJUNCT2[hP1];
      negArgEq = TRANS[HOL`Bool`SPEC[r1, HOL`Bool`SPEC[nv, ratNegAddThm]],
                   HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
                     HOL`Bool`SPEC[v, ratNegNegThm]], REFL[ratNegTm[r1]]]];
      (* −((−v)+r1) = (−(−v))+(−r1) = v+(−r1) = v−r1 *)
      vSubR1LtV = HOL`Bool`MP[HOL`Bool`SPEC[r1, HOL`Bool`SPEC[v, ratSubLtSelfThm]], h0Ltr1];   (* (v−r1) < v *)
      dcX = HOL`Bool`SPEC[ratSubTm[v, r1], HOL`Bool`SPEC[v, HOL`Bool`SPEC[xV, realDownClosedThm]]];
      memVsub = HOL`Bool`MP[HOL`Bool`MP[dcX, hMemV], vSubR1LtV];   (* REP x (v−r1) *)
      notMemVsub = EQMP[HOL`Equal`APTERM[notC[], HOL`Equal`APTERM[repRealTm[xV], negArgEq]], hNotMem];
      (* ¬(REP x (v−r1)) *)
      falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[notMemVsub], memVsub];   (* F *)
      falseChosen = HOL`Bool`CHOOSE[r1, hEx, falseT];   (* F  [∃r…, REP x v] *)
      notExThm = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[concl[hEx], falseChosen]];   (* ¬(∃r…) *)
      notSum = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[], betaNeg[nv]]], notExThm];   (* ¬(negCutBody (−v)) *)
      ex = HOL`Bool`EXISTS[c2Tm, nv, notSum];
      HOL`Bool`CHOOSE[v, neX, ex]
    ];

    (* --- c3 downward closed: r' = r0 + (u−w) --- *)
    c3Thm = Module[{uV, wV, hSum, exR, hLt, r0, hP, h0Ltr0, hNotMem, uMw, rPrime,
                    posUmw, commStep, assocStep, subLeftStep, witEq, negWitEq,
                    notMemNew, r0LtRp, lhsE, rhsE, r0LtRp2, posRprime, inner,
                    exNew, sumNew, chosen, disch},
      uV = mkVar["u", ratTy]; wV = mkVar["w", ratTy];
      hSum = ASSUME[mkComb[negBody, uV]];
      exR = EQMP[betaNeg[uV], hSum];
      hLt = ASSUME[ratLtTm[wV, uV]];
      r0 = mkVar["r0", ratTy];
      hP = ASSUME[conjTm[ratLtTm[zeroQ[], r0], notTm[repApp[xV, ratNegTm[ratAddTm[uV, r0]]]]]];
      h0Ltr0 = HOL`Bool`CONJUNCT1[hP]; hNotMem = HOL`Bool`CONJUNCT2[hP];
      uMw = ratSubTm[uV, wV]; rPrime = ratAddTm[r0, uMw];
      posUmw = HOL`Bool`MP[HOL`Bool`SPEC[uV, HOL`Bool`SPEC[wV, ratLtSubPosThm]], hLt];   (* 0 < u−w *)
      commStep = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[wV]],
                   HOL`Bool`SPEC[uMw, HOL`Bool`SPEC[r0, HOL`Stdlib`Rat`ratAddCommThm]]];
      (* w+(r0+(u−w)) = w+((u−w)+r0) *)
      assocStep = HOL`Equal`SYM[HOL`Bool`SPEC[r0, HOL`Bool`SPEC[uMw,
                    HOL`Bool`SPEC[wV, HOL`Stdlib`Rat`ratAddAssocThm]]]];
      (* w+((u−w)+r0) = (w+(u−w))+r0 *)
      subLeftStep = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
                      HOL`Bool`SPEC[uV, HOL`Bool`SPEC[wV, ratAddSubLeftThm]]], REFL[r0]];
      (* (w+(u−w))+r0 = u+r0 *)
      witEq = TRANS[commStep, TRANS[assocStep, subLeftStep]];   (* w+rPrime = u+r0 *)
      negWitEq = HOL`Equal`APTERM[ratNegConst[], witEq];   (* −(w+rPrime) = −(u+r0) *)
      notMemNew = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[],
                    HOL`Equal`APTERM[repRealTm[xV], negWitEq]]], hNotMem];   (* ¬(REP x (−(w+rPrime))) *)
      r0LtRp = HOL`Bool`MP[HOL`Bool`SPEC[r0, HOL`Bool`SPEC[uMw,
                 HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratLtAddMonoThm]]], posUmw];   (* 0+r0 < (u−w)+r0 *)
      lhsE = TRANS[HOL`Bool`SPEC[r0, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
               HOL`Bool`SPEC[r0, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+r0 = r0 *)
      rhsE = HOL`Bool`SPEC[r0, HOL`Bool`SPEC[uMw, HOL`Stdlib`Rat`ratAddCommThm]];   (* (u−w)+r0 = r0+(u−w) = rPrime *)
      r0LtRp2 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsE], rhsE], r0LtRp];   (* r0 < rPrime *)
      posRprime = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rPrime, HOL`Bool`SPEC[r0,
                    HOL`Bool`SPEC[zeroQ[], ratLtTransThm]]], h0Ltr0], r0LtRp2];   (* 0 < rPrime *)
      inner = HOL`Bool`CONJ[posRprime, notMemNew];
      exNew = HOL`Bool`EXISTS[negExTerm[xV, wV], rPrime, inner];
      sumNew = EQMP[HOL`Equal`SYM[betaNeg[wV]], exNew];   (* negCutBody w *)
      chosen = HOL`Bool`CHOOSE[r0, exR, sumNew];
      disch = HOL`Bool`DISCH[mkComb[negBody, uV], HOL`Bool`DISCH[ratLtTm[wV, uV], chosen]];
      HOL`Bool`GEN[uV, HOL`Bool`GEN[wV, disch]]
    ];

    (* --- c4 no greatest: pick 0<d<r0, p' = u+d, r' = r0−d --- *)
    c4Thm = Module[{uV, hSum, exR, r0, hP, h0Ltr0, hNotMem, dense, d, posD, dLtR0,
                    pPrime, rPrime, assocStep, subLeftStep, witEq, negWitEq,
                    notMemNew, posRprime, inner, exNew, sumNew, mono, lhsE, rhsE,
                    uLtPprime, bodyConj, exBody, chosen, disch},
      uV = mkVar["u", ratTy];
      hSum = ASSUME[mkComb[negBody, uV]];
      exR = EQMP[betaNeg[uV], hSum];
      r0 = mkVar["r0", ratTy];
      hP = ASSUME[conjTm[ratLtTm[zeroQ[], r0], notTm[repApp[xV, ratNegTm[ratAddTm[uV, r0]]]]]];
      h0Ltr0 = HOL`Bool`CONJUNCT1[hP]; hNotMem = HOL`Bool`CONJUNCT2[hP];
      dense = HOL`Bool`MP[HOL`Bool`SPEC[r0, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratDenseThm]], h0Ltr0];
      (* 0<mid ∧ mid<r0 *)
      d = concl[dense][[1, 2]][[2]];   (* mid *)
      posD = HOL`Bool`CONJUNCT1[dense]; dLtR0 = HOL`Bool`CONJUNCT2[dense];
      pPrime = ratAddTm[uV, d]; rPrime = ratSubTm[r0, d];
      assocStep = HOL`Bool`SPEC[rPrime, HOL`Bool`SPEC[d, HOL`Bool`SPEC[uV, HOL`Stdlib`Rat`ratAddAssocThm]]];
      (* (u+d)+(r0−d) = u+(d+(r0−d)) *)
      subLeftStep = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[uV]],
                      HOL`Bool`SPEC[r0, HOL`Bool`SPEC[d, ratAddSubLeftThm]]];
      (* u+(d+(r0−d)) = u+r0 *)
      witEq = TRANS[assocStep, subLeftStep];   (* (u+d)+(r0−d) = u+r0 *)
      negWitEq = HOL`Equal`APTERM[ratNegConst[], witEq];   (* −((u+d)+(r0−d)) = −(u+r0) *)
      notMemNew = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[],
                    HOL`Equal`APTERM[repRealTm[xV], negWitEq]]], hNotMem];
      posRprime = HOL`Bool`MP[HOL`Bool`SPEC[r0, HOL`Bool`SPEC[d, ratLtSubPosThm]], dLtR0];   (* 0 < r0−d *)
      inner = HOL`Bool`CONJ[posRprime, notMemNew];
      exNew = HOL`Bool`EXISTS[negExTerm[xV, pPrime], rPrime, inner];
      sumNew = EQMP[HOL`Equal`SYM[betaNeg[pPrime]], exNew];   (* negCutBody (u+d) *)
      mono = HOL`Bool`MP[HOL`Bool`SPEC[uV, HOL`Bool`SPEC[d,
               HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratLtAddMonoThm]]], posD];   (* 0+u < d+u *)
      lhsE = TRANS[HOL`Bool`SPEC[uV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
               HOL`Bool`SPEC[uV, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+u = u *)
      rhsE = HOL`Bool`SPEC[uV, HOL`Bool`SPEC[d, HOL`Stdlib`Rat`ratAddCommThm]];   (* d+u = u+d *)
      uLtPprime = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsE], rhsE], mono];   (* u < u+d *)
      bodyConj = HOL`Bool`CONJ[sumNew, uLtPprime];
      exBody = HOL`Bool`EXISTS[
        existsTm[mkVar["w", ratTy], conjTm[mkComb[negBody, mkVar["w", ratTy]],
          ratLtTm[uV, mkVar["w", ratTy]]]], pPrime, bodyConj];
      chosen = HOL`Bool`CHOOSE[r0, exR, exBody];
      disch = HOL`Bool`DISCH[mkComb[negBody, uV], chosen];
      HOL`Bool`GEN[uV, disch]
    ];

    conjAll = HOL`Bool`CONJ[c1Thm, HOL`Bool`CONJ[c2Thm, HOL`Bool`CONJ[c3Thm, c4Thm]]];
    HOL`Bool`GEN[xV, EQMP[HOL`Equal`SYM[unfold], conjAll]]
  ];

(* ⊢ ∀x. REP_real (realNeg x) = negCutBody x *)
repRealNegThm =
  Module[{xV, negBody, isCutX, lVar, repAbsInst, repAbsNeg, apRep},
    xV = mkVar["x", realTy];
    negBody = negCutBodyTm[xV];
    isCutX = HOL`Bool`SPEC[xV, negCutIsCutThm];
    lVar = concl[repAbsRealThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{lVar -> negBody}, repAbsRealThm];
    repAbsNeg = EQMP[repAbsInst, isCutX];
    apRep = HOL`Equal`APTERM[repRealConst[], unfoldRealNeg[xV]];
    HOL`Bool`GEN[xV, TRANS[apRep, repAbsNeg]]
  ];

(* ⊢ ∀x p. REP_real (realNeg x) p = (∃r. 0<r ∧ ¬(REP_real x (−(p+r)))) *)
realNegMemThm =
  Module[{xV, pV, repEq, apAtP},
    xV = mkVar["x", realTy]; pV = mkVar["p", ratTy];
    repEq = HOL`Bool`SPEC[xV, repRealNegThm];
    apAtP = HOL`Equal`APTHM[repEq, pV];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[pV,
      TRANS[apAtP, BETACONV[concl[apAtP][[2]]]]]]
  ];

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

(* ⊢ ∀x s w. REP_real x s ⇒ ∀n. ¬(REP x (s + n·w)) ⇒ ∃M. REP x (s+M·w) ∧ ¬(REP x (s+(SUC M)·w)) *)
cutStraddleThm =
  Module[{xV, sV, wV, hs, sPlus, MV, nV, kV, existsMstmt, pLam, sPlus0EqS,
          h0, notRepS, falseT, p0, ih, hnP, em, b1, b2, stepBody, stepImpl,
          stepK, stepThm, specInd, specBeta, allN},
    xV = mkVar["x", realTy]; sV = mkVar["s", ratTy]; wV = mkVar["w", ratTy];
    hs = ASSUME[repApp[xV, sV]];   (* REP x s *)
    sPlus[nT_] := ratAddTm[sV, natMulQ[nT, wV]];
    MV = mkVar["M", numTy]; nV = mkVar["n", numTy]; kV = mkVar["k", numTy];
    existsMstmt = existsTm[MV, conjTm[repApp[xV, sPlus[MV]], notTm[repApp[xV, sPlus[sucT[MV]]]]]];
    pLam = mkAbs[nV, impTm[notTm[repApp[xV, sPlus[nV]]], existsMstmt]];

    (* base: sPlus[0] = s *)
    sPlus0EqS = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[sV]],
        HOL`Bool`SPEC[wV, ratNatZeroMulThm]],   (* s + 0·w = s + 0 *)
      HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratAddZeroThm]];   (* s + 0 = s *)
    h0 = ASSUME[notTm[repApp[xV, sPlus[zeroN[]]]]];
    notRepS = EQMP[HOL`Equal`APTERM[notC[], HOL`Equal`APTERM[repRealTm[xV], sPlus0EqS]], h0];   (* ¬REP x s *)
    falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[notRepS], hs];
    p0 = HOL`Bool`DISCH[concl[h0], HOL`Bool`CONTR[existsMstmt, falseT]];   (* ¬REP x sPlus[0] ⇒ ∃M *)

    (* step *)
    ih = ASSUME[impTm[notTm[repApp[xV, sPlus[kV]]], existsMstmt]];   (* P(k) *)
    hnP = ASSUME[notTm[repApp[xV, sPlus[sucT[kV]]]]];   (* ¬REP x sPlus[SUC k] *)
    em = HOL`Bool`EXCLUDEDMIDDLE[repApp[xV, sPlus[kV]]];
    b1 = HOL`Bool`EXISTS[existsMstmt, kV, HOL`Bool`CONJ[ASSUME[repApp[xV, sPlus[kV]]], hnP]];
    b2 = HOL`Bool`MP[ih, ASSUME[notTm[repApp[xV, sPlus[kV]]]]];
    stepBody = HOL`Bool`DISJCASES[em, b1, b2];   (* ∃M *)
    stepImpl = HOL`Bool`DISCH[concl[hnP], stepBody];
    stepK = HOL`Bool`DISCH[concl[ih], stepImpl];
    stepThm = HOL`Bool`GEN[kV, stepK];   (* ∀k. P k ⇒ P(SUC k) *)

    specInd = HOL`Bool`ISPEC[pLam, HOL`Stdlib`Num`numInductionThm];
    specBeta = HOL`Drule`CONVRULE[HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];
    allN = HOL`Bool`MP[specBeta, HOL`Bool`CONJ[p0, stepThm]];   (* ∀n. ¬REP x sPlus[n] ⇒ ∃M *)
    HOL`Bool`GEN[xV, HOL`Bool`GEN[sV, HOL`Bool`GEN[wV,
      HOL`Bool`DISCH[concl[hs], allN]]]]
  ];

(* ============================================================ *)
(* Additive inverse: a + (−a) = 0.                              *)
(* ============================================================ *)

(* ⊢ ∀x. realLe (realAdd x (realNeg x)) (&ℝ 0)  (easy half) *)
realAddNegLeThm =
  Module[{xV, qV, negX, sumT, zeroR, hSum, exS, sV, hPs, memX, memNegS, exT, tV,
          bigX, hPt, h0t, hNeg, sLtNegX, monoSX, negXXeq0, sXlt0, sXeqQt, qtLt0,
          monoQ, lhsEq, rhsEq, qLtqt, qLt0, memZero, chosenT, chosenS, impl, allImpl},
    xV = mkVar["x", realTy]; qV = mkVar["q", ratTy];
    negX = realNegTm[xV]; sumT = realAddTm[xV, negX]; zeroR = realOfRatTm[zeroQ[]];
    hSum = ASSUME[repApp[sumT, qV]];
    exS = EQMP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[negX, HOL`Bool`SPEC[xV, realAddMemThm]]], hSum];
    sV = mkVar["s", ratTy];
    hPs = ASSUME[conjTm[repApp[xV, sV], repApp[negX, ratSubTm[qV, sV]]]];
    memX = HOL`Bool`CONJUNCT1[hPs]; memNegS = HOL`Bool`CONJUNCT2[hPs];
    exT = EQMP[HOL`Bool`SPEC[ratSubTm[qV, sV], HOL`Bool`SPEC[xV, realNegMemThm]], memNegS];
    tV = mkVar["t", ratTy];
    bigX = ratAddTm[ratSubTm[qV, sV], tV];   (* (q−s)+t *)
    hPt = ASSUME[conjTm[ratLtTm[zeroQ[], tV], notTm[repApp[xV, ratNegTm[bigX]]]]];
    h0t = HOL`Bool`CONJUNCT1[hPt]; hNeg = HOL`Bool`CONJUNCT2[hPt];
    sLtNegX = HOL`Bool`MP[HOL`Bool`MP[
                HOL`Bool`SPEC[ratNegTm[bigX], HOL`Bool`SPEC[sV, HOL`Bool`SPEC[xV, memNotMemLtThm]]],
                memX], hNeg];   (* s < −X *)
    monoSX = HOL`Bool`MP[HOL`Bool`SPEC[bigX, HOL`Bool`SPEC[ratNegTm[bigX],
               HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratLtAddMonoThm]]], sLtNegX];   (* s+X < (−X)+X *)
    negXXeq0 = TRANS[HOL`Bool`SPEC[bigX, HOL`Bool`SPEC[ratNegTm[bigX], HOL`Stdlib`Rat`ratAddCommThm]],
                 HOL`Bool`SPEC[bigX, HOL`Stdlib`Rat`ratAddNegThm]];   (* (−X)+X = X+(−X) = 0 *)
    sXlt0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], REFL[ratAddTm[sV, bigX]]], negXXeq0], monoSX];
    (* s+X < 0 *)
    sXeqQt = TRANS[
      HOL`Equal`SYM[HOL`Bool`SPEC[tV, HOL`Bool`SPEC[ratSubTm[qV, sV], HOL`Bool`SPEC[sV, HOL`Stdlib`Rat`ratAddAssocThm]]]],
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
        HOL`Bool`SPEC[qV, HOL`Bool`SPEC[sV, ratAddSubLeftThm]]], REFL[tV]]];
    (* s+X = (s+(q−s))+t = q+t *)
    qtLt0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], sXeqQt], REFL[zeroQ[]]], sXlt0];   (* q+t < 0 *)
    monoQ = HOL`Bool`MP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[tV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratLtAddMonoThm]]], h0t];
    (* 0+q < t+q *)
    lhsEq = TRANS[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
              HOL`Bool`SPEC[qV, HOL`Stdlib`Rat`ratAddZeroThm]];   (* 0+q = q *)
    rhsEq = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[tV, HOL`Stdlib`Rat`ratAddCommThm]];   (* t+q = q+t *)
    qLtqt = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsEq], rhsEq], monoQ];   (* q < q+t *)
    qLt0 = HOL`Bool`MP[HOL`Bool`MP[
             HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[ratAddTm[qV, tV], HOL`Bool`SPEC[qV, ratLtTransThm]]], qLtqt], qtLt0];
    (* q < 0 *)
    memZero = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]]], qLt0];
    (* REP (&ℝ 0) q *)
    chosenT = HOL`Bool`CHOOSE[tV, exT, memZero];
    chosenS = HOL`Bool`CHOOSE[sV, exS, chosenT];
    impl = HOL`Bool`DISCH[concl[hSum], chosenS];
    allImpl = HOL`Bool`GEN[qV, impl];
    HOL`Bool`GEN[xV, EQMP[HOL`Equal`SYM[unfoldRealLe[sumT, zeroR]], allImpl]]
  ];

raddT[a_] := mkComb[HOL`Stdlib`Rat`ratAddConst[], a];   (* curried ratAdd a *)

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

(* ⊢ ratNeg (ratAdd (ratSub q y) (ratNeg (ratAdd w q))) = ratAdd y w *)
negArgEq[qT_, yT_, wT_] :=
  Module[{nq, ny, nw, qSy, e0, congE0, s1, s2, s3, s4, s5, s6, shuffle, innerEq},
    nq = ratNegTm[qT]; ny = ratNegTm[yT]; nw = ratNegTm[wT];
    qSy = ratSubTm[qT, yT];
    e0 = HOL`Bool`SPEC[qT, HOL`Bool`SPEC[wT, ratNegAddThm]];   (* −(w+q) = (−w)+(−q) *)
    congE0 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[qSy]], e0];
    (* (q−y)+(−(w+q)) = (q−y)+((−w)+(−q)) *)
    s1 = HOL`Bool`SPEC[ratAddTm[nw, nq], HOL`Bool`SPEC[ny, HOL`Bool`SPEC[qT, HOL`Stdlib`Rat`ratAddAssocThm]]];
    (* (q+(−y))+((−w)+(−q)) = q+((−y)+((−w)+(−q))) *)
    s2 = HOL`Equal`APTERM[raddT[qT],
           HOL`Equal`SYM[HOL`Bool`SPEC[nq, HOL`Bool`SPEC[nw, HOL`Bool`SPEC[ny, HOL`Stdlib`Rat`ratAddAssocThm]]]]];
    (* q+((−y)+((−w)+(−q))) = q+(((−y)+(−w))+(−q)) *)
    s3 = HOL`Equal`APTERM[raddT[qT],
           HOL`Bool`SPEC[nq, HOL`Bool`SPEC[ratAddTm[ny, nw], HOL`Stdlib`Rat`ratAddCommThm]]];
    (* q+(((−y)+(−w))+(−q)) = q+((−q)+((−y)+(−w))) *)
    s4 = HOL`Equal`SYM[HOL`Bool`SPEC[ratAddTm[ny, nw], HOL`Bool`SPEC[nq, HOL`Bool`SPEC[qT, HOL`Stdlib`Rat`ratAddAssocThm]]]];
    (* q+((−q)+((−y)+(−w))) = (q+(−q))+((−y)+(−w)) *)
    s5 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[],
           HOL`Bool`SPEC[qT, HOL`Stdlib`Rat`ratAddNegThm]], REFL[ratAddTm[ny, nw]]];
    (* (q+(−q))+((−y)+(−w)) = 0+((−y)+(−w)) *)
    s6 = TRANS[HOL`Bool`SPEC[ratAddTm[ny, nw], HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]],
           HOL`Bool`SPEC[ratAddTm[ny, nw], HOL`Stdlib`Rat`ratAddZeroThm]];
    (* 0+((−y)+(−w)) = (−y)+(−w) *)
    shuffle = TRANS[s1, TRANS[s2, TRANS[s3, TRANS[s4, TRANS[s5, s6]]]]];
    (* (q+(−y))+((−w)+(−q)) = (−y)+(−w) *)
    innerEq = TRANS[congE0, TRANS[shuffle,
                HOL`Equal`SYM[HOL`Bool`SPEC[wT, HOL`Bool`SPEC[yT, ratNegAddThm]]]]];
    (* (q−y)+(−(w+q)) = (−y)+(−w) = −(y+w) *)
    TRANS[HOL`Equal`APTERM[ratNegConst[], innerEq], HOL`Bool`SPEC[ratAddTm[yT, wT], ratNegNegThm]]
    (* −((q−y)+(−(w+q))) = −(−(y+w)) = y+w *)
  ];

(* ⊢ ∀x. realLe (&ℝ 0) (realAdd x (realNeg x))  (hard half, Archimedean straddle) *)
realAddNegGeThm =
  Module[{xV, qV, negX, sumT, zeroR, h0q, qLt0, negQpos, dense, w0lt, wLtNegQ, wTm,
          nonemptyX, properX, s0V, uV, hS0, hU, nV, hN, monoU, lhsU, rhsU, uLtSum,
          sumNW, hRepSum, sumLtU, falseSum, notRepSum, straddleAll, straddle, MV,
          hM, yTm, hYin, hSucMout, sucMulEq, yPlusWeq, hYWout, tTm, wPlusQ,
          wpqLt0, t0lt, naEq, negArgRw, exNegMem, repNegQY, sumMem, exSum, repSum,
          chM, chN, chU, chS0, impl, allImpl},
    xV = mkVar["x", realTy]; qV = mkVar["q", ratTy];
    negX = realNegTm[xV]; sumT = realAddTm[xV, negX]; zeroR = realOfRatTm[zeroQ[]];
    h0q = ASSUME[repApp[zeroR, qV]];   (* REP (&ℝ 0) q *)
    qLt0 = EQMP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[zeroQ[], realOfRatMemThm]], h0q];   (* q < 0 *)
    negQpos = HOL`Bool`MP[HOL`Bool`SPEC[qV, ratNegPosThm], qLt0];   (* 0 < −q *)
    dense = HOL`Bool`MP[HOL`Bool`SPEC[ratNegTm[qV], HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratDenseThm]], negQpos];
    w0lt = HOL`Bool`CONJUNCT1[dense];   (* 0 < w *)
    wLtNegQ = HOL`Bool`CONJUNCT2[dense];   (* w < −q *)
    wTm = concl[w0lt][[2]];   (* the midpoint w *)

    nonemptyX = HOL`Bool`SPEC[xV, realNonemptyThm];   (* ∃s. REP x s *)
    properX = HOL`Bool`SPEC[xV, realProperThm];        (* ∃u. ¬REP x u *)
    s0V = mkVar["s0", ratTy]; uV = mkVar["u0", ratTy]; nV = mkVar["n", numTy];
    hS0 = ASSUME[repApp[xV, s0V]]; hU = ASSUME[notTm[repApp[xV, uV]]];

    (* n with (u−s0) < n·w *)
    hN = ASSUME[ratLtTm[ratSubTm[uV, s0V], natMulQ[nV, wTm]]];
    monoU = HOL`Bool`MP[HOL`Bool`SPEC[s0V, HOL`Bool`SPEC[natMulQ[nV, wTm],
              HOL`Bool`SPEC[ratSubTm[uV, s0V], HOL`Stdlib`Rat`ratLtAddMonoThm]]], hN];   (* (u−s0)+s0 < (n·w)+s0 *)
    lhsU = HOL`Bool`SPEC[s0V, HOL`Bool`SPEC[uV, ratSubAddThm]];   (* (u−s0)+s0 = u *)
    rhsU = HOL`Bool`SPEC[s0V, HOL`Bool`SPEC[natMulQ[nV, wTm], HOL`Stdlib`Rat`ratAddCommThm]];   (* (n·w)+s0 = s0+(n·w) *)
    uLtSum = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], lhsU], rhsU], monoU];   (* u < s0+(n·w) *)
    sumNW = ratAddTm[s0V, natMulQ[nV, wTm]];   (* s0 + n·w *)
    hRepSum = ASSUME[repApp[xV, sumNW]];
    sumLtU = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[uV, HOL`Bool`SPEC[sumNW, HOL`Bool`SPEC[xV, memNotMemLtThm]]], hRepSum], hU];
    (* (s0+n·w) < u *)
    falseSum = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[sumNW, ratLtIrreflThm]],
                 HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[sumNW, HOL`Bool`SPEC[uV, HOL`Bool`SPEC[sumNW, ratLtTransThm]]], sumLtU], uLtSum]];
    (* F  (sumNW < sumNW) *)
    notRepSum = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[repApp[xV, sumNW], falseSum]];   (* ¬REP x (s0+n·w) *)

    straddleAll = HOL`Bool`SPEC[nV, HOL`Bool`MP[
      HOL`Bool`SPEC[wTm, HOL`Bool`SPEC[s0V, HOL`Bool`SPEC[xV, cutStraddleThm]]], hS0]];
    (* ¬REP x (s0+n·w) ⇒ ∃M. … *)
    straddle = HOL`Bool`MP[straddleAll, notRepSum];   (* ∃M. REP x(s0+M·w) ∧ ¬REP x(s0+(SUC M)·w) *)
    MV = mkVar["MM", numTy];
    hM = ASSUME[conjTm[repApp[xV, ratAddTm[s0V, natMulQ[MV, wTm]]],
           notTm[repApp[xV, ratAddTm[s0V, natMulQ[sucT[MV], wTm]]]]]];
    hYin = HOL`Bool`CONJUNCT1[hM]; hSucMout = HOL`Bool`CONJUNCT2[hM];
    yTm = ratAddTm[s0V, natMulQ[MV, wTm]];   (* y = s0 + M·w *)
    sucMulEq = HOL`Bool`SPEC[MV, HOL`Bool`SPEC[wTm, ratNatSucMulThm]];   (* (SUC M)·w = M·w + w *)
    yPlusWeq = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[HOL`Stdlib`Rat`ratAddConst[], REFL[s0V]], sucMulEq],
      HOL`Equal`SYM[HOL`Bool`SPEC[wTm, HOL`Bool`SPEC[natMulQ[MV, wTm], HOL`Bool`SPEC[s0V, HOL`Stdlib`Rat`ratAddAssocThm]]]]];
    (* s0+(SUC M)·w = s0+(M·w+w) = (s0+M·w)+w = y+w *)
    hYWout = EQMP[HOL`Equal`APTERM[notC[], HOL`Equal`APTERM[repRealTm[xV], yPlusWeq]], hSucMout];
    (* ¬REP x (y+w) *)

    (* realNeg membership of q−y: witness t = −(w+q) *)
    tTm = ratNegTm[ratAddTm[wTm, qV]];   (* −(w+q) *)
    wPlusQ = ratAddTm[wTm, qV];
    wpqLt0 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[],
               REFL[wPlusQ]],
               TRANS[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[ratNegTm[qV], HOL`Stdlib`Rat`ratAddCommThm]],
                 HOL`Bool`SPEC[qV, HOL`Stdlib`Rat`ratAddNegThm]]],
               HOL`Bool`MP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[ratNegTm[qV], HOL`Bool`SPEC[wTm, HOL`Stdlib`Rat`ratLtAddMonoThm]]], wLtNegQ]];
    (* w+q < 0 :  w<−q ⟹ w+q < (−q)+q = 0 *)
    t0lt = HOL`Bool`MP[HOL`Bool`SPEC[wPlusQ, ratNegPosThm], wpqLt0];   (* 0 < −(w+q) = t *)
    naEq = negArgEq[qV, yTm, wTm];   (* −((q−y)+(−(w+q))) = y+w *)
    negArgRw = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[], HOL`Equal`APTERM[repRealTm[xV], naEq]]], hYWout];
    (* ¬REP x (−((q−y)+t))  from ¬REP x (y+w) *)
    exNegMem = HOL`Bool`EXISTS[
      existsTm[mkVar["t", ratTy], conjTm[ratLtTm[zeroQ[], mkVar["t", ratTy]],
        notTm[repApp[xV, ratNegTm[ratAddTm[ratSubTm[qV, yTm], mkVar["t", ratTy]]]]]]],
      tTm, HOL`Bool`CONJ[t0lt, negArgRw]];
    (* ∃t. 0<t ∧ ¬REP x (−((q−y)+t)) *)
    repNegQY = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[ratSubTm[qV, yTm], HOL`Bool`SPEC[xV, realNegMemThm]]], exNegMem];
    (* REP (realNeg x) (q−y) *)
    sumMem = HOL`Bool`CONJ[hYin, repNegQY];   (* REP x y ∧ REP(realNeg x)(q−y) *)
    exSum = HOL`Bool`EXISTS[
      existsTm[mkVar["s", ratTy], conjTm[repApp[xV, mkVar["s", ratTy]],
        repApp[negX, ratSubTm[qV, mkVar["s", ratTy]]]]],
      yTm, sumMem];   (* ∃s. REP x s ∧ REP(realNeg x)(q−s) *)
    repSum = EQMP[HOL`Equal`SYM[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[negX, HOL`Bool`SPEC[xV, realAddMemThm]]]], exSum];
    (* REP (realAdd x (realNeg x)) q *)

    chM = HOL`Bool`CHOOSE[MV, straddle, repSum];
    chN = HOL`Bool`CHOOSE[nV, HOL`Bool`MP[HOL`Bool`SPEC[ratSubTm[uV, s0V], HOL`Bool`SPEC[wTm, ratNatMulGtThm]], w0lt], chM];
    chU = HOL`Bool`CHOOSE[uV, properX, chN];
    chS0 = HOL`Bool`CHOOSE[s0V, nonemptyX, chU];
    impl = HOL`Bool`DISCH[concl[h0q], chS0];
    allImpl = HOL`Bool`GEN[qV, impl];
    HOL`Bool`GEN[xV, EQMP[HOL`Equal`SYM[unfoldRealLe[zeroR, sumT]], allImpl]]
  ];

(* ⊢ ∀x. realAdd x (realNeg x) = &ℝ 0 *)
realAddNegThm =
  Module[{xV, sumT, zeroR},
    xV = mkVar["x", realTy];
    sumT = realAddTm[xV, realNegTm[xV]]; zeroR = realOfRatTm[zeroQ[]];
    HOL`Bool`GEN[xV,
      HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[zeroR, HOL`Bool`SPEC[sumT, realLeAntisymThm]],
        HOL`Bool`SPEC[xV, realAddNegLeThm]],
        HOL`Bool`SPEC[xV, realAddNegGeThm]]]
  ];

End[];
EndPackage[];
