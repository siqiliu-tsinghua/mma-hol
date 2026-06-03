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

End[];
EndPackage[];
