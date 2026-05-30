(* ::Package:: *)

(* M7-5 / stdlib/Int.wl — ℤ via canonical representatives.

   int is carved from num × num by the predicate
       INT_REP = λp. FST p = 0 ∨ SND p = 0,
   so a representative (a, b) stands for the integer a − b, and the
   canonical reps are exactly (n, 0) [= +n] and (0, n) [= −n].

   Stage a (this file, so far): the type itself — INT_REP, the
   newBasicTypeDefinition carve, ABS_int / REP_int and the round-trip
   theorems. Operations (canon, &ℤ, neg/succ/pred, +, *, order,
   embedding, bidirectional induction) build on top in later stages. *)

BeginPackage["HOL`Stdlib`Int`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Auto`Arith`"
}];

intRepConst::usage  = "intRepConst[] — INT_REP : num × num → bool, the carving predicate λp. FST p = 0 ∨ SND p = 0.";
intRepDefThm::usage = "intRepDefThm — ⊢ INT_REP = (λp. FST p = 0 ∨ SND p = 0).";
intRepZeroPairThm::usage = "intRepZeroPairThm — ⊢ INT_REP (0, 0). Witness for the type definition.";
intTy::usage        = "intTy — the int type (tyApp[\"int\", {}]).";
absIntConst::usage  = "absIntConst[] — ABS_int : num × num → int.";
repIntConst::usage  = "repIntConst[] — REP_int : int → num × num.";
absRepIntThm::usage = "absRepIntThm — ⊢ ABS_int (REP_int a) = a (round-trip on int).";
repAbsIntThm::usage = "repAbsIntThm — ⊢ INT_REP r = (REP_int (ABS_int r) = r).";

intOfNumConst::usage  = "intOfNumConst[] — &ℤ : num → int, the embedding λn. ABS_int (n, 0).";
intOfNumDefThm::usage = "intOfNumDefThm — ⊢ &ℤ = (λn. ABS_int (n, 0)).";
intRepNatPairThm::usage = "intRepNatPairThm — ⊢ INT_REP (n, 0) (n free): natural pairs are canonical.";
repIntOfNumThm::usage = "repIntOfNumThm — ⊢ REP_int (&ℤ n) = (n, 0) (n free).";
intOfNumInjThm::usage = "intOfNumInjThm — ⊢ ∀m n. &ℤ m = &ℤ n ⇒ m = n.";

intRepRepThm::usage = "intRepRepThm — ⊢ INT_REP (REP_int z) (z free): REP_int lands in the carve.";
intNegConst::usage  = "intNegConst[] — intNeg : int → int, negation (swaps the representative components).";
intNegDefThm::usage = "intNegDefThm — ⊢ intNeg = (λz. ABS_int (SND (REP_int z), FST (REP_int z))).";
repIntNegThm::usage = "repIntNegThm — ⊢ REP_int (intNeg z) = (SND (REP_int z), FST (REP_int z)) (z free).";
intNegNegThm::usage = "intNegNegThm — ⊢ ∀z. intNeg (intNeg z) = z (involution).";

intCanonConst::usage  = "intCanonConst[] — intCanon : num × num → num × num, reduce a representative to canonical form.";
intCanonDefThm::usage = "intCanonDefThm — ⊢ intCanon = (λp. COND (SND p ≤ FST p) (FST p ∸ SND p, 0) (0, SND p ∸ FST p)).";
intRepCanonThm::usage = "intRepCanonThm — ⊢ INT_REP (intCanon p) (p free): canonicalization lands in the carve.";

intAddConst::usage  = "intAddConst[] — intAdd : int → int → int, addition. intAdd z w canonicalizes (FST(REP z)+FST(REP w), SND(REP z)+SND(REP w)).";
intAddDefThm::usage = "intAddDefThm — ⊢ intAdd = (λz w. ABS_int (intCanon (FST (REP_int z) + FST (REP_int w), SND (REP_int z) + SND (REP_int w)))).";
intAddCommThm::usage = "intAddCommThm — ⊢ ∀z w. intAdd z w = intAdd w z (additive commutativity).";

intCanonIdThm::usage = "intCanonIdThm — ⊢ ∀p. INT_REP p ⇒ intCanon p = p. Canonicalization is idempotent on canonical pairs.";
intAddZeroThm::usage = "intAddZeroThm — ⊢ ∀z. intAdd z (&ℤ 0) = z. Right additive identity.";
intAddNegThm::usage = "intAddNegThm — ⊢ ∀z. intAdd z (intNeg z) = &ℤ 0. Right additive inverse.";

Begin["`Private`"];

numTy = mkType["num", {}];
zeroN[] := HOL`Stdlib`Num`zeroConst[];
numPairTy = HOL`Stdlib`Pair`prodTy[numTy, numTy];
intRepTy = tyFun[numPairTy, boolTy];

(* local connective builders (Num's are in another file's Private) *)
orC[] := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
orTm[a_, b_] := mkComb[mkComb[orC[], a], b];
notOp[] := mkConst["¬", tyFun[boolTy, boolTy]];

fstNum[] := mkConst["FST", tyFun[numPairTy, numTy]];
sndNum[] := mkConst["SND", tyFun[numPairTy, numTy]];

(* the `,` constructor at the concrete num × num type *)
numPairCons[a_, b_] :=
  mkComb[mkComb[mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]], a], b];

(* INT_REP = λp. FST p = 0 ∨ SND p = 0 *)
intRepBody[] :=
  Module[{pV},
    pV = mkVar["p", numPairTy];
    mkAbs[pV, orTm[mkEq[mkComb[fstNum[], pV], zeroN[]],
                   mkEq[mkComb[sndNum[], pV], zeroN[]]]]
  ];

intRepDefThm = newDefinition[mkEq[mkVar["INT_REP", intRepTy], intRepBody[]]];

intRepConst[] := mkConst["INT_REP", intRepTy];

(* ⊢ INT_REP pTm = (FST pTm = 0 ∨ SND pTm = 0) *)
unfoldIntRep[pTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intRepDefThm, pTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ FST (0, 0) = 0 by instantiating fstPairEqThm to num × num. *)
fstZeroZeroThm =
  Module[{instTy, instAB},
    instTy = HOL`Kernel`INSTTYPE[
      {mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`fstPairEqThm];
    HOL`Kernel`INST[
      {mkVar["a", numTy] -> zeroN[], mkVar["b", numTy] -> zeroN[]},
      instTy]
  ];

(* ⊢ INT_REP (0, 0) — the witness, via the FST-disjunct. *)
intRepZeroPairThm =
  Module[{zeroPair, sndEqTm, disjThm},
    zeroPair = numPairCons[zeroN[], zeroN[]];
    sndEqTm = mkEq[mkComb[sndNum[], zeroPair], zeroN[]];
    disjThm = HOL`Bool`DISJ1[fstZeroZeroThm, sndEqTm];
    (* ⊢ FST (0,0) = 0 ∨ SND (0,0) = 0 *)
    EQMP[HOL`Equal`SYM[unfoldIntRep[zeroPair]], disjThm]
  ];

(* ============================================================ *)
(* int type via newBasicTypeDefinition                          *)
(* ============================================================ *)

{absRepIntThm, repAbsIntThm} =
  newBasicTypeDefinition["int", "ABS_int", "REP_int", intRepZeroPairThm];

intTy = mkType["int", {}];
absIntConst[] := mkConst["ABS_int", tyFun[numPairTy, intTy]];
repIntConst[] := mkConst["REP_int", tyFun[intTy, numPairTy]];

(* ============================================================ *)
(* &ℤ : num → int — the embedding n ↦ (n, 0).                    *)
(* ============================================================ *)

intOfNumTy = tyFun[numTy, intTy];

intOfNumDefThm = newDefinition[mkEq[
  mkVar["&ℤ", intOfNumTy],
  Module[{nV}, nV = mkVar["n", numTy];
    mkAbs[nV, mkComb[absIntConst[], numPairCons[nV, zeroN[]]]]]
]];

intOfNumConst[] := mkConst["&ℤ", intOfNumTy];
intOfNumTm[nTm_] := mkComb[intOfNumConst[], nTm];

(* ⊢ &ℤ n = ABS_int (n, 0) *)
unfoldIntOfNum[nTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intOfNumDefThm, nTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ SND (a, b) = b at num × num, instantiated to (nTm, mTm). *)
sndNumPairThm[aTm_, bTm_] :=
  HOL`Kernel`INST[{mkVar["a", numTy] -> aTm, mkVar["b", numTy] -> bTm},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`sndPairEqThm]];

(* ⊢ INT_REP (n, 0)  (n free) *)
intRepNatPairThm =
  Module[{nV, natPair, sndEq, fstTerm, disjThm},
    nV = mkVar["n", numTy];
    natPair = numPairCons[nV, zeroN[]];
    sndEq = sndNumPairThm[nV, zeroN[]];   (* ⊢ SND (n, 0) = 0 *)
    fstTerm = mkEq[mkComb[fstNum[], natPair], zeroN[]];
    disjThm = HOL`Bool`DISJ2[sndEq, fstTerm];   (* FST (n,0) = 0 ∨ SND (n,0) = 0 *)
    EQMP[HOL`Equal`SYM[unfoldIntRep[natPair]], disjThm]
  ];

(* ⊢ REP_int (&ℤ n) = (n, 0)  (n free) *)
repIntOfNumThm =
  Module[{nV, natPair, unfDef, rVar, repAbsInst, repEq, apRep},
    nV = mkVar["n", numTy];
    natPair = numPairCons[nV, zeroN[]];
    unfDef = unfoldIntOfNum[nV];   (* ⊢ &ℤ n = ABS_int (n, 0) *)
    rVar = concl[repAbsIntThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> natPair}, repAbsIntThm];
    (* ⊢ INT_REP (n,0) = (REP_int (ABS_int (n,0)) = (n,0)) *)
    repEq = EQMP[repAbsInst, intRepNatPairThm];
    (* ⊢ REP_int (ABS_int (n,0)) = (n,0) *)
    apRep = HOL`Equal`APTERM[repIntConst[], unfDef];
    (* ⊢ REP_int (&ℤ n) = REP_int (ABS_int (n,0)) *)
    TRANS[apRep, repEq]
  ];

(* ⊢ ∀m n. &ℤ m = &ℤ n ⇒ m = n *)
intOfNumInjThm =
  Module[{mV, nV, hyp, apRep, repM, repN, pairEq, injInst, mpInj,
          conj1, dischd, genN, genM},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    hyp = ASSUME[mkEq[intOfNumTm[mV], intOfNumTm[nV]]];   (* &ℤ m = &ℤ n *)
    apRep = HOL`Equal`APTERM[repIntConst[], hyp];
    (* ⊢ REP_int (&ℤ m) = REP_int (&ℤ n) *)
    repM = HOL`Kernel`INST[{mkVar["n", numTy] -> mV}, repIntOfNumThm];
    repN = repIntOfNumThm;
    pairEq = TRANS[TRANS[HOL`Equal`SYM[repM], apRep], repN];
    (* ⊢ (m, 0) = (n, 0) *)
    injInst = HOL`Kernel`INST[
      {mkVar["x", numTy] -> mV, mkVar["y", numTy] -> zeroN[],
       mkVar["xP", numTy] -> nV, mkVar["yP", numTy] -> zeroN[]},
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
        HOL`Stdlib`Pair`pairInjThm]];
    (* ⊢ ((m,0) = (n,0)) ⇒ (m = n ∧ 0 = 0) *)
    mpInj = HOL`Bool`MP[injInst, pairEq];
    conj1 = HOL`Bool`CONJUNCT1[mpInj];   (* ⊢ m = n *)
    dischd = HOL`Bool`DISCH[concl[hyp], conj1];
    genN = HOL`Bool`GEN[nV, dischd];
    genM = HOL`Bool`GEN[mV, genN]
  ];

(* ============================================================ *)
(* intNeg : int → int — negation by swapping representative      *)
(* components: intNeg z = ABS_int (SND (REP_int z), FST (REP_int z)). *)
(* Swapping a canonical pair stays canonical, so no recanon.     *)
(* ============================================================ *)

repIntTm[zT_] := mkComb[repIntConst[], zT];
fstOf[pT_] := mkComb[fstNum[], pT];
sndOf[pT_] := mkComb[sndNum[], pT];
swapPair[pT_] := numPairCons[sndOf[pT], fstOf[pT]];   (* (SND p, FST p) *)

(* ⊢ FST (a, b) = a at num × num *)
fstNumPairThm[aTm_, bTm_] :=
  HOL`Kernel`INST[{mkVar["a", numTy] -> aTm, mkVar["b", numTy] -> bTm},
    HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`fstPairEqThm]];

(* ⊢ INT_REP (REP_int z)  (z free): REP_int lands in the carve. *)
intRepRepThm =
  Module[{zV, repZ, rVar, repAbsInst, aVar, absRepZ, rhsThm},
    zV = mkVar["z", intTy]; repZ = repIntTm[zV];
    rVar = concl[repAbsIntThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> repZ}, repAbsIntThm];
    aVar = concl[absRepIntThm][[2]];
    absRepZ = HOL`Kernel`INST[{aVar -> zV}, absRepIntThm];
    rhsThm = HOL`Equal`APTERM[repIntConst[], absRepZ];
    EQMP[HOL`Equal`SYM[repAbsInst], rhsThm]
  ];

(* ⊢ q ∨ p  from  ⊢ p ∨ q *)
commuteDisj[disjThm_, pTm_, qTm_] :=
  HOL`Bool`DISJCASES[disjThm,
    HOL`Bool`DISJ2[ASSUME[pTm], qTm],
    HOL`Bool`DISJ1[ASSUME[qTm], pTm]];

(* ⊢ INT_REP (SND (REP_int z), FST (REP_int z))  (z free). *)
intRepSwappedThm =
  Module[{zV, repZ, sw, fstR, sndR, fstSw0, sndSw0, disjRep, comm,
          fstSwapEq, sndSwapEq, fstSwapAt0, sndSwapAt0, eqConst0,
          disjEq, swapDisj},
    zV = mkVar["z", intTy]; repZ = repIntTm[zV];
    sw = swapPair[repZ];
    fstR = fstOf[repZ]; sndR = sndOf[repZ];
    (* FST(REP z)=0 ∨ SND(REP z)=0  then commute *)
    disjRep = EQMP[unfoldIntRep[repZ], intRepRepThm];
    comm = commuteDisj[disjRep, mkEq[fstR, zeroN[]], mkEq[sndR, zeroN[]]];
    (* ⊢ SND(REP z)=0 ∨ FST(REP z)=0 *)
    (* FST(swap) = SND(REP z),  SND(swap) = FST(REP z) *)
    fstSwapEq = fstNumPairThm[sndR, fstR];   (* FST(SND R, FST R) = SND R *)
    sndSwapEq = sndNumPairThm[sndR, fstR];   (* SND(SND R, FST R) = FST R *)
    eqConst0 = mkConst["=", tyFun[numTy, tyFun[numTy, boolTy]]];
    (* (FST swap = 0) = (SND R = 0) *)
    fstSwapAt0 = HOL`Equal`APTHM[
      HOL`Equal`APTERM[eqConst0, fstSwapEq], zeroN[]];
    sndSwapAt0 = HOL`Equal`APTHM[
      HOL`Equal`APTERM[eqConst0, sndSwapEq], zeroN[]];
    (* ⊢ (SND R=0 ∨ FST R=0) = (FST swap=0 ∨ SND swap=0) *)
    disjEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[orC[], HOL`Equal`SYM[fstSwapAt0]],
      HOL`Equal`SYM[sndSwapAt0]];
    swapDisj = EQMP[disjEq, comm];
    (* ⊢ FST(swap)=0 ∨ SND(swap)=0 *)
    EQMP[HOL`Equal`SYM[unfoldIntRep[sw]], swapDisj]
  ];

intNegTy = tyFun[intTy, intTy];

intNegDefThm = newDefinition[mkEq[
  mkVar["intNeg", intNegTy],
  Module[{zV}, zV = mkVar["z", intTy];
    mkAbs[zV, mkComb[absIntConst[], swapPair[repIntTm[zV]]]]]
]];

intNegConst[] := mkConst["intNeg", intNegTy];
intNegTm[zT_] := mkComb[intNegConst[], zT];

(* ⊢ intNeg z = ABS_int (SND (REP_int z), FST (REP_int z)) *)
unfoldIntNeg[zT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intNegDefThm, zT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ REP_int (intNeg z) = (SND (REP_int z), FST (REP_int z))  (z free). *)
repIntNegThm =
  Module[{zV, repZ, sw, unfNeg, rVar, repAbsInst, repEq, apRep},
    zV = mkVar["z", intTy]; repZ = repIntTm[zV]; sw = swapPair[repZ];
    unfNeg = unfoldIntNeg[zV];   (* intNeg z = ABS_int (swap) *)
    rVar = concl[repAbsIntThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> sw}, repAbsIntThm];
    (* INT_REP(swap) = (REP_int(ABS_int swap) = swap) *)
    repEq = EQMP[repAbsInst, intRepSwappedThm];
    (* REP_int(ABS_int swap) = swap *)
    apRep = HOL`Equal`APTERM[repIntConst[], unfNeg];
    (* REP_int(intNeg z) = REP_int(ABS_int swap) *)
    TRANS[apRep, repEq]
  ];

(* ⊢ ∀z. intNeg (intNeg z) = z *)
intNegNegThm =
  Module[{zV, repZ, sw, negZ, repNeg, repNegNeg, fstNeg, sndNeg,
          unfNegNeg, swapBack, absBack, absRepZ, aVar, genZ},
    zV = mkVar["z", intTy]; repZ = repIntTm[zV]; sw = swapPair[repZ];
    negZ = intNegTm[zV];
    (* REP_int (intNeg z) = (SND R, FST R) = sw *)
    repNeg = repIntNegThm;
    (* intNeg (intNeg z) = ABS_int (SND (REP (intNeg z)), FST (REP (intNeg z))) *)
    unfNegNeg = unfoldIntNeg[negZ];
    (* SND (REP (intNeg z)) = SND sw = FST R ;  FST (REP (intNeg z)) = FST sw = SND R *)
    fstNeg = HOL`Equal`APTERM[fstNum[], repNeg];   (* FST(REP(intNeg z)) = FST sw *)
    sndNeg = HOL`Equal`APTERM[sndNum[], repNeg];   (* SND(REP(intNeg z)) = SND sw *)
    (* swap (REP (intNeg z)) = (SND(REP(intNeg z)), FST(REP(intNeg z)))
                             = (SND sw, FST sw) = (FST R, SND R) *)
    swapBack = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]],
        TRANS[sndNeg, sndNumPairThm[sndOf[repZ], fstOf[repZ]]]],
      TRANS[fstNeg, fstNumPairThm[sndOf[repZ], fstOf[repZ]]]];
    (* ⊢ (SND(REP(intNeg z)), FST(REP(intNeg z))) = (FST R, SND R) *)
    (* and (FST R, SND R) = REP_int z by surjective pairing *)
    swapBack = TRANS[swapBack, HOL`Bool`ISPEC[repZ, pairSurjThm]];
    (* ⊢ swap(REP(intNeg z)) = REP_int z *)
    absBack = HOL`Equal`APTERM[absIntConst[], swapBack];
    (* ABS_int(swap(REP(intNeg z))) = ABS_int(REP_int z) *)
    aVar = concl[absRepIntThm][[2]];
    absRepZ = HOL`Kernel`INST[{aVar -> zV}, absRepIntThm];   (* ABS_int(REP z) = z *)
    genZ = HOL`Bool`GEN[zV, TRANS[unfNegNeg, TRANS[absBack, absRepZ]]]
  ];

(* ============================================================ *)
(* intCanon : num × num → num × num — canonical form.            *)
(*   intCanon p = COND (SND p ≤ FST p)                           *)
(*                     (FST p ∸ SND p, 0)   [p ≥ 0]              *)
(*                     (0, SND p ∸ FST p)   [p < 0]              *)
(* ============================================================ *)

falseTm[] := mkConst["F", boolTy];
leqNum[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
monusNum[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`monusConst[], a], b];

(* from Γ ⊢ ¬p derive Γ ⊢ p = F *)
eqFIntro[notTh_] :=
  Module[{pTm, pToF, fToP},
    pTm = concl[notTh][[2]];
    pToF = HOL`Bool`MP[HOL`Bool`NOTELIM[notTh], ASSUME[pTm]];   (* Γ, p ⊢ F *)
    fToP = HOL`Bool`CONTR[pTm, ASSUME[falseTm[]]];   (* F ⊢ p *)
    HOL`Equal`SYM[HOL`Kernel`DEDUCTANTISYM[pToF, fToP]]   (* Γ ⊢ p = F *)
  ];

intCanonTy = tyFun[numPairTy, numPairTy];

intCanonBranchT[fp_, sp_] := numPairCons[monusNum[fp, sp], zeroN[]];
intCanonBranchF[fp_, sp_] := numPairCons[zeroN[], monusNum[sp, fp]];

intCanonDefThm = newDefinition[mkEq[
  mkVar["intCanon", intCanonTy],
  Module[{pV, fp, sp},
    pV = mkVar["p", numPairTy]; fp = fstOf[pV]; sp = sndOf[pV];
    mkAbs[pV,
      mkComb[mkComb[mkComb[condConst[numPairTy], leqNum[sp, fp]],
        intCanonBranchT[fp, sp]], intCanonBranchF[fp, sp]]]]
]];

intCanonConst[] := mkConst["intCanon", intCanonTy];

(* ⊢ intCanon p = COND (SND p ≤ FST p) (FST p ∸ SND p, 0) (0, SND p ∸ FST p) *)
unfoldIntCanon[pT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intCanonDefThm, pT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ COND gv bT bF = (bT if gEqTF rewrites gv→T, else bF) — given an
   equation gEqV : ⊢ gv = T (or = F), rewrite the guard and fire condT/F. *)
condRewrite[gEqV_, bT_, bF_, branchThm_] :=
  Module[{rw},
    rw = HOL`Equal`APTHM[HOL`Equal`APTHM[
      HOL`Equal`APTERM[condConst[numPairTy], gEqV], bT], bF];
    TRANS[rw, branchThm]
  ];

(* INT_REP of a pair whose SND is 0 (the +n branch). *)
intRepBySnd[pairTm_, sndZeroThm_] :=
  EQMP[HOL`Equal`SYM[unfoldIntRep[pairTm]],
    HOL`Bool`DISJ2[sndZeroThm, mkEq[mkComb[fstNum[], pairTm], zeroN[]]]];

(* INT_REP of a pair whose FST is 0 (the −n branch). *)
intRepByFst[pairTm_, fstZeroThm_] :=
  EQMP[HOL`Equal`SYM[unfoldIntRep[pairTm]],
    HOL`Bool`DISJ1[fstZeroThm, mkEq[mkComb[sndNum[], pairTm], zeroN[]]]];

(* ⊢ INT_REP (intCanon p)  (p free) *)
intRepCanonThm =
  Module[{pV, fp, sp, guard, bT, bF, canonEq, condTI, condFI, em,
          caseT, caseF},
    pV = mkVar["p", numPairTy]; fp = fstOf[pV]; sp = sndOf[pV];
    guard = leqNum[sp, fp];
    bT = intCanonBranchT[fp, sp]; bF = intCanonBranchF[fp, sp];
    canonEq = unfoldIntCanon[pV];
    condTI = HOL`Bool`SPEC[bF, HOL`Bool`SPEC[bT,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numPairTy}, condTThm]]];
    (* ⊢ COND T bT bF = bT *)
    condFI = HOL`Bool`SPEC[bF, HOL`Bool`SPEC[bT,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numPairTy}, condFThm]]];
    (* ⊢ COND F bT bF = bF *)
    em = HOL`Bool`EXCLUDEDMIDDLE[guard];

    caseT = Module[{gEqT, canonT, sndBT, repBT},
      gEqT = HOL`Bool`EQTINTRO[ASSUME[guard]];   (* guard = T *)
      canonT = TRANS[canonEq, condRewrite[gEqT, bT, bF, condTI]];
      (* (guard) ⊢ intCanon p = bT *)
      sndBT = sndNumPairThm[monusNum[fp, sp], zeroN[]];   (* SND bT = 0 *)
      repBT = intRepBySnd[bT, sndBT];   (* INT_REP bT *)
      EQMP[HOL`Equal`SYM[
        HOL`Equal`APTERM[intRepConst[], canonT]], repBT]
      (* (guard) ⊢ INT_REP (intCanon p) *)
    ];

    caseF = Module[{gEqF, canonF, fstBF, repBF},
      gEqF = eqFIntro[ASSUME[mkComb[notOp[], guard]]];   (* guard = F *)
      canonF = TRANS[canonEq, condRewrite[gEqF, bT, bF, condFI]];
      (* (¬guard) ⊢ intCanon p = bF *)
      fstBF = fstNumPairThm[zeroN[], monusNum[sp, fp]];   (* FST bF = 0 *)
      repBF = intRepByFst[bF, fstBF];   (* INT_REP bF *)
      EQMP[HOL`Equal`SYM[
        HOL`Equal`APTERM[intRepConst[], canonF]], repBF]
    ];

    HOL`Bool`DISJCASES[em, caseT, caseF]
  ];

(* ============================================================ *)
(* intAdd : int → int → int                                      *)
(*   intAdd z w = ABS_int (intCanon (FST(REP z) + FST(REP w),    *)
(*                                   SND(REP z) + SND(REP w)))   *)
(* ============================================================ *)

intAddTy = tyFun[intTy, tyFun[intTy, intTy]];

plusN[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], a], b];

intAddPairTm[zT_, wT_] :=
  Module[{rz, rw},
    rz = repIntTm[zT]; rw = repIntTm[wT];
    numPairCons[plusN[fstOf[rz], fstOf[rw]], plusN[sndOf[rz], sndOf[rw]]]
  ];

intAddDefThm = newDefinition[mkEq[
  mkVar["intAdd", intAddTy],
  Module[{zV, wV},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    mkAbs[zV, mkAbs[wV,
      mkComb[absIntConst[],
        mkComb[intCanonConst[], intAddPairTm[zV, wV]]]]]]
]];

intAddConst[] := mkConst["intAdd", intAddTy];
intAddTm[zT_, wT_] := mkComb[mkComb[intAddConst[], zT], wT];

(* ⊢ intAdd z w = ABS_int (intCanon (F(R z)+F(R w), S(R z)+S(R w))) *)
unfoldIntAdd[zT_, wT_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[intAddDefThm, zT];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, wT];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ ∀z w. intAdd z w = intAdd w z *)
intAddCommThm =
  Module[{zV, wV, rz, rw, fz, sz, fw, sw, ufZW, ufWZ,
          fstComm, sndComm, commaC, pairEq, canonEq, absEq, genW, genZ},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    rz = repIntTm[zV]; rw = repIntTm[wV];
    fz = fstOf[rz]; sz = sndOf[rz]; fw = fstOf[rw]; sw = sndOf[rw];
    ufZW = unfoldIntAdd[zV, wV];
    ufWZ = unfoldIntAdd[wV, zV];
    (* num addCommThm: ∀m n. m+n = n+m; SPEC m:=fz, n:=fw → fz+fw = fw+fz *)
    fstComm = HOL`Bool`SPEC[fw, HOL`Bool`SPEC[fz, HOL`Stdlib`Num`addCommThm]];
    sndComm = HOL`Bool`SPEC[sw, HOL`Bool`SPEC[sz, HOL`Stdlib`Num`addCommThm]];
    commaC = mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]];
    pairEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaC, fstComm], sndComm];
    (* ⊢ (fz+fw, sz+sw) = (fw+fz, sw+sz) *)
    canonEq = HOL`Equal`APTERM[intCanonConst[], pairEq];
    absEq = HOL`Equal`APTERM[absIntConst[], canonEq];
    (* ⊢ ABS_int(intCanon(fz+fw, sz+sw)) = ABS_int(intCanon(fw+fz, sw+sz)) *)
    genW = HOL`Bool`GEN[wV, TRANS[ufZW, TRANS[absEq, HOL`Equal`SYM[ufWZ]]]];
    genZ = HOL`Bool`GEN[zV, genW]
  ];

(* ============================================================ *)
(* intCanonIdThm: ⊢ ∀p. INT_REP p ⇒ intCanon p = p.              *)
(*                                                              *)
(* Case-split on the carve disjunction FST p = 0 ∨ SND p = 0.    *)
(*   SND p = 0: guard 0 ≤ FST p is T → canon = (FST ∸ 0, 0) =    *)
(*               (FST, 0), and p = (FST, 0) via surj + SND→0.    *)
(*   FST p = 0: split on guard.                                  *)
(*     guard T: SND ≤ 0 + 0 ≤ SND ⇒ SND = 0; both zero. canon =  *)
(*              (0 ∸ 0, 0) = (0, 0); p = (0, 0).                 *)
(*     guard F: canon = (0, SND ∸ 0) = (0, SND); p = (0, SND).   *)
(* ============================================================ *)

commaNumC[] := mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]];

intCanonIdThm =
  Module[{pV, fp, sp, guard, bT, bF, canonEq, condTI, condFI,
          leqC, monusC, intRepHyp, disjFS, surj, caseSnd0, caseFst0,
          mainCase, dischd, genP},
    pV = mkVar["p", numPairTy]; fp = fstOf[pV]; sp = sndOf[pV];
    guard = leqNum[sp, fp];
    bT = intCanonBranchT[fp, sp]; bF = intCanonBranchF[fp, sp];
    canonEq = unfoldIntCanon[pV];
    condTI = HOL`Bool`SPEC[bF, HOL`Bool`SPEC[bT,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numPairTy}, condTThm]]];
    condFI = HOL`Bool`SPEC[bF, HOL`Bool`SPEC[bT,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numPairTy}, condFThm]]];
    leqC = HOL`Stdlib`Num`leqConst[];
    monusC = HOL`Stdlib`Num`monusConst[];
    intRepHyp = ASSUME[mkComb[intRepConst[], pV]];
    disjFS = EQMP[unfoldIntRep[pV], intRepHyp];
    surj = HOL`Bool`ISPEC[pV, HOL`Stdlib`Pair`pairSurjThm];

    caseSnd0 =
      Module[{sEq0, guardRw, leqFp0, guardThm, gEqT, canonAtBT,
              monusFpRw, bTRw, pRw},
        sEq0 = ASSUME[mkEq[sp, zeroN[]]];
        guardRw = HOL`Equal`APTHM[HOL`Equal`APTERM[leqC, sEq0], fp];
        leqFp0 = HOL`Bool`SPEC[fp, HOL`Stdlib`Num`leqZeroThm];
        guardThm = EQMP[HOL`Equal`SYM[guardRw], leqFp0];
        gEqT = HOL`Bool`EQTINTRO[guardThm];
        canonAtBT = TRANS[canonEq, condRewrite[gEqT, bT, bF, condTI]];
        monusFpRw = TRANS[
          HOL`Equal`APTERM[mkComb[monusC, fp], sEq0],
          HOL`Bool`SPEC[fp, HOL`Stdlib`Num`monusZeroThm]];
        bTRw = HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[commaNumC[], monusFpRw], REFL[zeroN[]]];
        pRw = TRANS[HOL`Equal`SYM[surj],
          HOL`Kernel`MKCOMB[
            HOL`Equal`APTERM[commaNumC[], REFL[fp]], sEq0]];
        TRANS[TRANS[canonAtBT, bTRw], HOL`Equal`SYM[pRw]]
      ];

    caseFst0 =
      Module[{fEq0, em, caseGT, caseGF},
        fEq0 = ASSUME[mkEq[fp, zeroN[]]];
        em = HOL`Bool`EXCLUDEDMIDDLE[guard];

        caseGT =
          Module[{gHyp, guardRw0, sndLeq0, sndEq0, gEqT, canonAtBT,
                  monusRw, bTRw, pRw},
            gHyp = ASSUME[guard];
            guardRw0 = HOL`Equal`APTERM[mkComb[leqC, sp], fEq0];
            sndLeq0 = EQMP[guardRw0, gHyp];
            sndEq0 = HOL`Bool`MP[
              HOL`Bool`MP[
                HOL`Bool`SPEC[zeroN[],
                  HOL`Bool`SPEC[sp, HOL`Stdlib`Num`leqAntisymThm]],
                sndLeq0],
              HOL`Bool`SPEC[sp, HOL`Stdlib`Num`leqZeroThm]];
            gEqT = HOL`Bool`EQTINTRO[gHyp];
            canonAtBT = TRANS[canonEq, condRewrite[gEqT, bT, bF, condTI]];
            monusRw = TRANS[
              HOL`Equal`APTHM[HOL`Equal`APTERM[monusC, fEq0], sp],
              HOL`Bool`SPEC[sp, HOL`Stdlib`Num`zeroMonusThm]];
            bTRw = HOL`Kernel`MKCOMB[
              HOL`Equal`APTERM[commaNumC[], monusRw], REFL[zeroN[]]];
            pRw = TRANS[HOL`Equal`SYM[surj],
              HOL`Kernel`MKCOMB[
                HOL`Equal`APTERM[commaNumC[], fEq0], sndEq0]];
            TRANS[TRANS[canonAtBT, bTRw], HOL`Equal`SYM[pRw]]
          ];

        caseGF =
          Module[{notGHyp, gEqF, canonAtBF, monusRw, bFRw, pRw},
            notGHyp = ASSUME[mkComb[notOp[], guard]];
            gEqF = eqFIntro[notGHyp];
            canonAtBF = TRANS[canonEq, condRewrite[gEqF, bT, bF, condFI]];
            monusRw = TRANS[
              HOL`Equal`APTERM[mkComb[monusC, sp], fEq0],
              HOL`Bool`SPEC[sp, HOL`Stdlib`Num`monusZeroThm]];
            bFRw = HOL`Kernel`MKCOMB[
              HOL`Equal`APTERM[commaNumC[], REFL[zeroN[]]], monusRw];
            pRw = TRANS[HOL`Equal`SYM[surj],
              HOL`Kernel`MKCOMB[
                HOL`Equal`APTERM[commaNumC[], fEq0], REFL[sp]]];
            TRANS[TRANS[canonAtBF, bFRw], HOL`Equal`SYM[pRw]]
          ];

        HOL`Bool`DISJCASES[em, caseGT, caseGF]
      ];

    mainCase = HOL`Bool`DISJCASES[disjFS, caseFst0, caseSnd0];
    dischd = HOL`Bool`DISCH[concl[intRepHyp], mainCase];
    genP = HOL`Bool`GEN[pV, dischd]
  ];

(* ============================================================ *)
(* intAddZeroThm: ⊢ ∀z. intAdd z (&ℤ 0) = z (right identity).    *)
(*                                                              *)
(* REP(&ℤ 0) = (0,0) ⇒ FST/SND = 0 ⇒ FRz+0 = FRz, SRz+0 = SRz ⇒  *)
(* the pair becomes (FRz, SRz) = REP z (surj) ⇒ canon(REP z) =   *)
(* REP z (intCanonId + intRepRep) ⇒ ABS_int(REP z) = z.          *)
(* ============================================================ *)

intAddZeroThm =
  Module[{zV, rz, fz, sz, rzero, ufAdd, repAtZero, fZero, sZero,
          plusC, fstSimp, sndSimp, pairSimp, canonOfPair, surj,
          canonOfSurj, pVarCanon, canonIdInst, canonRepZ,
          aVarAbsRep, absRepZ, step1, step2, step3, step4, genZ},
    zV = mkVar["z", intTy];
    rz = repIntTm[zV]; fz = fstOf[rz]; sz = sndOf[rz];
    rzero = mkComb[intOfNumConst[], zeroN[]];
    ufAdd = unfoldIntAdd[zV, rzero];
    (* REP_int (&ℤ 0) = (0, 0) via repIntOfNumThm INST n→0 *)
    repAtZero = HOL`Kernel`INST[{mkVar["n", numTy] -> zeroN[]}, repIntOfNumThm];
    fZero = TRANS[HOL`Equal`APTERM[fstNum[], repAtZero],
      fstNumPairThm[zeroN[], zeroN[]]];
    sZero = TRANS[HOL`Equal`APTERM[sndNum[], repAtZero],
      sndNumPairThm[zeroN[], zeroN[]]];
    plusC = HOL`Stdlib`Num`plusConst[];
    fstSimp = TRANS[
      HOL`Equal`APTERM[mkComb[plusC, fz], fZero],
      HOL`Bool`SPEC[fz, HOL`Stdlib`Num`plusZeroEqThm]];
    sndSimp = TRANS[
      HOL`Equal`APTERM[mkComb[plusC, sz], sZero],
      HOL`Bool`SPEC[sz, HOL`Stdlib`Num`plusZeroEqThm]];
    pairSimp = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[], fstSimp], sndSimp];
    canonOfPair = HOL`Equal`APTERM[intCanonConst[], pairSimp];
    surj = HOL`Bool`ISPEC[rz, HOL`Stdlib`Pair`pairSurjThm];
    canonOfSurj = HOL`Equal`APTERM[intCanonConst[], surj];
    (* intCanonIdThm at p := REP z, MP with intRepRepThm *)
    pVarCanon = concl[intCanonIdThm][[2, 1]];   (* the bound p in ∀p. ... *)
    canonIdInst = HOL`Bool`SPEC[rz, intCanonIdThm];
    canonRepZ = HOL`Bool`MP[canonIdInst, intRepRepThm];
    aVarAbsRep = concl[absRepIntThm][[2]];
    absRepZ = HOL`Kernel`INST[{aVarAbsRep -> zV}, absRepIntThm];

    step1 = TRANS[ufAdd, HOL`Equal`APTERM[absIntConst[], canonOfPair]];
    step2 = TRANS[step1, HOL`Equal`APTERM[absIntConst[], canonOfSurj]];
    step3 = TRANS[step2, HOL`Equal`APTERM[absIntConst[], canonRepZ]];
    step4 = TRANS[step3, absRepZ];
    genZ = HOL`Bool`GEN[zV, step4]
  ];

(* ============================================================ *)
(* intAddNegThm: ⊢ ∀z. intAdd z (intNeg z) = &ℤ 0 (right inverse). *)
(*                                                              *)
(* REP(intNeg z) = (SND R, FST R) (repIntNeg), so the summed     *)
(* pair is (FST R + SND R, SND R + FST R); both components equal  *)
(* c := FST R + SND R (addComm on the second). intCanon (c, c)    *)
(* has guard c ≤ c = T, branch (c ∸ c, 0) = (0, 0) (monusSelf);   *)
(* ABS_int (0, 0) = &ℤ 0 (unfold &ℤ at 0).                        *)
(* ============================================================ *)

intAddNegThm =
  Module[{zV, rz, fz, sz, negZ, ufAdd, repNeg, fstNegEq, sndNegEq,
          plusC, leqC, monusC, cTm, ccPair, fstSum, sndSum0, commEq,
          sndSum, pairSimp, canonOfPair, canonEq, fstCC, sndCC,
          leqReflC, guardThm, gEqT, bT, bF, condTI, canonAtBT,
          monusRw, bTRw, canonZero, canonFull, absStep, zeroEq, genZ},
    zV = mkVar["z", intTy];
    rz = repIntTm[zV]; fz = fstOf[rz]; sz = sndOf[rz];
    negZ = intNegTm[zV];
    ufAdd = unfoldIntAdd[zV, negZ];
    (* ⊢ intAdd z (intNeg z) = ABS_int(intCanon(FRz+FR(neg), SRz+SR(neg))) *)
    repNeg = repIntNegThm;   (* REP(intNeg z) = (SND R, FST R) *)
    fstNegEq = TRANS[HOL`Equal`APTERM[fstNum[], repNeg],
      fstNumPairThm[sz, fz]];   (* FST(REP(intNeg z)) = SND R = sz *)
    sndNegEq = TRANS[HOL`Equal`APTERM[sndNum[], repNeg],
      sndNumPairThm[sz, fz]];   (* SND(REP(intNeg z)) = FST R = fz *)
    plusC = HOL`Stdlib`Num`plusConst[];
    leqC = HOL`Stdlib`Num`leqConst[];
    monusC = HOL`Stdlib`Num`monusConst[];
    cTm = plusN[fz, sz];   (* c = FST R + SND R *)
    ccPair = numPairCons[cTm, cTm];
    (* first summand: fz + FST(REP(neg)) = fz + sz = c *)
    fstSum = HOL`Equal`APTERM[mkComb[plusC, fz], fstNegEq];
    (* second summand: sz + SND(REP(neg)) = sz + fz = (comm) fz + sz = c *)
    sndSum0 = HOL`Equal`APTERM[mkComb[plusC, sz], sndNegEq];
    commEq = HOL`Bool`SPEC[fz, HOL`Bool`SPEC[sz, HOL`Stdlib`Num`addCommThm]];
    sndSum = TRANS[sndSum0, commEq];
    pairSimp = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[], fstSum], sndSum];
    (* ⊢ (FRz+FR(neg), SRz+SR(neg)) = (c, c) *)
    canonOfPair = HOL`Equal`APTERM[intCanonConst[], pairSimp];
    canonEq = unfoldIntCanon[ccPair];   (* intCanon(c,c) = COND … *)
    fstCC = fstNumPairThm[cTm, cTm];   (* FST(c,c) = c *)
    sndCC = sndNumPairThm[cTm, cTm];   (* SND(c,c) = c *)
    leqReflC = HOL`Bool`SPEC[cTm, HOL`Stdlib`Num`leqReflThm];   (* c ≤ c *)
    (* guard SND(c,c) ≤ FST(c,c) from c ≤ c by un-simplifying both args *)
    guardThm = EQMP[
      HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[leqC, HOL`Equal`SYM[sndCC]],
        HOL`Equal`SYM[fstCC]],
      leqReflC];
    gEqT = HOL`Bool`EQTINTRO[guardThm];
    bT = intCanonBranchT[fstOf[ccPair], sndOf[ccPair]];
    bF = intCanonBranchF[fstOf[ccPair], sndOf[ccPair]];
    condTI = HOL`Bool`SPEC[bF, HOL`Bool`SPEC[bT,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numPairTy}, condTThm]]];
    canonAtBT = TRANS[canonEq, condRewrite[gEqT, bT, bF, condTI]];
    (* ⊢ intCanon(c,c) = (FST(c,c) ∸ SND(c,c), 0) *)
    monusRw = TRANS[
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[monusC, fstCC], sndCC],
      HOL`Bool`SPEC[cTm, HOL`Stdlib`Num`monusSelfThm]];
    (* ⊢ FST(c,c) ∸ SND(c,c) = c ∸ c = 0 *)
    bTRw = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[], monusRw], REFL[zeroN[]]];
    canonZero = TRANS[canonAtBT, bTRw];   (* intCanon(c,c) = (0,0) *)
    canonFull = TRANS[canonOfPair, canonZero];
    absStep = HOL`Equal`APTERM[absIntConst[], canonFull];
    (* ⊢ ABS_int(intCanon(…)) = ABS_int(0,0) *)
    zeroEq = unfoldIntOfNum[zeroN[]];   (* &ℤ 0 = ABS_int(0,0) *)
    genZ = HOL`Bool`GEN[zV,
      TRANS[ufAdd, TRANS[absStep, HOL`Equal`SYM[zeroEq]]]]
  ];

End[];
EndPackage[];
