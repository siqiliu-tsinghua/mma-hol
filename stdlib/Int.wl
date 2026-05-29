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

End[];
EndPackage[];
