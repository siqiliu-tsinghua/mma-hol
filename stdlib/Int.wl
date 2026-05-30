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
canonEquivThm::usage = "canonEquivThm — ⊢ ∀p. FST (intCanon p) + SND p = FST p + SND (intCanon p). intCanon p is Grothendieck-equivalent to p.";
canonInjThm::usage = "canonInjThm — ⊢ ∀p q. INT_REP p ⇒ INT_REP q ⇒ FST p + SND q = FST q + SND p ⇒ p = q. Canonical representatives are unique within an equivalence class.";
canonRespectsThm::usage = "canonRespectsThm — ⊢ ∀a b c d. a + d = c + b ⇒ intCanon (a, b) = intCanon (c, d). intCanon depends only on the equivalence class.";
repIntAddThm::usage = "repIntAddThm — ⊢ ∀z w. REP_int (intAdd z w) = intCanon (FST (REP_int z) + FST (REP_int w), SND (REP_int z) + SND (REP_int w)). Characterizes intAdd's representative.";
intAddAssocThm::usage = "intAddAssocThm — ⊢ ∀z w v. intAdd (intAdd z w) v = intAdd z (intAdd w v). Additive associativity.";

intSuccConst::usage  = "intSuccConst[] — intSucc : int → int, successor (z ↦ intAdd z (&ℤ 1)).";
intSuccDefThm::usage = "intSuccDefThm — ⊢ intSucc = (λz. intAdd z (&ℤ 1)).";
intPredConst::usage  = "intPredConst[] — intPred : int → int, predecessor (z ↦ intAdd z (intNeg (&ℤ 1))).";
intPredDefThm::usage = "intPredDefThm — ⊢ intPred = (λz. intAdd z (intNeg (&ℤ 1))).";
intPredSuccThm::usage = "intPredSuccThm — ⊢ ∀z. intPred (intSucc z) = z.";
intSuccPredThm::usage = "intSuccPredThm — ⊢ ∀z. intSucc (intPred z) = z.";

intMulConst::usage  = "intMulConst[] — intMul : int → int → int, multiplication. (a−b)(c−d) = (ac+bd)−(ad+bc).";
intMulDefThm::usage = "intMulDefThm — ⊢ intMul = (λz w. ABS_int (intCanon (FST(REP z)*FST(REP w) + SND(REP z)*SND(REP w), FST(REP z)*SND(REP w) + SND(REP z)*FST(REP w)))).";
repIntMulThm::usage = "repIntMulThm — ⊢ ∀z w. REP_int (intMul z w) = intCanon (FST(REP z)*FST(REP w) + SND(REP z)*SND(REP w), FST(REP z)*SND(REP w) + SND(REP z)*FST(REP w)).";
intMulCommThm::usage = "intMulCommThm — ⊢ ∀z w. intMul z w = intMul w z.";
intMulOneThm::usage = "intMulOneThm — ⊢ ∀z. intMul z (&ℤ (SUC 0)) = z. Right multiplicative identity.";
intMulZeroThm::usage = "intMulZeroThm — ⊢ ∀z. intMul z (&ℤ 0) = &ℤ 0. Right absorbing element.";
intMulDistribThm::usage = "intMulDistribThm — ⊢ ∀z w v. intMul z (intAdd w v) = intAdd (intMul z w) (intMul z v). Left distributivity of intMul over intAdd.";
intMulAssocThm::usage = "intMulAssocThm — ⊢ ∀z w v. intMul (intMul z w) v = intMul z (intMul w v). Multiplicative associativity.";
intMulEqZeroThm::usage = "intMulEqZeroThm — ⊢ ∀z w. intMul z w = &ℤ 0 ⇒ z = &ℤ 0 ∨ w = &ℤ 0. ℤ has no zero divisors (integral domain).";

intLeConst::usage  = "intLeConst[] — intLe : int → int → bool, order. intLe z w ⟺ FST(REP z) + SND(REP w) ≤ FST(REP w) + SND(REP z).";
intLeDefThm::usage = "intLeDefThm — ⊢ intLe = (λz w. FST(REP z) + SND(REP w) ≤ FST(REP w) + SND(REP z)).";
intLeReflThm::usage = "intLeReflThm — ⊢ ∀z. intLe z z.";
intLeAntisymThm::usage = "intLeAntisymThm — ⊢ ∀z w. intLe z w ⇒ intLe w z ⇒ z = w.";
intLeTransThm::usage = "intLeTransThm — ⊢ ∀z w v. intLe z w ⇒ intLe w v ⇒ intLe z v.";
intLeTotalThm::usage = "intLeTotalThm — ⊢ ∀z w. intLe z w ∨ intLe w z.";
intLtConst::usage  = "intLtConst[] — intLt : int → int → bool, strict order. intLt z w ⟺ FST(REP z) + SND(REP w) < FST(REP w) + SND(REP z).";
intLtDefThm::usage = "intLtDefThm — ⊢ intLt = (λz w. FST(REP z) + SND(REP w) < FST(REP w) + SND(REP z)).";
intLtNotLeThm::usage = "intLtNotLeThm — ⊢ ∀z w. intLt z w = ¬ (intLe w z).";
intLeAddMonoThm::usage = "intLeAddMonoThm — ⊢ ∀z w u. intLe z w ⇒ intLe (intAdd z u) (intAdd w u). Additive monotonicity.";
intLeNegThm::usage = "intLeNegThm — ⊢ ∀z w. intLe z w ⇒ intLe (intNeg w) (intNeg z). Negation reverses order.";
intLeMulNonnegThm::usage = "intLeMulNonnegThm — ⊢ ∀z w u. intLe (&ℤ 0) u ⇒ intLe z w ⇒ intLe (intMul u z) (intMul u w). Monotonicity of intMul by a nonnegative factor.";

intOfNumAddThm::usage = "intOfNumAddThm — ⊢ ∀m n. &ℤ (m + n) = intAdd (&ℤ m) (&ℤ n). &ℤ is an additive homomorphism.";
intOfNumMulThm::usage = "intOfNumMulThm — ⊢ ∀m n. &ℤ (m * n) = intMul (&ℤ m) (&ℤ n). &ℤ is a multiplicative homomorphism.";
intOfNumLeThm::usage = "intOfNumLeThm — ⊢ ∀m n. intLe (&ℤ m) (&ℤ n) = (m ≤ n). &ℤ is an order embedding.";
intAbsConst::usage  = "intAbsConst[] — intAbs : int → int, absolute value (z ↦ &ℤ (FST(REP z) + SND(REP z)); one component is 0 so the sum is |z|).";
intAbsDefThm::usage = "intAbsDefThm — ⊢ intAbs = (λz. &ℤ (FST (REP_int z) + SND (REP_int z))).";
intAbsNumThm::usage = "intAbsNumThm — ⊢ ∀n. intAbs (&ℤ n) = &ℤ n.";
intAbsNegThm::usage = "intAbsNegThm — ⊢ ∀z. intAbs (intNeg z) = intAbs z.";
intAbsNonnegThm::usage = "intAbsNonnegThm — ⊢ ∀z. intLe (&ℤ 0) (intAbs z).";

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

(* ============================================================ *)
(* Associativity support: the equivalence-class machinery.       *)
(*                                                              *)
(* A pair (a,b) stands for a−b; (a,b) and (c,d) are equivalent   *)
(* (≈) iff a+d = c+b. intCanon maps each pair to THE canonical   *)
(* representative of its class. Three facts drive associativity: *)
(*   canonEquivThm    — intCanon p ≈ p.                          *)
(*   canonInjThm      — equivalent canonical pairs are equal.    *)
(*   canonRespectsThm — equivalent pairs canonicalize equally.   *)
(* The num-level linear glue is discharged by ARITH (loaded      *)
(* right after Num.wl), with FST/SND of opaque pairs abstracted  *)
(* to atoms.                                                     *)
(* ============================================================ *)

impliesTm[xTm_, yTm_] := mkComb[mkComb[
  mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], xTm], yTm];

(* ⊢ ∀p. FST (intCanon p) + SND p = FST p + SND (intCanon p) *)
canonEquivThm =
  Module[{pV, fp, sp, guard, bT, bF, canonEq, condTI, condFI,
          plusC, sucC, em, caseT, caseF},
    pV = mkVar["p", numPairTy]; fp = fstOf[pV]; sp = sndOf[pV];
    guard = leqNum[sp, fp];
    bT = intCanonBranchT[fp, sp]; bF = intCanonBranchF[fp, sp];
    canonEq = unfoldIntCanon[pV];
    condTI = HOL`Bool`SPEC[bF, HOL`Bool`SPEC[bT,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numPairTy}, condTThm]]];
    condFI = HOL`Bool`SPEC[bF, HOL`Bool`SPEC[bT,
      HOL`Kernel`INSTTYPE[{mkVarType["A"] -> numPairTy}, condFThm]]];
    plusC = HOL`Stdlib`Num`plusConst[];
    sucC = HOL`Stdlib`Num`sucConst[];
    em = HOL`Bool`EXCLUDEDMIDDLE[guard];

    caseT =
      Module[{gHyp, gEqT, canonT, fstCanon, sndCanon, lhsStep, monusFact,
              commFact, lhsToFp, lhsEqFp, rhsStep, rhsEqFp},
        gHyp = ASSUME[guard];
        gEqT = HOL`Bool`EQTINTRO[gHyp];
        canonT = TRANS[canonEq, condRewrite[gEqT, bT, bF, condTI]];
        fstCanon = TRANS[HOL`Equal`APTERM[fstNum[], canonT],
          fstNumPairThm[monusNum[fp, sp], zeroN[]]];
        sndCanon = TRANS[HOL`Equal`APTERM[sndNum[], canonT],
          sndNumPairThm[monusNum[fp, sp], zeroN[]]];
        lhsStep = HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[plusC, fstCanon], REFL[sp]];
        monusFact = HOL`Bool`MP[
          HOL`Bool`SPEC[sp, HOL`Bool`SPEC[fp, HOL`Stdlib`Num`leqAddMonusThm]],
          gHyp];   (* sp + (fp∸sp) = fp *)
        commFact = HOL`Bool`SPEC[sp,
          HOL`Bool`SPEC[monusNum[fp, sp], HOL`Stdlib`Num`addCommThm]];
        lhsToFp = TRANS[commFact, monusFact];   (* (fp∸sp)+sp = fp *)
        lhsEqFp = TRANS[lhsStep, lhsToFp];
        rhsStep = HOL`Equal`APTERM[mkComb[plusC, fp], sndCanon];
        rhsEqFp = TRANS[rhsStep, HOL`Bool`SPEC[fp, HOL`Stdlib`Num`plusZeroEqThm]];
        TRANS[lhsEqFp, HOL`Equal`SYM[rhsEqFp]]
      ];

    caseF =
      Module[{notGHyp, gEqF, canonF, fstCanon, sndCanon, ltFact, sucLeq,
              ltUnfold, leqFpSp, monusFact, rhsStep, rhsEqSp, lhsStep,
              zeroAddSp, lhsEqSp},
        notGHyp = ASSUME[mkComb[notOp[], guard]];
        gEqF = eqFIntro[notGHyp];
        canonF = TRANS[canonEq, condRewrite[gEqF, bT, bF, condFI]];
        fstCanon = TRANS[HOL`Equal`APTERM[fstNum[], canonF],
          fstNumPairThm[zeroN[], monusNum[sp, fp]]];   (* FST cp = 0 *)
        sndCanon = TRANS[HOL`Equal`APTERM[sndNum[], canonF],
          sndNumPairThm[zeroN[], monusNum[sp, fp]]];   (* SND cp = sp∸fp *)
        ltFact = EQMP[
          HOL`Bool`SPEC[fp, HOL`Bool`SPEC[sp, HOL`Stdlib`Num`notLeqEqLtThm]],
          notGHyp];   (* fp < sp *)
        ltUnfold = Module[{a1, a2},
          a1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, fp];
          a1 = TRANS[a1, BETACONV[concl[a1][[2]]]];
          a2 = HOL`Equal`APTHM[a1, sp];
          TRANS[a2, BETACONV[concl[a2][[2]]]]];
        sucLeq = EQMP[ltUnfold, ltFact];   (* SUC fp ≤ sp *)
        leqFpSp = HOL`Bool`MP[
          HOL`Bool`MP[
            HOL`Bool`SPEC[sp, HOL`Bool`SPEC[mkComb[sucC, fp],
              HOL`Bool`SPEC[fp, HOL`Stdlib`Num`leqTransThm]]],
            HOL`Bool`SPEC[fp, HOL`Stdlib`Num`leqSucThm]],
          sucLeq];   (* fp ≤ sp *)
        monusFact = HOL`Bool`MP[
          HOL`Bool`SPEC[fp, HOL`Bool`SPEC[sp, HOL`Stdlib`Num`leqAddMonusThm]],
          leqFpSp];   (* fp + (sp∸fp) = sp *)
        rhsStep = HOL`Equal`APTERM[mkComb[plusC, fp], sndCanon];
        rhsEqSp = TRANS[rhsStep, monusFact];
        lhsStep = HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[plusC, fstCanon], REFL[sp]];
        zeroAddSp = HOL`Bool`SPEC[sp, HOL`Stdlib`Num`addLeftZeroThm];
        lhsEqSp = TRANS[lhsStep, zeroAddSp];
        TRANS[lhsEqSp, HOL`Equal`SYM[rhsEqSp]]
      ];

    HOL`Bool`GEN[pV, HOL`Bool`DISJCASES[em, caseT, caseF]]
  ];

(* ⊢ ∀p q. INT_REP p ⇒ INT_REP q ⇒
            FST p + SND q = FST q + SND p ⇒ p = q                *)
canonInjThm =
  Module[{pV, qV, a, b, cc, d, H, repP, repQ, hypH, disjP, disjQ,
          surjP, surjQ, assemble, arithImp, mkCase,
          caseAC, caseAD, caseBC, caseBD, body, dH, dRq, dRp, genQ},
    pV = mkVar["p", numPairTy]; qV = mkVar["q", numPairTy];
    a = fstOf[pV]; b = sndOf[pV]; cc = fstOf[qV]; d = sndOf[qV];
    H = mkEq[plusN[a, d], plusN[cc, b]];
    repP = ASSUME[mkComb[intRepConst[], pV]];
    repQ = ASSUME[mkComb[intRepConst[], qV]];
    hypH = ASSUME[H];
    disjP = EQMP[unfoldIntRep[pV], repP];   (* FST p=0 ∨ SND p=0 *)
    disjQ = EQMP[unfoldIntRep[qV], repQ];
    surjP = HOL`Bool`ISPEC[pV, HOL`Stdlib`Pair`pairSurjThm];
    surjQ = HOL`Bool`ISPEC[qV, HOL`Stdlib`Pair`pairSurjThm];
    assemble[fcEq_, scEq_] :=
      TRANS[HOL`Equal`SYM[surjP],
        TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[commaNumC[], fcEq], scEq],
          surjQ]];   (* p = q *)
    arithImp[zeroP_, zeroQ_, goalEq_] :=
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
        HOL`Auto`Arith`arithProve[
          impliesTm[zeroP, impliesTm[zeroQ, impliesTm[H, goalEq]]]],
        ASSUME[zeroP]], ASSUME[zeroQ]], hypH];
    mkCase[zeroP_, zeroQ_] :=
      assemble[arithImp[zeroP, zeroQ, mkEq[a, cc]],
               arithImp[zeroP, zeroQ, mkEq[b, d]]];
    caseAC = mkCase[mkEq[a, zeroN[]], mkEq[cc, zeroN[]]];
    caseAD = mkCase[mkEq[a, zeroN[]], mkEq[d, zeroN[]]];
    caseBC = mkCase[mkEq[b, zeroN[]], mkEq[cc, zeroN[]]];
    caseBD = mkCase[mkEq[b, zeroN[]], mkEq[d, zeroN[]]];
    body = HOL`Bool`DISJCASES[disjP,
      HOL`Bool`DISJCASES[disjQ, caseAC, caseAD],
      HOL`Bool`DISJCASES[disjQ, caseBC, caseBD]];
    dH = HOL`Bool`DISCH[H, body];
    dRq = HOL`Bool`DISCH[mkComb[intRepConst[], qV], dH];
    dRp = HOL`Bool`DISCH[mkComb[intRepConst[], pV], dRq];
    genQ = HOL`Bool`GEN[qV, dRp];
    HOL`Bool`GEN[pV, genQ]
  ];

(* ⊢ ∀a b c d. a + d = c + b ⇒ intCanon (a,b) = intCanon (c,d) *)
canonRespectsThm =
  Module[{aV, bV, cV, dV, abPair, cdPair, c1, c2, H, repC1, repC2,
          pVarRC, raw1, raw2, eq1, eq2, plusC, lhsS1, rhsS1, lhsS2, rhsS2,
          bridgeGoal, bridgeImp, bridge, injInst, mpd,
          dischd, genD, genC, genB},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    cV = mkVar["c", numTy]; dV = mkVar["d", numTy];
    abPair = numPairCons[aV, bV]; cdPair = numPairCons[cV, dV];
    c1 = mkComb[intCanonConst[], abPair]; c2 = mkComb[intCanonConst[], cdPair];
    H = mkEq[plusN[aV, dV], plusN[cV, bV]];
    plusC = HOL`Stdlib`Num`plusConst[];
    pVarRC = mkVar["p", numPairTy];
    repC1 = HOL`Kernel`INST[{pVarRC -> abPair}, intRepCanonThm];
    repC2 = HOL`Kernel`INST[{pVarRC -> cdPair}, intRepCanonThm];
    raw1 = HOL`Bool`SPEC[abPair, canonEquivThm];
    lhsS1 = HOL`Equal`APTERM[mkComb[plusC, fstOf[c1]], sndNumPairThm[aV, bV]];
    rhsS1 = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[plusC, fstNumPairThm[aV, bV]], REFL[sndOf[c1]]];
    eq1 = TRANS[TRANS[HOL`Equal`SYM[lhsS1], raw1], rhsS1];   (* FST c1+b = a+SND c1 *)
    raw2 = HOL`Bool`SPEC[cdPair, canonEquivThm];
    lhsS2 = HOL`Equal`APTERM[mkComb[plusC, fstOf[c2]], sndNumPairThm[cV, dV]];
    rhsS2 = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[plusC, fstNumPairThm[cV, dV]], REFL[sndOf[c2]]];
    eq2 = TRANS[TRANS[HOL`Equal`SYM[lhsS2], raw2], rhsS2];
    bridgeGoal = mkEq[plusN[fstOf[c1], sndOf[c2]], plusN[fstOf[c2], sndOf[c1]]];
    bridgeImp = HOL`Auto`Arith`arithProve[
      impliesTm[concl[eq1], impliesTm[concl[eq2], impliesTm[H, bridgeGoal]]]];
    bridge = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[bridgeImp, eq1], eq2],
      ASSUME[H]];
    injInst = HOL`Bool`SPEC[c2, HOL`Bool`SPEC[c1, canonInjThm]];
    mpd = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[injInst, repC1], repC2], bridge];
    dischd = HOL`Bool`DISCH[H, mpd];
    genD = HOL`Bool`GEN[dV, dischd];
    genC = HOL`Bool`GEN[cV, genD];
    genB = HOL`Bool`GEN[bV, genC];
    HOL`Bool`GEN[aV, genB]
  ];

(* ============================================================ *)
(* intAddAssocThm: ⊢ ∀z w v. intAdd (intAdd z w) v =             *)
(*                           intAdd z (intAdd w v).              *)
(*                                                              *)
(* REP(intAdd z w) = intCanon(z1+w1, z2+w2) [repIntAddThm]. Both *)
(* sides reduce to ABS_int(intCanon(SUM)) where SUM's components *)
(* differ only by addAssoc; the canon-of-canon collapses via     *)
(* canonRespectsThm fed a canonEquivThm-derived equivalence.     *)
(* ============================================================ *)

(* ⊢ REP_int (intAdd zT wT) = intCanon (intAddPair zT wT) *)
repIntAddAt[zT_, wT_] :=
  Module[{ufAdd, canonP, applyRep, rVar, repAbsInst, repCanonP, repEq},
    ufAdd = unfoldIntAdd[zT, wT];
    canonP = mkComb[intCanonConst[], intAddPairTm[zT, wT]];
    applyRep = HOL`Equal`APTERM[repIntConst[], ufAdd];
    rVar = concl[repAbsIntThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> canonP}, repAbsIntThm];
    repCanonP = HOL`Kernel`INST[
      {mkVar["p", numPairTy] -> intAddPairTm[zT, wT]}, intRepCanonThm];
    repEq = EQMP[repAbsInst, repCanonP];
    TRANS[applyRep, repEq]
  ];

repIntAddThm =
  Module[{zV, wV},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV, repIntAddAt[zV, wV]]]
  ];

(* ⊢ FST (intCanon (x1,x2)) + x2 = x1 + SND (intCanon (x1,x2)) *)
canonEquivAt[x1_, x2_] :=
  Module[{pr, cc, plusC, raw, lhsS, rhsS},
    pr = numPairCons[x1, x2]; cc = mkComb[intCanonConst[], pr];
    plusC = HOL`Stdlib`Num`plusConst[];
    raw = HOL`Bool`SPEC[pr, canonEquivThm];
    lhsS = HOL`Equal`APTERM[mkComb[plusC, fstOf[cc]], sndNumPairThm[x1, x2]];
    rhsS = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[plusC, fstNumPairThm[x1, x2]], REFL[sndOf[cc]]];
    TRANS[TRANS[HOL`Equal`SYM[lhsS], raw], rhsS]
  ];

intAddAssocThm =
  Module[{zV, wV, vV, rz, rw, rv, z1, z2, w1, w2, v1, v2, s1, s2, t1, t2,
          P, Q, cp, dq, cpf, cps, dqf, dqs, plusC, lhsUf, repZW, fstRwL,
          sndRwL, innerL, lhsStep1, eqP, respL, lhsStep2, rhsUf, repWV,
          fstRwR, sndRwR, innerR, rhsStep1, eqQ, respR, rhsStep2, assoc1,
          assoc2, pairFinal, canonFinal, absFinal, body, genV, genW},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy]; vV = mkVar["v", intTy];
    rz = repIntTm[zV]; rw = repIntTm[wV]; rv = repIntTm[vV];
    z1 = fstOf[rz]; z2 = sndOf[rz]; w1 = fstOf[rw]; w2 = sndOf[rw];
    v1 = fstOf[rv]; v2 = sndOf[rv];
    s1 = plusN[z1, w1]; s2 = plusN[z2, w2];
    t1 = plusN[w1, v1]; t2 = plusN[w2, v2];
    P = intAddPairTm[zV, wV]; Q = intAddPairTm[wV, vV];
    cp = mkComb[intCanonConst[], P]; dq = mkComb[intCanonConst[], Q];
    cpf = fstOf[cp]; cps = sndOf[cp]; dqf = fstOf[dq]; dqs = sndOf[dq];
    plusC = HOL`Stdlib`Num`plusConst[];

    (* ---- LHS = ABS_int(intCanon(cpf+v1, cps+v2)) ---- *)
    lhsUf = unfoldIntAdd[intAddTm[zV, wV], vV];
    repZW = repIntAddAt[zV, wV];
    fstRwL = HOL`Equal`APTERM[fstNum[], repZW];   (* FST(REP(z+w)) = cpf *)
    sndRwL = HOL`Equal`APTERM[sndNum[], repZW];
    innerL = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[],
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fstRwL], REFL[v1]]],
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, sndRwL], REFL[v2]]];
    lhsStep1 = TRANS[lhsUf,
      HOL`Equal`APTERM[absIntConst[],
        HOL`Equal`APTERM[intCanonConst[], innerL]]];
    eqP = canonEquivAt[s1, s2];   (* cpf + s2 = s1 + cps *)
    respL = Module[{respInst, target, hImp},
      respInst = HOL`Bool`SPEC[plusN[s2, v2],
        HOL`Bool`SPEC[plusN[s1, v1],
          HOL`Bool`SPEC[plusN[cps, v2],
            HOL`Bool`SPEC[plusN[cpf, v1], canonRespectsThm]]]];
      target = mkEq[plusN[plusN[cpf, v1], plusN[s2, v2]],
                    plusN[plusN[s1, v1], plusN[cps, v2]]];
      hImp = HOL`Auto`Arith`arithProve[impliesTm[concl[eqP], target]];
      HOL`Bool`MP[respInst, HOL`Bool`MP[hImp, eqP]]];
    lhsStep2 = TRANS[lhsStep1, HOL`Equal`APTERM[absIntConst[], respL]];
    (* LHS = ABS_int(intCanon(s1+v1, s2+v2)) *)

    (* ---- RHS = ABS_int(intCanon(z1+dqf, z2+dqs)) ---- *)
    rhsUf = unfoldIntAdd[zV, intAddTm[wV, vV]];
    repWV = repIntAddAt[wV, vV];
    fstRwR = HOL`Equal`APTERM[fstNum[], repWV];
    sndRwR = HOL`Equal`APTERM[sndNum[], repWV];
    innerR = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[],
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, REFL[z1]], fstRwR]],
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, REFL[z2]], sndRwR]];
    rhsStep1 = TRANS[rhsUf,
      HOL`Equal`APTERM[absIntConst[],
        HOL`Equal`APTERM[intCanonConst[], innerR]]];
    eqQ = canonEquivAt[t1, t2];   (* dqf + t2 = t1 + dqs *)
    respR = Module[{respInst, target, hImp},
      respInst = HOL`Bool`SPEC[plusN[z2, t2],
        HOL`Bool`SPEC[plusN[z1, t1],
          HOL`Bool`SPEC[plusN[z2, dqs],
            HOL`Bool`SPEC[plusN[z1, dqf], canonRespectsThm]]]];
      target = mkEq[plusN[plusN[z1, dqf], plusN[z2, t2]],
                    plusN[plusN[z1, t1], plusN[z2, dqs]]];
      hImp = HOL`Auto`Arith`arithProve[impliesTm[concl[eqQ], target]];
      HOL`Bool`MP[respInst, HOL`Bool`MP[hImp, eqQ]]];
    rhsStep2 = TRANS[rhsStep1, HOL`Equal`APTERM[absIntConst[], respR]];
    (* RHS = ABS_int(intCanon(z1+t1, z2+t2)) *)

    (* ---- align: s1+v1 = z1+t1, s2+v2 = z2+t2 by addAssoc ---- *)
    assoc1 = HOL`Bool`SPEC[v1, HOL`Bool`SPEC[w1,
      HOL`Bool`SPEC[z1, HOL`Stdlib`Num`addAssocThm]]];
    assoc2 = HOL`Bool`SPEC[v2, HOL`Bool`SPEC[w2,
      HOL`Bool`SPEC[z2, HOL`Stdlib`Num`addAssocThm]]];
    pairFinal = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[], assoc1], assoc2];
    canonFinal = HOL`Equal`APTERM[intCanonConst[], pairFinal];
    absFinal = HOL`Equal`APTERM[absIntConst[], canonFinal];
    body = TRANS[lhsStep2, TRANS[absFinal, HOL`Equal`SYM[rhsStep2]]];
    genV = HOL`Bool`GEN[vV, body];
    genW = HOL`Bool`GEN[wV, genV];
    HOL`Bool`GEN[zV, genW]
  ];

(* ============================================================ *)
(* intSucc / intPred : int → int — shift by ±1ℤ.                 *)
(*   intSucc z = intAdd z (&ℤ 1),  intPred z = intAdd z (−&ℤ 1). *)
(* Mutually inverse bijections (the round-trips fall out of      *)
(* associativity + inverse + identity), the working tool for     *)
(* bidirectional int induction.                                  *)
(* ============================================================ *)

intOneTm = intOfNumTm[mkComb[HOL`Stdlib`Num`sucConst[], zeroN[]]];   (* &ℤ 1 *)
negOneTm = intNegTm[intOneTm];                                       (* intNeg (&ℤ 1) *)
intSuccTy = tyFun[intTy, intTy];

intSuccDefThm = newDefinition[mkEq[mkVar["intSucc", intSuccTy],
  Module[{zV}, zV = mkVar["z", intTy]; mkAbs[zV, intAddTm[zV, intOneTm]]]]];
intPredDefThm = newDefinition[mkEq[mkVar["intPred", intSuccTy],
  Module[{zV}, zV = mkVar["z", intTy]; mkAbs[zV, intAddTm[zV, negOneTm]]]]];

intSuccConst[] := mkConst["intSucc", intSuccTy];
intPredConst[] := mkConst["intPred", intSuccTy];
intSuccTm[zT_] := mkComb[intSuccConst[], zT];
intPredTm[zT_] := mkComb[intPredConst[], zT];

unfoldIntSucc[zT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intSuccDefThm, zT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];
unfoldIntPred[zT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intPredDefThm, zT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ ∀z. intPred (intSucc z) = z *)
intPredSuccThm =
  Module[{zV, sz, ufPred, ufSucc, step1, assocInst, step2, invInst,
          step3, step4},
    zV = mkVar["z", intTy]; sz = intSuccTm[zV];
    ufPred = unfoldIntPred[sz];   (* intPred(intSucc z) = intAdd (intSucc z) (−1) *)
    ufSucc = unfoldIntSucc[zV];   (* intSucc z = intAdd z 1 *)
    step1 = TRANS[ufPred,
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddConst[], ufSucc], REFL[negOneTm]]];
    (* = intAdd (intAdd z 1) (−1) *)
    assocInst = HOL`Bool`SPEC[negOneTm, HOL`Bool`SPEC[intOneTm,
      HOL`Bool`SPEC[zV, intAddAssocThm]]];
    step2 = TRANS[step1, assocInst];   (* = intAdd z (intAdd 1 (−1)) *)
    invInst = HOL`Bool`SPEC[intOneTm, intAddNegThm];   (* intAdd 1 (intNeg 1) = &ℤ 0 *)
    step3 = TRANS[step2,
      HOL`Equal`APTERM[mkComb[intAddConst[], zV], invInst]];   (* = intAdd z (&ℤ 0) *)
    step4 = TRANS[step3, HOL`Bool`SPEC[zV, intAddZeroThm]];   (* = z *)
    HOL`Bool`GEN[zV, step4]
  ];

(* ⊢ ∀z. intSucc (intPred z) = z *)
intSuccPredThm =
  Module[{zV, pz, ufSucc, ufPred, step1, assocInst, commInst, invInst,
          innerEq, step3, step4},
    zV = mkVar["z", intTy]; pz = intPredTm[zV];
    ufSucc = unfoldIntSucc[pz];   (* intSucc(intPred z) = intAdd (intPred z) 1 *)
    ufPred = unfoldIntPred[zV];   (* intPred z = intAdd z (−1) *)
    step1 = TRANS[ufSucc,
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[intAddConst[], ufPred], REFL[intOneTm]]];
    (* = intAdd (intAdd z (−1)) 1 *)
    assocInst = HOL`Bool`SPEC[intOneTm, HOL`Bool`SPEC[negOneTm,
      HOL`Bool`SPEC[zV, intAddAssocThm]]];
    step1 = TRANS[step1, assocInst];   (* = intAdd z (intAdd (−1) 1) *)
    commInst = HOL`Bool`SPEC[intOneTm, HOL`Bool`SPEC[negOneTm, intAddCommThm]];
    (* intAdd (−1) 1 = intAdd 1 (−1) *)
    invInst = HOL`Bool`SPEC[intOneTm, intAddNegThm];   (* intAdd 1 (−1) = &ℤ 0 *)
    innerEq = TRANS[commInst, invInst];   (* intAdd (−1) 1 = &ℤ 0 *)
    step3 = TRANS[step1,
      HOL`Equal`APTERM[mkComb[intAddConst[], zV], innerEq]];   (* = intAdd z (&ℤ 0) *)
    step4 = TRANS[step3, HOL`Bool`SPEC[zV, intAddZeroThm]];   (* = z *)
    HOL`Bool`GEN[zV, step4]
  ];

(* ============================================================ *)
(* intMul : int → int → int — multiplication.                   *)
(*   (a−b)(c−d) = (ac+bd) − (ad+bc), so intMul z w canonicalizes *)
(*   (z1*w1 + z2*w2, z1*w2 + z2*w1) where z1=FST(REP z) etc.     *)
(* repIntMulThm mirrors repIntAddThm (reusable for distributivity *)
(* / associativity); comm/identity/zero follow as for add but    *)
(* with num timesComm / timesZero / oneTimes lemmas (products    *)
(* are opaque to ARITH, so this glue is explicit num rewriting). *)
(* ============================================================ *)

timesNC[] := HOL`Stdlib`Num`timesConst[];
timesN[aTm_, bTm_] := mkComb[mkComb[timesNC[], aTm], bTm];
intMulTy = tyFun[intTy, tyFun[intTy, intTy]];

intMulPairTm[zT_, wT_] :=
  Module[{rz, rw, z1, z2, w1, w2},
    rz = repIntTm[zT]; rw = repIntTm[wT];
    z1 = fstOf[rz]; z2 = sndOf[rz]; w1 = fstOf[rw]; w2 = sndOf[rw];
    numPairCons[plusN[timesN[z1, w1], timesN[z2, w2]],
                plusN[timesN[z1, w2], timesN[z2, w1]]]
  ];

intMulDefThm = newDefinition[mkEq[mkVar["intMul", intMulTy],
  Module[{zV, wV}, zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    mkAbs[zV, mkAbs[wV,
      mkComb[absIntConst[],
        mkComb[intCanonConst[], intMulPairTm[zV, wV]]]]]]]];

intMulConst[] := mkConst["intMul", intMulTy];
intMulTm[zT_, wT_] := mkComb[mkComb[intMulConst[], zT], wT];

unfoldIntMul[zT_, wT_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[intMulDefThm, zT];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, wT];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ REP_int (intMul zT wT) = intCanon (intMulPair zT wT) *)
repIntMulAt[zT_, wT_] :=
  Module[{ufMul, canonP, applyRep, rVar, repAbsInst, repCanonP, repEq},
    ufMul = unfoldIntMul[zT, wT];
    canonP = mkComb[intCanonConst[], intMulPairTm[zT, wT]];
    applyRep = HOL`Equal`APTERM[repIntConst[], ufMul];
    rVar = concl[repAbsIntThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> canonP}, repAbsIntThm];
    repCanonP = HOL`Kernel`INST[
      {mkVar["p", numPairTy] -> intMulPairTm[zT, wT]}, intRepCanonThm];
    repEq = EQMP[repAbsInst, repCanonP];
    TRANS[applyRep, repEq]
  ];

repIntMulThm =
  Module[{zV, wV}, zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV, repIntMulAt[zV, wV]]]];

(* ⊢ m * n = n * m  at chosen m, n *)
timesCommAt[mTm_, nTm_] :=
  HOL`Bool`SPEC[nTm, HOL`Bool`SPEC[mTm, HOL`Stdlib`Num`timesCommThm]];

(* ⊢ ∀z w. intMul z w = intMul w z *)
intMulCommThm =
  Module[{zV, wV, rz, rw, z1, z2, w1, w2, ufZW, ufWZ, fstEq, sndC1,
          addCInst, sndEq, pairEq, genW},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    rz = repIntTm[zV]; rw = repIntTm[wV];
    z1 = fstOf[rz]; z2 = sndOf[rz]; w1 = fstOf[rw]; w2 = sndOf[rw];
    ufZW = unfoldIntMul[zV, wV];
    ufWZ = unfoldIntMul[wV, zV];
    fstEq = HOL`Kernel`MKCOMB[                       (* z1*w1+z2*w2 = w1*z1+w2*z2 *)
      HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], timesCommAt[z1, w1]],
      timesCommAt[z2, w2]];
    sndC1 = HOL`Kernel`MKCOMB[                        (* z1*w2+z2*w1 = w2*z1+w1*z2 *)
      HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], timesCommAt[z1, w2]],
      timesCommAt[z2, w1]];
    addCInst = HOL`Bool`SPEC[timesN[w1, z2],          (* w2*z1+w1*z2 = w1*z2+w2*z1 *)
      HOL`Bool`SPEC[timesN[w2, z1], HOL`Stdlib`Num`addCommThm]];
    sndEq = TRANS[sndC1, addCInst];
    pairEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[], fstEq], sndEq];
    genW = HOL`Bool`GEN[wV, TRANS[ufZW,
      TRANS[HOL`Equal`APTERM[absIntConst[],
        HOL`Equal`APTERM[intCanonConst[], pairEq]], HOL`Equal`SYM[ufWZ]]]];
    HOL`Bool`GEN[zV, genW]
  ];

(* ⊢ n * (SUC 0) = n  (via timesComm + oneTimes) *)
timesOneAt[nTm_] :=
  TRANS[timesCommAt[nTm, mkComb[HOL`Stdlib`Num`sucConst[], zeroN[]]],
    HOL`Bool`SPEC[nTm, HOL`Stdlib`Num`oneTimesEqThm]];

(* ⊢ ∀z. intMul z (&ℤ (SUC 0)) = z *)
intMulOneThm =
  Module[{zV, rz, z1, z2, suc0, intOne, ufMul, repAtOne, fstW, sndW,
          z1w1, z2w2, fc, z1w2, z2w1, sc, pairEq, surj, pairToRep,
          canonRepZ, canonEq, aVar, absRepZ, plusC, timesC},
    zV = mkVar["z", intTy]; rz = repIntTm[zV]; z1 = fstOf[rz]; z2 = sndOf[rz];
    suc0 = mkComb[HOL`Stdlib`Num`sucConst[], zeroN[]];
    intOne = intOfNumTm[suc0];
    plusC = HOL`Stdlib`Num`plusConst[]; timesC = timesNC[];
    ufMul = unfoldIntMul[zV, intOne];
    repAtOne = HOL`Kernel`INST[{mkVar["n", numTy] -> suc0}, repIntOfNumThm];
    fstW = TRANS[HOL`Equal`APTERM[fstNum[], repAtOne],
      fstNumPairThm[suc0, zeroN[]]];   (* FST(REP(&ℤ1)) = SUC 0 *)
    sndW = TRANS[HOL`Equal`APTERM[sndNum[], repAtOne],
      sndNumPairThm[suc0, zeroN[]]];   (* SND(REP(&ℤ1)) = 0 *)
    z1w1 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z1], fstW], timesOneAt[z1]];
    z2w2 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z2], sndW],
      HOL`Bool`SPEC[z2, HOL`Stdlib`Num`timesZeroEqThm]];
    fc = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, z1w1], z2w2],
      HOL`Bool`SPEC[z1, HOL`Stdlib`Num`plusZeroEqThm]];   (* = z1 *)
    z1w2 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z1], sndW],
      HOL`Bool`SPEC[z1, HOL`Stdlib`Num`timesZeroEqThm]];
    z2w1 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z2], fstW], timesOneAt[z2]];
    sc = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, z1w2], z2w1],
      HOL`Bool`SPEC[z2, HOL`Stdlib`Num`addLeftZeroThm]];   (* = z2 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[commaNumC[], fc], sc];
    surj = HOL`Bool`ISPEC[rz, HOL`Stdlib`Pair`pairSurjThm];
    pairToRep = TRANS[pairEq, surj];   (* pair = REP z *)
    canonRepZ = HOL`Bool`MP[HOL`Bool`SPEC[rz, intCanonIdThm], intRepRepThm];
    canonEq = TRANS[HOL`Equal`APTERM[intCanonConst[], pairToRep], canonRepZ];
    aVar = concl[absRepIntThm][[2]];
    absRepZ = HOL`Kernel`INST[{aVar -> zV}, absRepIntThm];
    HOL`Bool`GEN[zV, TRANS[ufMul,
      TRANS[HOL`Equal`APTERM[absIntConst[], canonEq], absRepZ]]]
  ];

(* ⊢ ∀z. intMul z (&ℤ 0) = &ℤ 0 *)
intMulZeroThm =
  Module[{zV, rz, z1, z2, intZero, ufMul, repAtZero, fstW0, sndW0,
          z1w1, z2w2, fc, z1w2, z2w1, sc, pairEq, zeroPair, canonIdZero,
          canonEq, zeroEq, plusC, timesC},
    zV = mkVar["z", intTy]; rz = repIntTm[zV]; z1 = fstOf[rz]; z2 = sndOf[rz];
    intZero = intOfNumTm[zeroN[]];
    plusC = HOL`Stdlib`Num`plusConst[]; timesC = timesNC[];
    ufMul = unfoldIntMul[zV, intZero];
    repAtZero = HOL`Kernel`INST[{mkVar["n", numTy] -> zeroN[]}, repIntOfNumThm];
    fstW0 = TRANS[HOL`Equal`APTERM[fstNum[], repAtZero],
      fstNumPairThm[zeroN[], zeroN[]]];
    sndW0 = TRANS[HOL`Equal`APTERM[sndNum[], repAtZero],
      sndNumPairThm[zeroN[], zeroN[]]];
    z1w1 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z1], fstW0],
      HOL`Bool`SPEC[z1, HOL`Stdlib`Num`timesZeroEqThm]];
    z2w2 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z2], sndW0],
      HOL`Bool`SPEC[z2, HOL`Stdlib`Num`timesZeroEqThm]];
    fc = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, z1w1], z2w2],
      HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`plusZeroEqThm]];   (* = 0 *)
    z1w2 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z1], sndW0],
      HOL`Bool`SPEC[z1, HOL`Stdlib`Num`timesZeroEqThm]];
    z2w1 = TRANS[HOL`Equal`APTERM[mkComb[timesC, z2], fstW0],
      HOL`Bool`SPEC[z2, HOL`Stdlib`Num`timesZeroEqThm]];
    sc = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, z1w2], z2w1],
      HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`plusZeroEqThm]];   (* = 0 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[commaNumC[], fc], sc];
    zeroPair = numPairCons[zeroN[], zeroN[]];
    canonIdZero = HOL`Bool`MP[HOL`Bool`SPEC[zeroPair, intCanonIdThm],
      intRepZeroPairThm];   (* intCanon(0,0) = (0,0) *)
    canonEq = TRANS[HOL`Equal`APTERM[intCanonConst[], pairEq], canonIdZero];
    zeroEq = unfoldIntOfNum[zeroN[]];   (* &ℤ 0 = ABS_int(0,0) *)
    HOL`Bool`GEN[zV, TRANS[ufMul,
      TRANS[HOL`Equal`APTERM[absIntConst[], canonEq], HOL`Equal`SYM[zeroEq]]]]
  ];

(* ============================================================ *)
(* intMulDistribThm: ⊢ ∀z w v.                                  *)
(*   intMul z (intAdd w v) = intAdd (intMul z w) (intMul z v).  *)
(*                                                              *)
(* Both sides reduce (repIntMulThm/repIntAddThm) to             *)
(* ABS_int(intCanon Pstar) for the SAME fully-distributed pair     *)
(* Pstar = ((z1w1+z2w2)+(z1v1+z2v2), (z1w2+z2w1)+(z1v2+z2v1)),      *)
(* the canon-of-canon collapsing through canonRespectsThm.      *)
(* LHS's equivalence needs canonEquivAt at (w1+v1, w2+v2)        *)
(* multiplied by z1, z2 and distributed by hand (timesDistrib —  *)
(* products are opaque to ARITH); the residual linear step      *)
(* closes via ARITH. RHS's products are already atoms so its     *)
(* two canonEquivAt facts feed ARITH directly.                  *)
(* ============================================================ *)

(* ⊢ a * (b + c) = a * b + a * c  at chosen a, b, c *)
timesDistribLeftAt[aTm_, bTm_, cTm_] :=
  HOL`Bool`SPEC[cTm, HOL`Bool`SPEC[bTm,
    HOL`Bool`SPEC[aTm, HOL`Stdlib`Num`timesDistribLeftThm]]];

(* from E : (aT + (w2+v2)) = ((w1+v1) + bT), multiplier k, build the
   fully-distributed  k*aT + (k*w2 + k*v2) = (k*w1 + k*v1) + k*bT *)
scaleDistribEquiv[kTm_, eqE_, aT_, bT_, w1_, v1_, w2_, v2_] :=
  Module[{plusC, kE, lhsD1, lhsD2, lhsDist, rhsD1, rhsD2, rhsDist},
    plusC = HOL`Stdlib`Num`plusConst[];
    kE = HOL`Equal`APTERM[mkComb[timesNC[], kTm], eqE];
    lhsD1 = timesDistribLeftAt[kTm, aT, plusN[w2, v2]];
    lhsD2 = timesDistribLeftAt[kTm, w2, v2];
    lhsDist = TRANS[lhsD1,
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, REFL[timesN[kTm, aT]]], lhsD2]];
    rhsD1 = timesDistribLeftAt[kTm, plusN[w1, v1], bT];
    rhsD2 = timesDistribLeftAt[kTm, w1, v1];
    rhsDist = TRANS[rhsD1,
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, rhsD2], REFL[timesN[kTm, bT]]]];
    TRANS[TRANS[HOL`Equal`SYM[lhsDist], kE], rhsDist]
  ];

intMulDistribThm =
  Module[{zV, wV, vV, rz, rw, rv, z1, z2, w1, w2, v1, v2, plusC, timesC,
          w1v1, w2v2, cpWV, aT, bT, addWV, ufMulL, repAdd, fstAB, sndAB,
          p1f, p1s, innerRw, lhsStep1, eqE, e1, e2, zw1, zw2, zv1, zv2,
          psF, psS, respInstL, targetL, hImpL, respL, lhsStep2,
          mulZW, mulZV, ufAddR, repMZW, repMZV, cpZW, cpZV, pp, qq, rr, ss,
          fstP, fstQ, sndP, sndQ, innerRwR, rhsStep1, ezw, ezv,
          respInstR, targetR, hImpR, respR, rhsStep2, body, genV, genW},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy]; vV = mkVar["v", intTy];
    rz = repIntTm[zV]; rw = repIntTm[wV]; rv = repIntTm[vV];
    z1 = fstOf[rz]; z2 = sndOf[rz]; w1 = fstOf[rw]; w2 = sndOf[rw];
    v1 = fstOf[rv]; v2 = sndOf[rv];
    plusC = HOL`Stdlib`Num`plusConst[]; timesC = timesNC[];
    w1v1 = plusN[w1, v1]; w2v2 = plusN[w2, v2];
    cpWV = mkComb[intCanonConst[], numPairCons[w1v1, w2v2]];
    aT = fstOf[cpWV]; bT = sndOf[cpWV];

    (* ---- LHS: intMul z (intAdd w v) ---- *)
    addWV = intAddTm[wV, vV];
    ufMulL = unfoldIntMul[zV, addWV];
    repAdd = repIntAddAt[wV, vV];                  (* REP(addWV) = intCanon(w1+v1,w2+v2) *)
    fstAB = HOL`Equal`APTERM[fstNum[], repAdd];    (* FST(REP addWV) = aT *)
    sndAB = HOL`Equal`APTERM[sndNum[], repAdd];    (* SND(REP addWV) = bT *)
    p1f = plusN[timesN[z1, aT], timesN[z2, bT]];
    p1s = plusN[timesN[z1, bT], timesN[z2, aT]];
    innerRw = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[],
        HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[plusC, HOL`Equal`APTERM[mkComb[timesC, z1], fstAB]],
          HOL`Equal`APTERM[mkComb[timesC, z2], sndAB]]],
      HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[plusC, HOL`Equal`APTERM[mkComb[timesC, z1], sndAB]],
        HOL`Equal`APTERM[mkComb[timesC, z2], fstAB]]];
    lhsStep1 = TRANS[ufMulL,
      HOL`Equal`APTERM[absIntConst[],
        HOL`Equal`APTERM[intCanonConst[], innerRw]]];
    (* LHS = ABS_int(intCanon(z1*aT+z2*bT, z1*bT+z2*aT)) *)
    eqE = canonEquivAt[w1v1, w2v2];                (* aT + (w2+v2) = (w1+v1) + bT *)
    e1 = scaleDistribEquiv[z1, eqE, aT, bT, w1, v1, w2, v2];
    e2 = scaleDistribEquiv[z2, eqE, aT, bT, w1, v1, w2, v2];
    zw1 = plusN[timesN[z1, w1], timesN[z2, w2]];
    zw2 = plusN[timesN[z1, w2], timesN[z2, w1]];
    zv1 = plusN[timesN[z1, v1], timesN[z2, v2]];
    zv2 = plusN[timesN[z1, v2], timesN[z2, v1]];
    psF = plusN[zw1, zv1]; psS = plusN[zw2, zv2];   (* Pstar components *)
    respInstL = HOL`Bool`SPEC[psS, HOL`Bool`SPEC[psF,
      HOL`Bool`SPEC[p1s, HOL`Bool`SPEC[p1f, canonRespectsThm]]]];
    targetL = mkEq[plusN[p1f, psS], plusN[psF, p1s]];
    hImpL = HOL`Auto`Arith`arithProve[
      impliesTm[concl[e1], impliesTm[concl[e2], targetL]]];
    respL = HOL`Bool`MP[respInstL,
      HOL`Bool`MP[HOL`Bool`MP[hImpL, e1], e2]];
    lhsStep2 = TRANS[lhsStep1, HOL`Equal`APTERM[absIntConst[], respL]];
    (* LHS = ABS_int(intCanon Pstar) *)

    (* ---- RHS: intAdd (intMul z w) (intMul z v) ---- *)
    mulZW = intMulTm[zV, wV]; mulZV = intMulTm[zV, vV];
    ufAddR = unfoldIntAdd[mulZW, mulZV];
    repMZW = repIntMulAt[zV, wV]; repMZV = repIntMulAt[zV, vV];
    cpZW = mkComb[intCanonConst[], intMulPairTm[zV, wV]];
    cpZV = mkComb[intCanonConst[], intMulPairTm[zV, vV]];
    pp = fstOf[cpZW]; qq = sndOf[cpZW]; rr = fstOf[cpZV]; ss = sndOf[cpZV];
    fstP = HOL`Equal`APTERM[fstNum[], repMZW]; fstQ = HOL`Equal`APTERM[fstNum[], repMZV];
    sndP = HOL`Equal`APTERM[sndNum[], repMZW]; sndQ = HOL`Equal`APTERM[sndNum[], repMZV];
    innerRwR = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[],
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fstP], fstQ]],
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, sndP], sndQ]];
    rhsStep1 = TRANS[ufAddR,
      HOL`Equal`APTERM[absIntConst[],
        HOL`Equal`APTERM[intCanonConst[], innerRwR]]];
    (* RHS = ABS_int(intCanon(pp+rr, qq+ss)) *)
    ezw = canonEquivAt[zw1, zw2];   (* pp + zw2 = zw1 + qq *)
    ezv = canonEquivAt[zv1, zv2];   (* rr + zv2 = zv1 + ss *)
    respInstR = HOL`Bool`SPEC[psS, HOL`Bool`SPEC[psF,
      HOL`Bool`SPEC[plusN[qq, ss], HOL`Bool`SPEC[plusN[pp, rr], canonRespectsThm]]]];
    targetR = mkEq[plusN[plusN[pp, rr], psS], plusN[psF, plusN[qq, ss]]];
    hImpR = HOL`Auto`Arith`arithProve[
      impliesTm[concl[ezw], impliesTm[concl[ezv], targetR]]];
    respR = HOL`Bool`MP[respInstR,
      HOL`Bool`MP[HOL`Bool`MP[hImpR, ezw], ezv]];
    rhsStep2 = TRANS[rhsStep1, HOL`Equal`APTERM[absIntConst[], respR]];
    (* RHS = ABS_int(intCanon Pstar) *)

    body = TRANS[lhsStep2, HOL`Equal`SYM[rhsStep2]];
    genV = HOL`Bool`GEN[vV, body];
    genW = HOL`Bool`GEN[wV, genV];
    HOL`Bool`GEN[zV, genW]
  ];

(* ============================================================ *)
(* intMulAssocThm: ⊢ ∀z w v.                                    *)
(*   intMul (intMul z w) v = intMul z (intMul w v).             *)
(*                                                              *)
(* Same canonRespects bridge, but with deeper product nesting.  *)
(* Each side reduces (repIntMulThm) to ABS_int(intCanon ·) for   *)
(* its own naturally-distributed pair: LHS scales canonEquivAt   *)
(* (at the z·w product pair) on the right by v1/v2 → monomials    *)
(* in left-associated form (zi*wj)*vk; RHS scales canonEquivAt   *)
(* (at the w·v pair) on the left by z1/z2 → monomials zi*(wj*vk). *)
(* The two distributed pairs L and R hold the SAME monomials in   *)
(* different association; L = R closes by feeding ARITH the eight *)
(* timesAssoc equalities (zi*wj)*vk = zi*(wj*vk) as antecedents,  *)
(* which is the only place associativity-of-product enters       *)
(* (products are atoms to ARITH).                                *)
(* ============================================================ *)

tripL[aTm_, bTm_, cTm_] := timesN[timesN[aTm, bTm], cTm];   (* (a*b)*c *)
tripR[aTm_, bTm_, cTm_] := timesN[aTm, timesN[bTm, cTm]];   (* a*(b*c) *)

(* ⊢ (a + b) * c = a*c + b*c  at chosen a, b, c *)
timesDistribRightAt[aTm_, bTm_, cTm_] :=
  HOL`Bool`SPEC[cTm, HOL`Bool`SPEC[bTm,
    HOL`Bool`SPEC[aTm, HOL`Stdlib`Num`timesDistribRightThm]]];

(* ⊢ (a * b) * c = a * (b * c)  at chosen a, b, c *)
timesAssocAt[aTm_, bTm_, cTm_] :=
  HOL`Bool`SPEC[cTm, HOL`Bool`SPEC[bTm,
    HOL`Bool`SPEC[aTm, HOL`Stdlib`Num`timesAssocThm]]];

(* right-scale mirror of scaleDistribEquiv: from
   eqE : (aT + (x2+y2)) = ((x1+y1) + bT),  build
   aT*k + (x2*k + y2*k) = (x1*k + y1*k) + bT*k *)
scaleDistribEquivRight[kTm_, eqE_, aT_, bT_, x1_, y1_, x2_, y2_] :=
  Module[{plusC, kE, lhsD1, lhsD2, lhsDist, rhsD1, rhsD2, rhsDist},
    plusC = HOL`Stdlib`Num`plusConst[];
    kE = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesNC[], eqE], REFL[kTm]];
    lhsD1 = timesDistribRightAt[aT, plusN[x2, y2], kTm];
    lhsD2 = timesDistribRightAt[x2, y2, kTm];
    lhsDist = TRANS[lhsD1,
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, REFL[timesN[aT, kTm]]], lhsD2]];
    rhsD1 = timesDistribRightAt[plusN[x1, y1], bT, kTm];
    rhsD2 = timesDistribRightAt[x1, y1, kTm];
    rhsDist = TRANS[rhsD1,
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, rhsD2], REFL[timesN[bT, kTm]]]];
    TRANS[TRANS[HOL`Equal`SYM[lhsDist], kE], rhsDist]
  ];

intMulAssocThm =
  Module[{zV, wV, vV, rz, rw, rv, z1, z2, w1, w2, v1, v2,
          zw1, zw2, wv1, wv2, cpZW, cpWV, pp, qq, rr, ss, plusC, timesC,
          mulZW, ufMulL, repMzw, fstPQ, sndPQ, pL0f, pL0s, innerL, lhsStep1,
          ezw, eL1, eL2, lf, ls, respInstL, targetL, hImpL, respL, lhsStep2,
          mulWV, ufMulR, repMwv, fstRS, sndRS, pR0f, pR0s, innerR, rhsStep1,
          ewv, eR1, eR2, rf, rs, respInstR, targetR, hImpR, respR, rhsStep2,
          h1, h2, h3, h4, fstImp, fstAlign, g1, g2, g3, g4, sndImp, sndAlign,
          pairLR, absAlign, body, genV, genW},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy]; vV = mkVar["v", intTy];
    rz = repIntTm[zV]; rw = repIntTm[wV]; rv = repIntTm[vV];
    z1 = fstOf[rz]; z2 = sndOf[rz]; w1 = fstOf[rw]; w2 = sndOf[rw];
    v1 = fstOf[rv]; v2 = sndOf[rv];
    plusC = HOL`Stdlib`Num`plusConst[]; timesC = timesNC[];
    zw1 = plusN[timesN[z1, w1], timesN[z2, w2]];
    zw2 = plusN[timesN[z1, w2], timesN[z2, w1]];
    wv1 = plusN[timesN[w1, v1], timesN[w2, v2]];
    wv2 = plusN[timesN[w1, v2], timesN[w2, v1]];
    cpZW = mkComb[intCanonConst[], numPairCons[zw1, zw2]];
    cpWV = mkComb[intCanonConst[], numPairCons[wv1, wv2]];
    pp = fstOf[cpZW]; qq = sndOf[cpZW]; rr = fstOf[cpWV]; ss = sndOf[cpWV];

    (* ---- LHS = intMul (intMul z w) v ---- *)
    mulZW = intMulTm[zV, wV];
    ufMulL = unfoldIntMul[mulZW, vV];
    repMzw = repIntMulAt[zV, wV];                  (* REP(intMul z w) = cpZW *)
    fstPQ = HOL`Equal`APTERM[fstNum[], repMzw];    (* FST(REP mulZW) = pp *)
    sndPQ = HOL`Equal`APTERM[sndNum[], repMzw];
    pL0f = plusN[timesN[pp, v1], timesN[qq, v2]];
    pL0s = plusN[timesN[pp, v2], timesN[qq, v1]];
    innerL = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[],
        HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[plusC,
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, fstPQ], REFL[v1]]],
          HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sndPQ], REFL[v2]]]],
      HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[plusC,
          HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, fstPQ], REFL[v2]]],
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sndPQ], REFL[v1]]]];
    lhsStep1 = TRANS[ufMulL,
      HOL`Equal`APTERM[absIntConst[],
        HOL`Equal`APTERM[intCanonConst[], innerL]]];
    (* LHS = ABS_int(intCanon(pp*v1+qq*v2, pp*v2+qq*v1)) *)
    ezw = canonEquivAt[zw1, zw2];                  (* pp + zw2 = zw1 + qq *)
    eL1 = scaleDistribEquivRight[v1, ezw, pp, qq,
      timesN[z1, w1], timesN[z2, w2], timesN[z1, w2], timesN[z2, w1]];
    eL2 = scaleDistribEquivRight[v2, ezw, pp, qq,
      timesN[z1, w1], timesN[z2, w2], timesN[z1, w2], timesN[z2, w1]];
    lf = plusN[plusN[tripL[z1, w1, v1], tripL[z2, w2, v1]],
              plusN[tripL[z1, w2, v2], tripL[z2, w1, v2]]];
    ls = plusN[plusN[tripL[z1, w1, v2], tripL[z2, w2, v2]],
              plusN[tripL[z1, w2, v1], tripL[z2, w1, v1]]];
    respInstL = HOL`Bool`SPEC[ls, HOL`Bool`SPEC[lf,
      HOL`Bool`SPEC[pL0s, HOL`Bool`SPEC[pL0f, canonRespectsThm]]]];
    targetL = mkEq[plusN[pL0f, ls], plusN[lf, pL0s]];
    hImpL = HOL`Auto`Arith`arithProve[
      impliesTm[concl[eL1], impliesTm[concl[eL2], targetL]]];
    respL = HOL`Bool`MP[respInstL, HOL`Bool`MP[HOL`Bool`MP[hImpL, eL1], eL2]];
    lhsStep2 = TRANS[lhsStep1, HOL`Equal`APTERM[absIntConst[], respL]];
    (* LHS = ABS_int(intCanon L) *)

    (* ---- RHS = intMul z (intMul w v) ---- *)
    mulWV = intMulTm[wV, vV];
    ufMulR = unfoldIntMul[zV, mulWV];
    repMwv = repIntMulAt[wV, vV];                  (* REP(intMul w v) = cpWV *)
    fstRS = HOL`Equal`APTERM[fstNum[], repMwv];    (* FST(REP mulWV) = rr *)
    sndRS = HOL`Equal`APTERM[sndNum[], repMwv];
    pR0f = plusN[timesN[z1, rr], timesN[z2, ss]];
    pR0s = plusN[timesN[z1, ss], timesN[z2, rr]];
    innerR = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[],
        HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[plusC,
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, REFL[z1]], fstRS]],
          HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, REFL[z2]], sndRS]]],
      HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[plusC,
          HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, REFL[z1]], sndRS]],
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, REFL[z2]], fstRS]]];
    rhsStep1 = TRANS[ufMulR,
      HOL`Equal`APTERM[absIntConst[],
        HOL`Equal`APTERM[intCanonConst[], innerR]]];
    (* RHS = ABS_int(intCanon(z1*rr+z2*ss, z1*ss+z2*rr)) *)
    ewv = canonEquivAt[wv1, wv2];                  (* rr + wv2 = wv1 + ss *)
    eR1 = scaleDistribEquiv[z1, ewv, rr, ss,
      timesN[w1, v1], timesN[w2, v2], timesN[w1, v2], timesN[w2, v1]];
    eR2 = scaleDistribEquiv[z2, ewv, rr, ss,
      timesN[w1, v1], timesN[w2, v2], timesN[w1, v2], timesN[w2, v1]];
    rf = plusN[plusN[tripR[z1, w1, v1], tripR[z1, w2, v2]],
              plusN[tripR[z2, w1, v2], tripR[z2, w2, v1]]];
    rs = plusN[plusN[tripR[z1, w1, v2], tripR[z1, w2, v1]],
              plusN[tripR[z2, w1, v1], tripR[z2, w2, v2]]];
    respInstR = HOL`Bool`SPEC[rs, HOL`Bool`SPEC[rf,
      HOL`Bool`SPEC[pR0s, HOL`Bool`SPEC[pR0f, canonRespectsThm]]]];
    targetR = mkEq[plusN[pR0f, rs], plusN[rf, pR0s]];
    hImpR = HOL`Auto`Arith`arithProve[
      impliesTm[concl[eR1], impliesTm[concl[eR2], targetR]]];
    respR = HOL`Bool`MP[respInstR, HOL`Bool`MP[HOL`Bool`MP[hImpR, eR1], eR2]];
    rhsStep2 = TRANS[rhsStep1, HOL`Equal`APTERM[absIntConst[], respR]];
    (* RHS = ABS_int(intCanon R) *)

    (* ---- align L = R: same monomials, reassociated, via ARITH ---- *)
    h1 = timesAssocAt[z1, w1, v1]; h2 = timesAssocAt[z2, w2, v1];
    h3 = timesAssocAt[z1, w2, v2]; h4 = timesAssocAt[z2, w1, v2];
    fstImp = HOL`Auto`Arith`arithProve[
      impliesTm[concl[h1], impliesTm[concl[h2],
        impliesTm[concl[h3], impliesTm[concl[h4], mkEq[lf, rf]]]]]];
    fstAlign = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`MP[fstImp, h1], h2], h3], h4];
    g1 = timesAssocAt[z1, w1, v2]; g2 = timesAssocAt[z2, w2, v2];
    g3 = timesAssocAt[z1, w2, v1]; g4 = timesAssocAt[z2, w1, v1];
    sndImp = HOL`Auto`Arith`arithProve[
      impliesTm[concl[g1], impliesTm[concl[g2],
        impliesTm[concl[g3], impliesTm[concl[g4], mkEq[ls, rs]]]]]];
    sndAlign = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`MP[sndImp, g1], g2], g3], g4];
    pairLR = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[commaNumC[], fstAlign], sndAlign];   (* L = R *)
    absAlign = HOL`Equal`APTERM[absIntConst[],
      HOL`Equal`APTERM[intCanonConst[], pairLR]];
    body = TRANS[lhsStep2, TRANS[absAlign, HOL`Equal`SYM[rhsStep2]]];
    genV = HOL`Bool`GEN[vV, body];
    genW = HOL`Bool`GEN[wV, genV];
    HOL`Bool`GEN[zV, genW]
  ];

(* ============================================================ *)
(* intMulEqZeroThm: ⊢ ∀z w. intMul z w = &ℤ 0 ⇒ z = &ℤ 0 ∨ w = &ℤ 0. *)
(* ℤ has no zero divisors (integral domain).                    *)
(*                                                              *)
(* intMul z w = &ℤ 0 ⟹ REP(intMul z w) = (0,0) ⟹ (canonEquivAt)  *)
(* the two product-pair components are equal:                    *)
(*   z1*w1 + z2*w2 = z1*w2 + z2*w1   (KEY).                      *)
(* Case-split z, w on their canonical carve (one component each   *)
(* is 0); each leaf reduces KEY — via the vanishing products and  *)
(* ARITH — to a single surviving product = 0, then num            *)
(* multEqZeroThm gives a zero factor, which with the leaf's known  *)
(* zero component makes z (or w) = &ℤ 0.                          *)
(* ============================================================ *)

(* from FST(REP x) = 0 and SND(REP x) = 0 derive x = &ℤ 0 *)
intEqZeroFrom[xV_, rx_, fstEq_, sndEq_] :=
  Module[{surj, repX0, aVar, absRepX, zeroEq},
    surj = HOL`Bool`ISPEC[rx, HOL`Stdlib`Pair`pairSurjThm];
    repX0 = TRANS[HOL`Equal`SYM[surj],
      HOL`Kernel`MKCOMB[HOL`Equal`APTERM[commaNumC[], fstEq], sndEq]];   (* rx = (0,0) *)
    aVar = concl[absRepIntThm][[2]];
    absRepX = HOL`Kernel`INST[{aVar -> xV}, absRepIntThm];   (* ABS_int(rx) = x *)
    zeroEq = unfoldIntOfNum[zeroN[]];   (* &ℤ 0 = ABS_int(0,0) *)
    TRANS[HOL`Equal`SYM[absRepX],
      TRANS[HOL`Equal`APTERM[absIntConst[], repX0], HOL`Equal`SYM[zeroEq]]]
  ];

intMulEqZeroThm =
  Module[{zV, wV, rz, rw, z1, z2, w1, w2, zw1, zw2, plusC, timesC,
          intZero, zEqZeroTm, wEqZeroTm, H, repMul, repAtZero, repMulZero,
          canonZeroEq, fstCp0, sndCp0, cEq, lhsRw, rhsRw, eq2, key,
          disjZ, disjW, leaf, mainBody},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    rz = repIntTm[zV]; rw = repIntTm[wV];
    z1 = fstOf[rz]; z2 = sndOf[rz]; w1 = fstOf[rw]; w2 = sndOf[rw];
    plusC = HOL`Stdlib`Num`plusConst[]; timesC = timesNC[];
    zw1 = plusN[timesN[z1, w1], timesN[z2, w2]];
    zw2 = plusN[timesN[z1, w2], timesN[z2, w1]];
    intZero = intOfNumTm[zeroN[]];
    zEqZeroTm = mkEq[zV, intZero]; wEqZeroTm = mkEq[wV, intZero];
    H = ASSUME[mkEq[intMulTm[zV, wV], intZero]];
    repMul = repIntMulAt[zV, wV];   (* REP(intMul z w) = intCanon(zw1,zw2) *)
    repAtZero = HOL`Kernel`INST[{mkVar["n", numTy] -> zeroN[]}, repIntOfNumThm];
    repMulZero = TRANS[HOL`Equal`APTERM[repIntConst[], H], repAtZero];
    canonZeroEq = TRANS[HOL`Equal`SYM[repMul], repMulZero];   (* intCanon(zw1,zw2) = (0,0) *)
    fstCp0 = TRANS[HOL`Equal`APTERM[fstNum[], canonZeroEq], fstNumPairThm[zeroN[], zeroN[]]];
    sndCp0 = TRANS[HOL`Equal`APTERM[sndNum[], canonZeroEq], sndNumPairThm[zeroN[], zeroN[]]];
    cEq = canonEquivAt[zw1, zw2];   (* FST(cp)+zw2 = zw1+SND(cp) *)
    lhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fstCp0], REFL[zw2]];
    rhsRw = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, REFL[zw1]], sndCp0];
    eq2 = TRANS[TRANS[HOL`Equal`SYM[lhsRw], cEq], rhsRw];   (* 0+zw2 = zw1+0 *)
    key = TRANS[TRANS[
      HOL`Equal`SYM[HOL`Bool`SPEC[zw2, HOL`Stdlib`Num`addLeftZeroThm]], eq2],
      HOL`Bool`SPEC[zw1, HOL`Stdlib`Num`plusZeroEqThm]];   (* zw2 = zw1 *)
    disjZ = EQMP[unfoldIntRep[rz], intRepRepThm];   (* z1=0 ∨ z2=0 *)
    disjW = EQMP[unfoldIntRep[rw],
      HOL`Kernel`INST[{zV -> wV}, intRepRepThm]];   (* w1=0 ∨ w2=0 *)

    leaf[zZeroEq_, zIsFst_, wZeroEq_, wIsFst_] :=
      Module[{zZ, zS, wZ, wS, survProd, vZZwZ, vZZwS, vZSwZ, survImp,
              survZero, mez, zSz, wSz, zRes, wRes, zBranch, wBranch},
        zZ = If[zIsFst, z1, z2]; zS = If[zIsFst, z2, z1];
        wZ = If[wIsFst, w1, w2]; wS = If[wIsFst, w2, w1];
        survProd = timesN[zS, wS];
        vZZwZ = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, zZeroEq], REFL[wZ]],
          HOL`Bool`SPEC[wZ, HOL`Stdlib`Num`timesLeftZeroThm]];
        vZZwS = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, zZeroEq], REFL[wS]],
          HOL`Bool`SPEC[wS, HOL`Stdlib`Num`timesLeftZeroThm]];
        vZSwZ = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, REFL[zS]], wZeroEq],
          HOL`Bool`SPEC[zS, HOL`Stdlib`Num`timesZeroEqThm]];
        survImp = HOL`Auto`Arith`arithProve[
          impliesTm[concl[key], impliesTm[concl[vZZwZ], impliesTm[concl[vZZwS],
            impliesTm[concl[vZSwZ], mkEq[survProd, zeroN[]]]]]]];
        survZero = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
          survImp, key], vZZwZ], vZZwS], vZSwZ];   (* zS*wS = 0 *)
        mez = HOL`Bool`MP[
          HOL`Bool`SPEC[wS, HOL`Bool`SPEC[zS, HOL`Stdlib`Num`multEqZeroThm]],
          survZero];   (* zS = 0 ∨ wS = 0 *)
        zSz = ASSUME[mkEq[zS, zeroN[]]]; wSz = ASSUME[mkEq[wS, zeroN[]]];
        zRes = intEqZeroFrom[zV, rz,
          If[zIsFst, zZeroEq, zSz], If[zIsFst, zSz, zZeroEq]];
        wRes = intEqZeroFrom[wV, rw,
          If[wIsFst, wZeroEq, wSz], If[wIsFst, wSz, wZeroEq]];
        zBranch = HOL`Bool`DISJ1[zRes, wEqZeroTm];
        wBranch = HOL`Bool`DISJ2[wRes, zEqZeroTm];
        HOL`Bool`DISJCASES[mez, zBranch, wBranch]
      ];

    mainBody = HOL`Bool`DISJCASES[disjZ,
      HOL`Bool`DISJCASES[disjW,
        leaf[ASSUME[mkEq[z1, zeroN[]]], True, ASSUME[mkEq[w1, zeroN[]]], True],
        leaf[ASSUME[mkEq[z1, zeroN[]]], True, ASSUME[mkEq[w2, zeroN[]]], False]],
      HOL`Bool`DISJCASES[disjW,
        leaf[ASSUME[mkEq[z2, zeroN[]]], False, ASSUME[mkEq[w1, zeroN[]]], True],
        leaf[ASSUME[mkEq[z2, zeroN[]]], False, ASSUME[mkEq[w2, zeroN[]]], False]]];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV,
      HOL`Bool`DISCH[mkEq[intMulTm[zV, wV], intZero], mainBody]]]
  ];

(* ============================================================ *)
(* Order: intLe / intLt — REP-based, subtraction-free.          *)
(*   intLe z w ⟺ z1 + w2 ≤ w1 + z2   (i.e. z1−z2 ≤ w1−w2),      *)
(*   intLt z w ⟺ z1 + w2 < w1 + z2,   zi/wi = FST/SND of REP.    *)
(* Reflexivity/totality are ℕ leqRefl/leqTotal on the two sums;  *)
(* transitivity is ℕ-linear (ARITH); antisymmetry uses           *)
(* canonInjThm (the equal-sum hypothesis says REP z ≈ REP w, so  *)
(* the canonical reps coincide). intLt = ¬(intLe w z) via the    *)
(* ℕ order-trichotomy negation notLeqEqLtThm.                    *)
(* ============================================================ *)

leSum[zT_, wT_] := plusN[fstOf[repIntTm[zT]], sndOf[repIntTm[wT]]];   (* z1 + w2 *)
intLeTy = tyFun[intTy, tyFun[intTy, boolTy]];

intLeDefThm = newDefinition[mkEq[mkVar["intLe", intLeTy],
  Module[{zV, wV}, zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    mkAbs[zV, mkAbs[wV, leqNum[leSum[zV, wV], leSum[wV, zV]]]]]]];
intLeConst[] := mkConst["intLe", intLeTy];
intLeTm[zT_, wT_] := mkComb[mkComb[intLeConst[], zT], wT];

unfoldIntLe[zT_, wT_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[intLeDefThm, zT];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, wT];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ ∀z. intLe z z *)
intLeReflThm =
  Module[{zV, z1, z2, refl},
    zV = mkVar["z", intTy];
    z1 = fstOf[repIntTm[zV]]; z2 = sndOf[repIntTm[zV]];
    refl = HOL`Bool`SPEC[plusN[z1, z2], HOL`Stdlib`Num`leqReflThm];
    HOL`Bool`GEN[zV, EQMP[HOL`Equal`SYM[unfoldIntLe[zV, zV]], refl]]
  ];

(* ⊢ ∀z w. intLe z w ⇒ intLe w z ⇒ z = w *)
intLeAntisymThm =
  Module[{zV, wV, rz, rw, h1, h2, le1, le2, eqSum, injInst, repZW,
          aVar, absRepZ, absRepW, zEqW},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    rz = repIntTm[zV]; rw = repIntTm[wV];
    h1 = ASSUME[intLeTm[zV, wV]]; h2 = ASSUME[intLeTm[wV, zV]];
    le1 = EQMP[unfoldIntLe[zV, wV], h1];   (* z1+w2 ≤ w1+z2 *)
    le2 = EQMP[unfoldIntLe[wV, zV], h2];   (* w1+z2 ≤ z1+w2 *)
    eqSum = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[leSum[wV, zV], HOL`Bool`SPEC[leSum[zV, wV],
        HOL`Stdlib`Num`leqAntisymThm]], le1], le2];   (* z1+w2 = w1+z2 *)
    injInst = HOL`Bool`SPEC[rw, HOL`Bool`SPEC[rz, canonInjThm]];
    repZW = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[injInst, intRepRepThm],
      HOL`Kernel`INST[{zV -> wV}, intRepRepThm]], eqSum];   (* REP z = REP w *)
    aVar = concl[absRepIntThm][[2]];
    absRepZ = HOL`Kernel`INST[{aVar -> zV}, absRepIntThm];
    absRepW = HOL`Kernel`INST[{aVar -> wV}, absRepIntThm];
    zEqW = TRANS[HOL`Equal`SYM[absRepZ],
      TRANS[HOL`Equal`APTERM[absIntConst[], repZW], absRepW]];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV,
      HOL`Bool`DISCH[intLeTm[zV, wV],
        HOL`Bool`DISCH[intLeTm[wV, zV], zEqW]]]]
  ];

(* ⊢ ∀z w v. intLe z w ⇒ intLe w v ⇒ intLe z v *)
intLeTransThm =
  Module[{zV, wV, vV, z1, z2, v1, v2, h1, h2, le1, le2, goalLeq, imp, leZV},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy]; vV = mkVar["v", intTy];
    z1 = fstOf[repIntTm[zV]]; z2 = sndOf[repIntTm[zV]];
    v1 = fstOf[repIntTm[vV]]; v2 = sndOf[repIntTm[vV]];
    h1 = ASSUME[intLeTm[zV, wV]]; h2 = ASSUME[intLeTm[wV, vV]];
    le1 = EQMP[unfoldIntLe[zV, wV], h1];   (* z1+w2 ≤ w1+z2 *)
    le2 = EQMP[unfoldIntLe[wV, vV], h2];   (* w1+v2 ≤ v1+w2 *)
    goalLeq = leqNum[plusN[z1, v2], plusN[v1, z2]];   (* z1+v2 ≤ v1+z2 *)
    imp = HOL`Auto`Arith`arithProve[
      impliesTm[concl[le1], impliesTm[concl[le2], goalLeq]]];
    leZV = HOL`Bool`MP[HOL`Bool`MP[imp, le1], le2];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV, HOL`Bool`GEN[vV,
      HOL`Bool`DISCH[intLeTm[zV, wV], HOL`Bool`DISCH[intLeTm[wV, vV],
        EQMP[HOL`Equal`SYM[unfoldIntLe[zV, vV]], leZV]]]]]]
  ];

(* ⊢ ∀z w. intLe z w ∨ intLe w z *)
intLeTotalThm =
  Module[{zV, wV, total, eqL, eqR, disjEq},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    total = HOL`Bool`SPEC[leSum[wV, zV], HOL`Bool`SPEC[leSum[zV, wV],
      HOL`Stdlib`Num`leqTotalThm]];
    eqL = HOL`Equal`SYM[unfoldIntLe[zV, wV]];
    eqR = HOL`Equal`SYM[unfoldIntLe[wV, zV]];
    disjEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[orC[], eqL], eqR];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV, EQMP[disjEq, total]]]
  ];

ltNumI[aTm_, bTm_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], aTm], bTm];
intLtTy = tyFun[intTy, tyFun[intTy, boolTy]];

intLtDefThm = newDefinition[mkEq[mkVar["intLt", intLtTy],
  Module[{zV, wV}, zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    mkAbs[zV, mkAbs[wV, ltNumI[leSum[zV, wV], leSum[wV, zV]]]]]]];
intLtConst[] := mkConst["intLt", intLtTy];
intLtTm[zT_, wT_] := mkComb[mkComb[intLtConst[], zT], wT];

unfoldIntLt[zT_, wT_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[intLtDefThm, zT];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, wT];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ ∀z w. intLt z w = ¬ (intLe w z) *)
intLtNotLeThm =
  Module[{zV, wV, step1, nleEqLt, unfoldLtZW},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    step1 = HOL`Equal`APTERM[notOp[], unfoldIntLe[wV, zV]];
    (* ¬(intLe w z) = ¬((w1+z2) ≤ (z1+w2)) *)
    nleEqLt = HOL`Bool`SPEC[leSum[zV, wV], HOL`Bool`SPEC[leSum[wV, zV],
      HOL`Stdlib`Num`notLeqEqLtThm]];
    (* ¬((w1+z2) ≤ (z1+w2)) = ((z1+w2) < (w1+z2)) *)
    unfoldLtZW = unfoldIntLt[zV, wV];   (* intLt z w = (z1+w2) < (w1+z2) *)
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV,
      TRANS[unfoldLtZW, HOL`Equal`SYM[TRANS[step1, nleEqLt]]]]]
  ];

(* ============================================================ *)
(* Order/arithmetic compatibility.                              *)
(*   intLeAddMonoThm: intLe z w ⇒ intLe (z+u) (w+u).            *)
(*   intLeNegThm:     intLe z w ⇒ intLe (−w) (−z).             *)
(* Both unfold intLe at the operation result, whose REP FST/SND  *)
(* are opaque canon (add) / a swap (neg). Add: canonEquivAt at   *)
(* the two summed pairs relates those to the raw sums, and ARITH  *)
(* closes the residual ℕ ≤. Neg: repIntNegThm rewrites the       *)
(* swapped REP, leaving a commuted copy of the hypothesis.       *)
(* ============================================================ *)

(* ⊢ ∀z w u. intLe z w ⇒ intLe (intAdd z u) (intAdd w u) *)
intLeAddMonoThm =
  Module[{zV, wV, uV, z1, z2, w1, w2, u1, u2, plusC, leqC, hypLe, leZW,
          addZU, addWU, pZU, pWU, cpZU, cpWU, aa, bb, cc, dd, repZU, repWU,
          rFstZU, rSndZU, rFstWU, rSndWU, ezu, ewu, goalLeq, imp, leqABCD,
          unfoldGoal, eqX, eqY, leqEq, final},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy]; uV = mkVar["u", intTy];
    z1 = fstOf[repIntTm[zV]]; z2 = sndOf[repIntTm[zV]];
    w1 = fstOf[repIntTm[wV]]; w2 = sndOf[repIntTm[wV]];
    u1 = fstOf[repIntTm[uV]]; u2 = sndOf[repIntTm[uV]];
    plusC = HOL`Stdlib`Num`plusConst[]; leqC = HOL`Stdlib`Num`leqConst[];
    hypLe = ASSUME[intLeTm[zV, wV]];
    leZW = EQMP[unfoldIntLe[zV, wV], hypLe];   (* z1+w2 ≤ w1+z2 *)
    addZU = intAddTm[zV, uV]; addWU = intAddTm[wV, uV];
    pZU = intAddPairTm[zV, uV]; pWU = intAddPairTm[wV, uV];
    cpZU = mkComb[intCanonConst[], pZU]; cpWU = mkComb[intCanonConst[], pWU];
    aa = fstOf[cpZU]; bb = sndOf[cpZU]; cc = fstOf[cpWU]; dd = sndOf[cpWU];
    repZU = repIntAddAt[zV, uV]; repWU = repIntAddAt[wV, uV];
    rFstZU = HOL`Equal`APTERM[fstNum[], repZU];   (* FST(R(z+u)) = aa *)
    rSndZU = HOL`Equal`APTERM[sndNum[], repZU];   (* SND(R(z+u)) = bb *)
    rFstWU = HOL`Equal`APTERM[fstNum[], repWU];
    rSndWU = HOL`Equal`APTERM[sndNum[], repWU];
    ezu = canonEquivAt[plusN[z1, u1], plusN[z2, u2]];   (* aa+(z2+u2) = (z1+u1)+bb *)
    ewu = canonEquivAt[plusN[w1, u1], plusN[w2, u2]];   (* cc+(w2+u2) = (w1+u1)+dd *)
    goalLeq = leqNum[plusN[aa, dd], plusN[cc, bb]];   (* aa+dd ≤ cc+bb *)
    imp = HOL`Auto`Arith`arithProve[
      impliesTm[concl[ezu], impliesTm[concl[ewu],
        impliesTm[concl[leZW], goalLeq]]]];
    leqABCD = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[imp, ezu], ewu], leZW];
    unfoldGoal = unfoldIntLe[addZU, addWU];
    eqX = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, rFstZU], rSndWU];
    eqY = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, rFstWU], rSndZU];
    leqEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[leqC, eqX], eqY];
    final = EQMP[HOL`Equal`SYM[TRANS[unfoldGoal, leqEq]], leqABCD];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV, HOL`Bool`GEN[uV,
      HOL`Bool`DISCH[intLeTm[zV, wV], final]]]]
  ];

(* ⊢ ∀z w. intLe z w ⇒ intLe (intNeg w) (intNeg z) *)
intLeNegThm =
  Module[{zV, wV, z1, z2, w1, w2, plusC, leqC, hypLe, leZW, negW, negZ,
          repNegW, repNegZ, fstNegW, sndNegW, fstNegZ, sndNegZ, goalLeq,
          imp, leqWZ, unfoldGoal, eqX, eqY, leqEq, final},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy];
    z1 = fstOf[repIntTm[zV]]; z2 = sndOf[repIntTm[zV]];
    w1 = fstOf[repIntTm[wV]]; w2 = sndOf[repIntTm[wV]];
    plusC = HOL`Stdlib`Num`plusConst[]; leqC = HOL`Stdlib`Num`leqConst[];
    hypLe = ASSUME[intLeTm[zV, wV]];
    leZW = EQMP[unfoldIntLe[zV, wV], hypLe];   (* z1+w2 ≤ w1+z2 *)
    negW = intNegTm[wV]; negZ = intNegTm[zV];
    repNegW = HOL`Kernel`INST[{zV -> wV}, repIntNegThm];   (* REP(−w) = (w2,w1) *)
    repNegZ = repIntNegThm;                                (* REP(−z) = (z2,z1) *)
    fstNegW = TRANS[HOL`Equal`APTERM[fstNum[], repNegW], fstNumPairThm[w2, w1]];
    sndNegW = TRANS[HOL`Equal`APTERM[sndNum[], repNegW], sndNumPairThm[w2, w1]];
    fstNegZ = TRANS[HOL`Equal`APTERM[fstNum[], repNegZ], fstNumPairThm[z2, z1]];
    sndNegZ = TRANS[HOL`Equal`APTERM[sndNum[], repNegZ], sndNumPairThm[z2, z1]];
    goalLeq = leqNum[plusN[w2, z1], plusN[z2, w1]];   (* w2+z1 ≤ z2+w1 *)
    imp = HOL`Auto`Arith`arithProve[impliesTm[concl[leZW], goalLeq]];
    leqWZ = HOL`Bool`MP[imp, leZW];
    unfoldGoal = unfoldIntLe[negW, negZ];
    eqX = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fstNegW], sndNegZ];
    eqY = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fstNegZ], sndNegW];
    leqEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[leqC, eqX], eqY];
    final = EQMP[HOL`Equal`SYM[TRANS[unfoldGoal, leqEq]], leqWZ];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV,
      HOL`Bool`DISCH[intLeTm[zV, wV], final]]]
  ];

(* ============================================================ *)
(* intLeMulNonnegThm: ⊢ ∀z w u.                                 *)
(*   intLe (&ℤ 0) u ⇒ intLe z w ⇒ intLe (intMul u z) (intMul u w). *)
(*                                                              *)
(* intLe (&ℤ 0) u unfolds to u2 ≤ u1 (REP(&ℤ0) = (0,0)). The     *)
(* goal unfolds to aa+dd ≤ cc+bb over the opaque canon FST/SND of *)
(* the two product REPs; canonEquivAt at the product pairs       *)
(* relates those to the raw product sums, reducing it to the ℕ   *)
(* inequality KEY (fUZ + sUW ≤ fUW + sUZ). KEY is the cross       *)
(* inequality crossMultLeqThm at (u1, u2, z1+w2, w1+z2), with its *)
(* product-of-sums distributed back to monomials; ARITH does the  *)
(* two linear gluing steps. (Products are opaque to ARITH, so the *)
(* multiplicative content lives entirely in crossMultLeqThm.)     *)
(* ============================================================ *)

intLeMulNonnegThm =
  Module[{zV, wV, uV, z1, z2, w1, w2, u1, u2, plusC, leqC, intZero, hyp0,
          le0u, repAtZero, fstZ0, sndZ0, lhsEq, rhsEq, u2leU1, hypZW, leZW,
          mulUZ, mulUW, cpUZ, cpUW, aa, bb, cc, dd, repUZ, repUW, rFstUZ,
          rSndUZ, rFstUW, rSndUW, fUZ, sUZ, fUW, sUW, euz, euw, crossInst,
          crossApplied, d1, d2, d3, d4, keyGoal, keyImp, key, goalABCD,
          abcdImp, leqABCD, unfoldGoal, eqX, eqY, leqEq, final},
    zV = mkVar["z", intTy]; wV = mkVar["w", intTy]; uV = mkVar["u", intTy];
    z1 = fstOf[repIntTm[zV]]; z2 = sndOf[repIntTm[zV]];
    w1 = fstOf[repIntTm[wV]]; w2 = sndOf[repIntTm[wV]];
    u1 = fstOf[repIntTm[uV]]; u2 = sndOf[repIntTm[uV]];
    plusC = HOL`Stdlib`Num`plusConst[]; leqC = HOL`Stdlib`Num`leqConst[];
    intZero = intOfNumTm[zeroN[]];
    hyp0 = ASSUME[intLeTm[intZero, uV]];
    le0u = EQMP[unfoldIntLe[intZero, uV], hyp0];
    repAtZero = HOL`Kernel`INST[{mkVar["n", numTy] -> zeroN[]}, repIntOfNumThm];
    fstZ0 = TRANS[HOL`Equal`APTERM[fstNum[], repAtZero], fstNumPairThm[zeroN[], zeroN[]]];
    sndZ0 = TRANS[HOL`Equal`APTERM[sndNum[], repAtZero], sndNumPairThm[zeroN[], zeroN[]]];
    lhsEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fstZ0], REFL[u2]],
      HOL`Bool`SPEC[u2, HOL`Stdlib`Num`addLeftZeroThm]];   (* FST(R&ℤ0)+u2 = u2 *)
    rhsEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, REFL[u1]], sndZ0],
      HOL`Bool`SPEC[u1, HOL`Stdlib`Num`plusZeroEqThm]];   (* u1+SND(R&ℤ0) = u1 *)
    u2leU1 = EQMP[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[leqC, lhsEq], rhsEq], le0u];
    hypZW = ASSUME[intLeTm[zV, wV]];
    leZW = EQMP[unfoldIntLe[zV, wV], hypZW];   (* z1+w2 ≤ w1+z2 *)
    mulUZ = intMulTm[uV, zV]; mulUW = intMulTm[uV, wV];
    cpUZ = mkComb[intCanonConst[], intMulPairTm[uV, zV]];
    cpUW = mkComb[intCanonConst[], intMulPairTm[uV, wV]];
    aa = fstOf[cpUZ]; bb = sndOf[cpUZ]; cc = fstOf[cpUW]; dd = sndOf[cpUW];
    repUZ = repIntMulAt[uV, zV]; repUW = repIntMulAt[uV, wV];
    rFstUZ = HOL`Equal`APTERM[fstNum[], repUZ]; rSndUZ = HOL`Equal`APTERM[sndNum[], repUZ];
    rFstUW = HOL`Equal`APTERM[fstNum[], repUW]; rSndUW = HOL`Equal`APTERM[sndNum[], repUW];
    fUZ = plusN[timesN[u1, z1], timesN[u2, z2]]; sUZ = plusN[timesN[u1, z2], timesN[u2, z1]];
    fUW = plusN[timesN[u1, w1], timesN[u2, w2]]; sUW = plusN[timesN[u1, w2], timesN[u2, w1]];
    euz = canonEquivAt[fUZ, sUZ];   (* aa + sUZ = fUZ + bb *)
    euw = canonEquivAt[fUW, sUW];   (* cc + sUW = fUW + dd *)
    (* KEY: fUZ + sUW ≤ fUW + sUZ, via crossMultLeqThm *)
    crossInst = HOL`Bool`SPEC[plusN[w1, z2], HOL`Bool`SPEC[plusN[z1, w2],
      HOL`Bool`SPEC[u2, HOL`Bool`SPEC[u1, HOL`Stdlib`Num`crossMultLeqThm]]]];
    crossApplied = HOL`Bool`MP[HOL`Bool`MP[crossInst, u2leU1], leZW];
    (* u1*(z1+w2)+u2*(w1+z2) ≤ u1*(w1+z2)+u2*(z1+w2) *)
    d1 = timesDistribLeftAt[u1, z1, w2]; d2 = timesDistribLeftAt[u2, w1, z2];
    d3 = timesDistribLeftAt[u1, w1, z2]; d4 = timesDistribLeftAt[u2, z1, w2];
    keyGoal = leqNum[plusN[fUZ, sUW], plusN[fUW, sUZ]];
    keyImp = HOL`Auto`Arith`arithProve[
      impliesTm[concl[crossApplied], impliesTm[concl[d1], impliesTm[concl[d2],
        impliesTm[concl[d3], impliesTm[concl[d4], keyGoal]]]]]];
    key = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
      keyImp, crossApplied], d1], d2], d3], d4];
    goalABCD = leqNum[plusN[aa, dd], plusN[cc, bb]];
    abcdImp = HOL`Auto`Arith`arithProve[
      impliesTm[concl[euz], impliesTm[concl[euw], impliesTm[keyGoal, goalABCD]]]];
    leqABCD = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[abcdImp, euz], euw], key];
    unfoldGoal = unfoldIntLe[mulUZ, mulUW];
    eqX = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, rFstUZ], rSndUW];
    eqY = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, rFstUW], rSndUZ];
    leqEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[leqC, eqX], eqY];
    final = EQMP[HOL`Equal`SYM[TRANS[unfoldGoal, leqEq]], leqABCD];
    HOL`Bool`GEN[zV, HOL`Bool`GEN[wV, HOL`Bool`GEN[uV,
      HOL`Bool`DISCH[intLeTm[intZero, uV],
        HOL`Bool`DISCH[intLeTm[zV, wV], final]]]]]
  ];

(* ============================================================ *)
(* &ℤ : num → int is a ring/order homomorphism.                 *)
(*   &ℤ(m+n) = intAdd (&ℤ m) (&ℤ n)                             *)
(*   &ℤ(m*n) = intMul (&ℤ m) (&ℤ n)                             *)
(*   intLe (&ℤ m) (&ℤ n) = (m ≤ n)                              *)
(* REP(&ℤ k) = (k, 0) is already canonical, so the operation     *)
(* pair simplifies to (m+n, 0) / (m*n, 0) and intCanonIdThm      *)
(* returns it unchanged; the order one needs no canon (m+0 = m). *)
(* ============================================================ *)

(* ⊢ FST(REP(&ℤ m)) = m  and  SND(REP(&ℤ m)) = 0 *)
repFstSnd[mTm_] :=
  Module[{rep},
    rep = HOL`Kernel`INST[{mkVar["n", numTy] -> mTm}, repIntOfNumThm];
    {TRANS[HOL`Equal`APTERM[fstNum[], rep], fstNumPairThm[mTm, zeroN[]]],
     TRANS[HOL`Equal`APTERM[sndNum[], rep], sndNumPairThm[mTm, zeroN[]]]}];

intOfNumAddThm =
  Module[{mV, nV, zM, zN, plusC, ufAdd, fm, sm, fn, sn, fstSum, sndSum, pairEq,
          natPair, repNat, canonId, canonChain, absChain, ufOfNum},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    zM = intOfNumTm[mV]; zN = intOfNumTm[nV];
    plusC = HOL`Stdlib`Num`plusConst[];
    ufAdd = unfoldIntAdd[zM, zN];
    {fm, sm} = repFstSnd[mV]; {fn, sn} = repFstSnd[nV];
    fstSum = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fm], fn];
    sndSum = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, sm], sn],
      HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`addLeftZeroThm]];
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[commaNumC[], fstSum], sndSum];
    natPair = numPairCons[plusN[mV, nV], zeroN[]];
    repNat = HOL`Kernel`INST[{mkVar["n", numTy] -> plusN[mV, nV]}, intRepNatPairThm];
    canonId = HOL`Bool`MP[HOL`Bool`SPEC[natPair, intCanonIdThm], repNat];
    canonChain = TRANS[HOL`Equal`APTERM[intCanonConst[], pairEq], canonId];
    absChain = HOL`Equal`APTERM[absIntConst[], canonChain];
    ufOfNum = unfoldIntOfNum[plusN[mV, nV]];
    HOL`Bool`GEN[mV, HOL`Bool`GEN[nV,
      TRANS[ufOfNum, HOL`Equal`SYM[TRANS[ufAdd, absChain]]]]]
  ];

intOfNumMulThm =
  Module[{mV, nV, zM, zN, ufMul, fm, sm, fn, sn, plusC, timesC, m1n1, m2n2,
          fstComp, m1n2, m2n1, sndComp, pairEq, natPair, repNat, canonId,
          canonChain, absChain, ufOfNum},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    zM = intOfNumTm[mV]; zN = intOfNumTm[nV];
    plusC = HOL`Stdlib`Num`plusConst[]; timesC = timesNC[];
    ufMul = unfoldIntMul[zM, zN];
    {fm, sm} = repFstSnd[mV]; {fn, sn} = repFstSnd[nV];
    m1n1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, fm], fn];   (* F*F = m*n *)
    m2n2 = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sm], sn],
      HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`timesLeftZeroThm]];   (* S*S = 0 *)
    fstComp = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, m1n1], m2n2],
      HOL`Bool`SPEC[timesN[mV, nV], HOL`Stdlib`Num`plusZeroEqThm]];   (* = m*n *)
    m1n2 = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, fm], sn],
      HOL`Bool`SPEC[mV, HOL`Stdlib`Num`timesZeroEqThm]];   (* m*0 = 0 *)
    m2n1 = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[timesC, sm], fn],
      HOL`Bool`SPEC[nV, HOL`Stdlib`Num`timesLeftZeroThm]];   (* 0*n = 0 *)
    sndComp = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, m1n2], m2n1],
      HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`addLeftZeroThm]];   (* = 0 *)
    pairEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[commaNumC[], fstComp], sndComp];
    natPair = numPairCons[timesN[mV, nV], zeroN[]];
    repNat = HOL`Kernel`INST[{mkVar["n", numTy] -> timesN[mV, nV]}, intRepNatPairThm];
    canonId = HOL`Bool`MP[HOL`Bool`SPEC[natPair, intCanonIdThm], repNat];
    canonChain = TRANS[HOL`Equal`APTERM[intCanonConst[], pairEq], canonId];
    absChain = HOL`Equal`APTERM[absIntConst[], canonChain];
    ufOfNum = unfoldIntOfNum[timesN[mV, nV]];
    HOL`Bool`GEN[mV, HOL`Bool`GEN[nV,
      TRANS[ufOfNum, HOL`Equal`SYM[TRANS[ufMul, absChain]]]]]
  ];

intOfNumLeThm =
  Module[{mV, nV, zM, zN, ufLe, fm, sm, fn, sn, plusC, leqC, lhsEq, rhsEq, leqEq},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    zM = intOfNumTm[mV]; zN = intOfNumTm[nV];
    plusC = HOL`Stdlib`Num`plusConst[]; leqC = HOL`Stdlib`Num`leqConst[];
    ufLe = unfoldIntLe[zM, zN];
    {fm, sm} = repFstSnd[mV]; {fn, sn} = repFstSnd[nV];
    lhsEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fm], sn],
      HOL`Bool`SPEC[mV, HOL`Stdlib`Num`plusZeroEqThm]];   (* FST(Rm)+SND(Rn) = m *)
    rhsEq = TRANS[HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC, fn], sm],
      HOL`Bool`SPEC[nV, HOL`Stdlib`Num`plusZeroEqThm]];   (* FST(Rn)+SND(Rm) = n *)
    leqEq = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[leqC, lhsEq], rhsEq];
    HOL`Bool`GEN[mV, HOL`Bool`GEN[nV, TRANS[ufLe, leqEq]]]
  ];

(* ============================================================ *)
(* intAbs : int → int — |z| = &ℤ (FST(REP z) + SND(REP z)).      *)
(* One representative component is 0, so the sum is the nonzero   *)
(* part = |z|.                                                   *)
(* ============================================================ *)

intAbsTy = tyFun[intTy, intTy];

intAbsDefThm = newDefinition[mkEq[mkVar["intAbs", intAbsTy],
  Module[{zV}, zV = mkVar["z", intTy];
    mkAbs[zV, intOfNumTm[plusN[fstOf[repIntTm[zV]], sndOf[repIntTm[zV]]]]]]]];
intAbsConst[] := mkConst["intAbs", intAbsTy];
intAbsTm[zT_] := mkComb[intAbsConst[], zT];

unfoldIntAbs[zT_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intAbsDefThm, zT];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ ∀n. intAbs (&ℤ n) = &ℤ n *)
intAbsNumThm =
  Module[{nV, zN, ufAbs, fn, sn, sumEq},
    nV = mkVar["n", numTy]; zN = intOfNumTm[nV];
    ufAbs = unfoldIntAbs[zN];
    {fn, sn} = repFstSnd[nV];
    sumEq = TRANS[HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], fn], sn],
      HOL`Bool`SPEC[nV, HOL`Stdlib`Num`plusZeroEqThm]];   (* FST+SND = n+0 = n *)
    HOL`Bool`GEN[nV, TRANS[ufAbs, HOL`Equal`APTERM[intOfNumConst[], sumEq]]]
  ];

(* ⊢ ∀z. intAbs (intNeg z) = intAbs z *)
intAbsNegThm =
  Module[{zV, z1, z2, negZ, ufAbsNeg, repNeg, fstNeg, sndNeg, sumEq, commEq, ufAbsZ},
    zV = mkVar["z", intTy]; z1 = fstOf[repIntTm[zV]]; z2 = sndOf[repIntTm[zV]];
    negZ = intNegTm[zV];
    ufAbsNeg = unfoldIntAbs[negZ];
    repNeg = repIntNegThm;   (* REP(−z) = (z2,z1) *)
    fstNeg = TRANS[HOL`Equal`APTERM[fstNum[], repNeg], fstNumPairThm[z2, z1]];
    sndNeg = TRANS[HOL`Equal`APTERM[sndNum[], repNeg], sndNumPairThm[z2, z1]];
    sumEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], fstNeg], sndNeg];   (* = z2+z1 *)
    commEq = HOL`Bool`SPEC[z1, HOL`Bool`SPEC[z2, HOL`Stdlib`Num`addCommThm]];
    ufAbsZ = unfoldIntAbs[zV];
    HOL`Bool`GEN[zV, TRANS[ufAbsNeg, TRANS[
      HOL`Equal`APTERM[intOfNumConst[], TRANS[sumEq, commEq]],
      HOL`Equal`SYM[ufAbsZ]]]]
  ];

(* ⊢ ∀z. intLe (&ℤ 0) (intAbs z) *)
intAbsNonnegThm =
  Module[{zV, z1, z2, intZero, absEq, leInst, leZero, leAbsVal, congEq},
    zV = mkVar["z", intTy]; z1 = fstOf[repIntTm[zV]]; z2 = sndOf[repIntTm[zV]];
    intZero = intOfNumTm[zeroN[]];
    absEq = unfoldIntAbs[zV];   (* intAbs z = &ℤ(z1+z2) *)
    leInst = HOL`Bool`SPEC[plusN[z1, z2], HOL`Bool`SPEC[zeroN[], intOfNumLeThm]];
    leZero = HOL`Bool`SPEC[plusN[z1, z2], HOL`Stdlib`Num`leqZeroThm];
    leAbsVal = EQMP[HOL`Equal`SYM[leInst], leZero];   (* intLe(&ℤ0)(&ℤ(z1+z2)) *)
    congEq = HOL`Equal`APTERM[mkComb[intLeConst[], intZero], absEq];
    HOL`Bool`GEN[zV, EQMP[HOL`Equal`SYM[congEq], leAbsVal]]
  ];

End[];
EndPackage[];
