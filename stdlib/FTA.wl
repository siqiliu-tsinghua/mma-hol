(* ::Package:: *)

(* FTA prerequisites (deferred from M7-3): a small set of number-theory
   helpers that are the immediate building blocks for the unique
   factorization theorem. The capstone itself — primeOrCompositeThm
   dichotomy → primeDivExistsThm (every n > 1 has a prime divisor) →
   factorization existence over lists → uniqueness modulo permutation
   — is staged in follow-on commits. *)

BeginPackage["HOL`Stdlib`FTA`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Stdlib`Num`", "HOL`Stdlib`List`"
}];

dividesPosThm::usage = "dividesPosThm — ⊢ ∀d n. ¬ (n = 0) ⇒ divides d n ⇒ ¬ (d = 0). If n is non-zero and d divides n, then d is non-zero.";
dividesTransThm::usage = "dividesTransThm — ⊢ ∀a b c. divides a b ⇒ divides b c ⇒ divides a c. Transitivity of divisibility.";
notOneNorZeroLtThm::usage = "notOneNorZeroLtThm — ⊢ ∀d. ¬ (d = 0) ⇒ ¬ (d = SUC 0) ⇒ SUC 0 < d. A num that is neither 0 nor 1 must be > 1.";
primeOrCompositeThm::usage = "primeOrCompositeThm — ⊢ ∀n. SUC 0 < n ⇒ prime n ∨ (∃d. SUC 0 < d ∧ d < n ∧ divides d n). Dichotomy: every n > 1 is prime or has a proper divisor.";
primeDivExistsThm::usage = "primeDivExistsThm — ⊢ ∀n. SUC 0 < n ⇒ ∃p. prime p ∧ divides p n. Every n > 1 has a prime divisor (FTA stage-1 capstone).";

posAddLtThm::usage = "posAddLtThm — ⊢ ∀c d. ¬ (d = 0) ⇒ c < c + d. Adding a positive amount strictly increases. (FTA stage-2 helper.)";
ltMultIfOneLtThm::usage = "ltMultIfOneLtThm — ⊢ ∀p c. SUC 0 < p ⇒ ¬ (c = 0) ⇒ c < p * c. Multiplying a positive amount by p > 1 strictly increases. (FTA stage-2 helper.)";
primeFactorsExistsThm::usage = "primeFactorsExistsThm — ⊢ ∀n. ¬ (n = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n. Every positive integer admits a prime factorization (FTA stage-2 capstone).";

notLeqSucSelfThm::usage = "notLeqSucSelfThm — ⊢ ∀n. ¬ (SUC n ≤ n). (Stage 3.a helper.)";
primeNotDivOneThm::usage = "primeNotDivOneThm — ⊢ ∀p. prime p ⇒ ¬ (divides p (SUC 0)). A prime cannot divide 1. (Stage 3.a helper.)";
primeDivFoldrTimesThm::usage = "primeDivFoldrTimesThm — ⊢ ∀p l. prime p ⇒ divides p (FOLDR * (SUC 0) l) ⇒ ∃y. MEM y l ∧ divides p y. Euclid's lemma on lists: a prime dividing a product of primes divides one of them. (FTA stage 3.a.)";

permConst::usage = "permConst[] — PERM : α list → α list → bool. Smallest binary relation containing PERM NIL NIL and closed under (i) CONS congruence (PERM l1 l2 ⇒ PERM (CONS x l1) (CONS x l2)), (ii) adjacent swap (PERM (CONS x (CONS y l)) (CONS y (CONS x l))), (iii) transitivity.";
permDefThm::usage = "permDefThm — ⊢ PERM = (λl1 l2. ∀R. (R NIL NIL ∧ (∀x l1 l2. R l1 l2 ⇒ R (CONS x l1) (CONS x l2)) ∧ (∀x y l. R (CONS x (CONS y l)) (CONS y (CONS x l))) ∧ (∀l1 l2 l3. R l1 l2 ⇒ R l2 l3 ⇒ R l1 l3)) ⇒ R l1 l2).";
permNilThm::usage = "permNilThm — ⊢ PERM NIL NIL.";
permConsThm::usage = "permConsThm — ⊢ ∀x l1 l2. PERM l1 l2 ⇒ PERM (CONS x l1) (CONS x l2). CONS congruence.";
permSwapThm::usage = "permSwapThm — ⊢ ∀x y l. PERM (CONS x (CONS y l)) (CONS y (CONS x l)). Adjacent transposition.";
permTransThm::usage = "permTransThm — ⊢ ∀l1 l2 l3. PERM l1 l2 ⇒ PERM l2 l3 ⇒ PERM l1 l3. Transitivity.";
permInductThm::usage = "permInductThm — ⊢ ∀P. (P NIL NIL ∧ (∀x l1 l2. P l1 l2 ⇒ P (CONS x l1) (CONS x l2)) ∧ (∀x y l. P (CONS x (CONS y l)) (CONS y (CONS x l))) ∧ (∀l1 l2 l3. P l1 l2 ⇒ P l2 l3 ⇒ P l1 l3)) ⇒ ∀l1 l2. PERM l1 l2 ⇒ P l1 l2. The PERM induction principle (just permDefThm folded forward).";
permReflThm::usage = "permReflThm — ⊢ ∀l. PERM l l. List induction; NIL via permNil, CONS via permCons.";
permSymThm::usage = "permSymThm — ⊢ ∀l1 l2. PERM l1 l2 ⇒ PERM l2 l1. PERM induction with Q l1 l2 = PERM l2 l1.";
permFoldrTimesThm::usage = "permFoldrTimesThm — ⊢ ∀l1 l2. PERM l1 l2 ⇒ FOLDR * (SUC 0) l1 = FOLDR * (SUC 0) l2. Permutation preserves the * fold (stage 3.d prerequisite); swap case uses timesAssoc + timesComm + timesAssoc.";
permAllThm::usage = "permAllThm — ⊢ ∀p l1 l2. PERM l1 l2 ⇒ ALL p l1 = ALL p l2. Permutation preserves universal-quantifier-over-list.";

memSplitThm::usage = "memSplitThm — ⊢ ∀x l. MEM x l ⇒ ∃l1 l2. l = APPEND l1 (CONS x l2). Membership induces a split: a witnessed member can be extracted with the surrounding prefix and suffix. (FTA stage 3.c.)";
permAppendConsThm::usage = "permAppendConsThm — ⊢ ∀x l1 l2. PERM (APPEND l1 (CONS x l2)) (CONS x (APPEND l1 l2)). Moving CONS-x across the prefix l1 is a permutation. (FTA stage 3.c.)";

multEqZeroThm::usage = "multEqZeroThm — ⊢ ∀x a. x * a = 0 ⇒ x = 0 ∨ a = 0. No zero divisors in ℕ. (FTA stage 3.d helper.)";
multLeftCancelThm::usage = "multLeftCancelThm — ⊢ ∀x. ¬(x = 0) ⇒ ∀a b. x * a = x * b ⇒ a = b. Left multiplicative cancellation in ℕ. (FTA stage 3.d helper.)";
primeNotZeroThm::usage = "primeNotZeroThm — ⊢ ∀p. prime p ⇒ ¬(p = 0). (FTA stage 3.d helper.)";
primesEqIfDividesThm::usage = "primesEqIfDividesThm — ⊢ ∀p q. prime p ⇒ prime q ⇒ divides p q ⇒ p = q. Two primes are equal whenever one divides the other. (FTA stage 3.d helper.)";
allMemImpThm::usage = "allMemImpThm — ⊢ ∀P l. ALL P l ⇒ ∀x. MEM x l ⇒ P x. ALL is universally quantified MEM. (FTA stage 3.d helper.)";
foldrEqOneNilThm::usage = "foldrEqOneNilThm — ⊢ ∀l. ALL prime l ⇒ FOLDR * (SUC 0) l = SUC 0 ⇒ l = NIL. A product of primes equals 1 only for the empty list. (FTA stage 3.d helper.)";
primeFactorsUniqueThm::usage = "primeFactorsUniqueThm — ⊢ ∀l1 l2. ALL prime l1 ⇒ ALL prime l2 ⇒ FOLDR * (SUC 0) l1 = FOLDR * (SUC 0) l2 ⇒ PERM l1 l2. Uniqueness of prime factorization modulo permutation. FTA stage 3 capstone.";

Begin["`Private`"];

numTy = mkType["num", {}];

zeroN[] := mkConst["0", numTy];
oneN[]  := mkComb[HOL`Stdlib`Num`sucConst[], zeroN[]];
timesN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`timesConst[], m], n];
ltN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`ltConst[], m], n];
dividesN[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], a], b];
notTm[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
orTm[a_, b_] := mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
existsNum[v_, body_] := mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
  mkAbs[v, body]];
andTm[a_, b_] := mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
impTm[a_, b_] := mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
primeN[p_] := mkComb[HOL`Stdlib`Num`primeConst[], p];

(* ⊢ divides a b = ∃c. b = a * c *)
unfoldDivides[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`dividesDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ a ≤ b = ∃k. a + k = b *)
unfoldLeq[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ a < b = SUC a ≤ b *)
unfoldLt[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

plusN[m_, n_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], m], n];
sucN[n_]      := mkComb[HOL`Stdlib`Num`sucConst[], n];
leqN[m_, n_]  := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], m], n];

(* Term builders at concrete num types for stage-2. *)
numListTy[] := HOL`Stdlib`List`listTy[numTy];
nilNumTm[]  := mkConst["NIL", numListTy[]];
consNumConst[] := mkConst["CONS",
  tyFun[numTy, tyFun[numListTy[], numListTy[]]]];
consNumApp[x_, l_] := mkComb[mkComb[consNumConst[], x], l];
allPredNumTy[] :=
  tyFun[tyFun[numTy, boolTy], tyFun[numListTy[], boolTy]];
allNumConst[] := mkConst["ALL", allPredNumTy[]];
allTm[pred_, list_] := mkComb[mkComb[allNumConst[], pred], list];
foldrNumNumConst[] :=
  mkConst["FOLDR", tyFun[
    tyFun[numTy, tyFun[numTy, numTy]],
    tyFun[numTy, tyFun[numListTy[], numTy]]]];
foldrTm[fn_, base_, list_] :=
  mkComb[mkComb[mkComb[foldrNumNumConst[], fn], base], list];
existsListTm[v_, body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[numListTy[], boolTy], boolTy]],
    mkAbs[v, body]];
memNumConst[] := mkConst["MEM", tyFun[numTy, tyFun[numListTy[], boolTy]]];
memNumTm[x_, l_] := mkComb[mkComb[memNumConst[], x], l];
appendNumConst[] := mkConst["APPEND",
  tyFun[numListTy[], tyFun[numListTy[], numListTy[]]]];
appendNumTm[a_, b_] := mkComb[mkComb[appendNumConst[], a], b];
permNumConst[] := mkConst["PERM",
  tyFun[numListTy[], tyFun[numListTy[], boolTy]]];
permNumTm[a_, b_] := mkComb[mkComb[permNumConst[], a], b];

(* ============================================================ *)
(* posAddLtThm  (stage-2 helper)                                 *)
(* From ¬(d=0): d = SUC d' (numCasesThm). Then                   *)
(*   c + d = c + SUC d' = SUC (c + d') = SUC c + d'.             *)
(* So ∃k. SUC c + k = c + d, i.e. SUC c ≤ c + d, i.e. c < c + d.  *)
(* ============================================================ *)

posAddLtThm =
  Module[{cV, dV, dpV, kV, dNotZHyp, casesAtD, zeroCase, sucCase,
          body, dischNotZ, gen},
    cV  = mkVar["cP", numTy];
    dV  = mkVar["dP", numTy];
    dpV = mkVar["dPpr", numTy];
    kV  = mkVar["kP", numTy];

    dNotZHyp = ASSUME[notTm[mkEq[dV, zeroN[]]]];
    casesAtD = HOL`Bool`SPEC[dV, HOL`Stdlib`Num`numCasesThm];
    (* ⊢ d = 0 ∨ ∃d'. d = SUC d' *)

    zeroCase = Module[{dEq0, fThm},
      dEq0 = ASSUME[mkEq[dV, zeroN[]]];
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[dNotZHyp], dEq0];
      HOL`Bool`CONTR[ltN[cV, plusN[cV, dV]], fThm]
    ];

    sucCase = Module[{exDpTm, exDpHyp, dEqSucDpHyp, cAddSucDp,
                      sucCAddDp, eqViaSuc, eqRewriteD, existsBody,
                      existsK, leqFolded, ltFolded, chosen},
      exDpTm = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[dpV, mkEq[dV, sucN[dpV]]]];
      exDpHyp = ASSUME[exDpTm];
      dEqSucDpHyp = ASSUME[mkEq[dV, sucN[dpV]]];

      cAddSucDp = HOL`Bool`SPEC[dpV, HOL`Bool`SPEC[cV,
        HOL`Stdlib`Num`plusSucEqThm]];
      (* ⊢ c + SUC d' = SUC (c + d') *)
      sucCAddDp = HOL`Bool`SPEC[dpV, HOL`Bool`SPEC[cV,
        HOL`Stdlib`Num`addLeftSucThm]];
      (* ⊢ SUC c + d' = SUC (c + d') *)
      eqViaSuc = TRANS[sucCAddDp, HOL`Equal`SYM[cAddSucDp]];
      (* ⊢ SUC c + d' = c + SUC d' *)
      eqRewriteD = HOL`Drule`SUBS[{HOL`Equal`SYM[dEqSucDpHyp]}, eqViaSuc];
      (* (d = SUC d') ⊢ SUC c + d' = c + d *)

      existsBody = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[kV, mkEq[plusN[sucN[cV], kV], plusN[cV, dV]]]];
      existsK = HOL`Bool`EXISTS[existsBody, dpV, eqRewriteD];
      (* (d = SUC d') ⊢ ∃k. SUC c + k = c + d *)
      leqFolded = EQMP[
        HOL`Equal`SYM[unfoldLeq[sucN[cV], plusN[cV, dV]]], existsK];
      (* (d = SUC d') ⊢ SUC c ≤ c + d *)
      ltFolded = EQMP[
        HOL`Equal`SYM[unfoldLt[cV, plusN[cV, dV]]], leqFolded];
      (* (d = SUC d') ⊢ c < c + d *)
      chosen = HOL`Bool`CHOOSE[dpV, exDpHyp, ltFolded];
      (* (∃d'. d = SUC d') ⊢ c < c + d *)
      chosen
    ];

    body = HOL`Bool`DISJCASES[casesAtD, zeroCase, sucCase];
    dischNotZ = HOL`Bool`DISCH[notTm[mkEq[dV, zeroN[]]], body];
    gen = HOL`Bool`GEN[cV, HOL`Bool`GEN[dV, dischNotZ]];
    gen
  ];

(* ============================================================ *)
(* ltMultIfOneLtThm  (stage-2 helper)                            *)
(* From SUC 0 < p: ∃k. SUC (SUC 0) + k = p. Simplify:            *)
(*   SUC (SUC 0) + k = SUC (SUC k), so p = SUC (SUC k).          *)
(*   Then p * c = SUC (SUC k) * c = c + (SUC k * c)              *)
(*              = c + (c + k * c).                                *)
(* Since c ≠ 0, c + k*c ≠ 0 (addEqZeroLeftThm); posAddLtThm       *)
(* gives c < c + (c + k*c) = p * c.                              *)
(* ============================================================ *)

ltMultIfOneLtThm =
  Module[{pV, cV, kV, oneLtPHyp, cNotZHyp, oneLtPUnf, leqExUnf,
          pEqAddHyp, innerEq, midEq, outerEq, pEqSSk,
          pTimesAt, outerTimesEq, innerTimesEq, pTimesDecomp,
          pTimesEq2, addNotZero, cLtDecomp, cLtPC, chosen,
          dischNotZ, dischOneLt, gen},
    pV = mkVar["pL", numTy]; cV = mkVar["cL", numTy];
    kV = mkVar["kL", numTy];

    oneLtPHyp = ASSUME[ltN[oneN[], pV]];
    cNotZHyp = ASSUME[notTm[mkEq[cV, zeroN[]]]];

    oneLtPUnf = EQMP[unfoldLt[oneN[], pV], oneLtPHyp];
    (* ⊢ SUC (SUC 0) ≤ p *)
    leqExUnf = EQMP[unfoldLeq[sucN[oneN[]], pV], oneLtPUnf];
    (* ⊢ ∃k. SUC (SUC 0) + k = p *)

    pEqAddHyp = ASSUME[mkEq[plusN[sucN[oneN[]], kV], pV]];
    (* (SUC (SUC 0) + k = p) ⊢ … *)

    innerEq = HOL`Bool`SPEC[kV, HOL`Stdlib`Num`addLeftZeroThm];
    (* ⊢ 0 + k = k *)
    midEq = TRANS[
      HOL`Bool`SPEC[kV, HOL`Bool`SPEC[zeroN[],
        HOL`Stdlib`Num`addLeftSucThm]],
      HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], innerEq]];
    (* ⊢ SUC 0 + k = SUC k *)
    outerEq = TRANS[
      HOL`Bool`SPEC[kV, HOL`Bool`SPEC[oneN[],
        HOL`Stdlib`Num`addLeftSucThm]],
      HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], midEq]];
    (* ⊢ SUC (SUC 0) + k = SUC (SUC k) *)

    pEqSSk = TRANS[HOL`Equal`SYM[pEqAddHyp], outerEq];
    (* (SUC (SUC 0) + k = p) ⊢ p = SUC (SUC k) *)

    pTimesAt = HOL`Equal`APTHM[
      HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], pEqSSk], cV];
    (* (…) ⊢ p * c = SUC (SUC k) * c *)

    outerTimesEq = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[sucN[kV],
      HOL`Stdlib`Num`timesLeftSucThm]];
    (* ⊢ SUC (SUC k) * c = c + (SUC k * c) *)
    innerTimesEq = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[kV,
      HOL`Stdlib`Num`timesLeftSucThm]];
    (* ⊢ SUC k * c = c + k * c *)
    pTimesDecomp = TRANS[outerTimesEq,
      HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`plusConst[], cV],
        innerTimesEq]];
    (* ⊢ SUC (SUC k) * c = c + (c + k * c) *)
    pTimesEq2 = TRANS[pTimesAt, pTimesDecomp];
    (* (…) ⊢ p * c = c + (c + k * c) *)

    addNotZero = Module[{addZHyp, cEq0FromAdd, fThm},
      addZHyp = ASSUME[mkEq[plusN[cV, timesN[kV, cV]], zeroN[]]];
      cEq0FromAdd = HOL`Bool`MP[
        HOL`Bool`SPEC[timesN[kV, cV], HOL`Bool`SPEC[cV,
          HOL`Stdlib`Num`addEqZeroLeftThm]], addZHyp];
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[cNotZHyp], cEq0FromAdd];
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[
        mkEq[plusN[cV, timesN[kV, cV]], zeroN[]], fThm]]
    ];
    (* (¬(c = 0)) ⊢ ¬(c + k * c = 0) *)

    cLtDecomp = HOL`Bool`MP[HOL`Bool`SPEC[plusN[cV, timesN[kV, cV]],
      HOL`Bool`SPEC[cV, posAddLtThm]], addNotZero];
    (* (¬(c = 0)) ⊢ c < c + (c + k * c) *)
    cLtPC = HOL`Drule`SUBS[{HOL`Equal`SYM[pTimesEq2]}, cLtDecomp];
    (* (¬(c = 0), SUC (SUC 0) + k = p) ⊢ c < p * c *)

    chosen = HOL`Bool`CHOOSE[kV, leqExUnf, cLtPC];
    (* (¬(c = 0), SUC 0 < p) ⊢ c < p * c *)
    dischNotZ = HOL`Bool`DISCH[notTm[mkEq[cV, zeroN[]]], chosen];
    dischOneLt = HOL`Bool`DISCH[ltN[oneN[], pV], dischNotZ];
    gen = HOL`Bool`GEN[pV, HOL`Bool`GEN[cV, dischOneLt]];
    gen
  ];

(* ============================================================ *)
(* dividesPosThm                                                 *)
(* Assume d|n and d = 0 (for contradiction). Unfold divides:    *)
(* ∃c. n = d*c. CHOOSE c. Substitute d = 0 → n = 0*c. Use        *)
(* timesCommThm + timesZeroEqThm: 0*c = c*0 = 0. So n = 0,       *)
(* contradicting ¬(n = 0).                                       *)
(* ============================================================ *)

dividesPosThm =
  Module[{dV, nV, notNzHyp, divHyp, dEq0Hyp, divUnf, cV,
          bodyEq, exHyp, nEqZC, zeroTimesC, nEqZero, fThm,
          chosenC, notDzero, dischDiv, dischNotN, gens},
    dV = mkVar["d", numTy]; nV = mkVar["n", numTy];
    notNzHyp = ASSUME[notTm[mkEq[nV, zeroN[]]]];
    divHyp = ASSUME[dividesN[dV, nV]];
    divUnf = EQMP[unfoldDivides[dV, nV], divHyp];

    dEq0Hyp = ASSUME[mkEq[dV, zeroN[]]];

    cV = mkVar["cD", numTy];
    bodyEq = mkEq[nV, timesN[dV, cV]];
    exHyp = ASSUME[bodyEq];
    nEqZC = HOL`Drule`SUBS[{dEq0Hyp}, exHyp];
    (* (bodyEq, dEq0Hyp) ⊢ n = 0*c *)
    zeroTimesC = TRANS[
      HOL`Bool`SPEC[cV, HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`timesCommThm]],
      HOL`Bool`SPEC[cV, HOL`Stdlib`Num`timesZeroEqThm]];
    (* ⊢ 0*c = 0  (via 0*c = c*0 = 0) *)
    nEqZero = TRANS[nEqZC, zeroTimesC];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notNzHyp], nEqZero];
    chosenC = HOL`Bool`CHOOSE[cV, divUnf, fThm];
    notDzero = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[dV, zeroN[]], chosenC]];
    dischDiv = HOL`Bool`DISCH[dividesN[dV, nV], notDzero];
    dischNotN = HOL`Bool`DISCH[notTm[mkEq[nV, zeroN[]]], dischDiv];
    gens = HOL`Bool`GEN[dV, HOL`Bool`GEN[nV, dischNotN]];
    gens
  ];

(* ============================================================ *)
(* dividesTransThm                                               *)
(* a|b: ∃j. b = a*j. b|c: ∃k. c = b*k. Substitute b = a*j:        *)
(* c = (a*j)*k. timesAssocThm: (a*j)*k = a*(j*k). EXISTS at      *)
(* (j*k) inside divides def of a|c.                              *)
(* ============================================================ *)

dividesTransThm =
  Module[{aV, bV, cV, divAB, divBC, divABunf, divBCunf, jV, kV,
          bEqAJhyp, cEqBKhyp, cEqAJKunassoc, assoc, cEqAJK,
          exTmA, divACInner, divACThm, chosenK, chosenJ,
          dischBC, dischAB, gens},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    divAB = ASSUME[dividesN[aV, bV]];
    divBC = ASSUME[dividesN[bV, cV]];
    divABunf = EQMP[unfoldDivides[aV, bV], divAB];
    divBCunf = EQMP[unfoldDivides[bV, cV], divBC];

    jV = mkVar["jD", numTy]; kV = mkVar["kD", numTy];
    bEqAJhyp = ASSUME[mkEq[bV, timesN[aV, jV]]];
    cEqBKhyp = ASSUME[mkEq[cV, timesN[bV, kV]]];

    cEqAJKunassoc = HOL`Drule`SUBS[{bEqAJhyp}, cEqBKhyp];
    (* (bEq, cEq) ⊢ c = (a*j) * k *)
    assoc = HOL`Bool`SPEC[kV, HOL`Bool`SPEC[jV, HOL`Bool`SPEC[aV,
      HOL`Stdlib`Num`timesAssocThm]]];
    cEqAJK = TRANS[cEqAJKunassoc, assoc];
    (* (bEq, cEq) ⊢ c = a * (j*k) *)

    exTmA = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mkVar["cD", numTy],
        mkEq[cV, timesN[aV, mkVar["cD", numTy]]]]];
    divACInner = HOL`Bool`EXISTS[exTmA, timesN[jV, kV], cEqAJK];
    divACThm = EQMP[HOL`Equal`SYM[unfoldDivides[aV, cV]], divACInner];
    (* (bEq, cEq) ⊢ divides a c *)
    chosenK = HOL`Bool`CHOOSE[kV, divBCunf, divACThm];
    chosenJ = HOL`Bool`CHOOSE[jV, divABunf, chosenK];
    dischBC = HOL`Bool`DISCH[dividesN[bV, cV], chosenJ];
    dischAB = HOL`Bool`DISCH[dividesN[aV, bV], dischBC];
    gens = HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, dischAB]]];
    gens
  ];

(* ============================================================ *)
(* notOneNorZeroLtThm                                            *)
(* ¬(d = 0) ⇒ 0 < d (= SUC 0 ≤ d via ltDefThm = 1 ≤ d).          *)
(* leqCaseEqLtThm: 1 ≤ d ⇒ 1 = d ∨ 1 < d. ¬(d = 1) = ¬(1 = d)    *)
(* by SYM rules out first; second is the goal.                   *)
(* ============================================================ *)

notOneNorZeroLtThm =
  Module[{dV, notDz, notD1, posD, oneLeqD, ap1, e1, ap2, e2, ltUnf,
          caseEq, oneEqDhyp, dEqOne, fThm, contrCase, idCase, body,
          dischNotD1, dischNotDz, gen},
    dV = mkVar["d", numTy];
    notDz = ASSUME[notTm[mkEq[dV, zeroN[]]]];
    notD1 = ASSUME[notTm[mkEq[dV, oneN[]]]];
    posD = HOL`Bool`MP[HOL`Bool`SPEC[dV, HOL`Stdlib`Num`ltZeroNotZeroThm],
      notDz];
    (* ⊢ 0 < d *)
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, zeroN[]];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, dV];
    ltUnf = TRANS[ap2, BETACONV[concl[ap2][[2]]]];
    (* ⊢ 0 < d = SUC 0 ≤ d  (i.e. = 1 ≤ d) *)
    oneLeqD = EQMP[ltUnf, posD];
    (* ⊢ 1 ≤ d *)
    caseEq = HOL`Bool`MP[HOL`Bool`SPEC[dV, HOL`Bool`SPEC[oneN[],
      HOL`Stdlib`Num`leqCaseEqLtThm]], oneLeqD];
    (* ⊢ 1 = d ∨ 1 < d *)
    oneEqDhyp = ASSUME[mkEq[oneN[], dV]];
    dEqOne = HOL`Equal`SYM[oneEqDhyp];
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notD1], dEqOne];
    contrCase = HOL`Bool`CONTR[ltN[oneN[], dV], fThm];
    idCase = ASSUME[ltN[oneN[], dV]];
    body = HOL`Bool`DISJCASES[caseEq, contrCase, idCase];
    (* (notDz, notD1) ⊢ 1 < d *)
    dischNotD1 = HOL`Bool`DISCH[notTm[mkEq[dV, oneN[]]], body];
    dischNotDz = HOL`Bool`DISCH[notTm[mkEq[dV, zeroN[]]], dischNotD1];
    gen = HOL`Bool`GEN[dV, dischNotDz];
    gen
  ];

(* ============================================================ *)
(* primeOrCompositeThm                                           *)
(* EM[∃d. 1<d ∧ d<n ∧ d|n]. Yes-branch: DISJ2 directly.          *)
(* No-branch: prove prime n via primeDefThm — for any d|n,       *)
(* EM[d=1]; d≠1 case uses dividesPosThm + notOneNorZeroLtThm to  *)
(* get 1<d, dividesLeqThm to get d≤n, leqCaseEqLtThm to split    *)
(* d=n vs d<n; d<n gives a witness contradicting the no-branch.  *)
(* ============================================================ *)

primeOrCompositeThm =
  Module[{nV, oneLtNHyp, nNotZero, dV, exBody, exTm, em, conclTm,
          yesCase, noCase, primeUnf, allDivClause, primeFmt, primeAtN,
          conclBody, dischOneLtN, gen},
    nV = mkVar["n", numTy];
    oneLtNHyp = ASSUME[ltN[oneN[], nV]];

    nNotZero = Module[{nEq0Hyp, oneLtZero, fThm},
      nEq0Hyp = ASSUME[mkEq[nV, zeroN[]]];
      oneLtZero = HOL`Drule`SUBS[{nEq0Hyp}, oneLtNHyp];
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[HOL`Bool`SPEC[oneN[],
        HOL`Stdlib`Num`notLtZeroThm]], oneLtZero];
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[nV, zeroN[]], fThm]]
    ];
    (* (1 < n) ⊢ ¬(n = 0) *)

    dV = mkVar["dV", numTy];
    exBody = andTm[ltN[oneN[], dV], andTm[ltN[dV, nV], dividesN[dV, nV]]];
    exTm = existsNum[dV, exBody];
    em = HOL`Bool`EXCLUDEDMIDDLE[exTm];

    conclTm = orTm[primeN[nV], exTm];

    yesCase = HOL`Bool`DISJ2[ASSUME[exTm], primeN[nV]];

    noCase = Module[{notExHyp, ap, allDivBody, dV2, divDNHyp, em2, caseEq,
                     caseNeq, body, disch, gen2, allDivThm, primeAtNLocal,
                     primeFmtLocal, primeUnfLocal},
      notExHyp = ASSUME[notTm[exTm]];

      primeUnfLocal = Module[{apP},
        apP = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, nV];
        TRANS[apP, BETACONV[concl[apP][[2]]]]
      ];
      (* ⊢ prime n = (SUC 0 < n) ∧ (∀d. divides d n ⇒ d = SUC 0 ∨ d = n) *)

      dV2 = mkVar["dD", numTy];
      divDNHyp = ASSUME[dividesN[dV2, nV]];
      em2 = HOL`Bool`EXCLUDEDMIDDLE[mkEq[dV2, oneN[]]];

      caseEq = HOL`Bool`DISJ1[ASSUME[mkEq[dV2, oneN[]]], mkEq[dV2, nV]];

      caseNeq = Module[{notDeq1, dNotZero, oneLtD, dLeqN, leqCase,
                        dEqNCase, dLtNCase, body2},
        notDeq1 = ASSUME[notTm[mkEq[dV2, oneN[]]]];
        dNotZero = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[nV, HOL`Bool`SPEC[dV2, dividesPosThm]],
          nNotZero], divDNHyp];
        oneLtD = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[dV2, notOneNorZeroLtThm], dNotZero], notDeq1];
        dLeqN = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[nV, HOL`Bool`SPEC[dV2, HOL`Stdlib`Num`dividesLeqThm]],
          nNotZero], divDNHyp];
        leqCase = HOL`Bool`MP[HOL`Bool`SPEC[nV, HOL`Bool`SPEC[dV2,
          HOL`Stdlib`Num`leqCaseEqLtThm]], dLeqN];
        (* ⊢ d = n ∨ d < n *)
        dEqNCase = HOL`Bool`DISJ2[ASSUME[mkEq[dV2, nV]], mkEq[dV2, oneN[]]];
        dLtNCase = Module[{dLtN, conjPart, exAtD, fThm3},
          dLtN = ASSUME[ltN[dV2, nV]];
          conjPart = HOL`Bool`CONJ[oneLtD, HOL`Bool`CONJ[dLtN, divDNHyp]];
          exAtD = HOL`Bool`EXISTS[exTm, dV2, conjPart];
          fThm3 = HOL`Bool`MP[HOL`Bool`NOTELIM[notExHyp], exAtD];
          HOL`Bool`CONTR[orTm[mkEq[dV2, oneN[]], mkEq[dV2, nV]], fThm3]
        ];
        body2 = HOL`Bool`DISJCASES[leqCase, dEqNCase, dLtNCase];
        body2
      ];

      body = HOL`Bool`DISJCASES[em2, caseEq, caseNeq];
      disch = HOL`Bool`DISCH[dividesN[dV2, nV], body];
      gen2 = HOL`Bool`GEN[dV2, disch];
      allDivThm = gen2;

      primeFmtLocal = HOL`Bool`CONJ[oneLtNHyp, allDivThm];
      primeAtNLocal = EQMP[HOL`Equal`SYM[primeUnfLocal], primeFmtLocal];
      HOL`Bool`DISJ1[primeAtNLocal, exTm]
    ];

    conclBody = HOL`Bool`DISJCASES[em, yesCase, noCase];
    dischOneLtN = HOL`Bool`DISCH[ltN[oneN[], nV], conclBody];
    gen = HOL`Bool`GEN[nV, dischOneLtN];
    gen
  ];

(* ============================================================ *)
(* primeDivExistsThm                                             *)
(* Strong induction on n: pLam n = 1<n ⇒ ∃p. prime p ∧ p|n.      *)
(* Apply primeOrCompositeThm. Prime case: p = n (dividesReflThm).*)
(* Composite case: CHOOSE d with 1<d ∧ d<n ∧ d|n; IH gives p|d;  *)
(* dividesTransThm gives p|n.                                    *)
(* ============================================================ *)

primeDivExistsThm =
  Module[{nV, kV, pV, ihBodyAtN, pLam, specInd, specBeta, stepAnte,
          stepLam, mainConcl},
    nV = mkVar["n", numTy]; kV = mkVar["kS", numTy]; pV = mkVar["pP", numTy];

    pLam = mkAbs[nV, impTm[ltN[oneN[], nV],
      existsNum[pV, andTm[primeN[pV], dividesN[pV, nV]]]]];

    specInd = HOL`Bool`ISPEC[pLam, HOL`Stdlib`Num`strongInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];
    (* ⊢ (∀n. (∀k. k<n ⇒ (1<k ⇒ ∃p. prime p ∧ p|k))
              ⇒ (1<n ⇒ ∃p. prime p ∧ p|n))
       ⇒ ∀n. 1<n ⇒ ∃p. prime p ∧ p|n *)

    stepAnte = Module[{nLocal, ihHyp, oneLtN, primeOrCompAt, mp, pocConcl,
                       primeCase, compositeCase, dV3, exTmLoc, exHyp,
                       conjBody, conjHyp, oneLtD, dLtN, dDivN, ihAtD, mpFromIH,
                       expConcl, pVLoc, exP, exPHyp, primePbody, primePbodyHyp,
                       primeP, pDivD, pDivN, conjOut, exAtP, chosenP, chosenDV,
                       finalEx, dischOneLtN, dischIH, gens},
      nLocal = mkVar["n", numTy];

      ihHyp = ASSUME[Module[{innerBody},
        innerBody = impTm[ltN[oneN[], kV],
          existsNum[pV, andTm[primeN[pV], dividesN[pV, kV]]]];
        mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[kV, impTm[ltN[kV, nLocal], innerBody]]]]];
      (* ihHyp: ∀k. k<n ⇒ (1<k ⇒ ∃p. prime p ∧ p|k) *)

      oneLtN = ASSUME[ltN[oneN[], nLocal]];

      primeOrCompAt = HOL`Bool`MP[
        HOL`Bool`SPEC[nLocal, primeOrCompositeThm], oneLtN];
      (* ⊢ prime n ∨ ∃d. 1<d ∧ d<n ∧ d|n *)

      primeCase = Module[{primeNHyp, divNN, conjP, exNoutTm, exOut},
        primeNHyp = ASSUME[primeN[nLocal]];
        divNN = HOL`Bool`SPEC[nLocal, HOL`Stdlib`Num`dividesReflThm];
        conjP = HOL`Bool`CONJ[primeNHyp, divNN];
        exNoutTm = existsNum[pV, andTm[primeN[pV], dividesN[pV, nLocal]]];
        HOL`Bool`EXISTS[exNoutTm, nLocal, conjP]
      ];

      compositeCase = Module[{dV3Loc, exTmLoc2, exHyp2, conjT, conjHyp2,
                              oneLtD2, restCJ, dLtN2, dDivN2, ihAtDLoc,
                              implFromIH, exPbody, exP2, exPbodyHyp2,
                              primeP2, pDivD2, pDivN2, conjOut2, exTmOut, exAtPout,
                              chosenPLoc, chosenDVLoc},
        dV3Loc = mkVar["dV", numTy];
        exTmLoc2 = existsNum[dV3Loc, andTm[ltN[oneN[], dV3Loc],
          andTm[ltN[dV3Loc, nLocal], dividesN[dV3Loc, nLocal]]]];
        exHyp2 = ASSUME[exTmLoc2];
        conjT = andTm[ltN[oneN[], dV3Loc],
          andTm[ltN[dV3Loc, nLocal], dividesN[dV3Loc, nLocal]]];
        conjHyp2 = ASSUME[conjT];
        oneLtD2 = HOL`Bool`CONJUNCT1[conjHyp2];
        restCJ = HOL`Bool`CONJUNCT2[conjHyp2];
        dLtN2 = HOL`Bool`CONJUNCT1[restCJ];
        dDivN2 = HOL`Bool`CONJUNCT2[restCJ];

        ihAtDLoc = HOL`Bool`SPEC[dV3Loc, ihHyp];
        (* ⊢ dV<n ⇒ (1<dV ⇒ ∃p. prime p ∧ p|dV) *)
        implFromIH = HOL`Bool`MP[HOL`Bool`MP[ihAtDLoc, dLtN2], oneLtD2];
        (* (…) ⊢ ∃p. prime p ∧ p|dV *)

        exPbody = andTm[primeN[pV], dividesN[pV, dV3Loc]];
        exP2 = existsNum[pV, exPbody];
        exPbodyHyp2 = ASSUME[exPbody];
        primeP2 = HOL`Bool`CONJUNCT1[exPbodyHyp2];
        pDivD2 = HOL`Bool`CONJUNCT2[exPbodyHyp2];
        pDivN2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[nLocal,
          HOL`Bool`SPEC[dV3Loc, HOL`Bool`SPEC[pV, dividesTransThm]]],
          pDivD2], dDivN2];
        (* (…) ⊢ divides p n *)
        conjOut2 = HOL`Bool`CONJ[primeP2, pDivN2];
        exTmOut = existsNum[pV, andTm[primeN[pV], dividesN[pV, nLocal]]];
        exAtPout = HOL`Bool`EXISTS[exTmOut, pV, conjOut2];
        chosenPLoc = HOL`Bool`CHOOSE[pV, implFromIH, exAtPout];
        chosenDVLoc = HOL`Bool`CHOOSE[dV3Loc, exHyp2, chosenPLoc];
        chosenDVLoc
      ];

      finalEx = HOL`Bool`DISJCASES[primeOrCompAt, primeCase, compositeCase];

      dischOneLtN = HOL`Bool`DISCH[ltN[oneN[], nLocal], finalEx];
      dischIH = HOL`Bool`DISCH[concl[ihHyp], dischOneLtN];
      gens = HOL`Bool`GEN[nLocal, dischIH];
      gens
    ];

    mainConcl = HOL`Bool`MP[specBeta, stepAnte];
    mainConcl
  ];

(* ============================================================ *)
(* primeFactorsExistsThm  (FTA stage 2)                          *)
(*                                                              *)
(* Strong induction on n with predicate                         *)
(*   P n = ¬(n = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n.   *)
(*                                                              *)
(* Step: assume IH for all k < n, and ¬(n = 0).                  *)
(*   ltZeroNotZeroThm: 0 < n.                                    *)
(*   ltDef + leqCaseEqLtThm: SUC 0 = n ∨ SUC 0 < n.              *)
(*                                                              *)
(*   Case SUC 0 = n: l = NIL.                                    *)
(*     allNilThm gives ALL prime NIL.                            *)
(*     foldrNilThm + the case hypothesis give FOLDR … NIL = n.   *)
(*                                                              *)
(*   Case SUC 0 < n: primeDivExistsThm yields prime p with p|n.  *)
(*     Unfolding p|n: ∃c. n = p*c.                                *)
(*     c ≠ 0 (else n = 0 contradicts ¬(n = 0)).                  *)
(*     prime p ⇒ SUC 0 < p; ltMultIfOneLtThm ⇒ c < p*c = n.       *)
(*     IH at c: ∃l'. ALL prime l' ∧ FOLDR * (SUC 0) l' = c.       *)
(*     Take l = CONS p l'.                                       *)
(*       allConsThm: ALL prime (CONS p l') = prime p ∧ ALL p l';  *)
(*       foldrConsThm: FOLDR * (SUC 0) (CONS p l')                *)
(*                    = p * (FOLDR * (SUC 0) l') = p * c = n.     *)
(* ============================================================ *)

primeFactorsExistsThm =
  Module[{αTy, βTy, nV, lV, pLam, exTmAtN, specInd, specBeta, stepAnte,
          mainConcl},
    αTy = mkVarType["A"]; βTy = mkVarType["B"];
    nV = mkVar["nF", numTy];
    lV = mkVar["lF", numListTy[]];

    (* P = λn. ¬(n = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n *)
    pLam = mkAbs[nV, impTm[notTm[mkEq[nV, zeroN[]]],
      existsListTm[lV, andTm[
        allTm[HOL`Stdlib`Num`primeConst[], lV],
        mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], nV]]]]];

    specInd = HOL`Bool`ISPEC[pLam, HOL`Stdlib`Num`strongInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];

    stepAnte = Module[{nLocal, kV, ihHypT, ihHyp, nNotZHyp, posN,
                       sucOneLeqN, caseEq, oneEqNCase, oneLtNCase,
                       finalCase, dischNotZ, dischIH, gen,
                       exConclTm},
      nLocal = mkVar["nF", numTy];
      kV     = mkVar["kF", numTy];

      exConclTm = existsListTm[lV, andTm[
        allTm[HOL`Stdlib`Num`primeConst[], lV],
        mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], nLocal]]];

      ihHypT = mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[kV, impTm[ltN[kV, nLocal],
          impTm[notTm[mkEq[kV, zeroN[]]],
            existsListTm[lV, andTm[
              allTm[HOL`Stdlib`Num`primeConst[], lV],
              mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], kV]]]]]]];
      ihHyp = ASSUME[ihHypT];

      nNotZHyp = ASSUME[notTm[mkEq[nLocal, zeroN[]]]];

      posN = HOL`Bool`MP[
        HOL`Bool`SPEC[nLocal, HOL`Stdlib`Num`ltZeroNotZeroThm],
        nNotZHyp];
      (* ⊢ 0 < n *)
      sucOneLeqN = EQMP[unfoldLt[zeroN[], nLocal], posN];
      (* ⊢ SUC 0 ≤ n *)
      caseEq = HOL`Bool`MP[
        HOL`Bool`SPEC[nLocal, HOL`Bool`SPEC[oneN[],
          HOL`Stdlib`Num`leqCaseEqLtThm]], sucOneLeqN];
      (* ⊢ SUC 0 = n ∨ SUC 0 < n *)

      (* --- Branch 1: SUC 0 = n. Use NIL. --- *)
      oneEqNCase = Module[{oneEqNHyp, allNilAtPrime, allNilTrue,
                           foldrNilAtNum, foldrNilEqN, conjBody, exAtNil},
        oneEqNHyp = ASSUME[mkEq[oneN[], nLocal]];

        allNilAtPrime = HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
          INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`allNilThm]];
        (* ⊢ ALL prime NIL = T *)
        allNilTrue = HOL`Bool`EQTELIM[allNilAtPrime];
        (* ⊢ ALL prime NIL *)

        foldrNilAtNum = HOL`Bool`SPEC[oneN[],
          HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
            INSTTYPE[{αTy -> numTy, βTy -> numTy},
              HOL`Stdlib`List`foldrNilThm]]];
        (* ⊢ FOLDR * (SUC 0) NIL = SUC 0 *)
        foldrNilEqN = TRANS[foldrNilAtNum, oneEqNHyp];
        (* (SUC 0 = n) ⊢ FOLDR * (SUC 0) NIL = n *)

        conjBody = HOL`Bool`CONJ[allNilTrue, foldrNilEqN];
        exAtNil = HOL`Bool`EXISTS[exConclTm, nilNumTm[], conjBody];
        exAtNil
      ];

      (* --- Branch 2: SUC 0 < n. Recurse via primeDivExistsThm. --- *)
      oneLtNCase = Module[{oneLtNHyp, primeDivAtN, pV, cV, primeAndDivBody,
                           primeAndDivHyp, primePThm, pDivN, pDivNUnf,
                           nEqPCBody, nEqPCHyp, cNotZ, primeUnfP, primePApplied,
                           oneLtPThm, cLtPC, cLtN, ihAtC, mpFromIH,
                           lBody, lHyp, allPrimeL, foldrLEqC, consPLTm,
                           allConsAtPL, conjAllPart, allPrimeCons,
                           foldrConsAtPL, replaceFoldr, replaceN, foldrConsEqN,
                           conjCons, exAtConsPL, chosenL, chosenC, chosenP},
        oneLtNHyp = ASSUME[ltN[oneN[], nLocal]];
        primeDivAtN = HOL`Bool`MP[
          HOL`Bool`SPEC[nLocal, primeDivExistsThm], oneLtNHyp];
        (* ⊢ ∃p. prime p ∧ p|n *)

        pV = mkVar["pF", numTy];
        cV = mkVar["cF", numTy];
        primeAndDivBody = andTm[primeN[pV], dividesN[pV, nLocal]];
        primeAndDivHyp = ASSUME[primeAndDivBody];
        primePThm = HOL`Bool`CONJUNCT1[primeAndDivHyp];
        pDivN = HOL`Bool`CONJUNCT2[primeAndDivHyp];

        pDivNUnf = EQMP[unfoldDivides[pV, nLocal], pDivN];
        (* (…) ⊢ ∃c. n = p * c *)
        nEqPCBody = mkEq[nLocal, timesN[pV, cV]];
        nEqPCHyp = ASSUME[nEqPCBody];

        cNotZ = Module[{cEq0Hyp, pTimes0, nEqPTimes0, nEq0, fThm},
          cEq0Hyp = ASSUME[mkEq[cV, zeroN[]]];
          pTimes0 = HOL`Bool`SPEC[pV, HOL`Stdlib`Num`timesZeroEqThm];
          nEqPTimes0 = TRANS[nEqPCHyp,
            HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], pV],
              cEq0Hyp]];
          nEq0 = TRANS[nEqPTimes0, pTimes0];
          fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[nNotZHyp], nEq0];
          HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[cV, zeroN[]], fThm]]
        ];
        (* (¬(n=0), n = p*c) ⊢ ¬(c = 0) *)

        primeUnfP = Module[{apP},
          apP = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, pV];
          TRANS[apP, BETACONV[concl[apP][[2]]]]
        ];
        (* ⊢ prime p = SUC 0 < p ∧ (∀d. divides d p ⇒ d = SUC 0 ∨ d = p) *)
        primePApplied = EQMP[primeUnfP, primePThm];
        oneLtPThm = HOL`Bool`CONJUNCT1[primePApplied];
        (* (…) ⊢ SUC 0 < p *)

        cLtPC = HOL`Bool`MP[HOL`Bool`MP[
          HOL`Bool`SPEC[cV, HOL`Bool`SPEC[pV, ltMultIfOneLtThm]],
          oneLtPThm], cNotZ];
        (* (…) ⊢ c < p * c *)
        cLtN = HOL`Drule`SUBS[{HOL`Equal`SYM[nEqPCHyp]}, cLtPC];
        (* (…) ⊢ c < n *)

        ihAtC = HOL`Bool`SPEC[cV, ihHyp];
        (* ⊢ c < n ⇒ ¬(c = 0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = c *)
        mpFromIH = HOL`Bool`MP[HOL`Bool`MP[ihAtC, cLtN], cNotZ];
        (* (…) ⊢ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = c *)

        lBody = andTm[
          allTm[HOL`Stdlib`Num`primeConst[], lV],
          mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], cV]];
        lHyp = ASSUME[lBody];
        allPrimeL = HOL`Bool`CONJUNCT1[lHyp];
        foldrLEqC = HOL`Bool`CONJUNCT2[lHyp];

        consPLTm = consNumApp[pV, lV];

        allConsAtPL = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[pV,
          HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
            INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`allConsThm]]]];
        (* ⊢ ALL prime (CONS p l) = prime p ∧ ALL prime l *)
        conjAllPart = HOL`Bool`CONJ[primePThm, allPrimeL];
        allPrimeCons = EQMP[HOL`Equal`SYM[allConsAtPL], conjAllPart];
        (* (…) ⊢ ALL prime (CONS p l) *)

        foldrConsAtPL = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[pV,
          HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
            INSTTYPE[{αTy -> numTy, βTy -> numTy},
              HOL`Stdlib`List`foldrConsThm]]]]];
        (* ⊢ FOLDR * (SUC 0) (CONS p l) = p * (FOLDR * (SUC 0) l) *)
        replaceFoldr = HOL`Equal`APTERM[
          mkComb[HOL`Stdlib`Num`timesConst[], pV], foldrLEqC];
        (* (…) ⊢ p * (FOLDR * (SUC 0) l) = p * c *)
        replaceN = HOL`Equal`SYM[nEqPCHyp];
        (* (n = p*c) ⊢ p * c = n *)
        foldrConsEqN = TRANS[foldrConsAtPL, TRANS[replaceFoldr, replaceN]];
        (* (…) ⊢ FOLDR * (SUC 0) (CONS p l) = n *)

        conjCons = HOL`Bool`CONJ[allPrimeCons, foldrConsEqN];
        exAtConsPL = HOL`Bool`EXISTS[exConclTm, consPLTm, conjCons];
        (* (…) ⊢ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n *)

        chosenL = HOL`Bool`CHOOSE[lV, mpFromIH, exAtConsPL];
        chosenC = HOL`Bool`CHOOSE[cV, pDivNUnf, chosenL];
        chosenP = HOL`Bool`CHOOSE[pV, primeDivAtN, chosenC];
        chosenP
      ];

      finalCase = HOL`Bool`DISJCASES[caseEq, oneEqNCase, oneLtNCase];

      dischNotZ = HOL`Bool`DISCH[notTm[mkEq[nLocal, zeroN[]]], finalCase];
      dischIH = HOL`Bool`DISCH[ihHypT, dischNotZ];
      gen = HOL`Bool`GEN[nLocal, dischIH];
      gen
    ];

    mainConcl = HOL`Bool`MP[specBeta, stepAnte];
    mainConcl
  ];

(* ============================================================ *)
(* notLeqSucSelfThm  (stage-3.a helper)                          *)
(*   ⊢ ∀n. ¬ (SUC n ≤ n).                                        *)
(*                                                              *)
(* Assume SUC n ≤ n; combine with leqSucThm (n ≤ SUC n) via      *)
(* leqAntisymThm to get SUC n = n, contradicting sucNotEqSelfThm.*)
(* ============================================================ *)

notLeqSucSelfThm =
  Module[{nV, sucLeqHyp, nLeqSuc, antisym, sucEqN, notEq, fThm,
          notIntro, gen},
    nV = mkVar["nSL", numTy];
    sucLeqHyp = ASSUME[leqN[sucN[nV], nV]];
    nLeqSuc = HOL`Bool`SPEC[nV, HOL`Stdlib`Num`leqSucThm];
    (* ⊢ n ≤ SUC n *)
    antisym = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[nV, HOL`Bool`SPEC[sucN[nV],
        HOL`Stdlib`Num`leqAntisymThm]],
      sucLeqHyp], nLeqSuc];
    (* (SUC n ≤ n) ⊢ SUC n = n *)
    notEq = HOL`Bool`SPEC[nV, HOL`Stdlib`Num`sucNotEqSelfThm];
    (* ⊢ ¬(SUC n = n) *)
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notEq], antisym];
    (* (SUC n ≤ n) ⊢ F *)
    notIntro = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[leqN[sucN[nV], nV], fThm]];
    gen = HOL`Bool`GEN[nV, notIntro];
    gen
  ];

(* ============================================================ *)
(* primeNotDivOneThm  (stage-3.a helper)                         *)
(*   ⊢ ∀p. prime p ⇒ ¬ (divides p (SUC 0)).                      *)
(*                                                              *)
(* From prime p extract SUC 0 < p (primeDef CONJUNCT1).          *)
(* Unfold < to get SUC (SUC 0) ≤ p.                              *)
(* Assume divides p (SUC 0); dividesLeqThm with SUC 0 ≠ 0 gives  *)
(*   p ≤ SUC 0.                                                  *)
(* Combine SUC (SUC 0) ≤ p and p ≤ SUC 0 via leqTrans:            *)
(*   SUC (SUC 0) ≤ SUC 0, contradicting notLeqSucSelfThm.        *)
(* ============================================================ *)

primeNotDivOneThm =
  Module[{pV, primeHyp, primeUnf, primeUnfApplied, oneLtP, ltUnfP,
          dividesHyp, oneNotZero, pLeqOne, sucOneLeqOne, fThm,
          notIntro, dischPrime, gen, oneTm, sucOneTm},
    pV = mkVar["pND", numTy];
    oneTm = oneN[];
    sucOneTm = sucN[oneTm];

    primeHyp = ASSUME[primeN[pV]];
    primeUnf = Module[{apP},
      apP = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, pV];
      TRANS[apP, BETACONV[concl[apP][[2]]]]
    ];
    (* ⊢ prime p = SUC 0 < p ∧ (∀d. divides d p ⇒ d = SUC 0 ∨ d = p) *)
    primeUnfApplied = EQMP[primeUnf, primeHyp];
    oneLtP = HOL`Bool`CONJUNCT1[primeUnfApplied];
    (* (prime p) ⊢ SUC 0 < p *)
    ltUnfP = EQMP[unfoldLt[oneTm, pV], oneLtP];
    (* (prime p) ⊢ SUC (SUC 0) ≤ p *)

    dividesHyp = ASSUME[dividesN[pV, oneTm]];
    (* (divides p 1) ⊢ … *)

    oneNotZero = Module[{eqHyp, fT, suc0NeqZ},
      eqHyp = ASSUME[mkEq[oneTm, zeroN[]]];
      suc0NeqZ = HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`sucNotZeroThm];
      (* ⊢ ¬(SUC 0 = 0) *)
      fT = HOL`Bool`MP[HOL`Bool`NOTELIM[suc0NeqZ], eqHyp];
      HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[oneTm, zeroN[]], fT]]
    ];
    (* ⊢ ¬(SUC 0 = 0) *)

    pLeqOne = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[oneTm, HOL`Bool`SPEC[pV,
        HOL`Stdlib`Num`dividesLeqThm]],
      oneNotZero], dividesHyp];
    (* (divides p 1) ⊢ p ≤ SUC 0 *)

    sucOneLeqOne = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[oneTm, HOL`Bool`SPEC[pV,
        HOL`Bool`SPEC[sucOneTm, HOL`Stdlib`Num`leqTransThm]]],
      ltUnfP], pLeqOne];
    (* (prime p, divides p 1) ⊢ SUC (SUC 0) ≤ SUC 0 *)

    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[
      HOL`Bool`SPEC[oneTm, notLeqSucSelfThm]],
      sucOneLeqOne];
    (* (prime p, divides p 1) ⊢ F *)

    notIntro = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[
      dividesN[pV, oneTm], fThm]];
    (* (prime p) ⊢ ¬(divides p (SUC 0)) *)
    dischPrime = HOL`Bool`DISCH[primeN[pV], notIntro];
    gen = HOL`Bool`GEN[pV, dischPrime];
    gen
  ];

(* ============================================================ *)
(* primeDivFoldrTimesThm  (FTA stage 3.a)                        *)
(*   ⊢ ∀p l. prime p ⇒ divides p (FOLDR * (SUC 0) l)             *)
(*           ⇒ ∃y. MEM y l ∧ divides p y.                         *)
(*                                                              *)
(* For fixed prime p, list-induct on l.                          *)
(*   NIL: FOLDR * (SUC 0) NIL = SUC 0; divides p (SUC 0)         *)
(*         contradicts primeNotDivOneThm.                        *)
(*   CONS y l': FOLDR * (SUC 0) (CONS y l')                      *)
(*               = y * FOLDR * (SUC 0) l' (foldrConsThm).        *)
(*     euclidLemmaThm: p | y ∨ p | (FOLDR * (SUC 0) l').          *)
(*     - p|y branch: take MEM y (CONS y l') (head).               *)
(*     - p|FOLDR branch: IH gives ∃y'. MEM y' l' ∧ p|y';          *)
(*       MEM y' (CONS y l') via tail of memCons.                  *)
(* ============================================================ *)

primeDivFoldrTimesThm =
  Module[{αTy, βTy, pV, lV, yV, bndV, primeHyp, predLam, inductSpec,
          inductBeta, baseCase, indStep, conjForall, finalGen,
          dischPrime, gen, foldrAt, memAt, exConcl},
    αTy = mkVarType["A"]; βTy = mkVarType["B"];
    pV = mkVar["pE", numTy];
    lV = mkVar["lE", numListTy[]];
    yV = mkVar["yE", numTy];
    (* bndV is the fresh ∃-binder used in exConcl — distinct from the
       per-case witnesses yLocal / ypV so listTm can mention either freely. *)
    bndV = mkVar["yBnd", numTy];

    primeHyp = ASSUME[primeN[pV]];

    (* The MEM and FOLDR terms specialized to num. *)
    memAt[xTm_, listTm_] := mkComb[mkComb[
      mkConst["MEM", tyFun[numTy, tyFun[numListTy[], boolTy]]],
      xTm], listTm];

    foldrAt[listTm_] := foldrTm[
      HOL`Stdlib`Num`timesConst[], oneN[], listTm];

    (* exConcl[listTm] = ∃bndV. MEM bndV listTm ∧ divides p bndV *)
    exConcl[listTm_] := mkComb[
      mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[bndV, andTm[memAt[bndV, listTm], dividesN[pV, bndV]]]];

    (* P l ≡ divides p (FOLDR * (SUC 0) l) ⇒ ∃y. MEM y l ∧ divides p y *)
    predLam = mkAbs[lV,
      impTm[dividesN[pV, foldrAt[lV]], exConcl[lV]]];

    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];
    (* ⊢ (divides p (FOLDR * 1 NIL) ⇒ ∃y. MEM y NIL ∧ divides p y)
       ∧ (∀x l. (divides p (FOLDR * 1 l) ⇒ ∃y. MEM y l ∧ divides p y)
              ⇒ (divides p (FOLDR * 1 (CONS x l))
                   ⇒ ∃y. MEM y (CONS x l) ∧ divides p y))
       ⇒ ∀l. divides p (FOLDR * 1 l) ⇒ ∃y. MEM y l ∧ divides p y *)

    (* NIL case: divides p 1 contradicts primeNotDivOneThm. *)
    baseCase = Module[{foldrNilAtNum, divPFoldrHyp, divP1, notDivP1,
                       fThm, dischDiv},
      foldrNilAtNum = HOL`Bool`SPEC[oneN[],
        HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
          INSTTYPE[{αTy -> numTy, βTy -> numTy},
            HOL`Stdlib`List`foldrNilThm]]];
      (* ⊢ FOLDR * (SUC 0) NIL = SUC 0 *)
      divPFoldrHyp = ASSUME[dividesN[pV, foldrAt[nilNumTm[]]]];
      divP1 = HOL`Drule`SUBS[{foldrNilAtNum}, divPFoldrHyp];
      (* (divides p (FOLDR * 1 NIL)) ⊢ divides p (SUC 0) *)
      notDivP1 = HOL`Bool`MP[
        HOL`Bool`SPEC[pV, primeNotDivOneThm], primeHyp];
      (* (prime p) ⊢ ¬(divides p (SUC 0)) *)
      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notDivP1], divP1];
      (* (prime p, divides p (FOLDR * 1 NIL)) ⊢ F *)
      dischDiv = HOL`Bool`DISCH[dividesN[pV, foldrAt[nilNumTm[]]],
        HOL`Bool`CONTR[exConcl[nilNumTm[]], fThm]];
      dischDiv
    ];

    (* CONS case: ∀y l. (IH) ⇒ (divides p (FOLDR * 1 (CONS y l))
                                ⇒ ∃z. MEM z (CONS y l) ∧ divides p z). *)
    indStep = Module[{yLocal, lLocal, ihHypT, ihHyp, foldrConsAt, divHyp,
                      divPYTimesFold, euclidAt, splitDisj,
                      headBranch, tailBranch, exFromBranches,
                      dischDiv, stepInner, allLOuter},
      yLocal = yV;
      lLocal = lV;

      ihHypT = impTm[dividesN[pV, foldrAt[lLocal]], exConcl[lLocal]];
      ihHyp = ASSUME[ihHypT];

      foldrConsAt = HOL`Bool`SPEC[lLocal, HOL`Bool`SPEC[yLocal,
        HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
          INSTTYPE[{αTy -> numTy, βTy -> numTy},
            HOL`Stdlib`List`foldrConsThm]]]]];
      (* ⊢ FOLDR * (SUC 0) (CONS y l)
           = y * FOLDR * (SUC 0) l *)

      divHyp = ASSUME[dividesN[pV, foldrAt[consNumApp[yLocal, lLocal]]]];
      divPYTimesFold = HOL`Drule`SUBS[{foldrConsAt}, divHyp];
      (* (…) ⊢ divides p (y * FOLDR * (SUC 0) l) *)

      euclidAt = HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[foldrAt[lLocal],
          HOL`Bool`SPEC[yLocal, HOL`Bool`SPEC[pV,
            HOL`Stdlib`Num`euclidLemmaThm]]],
        primeHyp], divPYTimesFold];
      (* (prime p, …) ⊢ divides p y ∨ divides p (FOLDR * 1 l) *)

      headBranch = Module[{divPYHyp, memConsAtY, eqYY, headDisj,
                           memYConsRaw, memYCons, conjY, exAtY},
        divPYHyp = ASSUME[dividesN[pV, yLocal]];

        memConsAtY = HOL`Bool`SPEC[lLocal, HOL`Bool`SPEC[yLocal,
          HOL`Bool`SPEC[yLocal,
            INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`memConsThm]]]];
        (* ⊢ MEM y (CONS y l) = (y = y ∨ MEM y l) *)
        eqYY = REFL[yLocal];
        (* ⊢ y = y *)
        headDisj = HOL`Bool`DISJ1[eqYY,
          mkComb[mkComb[
            mkConst["MEM", tyFun[numTy, tyFun[numListTy[], boolTy]]],
            yLocal], lLocal]];
        (* ⊢ y = y ∨ MEM y l *)
        memYCons = EQMP[HOL`Equal`SYM[memConsAtY], headDisj];
        (* ⊢ MEM y (CONS y l) *)
        conjY = HOL`Bool`CONJ[memYCons, divPYHyp];
        exAtY = HOL`Bool`EXISTS[exConcl[consNumApp[yLocal, lLocal]],
          yLocal, conjY];
        exAtY
      ];

      tailBranch = Module[{divPFoldHyp, ihApplied, ypV, conjYpBody,
                           conjYpHyp, memYpL, divPYp, memConsAtYp, tailDisj,
                           memYpCons, conjYpFinal, exAtYp, chosenYp},
        divPFoldHyp = ASSUME[dividesN[pV, foldrAt[lLocal]]];
        ihApplied = HOL`Bool`MP[ihHyp, divPFoldHyp];
        (* (IH, divides p (FOLDR * 1 l)) ⊢ ∃y. MEM y l ∧ divides p y *)

        ypV = mkVar["ypE", numTy];
        conjYpBody = andTm[memAt[ypV, lLocal], dividesN[pV, ypV]];
        conjYpHyp = ASSUME[conjYpBody];
        memYpL = HOL`Bool`CONJUNCT1[conjYpHyp];
        divPYp = HOL`Bool`CONJUNCT2[conjYpHyp];

        memConsAtYp = HOL`Bool`SPEC[lLocal, HOL`Bool`SPEC[yLocal,
          HOL`Bool`SPEC[ypV,
            INSTTYPE[{αTy -> numTy}, HOL`Stdlib`List`memConsThm]]]];
        (* ⊢ MEM y' (CONS y l) = (y' = y ∨ MEM y' l) *)
        tailDisj = HOL`Bool`DISJ2[memYpL, mkEq[ypV, yLocal]];
        (* ⊢ y' = y ∨ MEM y' l *)
        memYpCons = EQMP[HOL`Equal`SYM[memConsAtYp], tailDisj];
        (* (MEM y' l) ⊢ MEM y' (CONS y l) *)
        conjYpFinal = HOL`Bool`CONJ[memYpCons, divPYp];
        exAtYp = HOL`Bool`EXISTS[exConcl[consNumApp[yLocal, lLocal]],
          ypV, conjYpFinal];
        chosenYp = HOL`Bool`CHOOSE[ypV, ihApplied, exAtYp];
        chosenYp
      ];

      exFromBranches = HOL`Bool`DISJCASES[euclidAt, headBranch, tailBranch];
      (* (prime p, IH, divides p (FOLDR * 1 (CONS y l))) ⊢ ∃z. MEM z (CONS y l) ∧ divides p z *)

      dischDiv = HOL`Bool`DISCH[
        dividesN[pV, foldrAt[consNumApp[yLocal, lLocal]]],
        exFromBranches];
      stepInner = HOL`Bool`DISCH[ihHypT, dischDiv];
      allLOuter = HOL`Bool`GEN[yLocal, HOL`Bool`GEN[lLocal, stepInner]];
      allLOuter
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalGen = HOL`Bool`MP[inductBeta, conjForall];
    (* (prime p) ⊢ ∀l. divides p (FOLDR * 1 l) ⇒ ∃y. MEM y l ∧ divides p y *)

    dischPrime = HOL`Bool`DISCH[primeN[pV], finalGen];
    gen = HOL`Bool`GEN[pV, dischPrime];
    gen
  ];

(* ============================================================ *)
(* PERM — polymorphic permutation relation                       *)
(*   PERM = (λl1 l2. ∀R. closedRel R ⇒ R l1 l2)                  *)
(*   where closedRel R asserts the four closure properties.      *)
(*                                                              *)
(* The four properties are: R NIL NIL, CONS-congruence,          *)
(* adjacent CONS-swap, and transitivity. PERM is the smallest    *)
(* binary relation on α list closed under these four.            *)
(* ============================================================ *)

αPerm = mkVarType["A"];
listAP[] := HOL`Stdlib`List`listTy[αPerm];
permFunTyP[] := tyFun[listAP[], tyFun[listAP[], boolTy]];
nilAP[] := mkConst["NIL", listAP[]];
consAP[] := mkConst["CONS",
  tyFun[αPerm, tyFun[listAP[], listAP[]]]];
consAPApp[xTm_, lTm_] := mkComb[mkComb[consAP[], xTm], lTm];
rAP[xTm_, yTm_, lTm_] := mkComb[mkComb[lTm, xTm], yTm];

forallAP[v_, body_] := mkComb[
  mkConst["∀", tyFun[tyFun[αPerm, boolTy], boolTy]],
  mkAbs[v, body]];
forallLP[v_, body_] := mkComb[
  mkConst["∀", tyFun[tyFun[listAP[], boolTy], boolTy]],
  mkAbs[v, body]];
forallRP[v_, body_] := mkComb[
  mkConst["∀", tyFun[tyFun[permFunTyP[], boolTy], boolTy]],
  mkAbs[v, body]];

(* closedRelTm[rTm] : R-instantiated closure conjunction.        *)
(* Bound vars used internally: x, y, l, l1, l2, l3. rTm must     *)
(* not have any of these as free variables.                      *)
closedRelTm[rTm_] :=
  Module[{xV, yV, lV, l1V, l2V, l3V, clauseNil, clauseCong,
          clauseSwap, clauseTrans},
    xV  = mkVar["xCR", αPerm];
    yV  = mkVar["yCR", αPerm];
    lV  = mkVar["lCR", listAP[]];
    l1V = mkVar["l1CR", listAP[]];
    l2V = mkVar["l2CR", listAP[]];
    l3V = mkVar["l3CR", listAP[]];

    clauseNil = rAP[nilAP[], nilAP[], rTm];

    clauseCong = forallAP[xV, forallLP[l1V, forallLP[l2V,
      impTm[rAP[l1V, l2V, rTm],
            rAP[consAPApp[xV, l1V], consAPApp[xV, l2V], rTm]]]]];

    clauseSwap = forallAP[xV, forallAP[yV, forallLP[lV,
      rAP[consAPApp[xV, consAPApp[yV, lV]],
          consAPApp[yV, consAPApp[xV, lV]], rTm]]]];

    clauseTrans = forallLP[l1V, forallLP[l2V, forallLP[l3V,
      impTm[rAP[l1V, l2V, rTm],
        impTm[rAP[l2V, l3V, rTm], rAP[l1V, l3V, rTm]]]]]];

    andTm[clauseNil, andTm[clauseCong, andTm[clauseSwap, clauseTrans]]]
  ];

(* PERM definition. *)
Module[{aV, bV, rV, permBody},
  aV = mkVar["aPm", listAP[]];
  bV = mkVar["bPm", listAP[]];
  rV = mkVar["RPm", permFunTyP[]];
  permBody = mkAbs[aV, mkAbs[bV,
    forallRP[rV,
      impTm[closedRelTm[rV], rAP[aV, bV, rV]]]]];
  permDefThm = newDefinition[mkEq[
    mkVar["PERM", permFunTyP[]], permBody]];
];

permConst[] := mkConst["PERM", permFunTyP[]];

(* ⊢ PERM l1 l2 = ∀R. closedRelTm[R] ⇒ R l1 l2  *)
unfoldPerm[l1Tm_, l2Tm_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[permDefThm, l1Tm];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, l2Tm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

permTm[l1Tm_, l2Tm_] := mkComb[mkComb[permConst[], l1Tm], l2Tm];

(* ============================================================ *)
(* permNilThm : ⊢ PERM NIL NIL                                  *)
(* Unfold; the closure hypothesis directly gives R NIL NIL.     *)
(* ============================================================ *)

permNilThm =
  Module[{rV, unf, closed, rNilNil, disch, gen},
    rV = mkVar["RPm", permFunTyP[]];
    unf = unfoldPerm[nilAP[], nilAP[]];
    closed = ASSUME[closedRelTm[rV]];
    rNilNil = HOL`Bool`CONJUNCT1[closed];
    disch = HOL`Bool`DISCH[closedRelTm[rV], rNilNil];
    gen = HOL`Bool`GEN[rV, disch];
    EQMP[HOL`Equal`SYM[unf], gen]
  ];

(* ============================================================ *)
(* permConsThm : ⊢ ∀x l1 l2. PERM l1 l2 ⇒                       *)
(*                   PERM (CONS x l1) (CONS x l2)                *)
(* Unfold PERM (CONS x l1) (CONS x l2); use closure congruence   *)
(* clause + unfolded PERM l1 l2.                                 *)
(* ============================================================ *)

permConsThm =
  Module[{xV, l1V, l2V, rV, permHyp, permUnf, unfCons, closedTm,
          closedHyp, rL1L2, congrClause, stepAt, rConsConsApp,
          dischClosed, genR, permConsConcl, dischPerm, gens},
    xV = mkVar["xPC", αPerm];
    l1V = mkVar["l1PC", listAP[]];
    l2V = mkVar["l2PC", listAP[]];
    rV = mkVar["RPm", permFunTyP[]];

    permHyp = ASSUME[permTm[l1V, l2V]];
    permUnf = EQMP[unfoldPerm[l1V, l2V], permHyp];
    (* (PERM l1 l2) ⊢ ∀R. closedRel R ⇒ R l1 l2 *)
    unfCons = unfoldPerm[consAPApp[xV, l1V], consAPApp[xV, l2V]];
    closedTm = closedRelTm[rV];
    closedHyp = ASSUME[closedTm];
    rL1L2 = HOL`Bool`MP[HOL`Bool`SPEC[rV, permUnf], closedHyp];
    (* (PERM l1 l2, closed R) ⊢ R l1 l2 *)

    (* Cong clause: ∀x l1 l2. R l1 l2 ⇒ R (CONS x l1) (CONS x l2) *)
    congrClause = HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[closedHyp]];
    stepAt = HOL`Bool`SPEC[l2V, HOL`Bool`SPEC[l1V,
      HOL`Bool`SPEC[xV, congrClause]]];
    (* (closed R) ⊢ R l1 l2 ⇒ R (CONS x l1) (CONS x l2) *)
    rConsConsApp = HOL`Bool`MP[stepAt, rL1L2];
    (* (PERM l1 l2, closed R) ⊢ R (CONS x l1) (CONS x l2) *)

    dischClosed = HOL`Bool`DISCH[closedTm, rConsConsApp];
    genR = HOL`Bool`GEN[rV, dischClosed];
    permConsConcl = EQMP[HOL`Equal`SYM[unfCons], genR];
    (* (PERM l1 l2) ⊢ PERM (CONS x l1) (CONS x l2) *)

    dischPerm = HOL`Bool`DISCH[permTm[l1V, l2V], permConsConcl];
    gens = HOL`Bool`GEN[xV, HOL`Bool`GEN[l1V, HOL`Bool`GEN[l2V, dischPerm]]];
    gens
  ];

(* ============================================================ *)
(* permSwapThm : ⊢ ∀x y l. PERM (CONS x (CONS y l))             *)
(*                              (CONS y (CONS x l))              *)
(* Unfold; specialize the swap clause directly.                  *)
(* ============================================================ *)

permSwapThm =
  Module[{xV, yV, lV, rV, lhsTm, rhsTm, unf, closedTm, closedHyp,
          swapClause, swapAt, dischClosed, genR, permConcl, gens},
    xV = mkVar["xPS", αPerm];
    yV = mkVar["yPS", αPerm];
    lV = mkVar["lPS", listAP[]];
    rV = mkVar["RPm", permFunTyP[]];
    lhsTm = consAPApp[xV, consAPApp[yV, lV]];
    rhsTm = consAPApp[yV, consAPApp[xV, lV]];

    unf = unfoldPerm[lhsTm, rhsTm];
    closedTm = closedRelTm[rV];
    closedHyp = ASSUME[closedTm];
    swapClause = HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[
      HOL`Bool`CONJUNCT2[closedHyp]]];
    swapAt = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[yV,
      HOL`Bool`SPEC[xV, swapClause]]];
    (* (closed R) ⊢ R (CONS x (CONS y l)) (CONS y (CONS x l)) *)

    dischClosed = HOL`Bool`DISCH[closedTm, swapAt];
    genR = HOL`Bool`GEN[rV, dischClosed];
    permConcl = EQMP[HOL`Equal`SYM[unf], genR];

    gens = HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[lV, permConcl]]];
    gens
  ];

(* ============================================================ *)
(* permTransThm : ⊢ ∀l1 l2 l3. PERM l1 l2 ⇒ PERM l2 l3 ⇒        *)
(*                              PERM l1 l3                        *)
(* Standard pattern: each PERM gives closed R ⇒ R l_i l_{i+1};   *)
(* combine via the trans clause.                                  *)
(* ============================================================ *)

permTransThm =
  Module[{l1V, l2V, l3V, rV, permH12, permH23, unf12, unf23,
          unfFinal, closedTm, closedHyp, rL12, rL23, transClause,
          transAt1, transAt2, rL13, dischClosed, genR, finalThm,
          dischP23, dischP12, gens},
    l1V = mkVar["l1PT", listAP[]];
    l2V = mkVar["l2PT", listAP[]];
    l3V = mkVar["l3PT", listAP[]];
    rV = mkVar["RPm", permFunTyP[]];

    permH12 = ASSUME[permTm[l1V, l2V]];
    permH23 = ASSUME[permTm[l2V, l3V]];
    unf12 = EQMP[unfoldPerm[l1V, l2V], permH12];
    unf23 = EQMP[unfoldPerm[l2V, l3V], permH23];

    unfFinal = unfoldPerm[l1V, l3V];
    closedTm = closedRelTm[rV];
    closedHyp = ASSUME[closedTm];

    rL12 = HOL`Bool`MP[HOL`Bool`SPEC[rV, unf12], closedHyp];
    rL23 = HOL`Bool`MP[HOL`Bool`SPEC[rV, unf23], closedHyp];

    transClause = HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[
      HOL`Bool`CONJUNCT2[closedHyp]]];
    transAt1 = HOL`Bool`SPEC[l3V, HOL`Bool`SPEC[l2V,
      HOL`Bool`SPEC[l1V, transClause]]];
    (* (closed R) ⊢ R l1 l2 ⇒ R l2 l3 ⇒ R l1 l3 *)
    transAt2 = HOL`Bool`MP[HOL`Bool`MP[transAt1, rL12], rL23];
    rL13 = transAt2;

    dischClosed = HOL`Bool`DISCH[closedTm, rL13];
    genR = HOL`Bool`GEN[rV, dischClosed];
    finalThm = EQMP[HOL`Equal`SYM[unfFinal], genR];

    dischP23 = HOL`Bool`DISCH[permTm[l2V, l3V], finalThm];
    dischP12 = HOL`Bool`DISCH[permTm[l1V, l2V], dischP23];
    gens = HOL`Bool`GEN[l1V, HOL`Bool`GEN[l2V,
      HOL`Bool`GEN[l3V, dischP12]]];
    gens
  ];

(* ============================================================ *)
(* permInductThm : ⊢ ∀P. closedRel P ⇒ ∀l1 l2. PERM l1 l2 ⇒     *)
(*                       P l1 l2.                                 *)
(* Just permDefThm restated: unfold PERM and SPEC the ∀R at P.   *)
(* ============================================================ *)

permInductThm =
  Module[{pV, l1V, l2V, hypTm, hHyp, permH, permUnf, specP, pL1L2,
          dischPerm, genL2, genL1, dischH, genP},
    pV = mkVar["PPI", permFunTyP[]];
    l1V = mkVar["l1PI", listAP[]];
    l2V = mkVar["l2PI", listAP[]];

    hypTm = closedRelTm[pV];
    hHyp = ASSUME[hypTm];
    permH = ASSUME[permTm[l1V, l2V]];
    permUnf = EQMP[unfoldPerm[l1V, l2V], permH];
    specP = HOL`Bool`SPEC[pV, permUnf];
    pL1L2 = HOL`Bool`MP[specP, hHyp];

    dischPerm = HOL`Bool`DISCH[permTm[l1V, l2V], pL1L2];
    genL2 = HOL`Bool`GEN[l2V, dischPerm];
    genL1 = HOL`Bool`GEN[l1V, genL2];
    dischH = HOL`Bool`DISCH[hypTm, genL1];
    genP = HOL`Bool`GEN[pV, dischH];
    genP
  ];

(* ============================================================ *)
(* permReflThm : ⊢ ∀l. PERM l l                                 *)
(* List induction; NIL via permNilThm, CONS via permConsThm.    *)
(* ============================================================ *)

permReflThm =
  Module[{lV, xV, predLam, inductSpec, inductBeta, baseCase, indStep,
          conjForall, finalGen},
    lV = mkVar["lPR", listAP[]];
    xV = mkVar["xPR", αPerm];

    predLam = mkAbs[lV, permTm[lV, lV]];
    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{αPerm -> αPerm}, HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];
    (* ⊢ (PERM NIL NIL ∧ (∀x l. PERM l l ⇒ PERM (CONS x l) (CONS x l)))
       ⇒ ∀l. PERM l l *)

    baseCase = permNilThm;

    indStep = Module[{ihHyp, consAt, mp, dischIH},
      ihHyp = ASSUME[permTm[lV, lV]];
      consAt = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[lV,
        HOL`Bool`SPEC[xV, permConsThm]]];
      (* ⊢ PERM l l ⇒ PERM (CONS x l) (CONS x l) *)
      mp = HOL`Bool`MP[consAt, ihHyp];
      dischIH = HOL`Bool`DISCH[permTm[lV, lV], mp];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[lV, dischIH]]
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalGen = HOL`Bool`MP[inductBeta, conjForall];
    finalGen
  ];

(* ============================================================ *)
(* permSymThm : ⊢ ∀l1 l2. PERM l1 l2 ⇒ PERM l2 l1               *)
(* PERM induction with predicate λa b. PERM b a.                 *)
(*                                                              *)
(* Closure (post-β):                                            *)
(*  1. PERM NIL NIL                              — permNilThm     *)
(*  2. ∀x l1 l2. PERM l2 l1 ⇒ PERM (CONS x l2) (CONS x l1)        *)
(*                                                — permConsThm    *)
(*  3. ∀x y l. PERM (CONS y (CONS x l)) (CONS x (CONS y l))      *)
(*                                                — permSwapThm    *)
(*  4. ∀l1 l2 l3. PERM l2 l1 ⇒ PERM l3 l2 ⇒ PERM l3 l1            *)
(*                                                — permTransThm   *)
(* ============================================================ *)

permSymThm =
  Module[{aPV, bPV, predLam, indAt, indBeta, conj1, conj2, conj3,
          conj4, closureProof, applyAll, l1V, l2V, postBeta,
          finalCorrected},
    aPV = mkVar["aPSym", listAP[]];
    bPV = mkVar["bPSym", listAP[]];
    l1V = mkVar["l1PSym", listAP[]];
    l2V = mkVar["l2PSym", listAP[]];

    predLam = mkAbs[aPV, mkAbs[bPV, permTm[bPV, aPV]]];
    indAt = HOL`Bool`SPEC[predLam, permInductThm];
    indBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], indAt];
    (* ⊢ (PERM NIL NIL
         ∧ (∀x l1 l2. PERM l2 l1 ⇒ PERM (CONS x l2) (CONS x l1))
         ∧ (∀x y l. PERM (CONS y (CONS x l)) (CONS x (CONS y l)))
         ∧ (∀l1 l2 l3. PERM l2 l1 ⇒ PERM l3 l2 ⇒ PERM l3 l1))
       ⇒ ∀l1 l2. PERM l1 l2 ⇒ PERM l2 l1 *)

    conj1 = permNilThm;

    conj2 = Module[{xV, l1L, l2L, hypH, consAt, mp, dischH},
      xV  = mkVar["xC2", αPerm];
      l1L = mkVar["l1C2", listAP[]];
      l2L = mkVar["l2C2", listAP[]];
      hypH = ASSUME[permTm[l2L, l1L]];
      consAt = HOL`Bool`SPEC[l1L, HOL`Bool`SPEC[l2L,
        HOL`Bool`SPEC[xV, permConsThm]]];
      (* ⊢ PERM l2 l1 ⇒ PERM (CONS x l2) (CONS x l1) *)
      mp = HOL`Bool`MP[consAt, hypH];
      dischH = HOL`Bool`DISCH[permTm[l2L, l1L], mp];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[l1L, HOL`Bool`GEN[l2L, dischH]]]
    ];

    conj3 = Module[{xV, yV, lV, swapAt},
      xV = mkVar["xC3", αPerm]; yV = mkVar["yC3", αPerm];
      lV = mkVar["lC3", listAP[]];
      swapAt = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[xV,
        HOL`Bool`SPEC[yV, permSwapThm]]];
      (* ⊢ PERM (CONS y (CONS x l)) (CONS x (CONS y l)) *)
      HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[lV, swapAt]]]
    ];

    conj4 = Module[{l1L, l2L, l3L, h21, h32, transAt, mp1, mp2,
                    dH32, dH21},
      l1L = mkVar["l1C4", listAP[]];
      l2L = mkVar["l2C4", listAP[]];
      l3L = mkVar["l3C4", listAP[]];
      h21 = ASSUME[permTm[l2L, l1L]];
      h32 = ASSUME[permTm[l3L, l2L]];
      transAt = HOL`Bool`SPEC[l1L, HOL`Bool`SPEC[l2L,
        HOL`Bool`SPEC[l3L, permTransThm]]];
      (* ⊢ PERM l3 l2 ⇒ PERM l2 l1 ⇒ PERM l3 l1 *)
      mp1 = HOL`Bool`MP[transAt, h32];
      mp2 = HOL`Bool`MP[mp1, h21];
      dH32 = HOL`Bool`DISCH[permTm[l3L, l2L], mp2];
      dH21 = HOL`Bool`DISCH[permTm[l2L, l1L], dH32];
      HOL`Bool`GEN[l1L, HOL`Bool`GEN[l2L, HOL`Bool`GEN[l3L, dH21]]]
    ];

    closureProof = HOL`Bool`CONJ[conj1,
      HOL`Bool`CONJ[conj2, HOL`Bool`CONJ[conj3, conj4]]];
    applyAll = HOL`Bool`MP[indBeta, closureProof];
    applyAll
  ];

(* ============================================================ *)
(* permFoldrTimesThm                                             *)
(*   ⊢ ∀l1 l2. PERM l1 l2 ⇒ FOLDR * (SUC 0) l1                  *)
(*                            = FOLDR * (SUC 0) l2.              *)
(* PERM induction at predicate λa b. FOLDR * 1 a = FOLDR * 1 b.   *)
(*                                                              *)
(* Swap clause uses x * (y * z) = y * (x * z) via                *)
(*   x * (y * z) = (x * y) * z          (timesAssoc, reversed)   *)
(*               = (y * x) * z          (timesComm at x, y)      *)
(*               = y * (x * z)          (timesAssoc forward).    *)
(* ============================================================ *)

(* foldrConsNumAt[x, l] : ⊢ FOLDR * 1 (CONS x l) = x * FOLDR * 1 l *)
foldrConsNumAt[xTm_, lTm_] :=
  Module[{αTyL, βTyL, foldrConsInst},
    αTyL = mkVarType["A"]; βTyL = mkVarType["B"];
    foldrConsInst = INSTTYPE[{αTyL -> numTy, βTyL -> numTy},
      HOL`Stdlib`List`foldrConsThm];
    HOL`Bool`SPEC[lTm, HOL`Bool`SPEC[xTm, HOL`Bool`SPEC[oneN[],
      HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[], foldrConsInst]]]]
  ];

permFoldrTimesThm =
  Module[{aV, bV, predLam, indAt, indBeta, conj1, conj2, conj3,
          conj4, closureProof, applyAll},
    aV = mkVar["aPF", numListTy[]];
    bV = mkVar["bPF", numListTy[]];

    predLam = mkAbs[aV, mkAbs[bV,
      mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], aV],
           foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], bV]]]];
    indAt = HOL`Bool`ISPEC[predLam, permInductThm];
    indBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], indAt];

    conj1 = REFL[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], nilNumTm[]]];

    conj2 = Module[{xV, l1L, l2L, hypH, foldrL1, foldrL2, hypApp,
                    chain, dischH},
      xV  = mkVar["xF2", numTy];
      l1L = mkVar["l1F2", numListTy[]];
      l2L = mkVar["l2F2", numListTy[]];
      hypH = ASSUME[mkEq[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], l1L],
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], l2L]]];
      foldrL1 = foldrConsNumAt[xV, l1L];
      foldrL2 = foldrConsNumAt[xV, l2L];
      hypApp = HOL`Equal`APTERM[
        mkComb[HOL`Stdlib`Num`timesConst[], xV], hypH];
      (* ⊢ x * FOLDR * 1 l1 = x * FOLDR * 1 l2 *)
      chain = TRANS[foldrL1, TRANS[hypApp, HOL`Equal`SYM[foldrL2]]];
      (* ⊢ FOLDR * 1 (CONS x l1) = FOLDR * 1 (CONS x l2) *)
      dischH = HOL`Bool`DISCH[concl[hypH], chain];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[l1L, HOL`Bool`GEN[l2L, dischH]]]
    ];

    conj3 = Module[{xV, yV, lV, foldrLhs1, foldrLhs2, foldrRhs1,
                    foldrRhs2, lhsExpanded, rhsExpanded, swapEq,
                    assocBack, commXY, commXYTimesZ, assocFwd,
                    chain, finalChain, foldrLAt},
      xV = mkVar["xF3", numTy]; yV = mkVar["yF3", numTy];
      lV = mkVar["lF3", numListTy[]];

      (* LHS = FOLDR * 1 (CONS x (CONS y l)) = x * FOLDR * 1 (CONS y l) *)
      foldrLhs1 = foldrConsNumAt[xV, consNumApp[yV, lV]];
      (*       = x * (y * FOLDR * 1 l) *)
      foldrLAt = foldrConsNumAt[yV, lV];
      foldrLhs2 = HOL`Equal`APTERM[
        mkComb[HOL`Stdlib`Num`timesConst[], xV], foldrLAt];
      lhsExpanded = TRANS[foldrLhs1, foldrLhs2];
      (* ⊢ FOLDR * 1 (CONS x (CONS y l)) = x * (y * FOLDR * 1 l) *)

      foldrRhs1 = foldrConsNumAt[yV, consNumApp[xV, lV]];
      foldrRhs2 = HOL`Equal`APTERM[
        mkComb[HOL`Stdlib`Num`timesConst[], yV],
        foldrConsNumAt[xV, lV]];
      rhsExpanded = TRANS[foldrRhs1, foldrRhs2];
      (* ⊢ FOLDR * 1 (CONS y (CONS x l)) = y * (x * FOLDR * 1 l) *)

      (* x * (y * z) = y * (x * z): assoc-back; comm on (x*y); assoc-fwd. *)
      (* Use timesAssocThm: ⊢ ∀a b c. (a * b) * c = a * (b * c) *)
      assocBack = HOL`Equal`SYM[HOL`Bool`SPEC[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV],
        HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV,
          HOL`Stdlib`Num`timesAssocThm]]]];
      (* ⊢ x * (y * FOLDR…l) = (x * y) * FOLDR…l *)
      commXY = HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xV,
        HOL`Stdlib`Num`timesCommThm]];
      (* ⊢ x * y = y * x *)
      commXYTimesZ = HOL`Equal`APTHM[
        HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], commXY],
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV]];
      (* ⊢ (x * y) * FOLDR…l = (y * x) * FOLDR…l *)
      assocFwd = HOL`Bool`SPEC[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV],
        HOL`Bool`SPEC[xV, HOL`Bool`SPEC[yV,
          HOL`Stdlib`Num`timesAssocThm]]];
      (* ⊢ (y * x) * FOLDR…l = y * (x * FOLDR…l) *)
      swapEq = TRANS[assocBack, TRANS[commXYTimesZ, assocFwd]];
      (* ⊢ x * (y * FOLDR…l) = y * (x * FOLDR…l) *)

      chain = TRANS[lhsExpanded, swapEq];
      finalChain = TRANS[chain, HOL`Equal`SYM[rhsExpanded]];
      (* ⊢ FOLDR * 1 (CONS x (CONS y l)) = FOLDR * 1 (CONS y (CONS x l)) *)

      HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[lV, finalChain]]]
    ];

    conj4 = Module[{l1L, l2L, l3L, hyp12, hyp23, trChain, dH23, dH12},
      l1L = mkVar["l1F4", numListTy[]];
      l2L = mkVar["l2F4", numListTy[]];
      l3L = mkVar["l3F4", numListTy[]];
      hyp12 = ASSUME[mkEq[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], l1L],
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], l2L]]];
      hyp23 = ASSUME[mkEq[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], l2L],
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], l3L]]];
      trChain = TRANS[hyp12, hyp23];
      dH23 = HOL`Bool`DISCH[concl[hyp23], trChain];
      dH12 = HOL`Bool`DISCH[concl[hyp12], dH23];
      HOL`Bool`GEN[l1L, HOL`Bool`GEN[l2L, HOL`Bool`GEN[l3L, dH12]]]
    ];

    closureProof = HOL`Bool`CONJ[conj1,
      HOL`Bool`CONJ[conj2, HOL`Bool`CONJ[conj3, conj4]]];
    applyAll = HOL`Bool`MP[indBeta, closureProof];
    applyAll
  ];

(* ============================================================ *)
(* permAllThm                                                    *)
(*   ⊢ ∀p l1 l2. PERM l1 l2 ⇒ ALL p l1 = ALL p l2.               *)
(* Fix p outside; PERM induction at predicate                    *)
(*   λa b. ALL p a = ALL p b.                                    *)
(*                                                              *)
(* Swap clause needs ALL p (CONS x (CONS y l))                   *)
(*   = (p x ∧ (p y ∧ ALL p l))                                   *)
(*   = (p y ∧ (p x ∧ ALL p l))   (and-swap on a, b, c).          *)
(* ============================================================ *)

(* andSwapMidThm : ⊢ ∀a b c. (a ∧ (b ∧ c)) = (b ∧ (a ∧ c)).      *)
andSwapMidThm =
  Module[{aV, bV, cV, fwdHyp, fwdResult, bwdHyp, bwdResult},
    aV = mkVar["aSW", boolTy]; bV = mkVar["bSW", boolTy];
    cV = mkVar["cSW", boolTy];

    fwdHyp = ASSUME[andTm[aV, andTm[bV, cV]]];
    fwdResult = HOL`Bool`CONJ[
      HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[fwdHyp]],
      HOL`Bool`CONJ[HOL`Bool`CONJUNCT1[fwdHyp],
        HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[fwdHyp]]]];
    (* {a ∧ (b ∧ c)} ⊢ b ∧ (a ∧ c) *)

    bwdHyp = ASSUME[andTm[bV, andTm[aV, cV]]];
    bwdResult = HOL`Bool`CONJ[
      HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[bwdHyp]],
      HOL`Bool`CONJ[HOL`Bool`CONJUNCT1[bwdHyp],
        HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[bwdHyp]]]];
    (* {b ∧ (a ∧ c)} ⊢ a ∧ (b ∧ c) *)

    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Kernel`DEDUCTANTISYM[bwdResult, fwdResult]]]]
    (* DEDUCTANTISYM[thA, thB] : p=q where p=concl(thA), q=concl(thB). *)
    (* thA = bwdResult : ⊢ a ∧ (b ∧ c); thB = fwdResult : ⊢ b ∧ (a ∧ c). *)
    (* Result: ⊢ a ∧ (b ∧ c) = b ∧ (a ∧ c).                              *)
  ];

(* allConsAt[predTm, x, l] : ⊢ ALL p (CONS x l) = p x ∧ ALL p l *)
allConsAt[predTm_, xTm_, lTm_] :=
  Module[{αTyL, allConsInst},
    αTyL = mkVarType["A"];
    allConsInst = INSTTYPE[{αTyL -> typeOf[xTm]},
      HOL`Stdlib`List`allConsThm];
    HOL`Bool`SPEC[lTm, HOL`Bool`SPEC[xTm,
      HOL`Bool`SPEC[predTm, allConsInst]]]
  ];

permAllThm =
  Module[{predFnTy, pV, aV, bV, predLam, indAt, indBeta, conj1, conj2,
          conj3, conj4, closureProof, applyAll, dischP, gen},
    predFnTy = tyFun[αPerm, boolTy];
    pV = mkVar["pPA", predFnTy];
    aV = mkVar["aPA", listAP[]];
    bV = mkVar["bPA", listAP[]];

    predLam = mkAbs[aV, mkAbs[bV,
      mkEq[mkComb[mkComb[
        mkConst["ALL", tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], aV],
        mkComb[mkComb[
          mkConst["ALL", tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], bV]
      ]]];
    indAt = HOL`Bool`SPEC[predLam, permInductThm];
    indBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], indAt];
    (* ⊢ (closure-conjuncts at λa b. ALL p a = ALL p b)
       ⇒ ∀l1 l2. PERM l1 l2 ⇒ ALL p l1 = ALL p l2 *)

    conj1 = REFL[mkComb[mkComb[
      mkConst["ALL", tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV],
      nilAP[]]];

    conj2 = Module[{xV, l1L, l2L, hypH, allL1, allL2, hypApp,
                    chain, dischH},
      xV  = mkVar["xA2", αPerm];
      l1L = mkVar["l1A2", listAP[]];
      l2L = mkVar["l2A2", listAP[]];
      hypH = ASSUME[mkEq[
        mkComb[mkComb[mkConst["ALL",
          tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], l1L],
        mkComb[mkComb[mkConst["ALL",
          tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], l2L]]];
      allL1 = allConsAt[pV, xV, l1L];
      allL2 = allConsAt[pV, xV, l2L];
      hypApp = HOL`Equal`APTERM[
        mkComb[mkConst["∧",
          tyFun[boolTy, tyFun[boolTy, boolTy]]], mkComb[pV, xV]], hypH];
      (* ⊢ p x ∧ ALL p l1 = p x ∧ ALL p l2 *)
      chain = TRANS[allL1, TRANS[hypApp, HOL`Equal`SYM[allL2]]];
      dischH = HOL`Bool`DISCH[concl[hypH], chain];
      HOL`Bool`GEN[xV, HOL`Bool`GEN[l1L, HOL`Bool`GEN[l2L, dischH]]]
    ];

    conj3 = Module[{xV, yV, lV, allLhsOuter, allLhsInner, allRhsOuter,
                    allRhsInner, lhsExpanded, rhsExpanded, swapEq,
                    chain, finalChain, allPLTm},
      xV = mkVar["xA3", αPerm]; yV = mkVar["yA3", αPerm];
      lV = mkVar["lA3", listAP[]];

      allPLTm = mkComb[mkComb[mkConst["ALL",
        tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], lV];

      (* LHS = ALL p (CONS x (CONS y l)) = p x ∧ ALL p (CONS y l) *)
      allLhsOuter = allConsAt[pV, xV, consAPApp[yV, lV]];
      (*               = p x ∧ (p y ∧ ALL p l) *)
      allLhsInner = HOL`Equal`APTERM[
        mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]],
          mkComb[pV, xV]], allConsAt[pV, yV, lV]];
      lhsExpanded = TRANS[allLhsOuter, allLhsInner];
      (* ⊢ ALL p (CONS x (CONS y l)) = p x ∧ (p y ∧ ALL p l) *)

      allRhsOuter = allConsAt[pV, yV, consAPApp[xV, lV]];
      allRhsInner = HOL`Equal`APTERM[
        mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]],
          mkComb[pV, yV]], allConsAt[pV, xV, lV]];
      rhsExpanded = TRANS[allRhsOuter, allRhsInner];

      swapEq = HOL`Bool`SPEC[allPLTm, HOL`Bool`SPEC[mkComb[pV, yV],
        HOL`Bool`SPEC[mkComb[pV, xV], andSwapMidThm]]];
      (* ⊢ p x ∧ (p y ∧ ALL p l) = p y ∧ (p x ∧ ALL p l) *)

      chain = TRANS[lhsExpanded, swapEq];
      finalChain = TRANS[chain, HOL`Equal`SYM[rhsExpanded]];
      (* ⊢ ALL p (CONS x (CONS y l)) = ALL p (CONS y (CONS x l)) *)

      HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[lV, finalChain]]]
    ];

    conj4 = Module[{l1L, l2L, l3L, hyp12, hyp23, trChain, dH23, dH12},
      l1L = mkVar["l1A4", listAP[]];
      l2L = mkVar["l2A4", listAP[]];
      l3L = mkVar["l3A4", listAP[]];
      hyp12 = ASSUME[mkEq[
        mkComb[mkComb[mkConst["ALL",
          tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], l1L],
        mkComb[mkComb[mkConst["ALL",
          tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], l2L]]];
      hyp23 = ASSUME[mkEq[
        mkComb[mkComb[mkConst["ALL",
          tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], l2L],
        mkComb[mkComb[mkConst["ALL",
          tyFun[predFnTy, tyFun[listAP[], boolTy]]], pV], l3L]]];
      trChain = TRANS[hyp12, hyp23];
      dH23 = HOL`Bool`DISCH[concl[hyp23], trChain];
      dH12 = HOL`Bool`DISCH[concl[hyp12], dH23];
      HOL`Bool`GEN[l1L, HOL`Bool`GEN[l2L, HOL`Bool`GEN[l3L, dH12]]]
    ];

    closureProof = HOL`Bool`CONJ[conj1,
      HOL`Bool`CONJ[conj2, HOL`Bool`CONJ[conj3, conj4]]];
    applyAll = HOL`Bool`MP[indBeta, closureProof];
    (* (free p) ⊢ ∀l1 l2. PERM l1 l2 ⇒ ALL p l1 = ALL p l2 *)
    gen = HOL`Bool`GEN[pV, applyAll];
    gen
  ];

(* ============================================================ *)
(* memSplitThm                                                  *)
(*   ⊢ ∀x l. MEM x l ⇒ ∃l1 l2. l = APPEND l1 (CONS x l2).        *)
(*                                                              *)
(* List induction on l (x fixed). NIL: MEM x NIL = F ⇒ vacuous   *)
(* via CONTR. CONS y l': memCons → (x = y ∨ MEM x l');           *)
(*   x = y branch: l1 = NIL, l2 = l' (use SUBS[x = y]);          *)
(*   MEM x l' branch: IH gives l1', l2' for l';                  *)
(*     take l1 = CONS y l1', l2 = l2' (appendConsThm rewrites    *)
(*     APPEND (CONS y l1') (CONS x l2') = CONS y (APPEND l1'     *)
(*     (CONS x l2')) = CONS y l').                                *)
(* ============================================================ *)

memSplitThm =
  Module[{αP, αPL, xT, lV, l1V, l2V, appendC, consC, nilC, memC,
          existsLTy, exConcl, memAt, predLam, inductSpec, inductBeta,
          baseCase, indStep, conjForall, finalAtL, genX},
    αP  = mkVarType["A"];
    αPL = HOL`Stdlib`List`listTy[αP];
    xT  = mkVar["xMS", αP];
    lV  = mkVar["lMS", αPL];
    l1V = mkVar["l1MS", αPL];
    l2V = mkVar["l2MS", αPL];

    appendC = mkConst["APPEND", tyFun[αPL, tyFun[αPL, αPL]]];
    consC   = mkConst["CONS", tyFun[αP, tyFun[αPL, αPL]]];
    nilC    = mkConst["NIL", αPL];
    memC    = mkConst["MEM", tyFun[αP, tyFun[αPL, boolTy]]];

    existsLTy[v_, body_] :=
      mkComb[mkConst["∃", tyFun[tyFun[αPL, boolTy], boolTy]],
        mkAbs[v, body]];

    exConcl[lt_] := existsLTy[l1V, existsLTy[l2V,
      mkEq[lt, mkComb[mkComb[appendC, l1V],
        mkComb[mkComb[consC, xT], l2V]]]]];

    memAt[lt_] := mkComb[mkComb[memC, xT], lt];

    predLam = mkAbs[lV, impTm[memAt[lV], exConcl[lV]]];
    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{mkVarType["A"] -> αP},
        HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];

    (* --- NIL case --- *)
    baseCase = Module[{memNilAt, memHyp, fThm},
      memNilAt = HOL`Bool`SPEC[xT,
        INSTTYPE[{mkVarType["A"] -> αP},
          HOL`Stdlib`List`memNilThm]];
      (* ⊢ MEM xT NIL = F *)
      memHyp = ASSUME[memAt[nilC]];
      fThm = EQMP[memNilAt, memHyp];
      HOL`Bool`DISCH[memAt[nilC],
        HOL`Bool`CONTR[exConcl[nilC], fThm]]
    ];

    (* --- CONS case --- *)
    indStep = Module[{yV, lLoc, ihHypT, ihHyp, memConsHyp, memConsAt,
                      memConsDisj, headCase, tailCase, bodyEx,
                      dischMem, stepInner},
      yV   = mkVar["yMS", αP];
      lLoc = mkVar["lMSI", αPL];

      ihHypT = impTm[memAt[lLoc], exConcl[lLoc]];
      ihHyp = ASSUME[ihHypT];

      memConsHyp = ASSUME[memAt[mkComb[mkComb[consC, yV], lLoc]]];
      memConsAt = HOL`Bool`SPEC[lLoc, HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[xT,
          INSTTYPE[{mkVarType["A"] -> αP},
            HOL`Stdlib`List`memConsThm]]]];
      (* ⊢ MEM xT (CONS y l) = (xT = y ∨ MEM xT l) *)
      memConsDisj = EQMP[memConsAt, memConsHyp];

      (* head branch: x = y. Take l1 = NIL, l2 = lLoc. *)
      headCase = Module[{xEqY, appendNilAt, consXLEq, eqL,
                        eqLSym, exL2Tm, exL2, exL1Tm, exL1},
        xEqY = ASSUME[mkEq[xT, yV]];

        appendNilAt = HOL`Bool`SPEC[
          mkComb[mkComb[consC, xT], lLoc],
          INSTTYPE[{mkVarType["A"] -> αP},
            HOL`Stdlib`List`appendNilThm]];
        (* ⊢ APPEND NIL (CONS xT lLoc) = CONS xT lLoc *)

        consXLEq = HOL`Equal`APTHM[
          HOL`Equal`APTERM[consC, xEqY], lLoc];
        (* (xT = yV) ⊢ CONS xT lLoc = CONS yV lLoc *)
        eqL = TRANS[appendNilAt, consXLEq];
        (* (xT = yV) ⊢ APPEND NIL (CONS xT lLoc) = CONS yV lLoc *)
        eqLSym = HOL`Equal`SYM[eqL];
        (* (xT = yV) ⊢ CONS yV lLoc = APPEND NIL (CONS xT lLoc) *)

        exL2Tm = existsLTy[l2V,
          mkEq[mkComb[mkComb[consC, yV], lLoc],
            mkComb[mkComb[appendC, nilC],
              mkComb[mkComb[consC, xT], l2V]]]];
        exL2 = HOL`Bool`EXISTS[exL2Tm, lLoc, eqLSym];
        (* (xT = yV) ⊢ ∃l2. CONS yV lLoc = APPEND NIL (CONS xT l2) *)

        exL1Tm = existsLTy[l1V,
          existsLTy[l2V,
            mkEq[mkComb[mkComb[consC, yV], lLoc],
              mkComb[mkComb[appendC, l1V],
                mkComb[mkComb[consC, xT], l2V]]]]];
        exL1 = HOL`Bool`EXISTS[exL1Tm, nilC, exL2];
        (* (xT = yV) ⊢ ∃l1 l2. CONS yV lLoc = APPEND l1 (CONS xT l2) *)
        exL1
      ];

      (* tail branch: MEM xT lLoc. Apply IH to get l1', l2' for lLoc, *)
      (* then prepend yV.                                              *)
      tailCase = Module[{memHyp, mpFromIH, l1pV, l2pV, innerEqTm,
                        innerEqHyp, appendConsAt, consSymL, chainEq,
                        chainSymEq, exL2Tm, exL2, exL1Tm, exL1,
                        outerExTm, innerChose, outerChose},
        memHyp = ASSUME[memAt[lLoc]];
        mpFromIH = HOL`Bool`MP[ihHyp, memHyp];
        (* (IH, MEM xT lLoc) ⊢ ∃l1 l2. lLoc = APPEND l1 (CONS xT l2) *)

        l1pV = mkVar["l1pMS", αPL];
        l2pV = mkVar["l2pMS", αPL];

        innerEqTm = mkEq[lLoc,
          mkComb[mkComb[appendC, l1pV],
            mkComb[mkComb[consC, xT], l2pV]]];
        innerEqHyp = ASSUME[innerEqTm];
        (* (lLoc = APPEND l1p (CONS xT l2p)) ⊢ … *)

        appendConsAt = HOL`Bool`SPEC[
          mkComb[mkComb[consC, xT], l2pV],
          HOL`Bool`SPEC[l1pV, HOL`Bool`SPEC[yV,
            INSTTYPE[{mkVarType["A"] -> αP},
              HOL`Stdlib`List`appendConsThm]]]];
        (* ⊢ APPEND (CONS yV l1p) (CONS xT l2p)
             = CONS yV (APPEND l1p (CONS xT l2p)) *)

        consSymL = HOL`Equal`APTERM[
          mkComb[consC, yV],
          HOL`Equal`SYM[innerEqHyp]];
        (* (innerEq) ⊢ CONS yV (APPEND l1p (CONS xT l2p)) = CONS yV lLoc *)

        chainEq = TRANS[appendConsAt, consSymL];
        (* (innerEq) ⊢ APPEND (CONS yV l1p) (CONS xT l2p) = CONS yV lLoc *)
        chainSymEq = HOL`Equal`SYM[chainEq];
        (* (innerEq) ⊢ CONS yV lLoc = APPEND (CONS yV l1p) (CONS xT l2p) *)

        exL2Tm = existsLTy[l2V,
          mkEq[mkComb[mkComb[consC, yV], lLoc],
            mkComb[mkComb[appendC, mkComb[mkComb[consC, yV], l1pV]],
              mkComb[mkComb[consC, xT], l2V]]]];
        exL2 = HOL`Bool`EXISTS[exL2Tm, l2pV, chainSymEq];
        (* (innerEq) ⊢ ∃l2. CONS yV lLoc = APPEND (CONS yV l1p) (CONS xT l2) *)

        exL1Tm = existsLTy[l1V,
          existsLTy[l2V,
            mkEq[mkComb[mkComb[consC, yV], lLoc],
              mkComb[mkComb[appendC, l1V],
                mkComb[mkComb[consC, xT], l2V]]]]];
        exL1 = HOL`Bool`EXISTS[exL1Tm, mkComb[mkComb[consC, yV], l1pV], exL2];
        (* (innerEq) ⊢ ∃l1 l2. CONS yV lLoc = APPEND l1 (CONS xT l2) *)

        outerExTm = existsLTy[l2pV, innerEqTm];
        (* ∃l2p. lLoc = APPEND l1p (CONS xT l2p)  (outer of two ∃) *)
        innerChose = HOL`Bool`CHOOSE[l2pV, ASSUME[outerExTm], exL1];
        (* (∃l2. lLoc = APPEND l1p (CONS xT l2)) ⊢ ∃l1 l2. CONS yV lLoc = … *)

        outerChose = HOL`Bool`CHOOSE[l1pV, mpFromIH, innerChose];
        (* (IH, MEM xT lLoc) ⊢ ∃l1 l2. CONS yV lLoc = APPEND l1 (CONS xT l2) *)
        outerChose
      ];

      bodyEx = HOL`Bool`DISJCASES[memConsDisj, headCase, tailCase];
      dischMem = HOL`Bool`DISCH[memAt[mkComb[mkComb[consC, yV], lLoc]],
        bodyEx];
      stepInner = HOL`Bool`DISCH[ihHypT, dischMem];
      HOL`Bool`GEN[yV, HOL`Bool`GEN[lLoc, stepInner]]
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalAtL = HOL`Bool`MP[inductBeta, conjForall];
    (* ⊢ ∀l. MEM xT l ⇒ ∃l1 l2. l = APPEND l1 (CONS xT l2) *)
    genX = HOL`Bool`GEN[xT, finalAtL];
    genX
  ];

(* ============================================================ *)
(* permAppendConsThm                                            *)
(*   ⊢ ∀x l1 l2. PERM (APPEND l1 (CONS x l2)) (CONS x (APPEND l1 l2)). *)
(*                                                              *)
(* List induction on l1 (x and l2 free in the induction).        *)
(*   NIL: APPEND NIL (CONS x l2) = CONS x l2 (appendNil);        *)
(*        CONS x (APPEND NIL l2) = CONS x l2.                     *)
(*        So both sides equal CONS x l2 and permReflThm closes.   *)
(*   CONS y l1':                                                  *)
(*     APPEND (CONS y l1') (CONS x l2) = CONS y (APPEND l1' …)   *)
(*     IH:  PERM (APPEND l1' (CONS x l2)) (CONS x (APPEND l1' l2)) *)
(*     permCons at y:                                             *)
(*       PERM (CONS y (APPEND l1' (CONS x l2)))                    *)
(*            (CONS y (CONS x (APPEND l1' l2)))                    *)
(*     permSwap at y, x, APPEND l1' l2:                            *)
(*       PERM (CONS y (CONS x (APPEND l1' l2)))                    *)
(*            (CONS x (CONS y (APPEND l1' l2)))                    *)
(*     CONS y (APPEND l1' l2) = APPEND (CONS y l1') l2.            *)
(*     Chain via permTransThm + rewrite under CONS y at the head.  *)
(* ============================================================ *)

permAppendConsThm =
  Module[{αP, αPL, xT, l2T, l1V, yV, appendC, consC, nilC,
          predLam, inductSpec, inductBeta, baseCase, indStep,
          conjForall, finalAtL1, genX, genL2},
    αP  = mkVarType["A"];
    αPL = HOL`Stdlib`List`listTy[αP];
    xT  = mkVar["xPAC", αP];
    l2T = mkVar["l2PAC", αPL];
    l1V = mkVar["l1PAC", αPL];
    yV  = mkVar["yPAC", αP];

    appendC = mkConst["APPEND", tyFun[αPL, tyFun[αPL, αPL]]];
    consC   = mkConst["CONS", tyFun[αP, tyFun[αPL, αPL]]];
    nilC    = mkConst["NIL", αPL];

    (* predLam[L1] = PERM (APPEND L1 (CONS xT l2T))
                          (CONS xT (APPEND L1 l2T)) *)
    predLam = mkAbs[l1V,
      permTm[
        mkComb[mkComb[appendC, l1V],
          mkComb[mkComb[consC, xT], l2T]],
        mkComb[mkComb[consC, xT],
          mkComb[mkComb[appendC, l1V], l2T]]]];

    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{mkVarType["A"] -> αP},
        HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];
    (* ⊢ (P NIL ∧ ∀y l1. P l1 ⇒ P (CONS y l1)) ⇒ ∀l1. P l1 *)

    (* --- NIL case --- *)
    (* Both APPEND NIL (CONS x l2) and CONS x (APPEND NIL l2) reduce to     *)
    (* CONS x l2 via appendNilThm. Build the equation A = B (= CONS x l2)   *)
    (* then APTERM(PERM A) lifts refl PERM A A to PERM A B.                 *)
    baseCase = Module[{appendNil1, appendNil2, rhsEq, aTm, bTm, eqAB,
                       reflAA, permA, apEq, permAB},
      appendNil1 = HOL`Bool`SPEC[
        mkComb[mkComb[consC, xT], l2T],
        INSTTYPE[{mkVarType["A"] -> αP},
          HOL`Stdlib`List`appendNilThm]];
      (* ⊢ APPEND NIL (CONS xT l2T) = CONS xT l2T *)
      appendNil2 = HOL`Bool`SPEC[l2T,
        INSTTYPE[{mkVarType["A"] -> αP},
          HOL`Stdlib`List`appendNilThm]];
      (* ⊢ APPEND NIL l2T = l2T *)
      rhsEq = HOL`Equal`APTERM[mkComb[consC, xT], appendNil2];
      (* ⊢ CONS xT (APPEND NIL l2T) = CONS xT l2T *)

      aTm = mkComb[mkComb[appendC, nilC],
        mkComb[mkComb[consC, xT], l2T]];
      bTm = mkComb[mkComb[consC, xT],
        mkComb[mkComb[appendC, nilC], l2T]];
      eqAB = TRANS[appendNil1, HOL`Equal`SYM[rhsEq]];
      (* ⊢ aTm = bTm *)

      reflAA = HOL`Bool`SPEC[aTm,
        INSTTYPE[{αPerm -> αP}, permReflThm]];
      (* ⊢ PERM aTm aTm *)
      permA = mkComb[permConst[], aTm];
      apEq = HOL`Equal`APTERM[permA, eqAB];
      (* ⊢ PERM aTm aTm = PERM aTm bTm *)
      permAB = EQMP[apEq, reflAA];
      permAB
    ];

    (* --- CONS y l1' case --- *)
    indStep = Module[{l1pV, ihHypT, ihHyp, appendConsAtLhs, appendConsAtRhs,
                      lhsExpand, rhsExpand, permConsAt, permSwapAt,
                      transFirst, transChainAt, transChain, rhsRewrite,
                      finalPerm, dischIH},
      l1pV = mkVar["l1pPAC", αPL];

      ihHypT = permTm[
        mkComb[mkComb[appendC, l1pV],
          mkComb[mkComb[consC, xT], l2T]],
        mkComb[mkComb[consC, xT],
          mkComb[mkComb[appendC, l1pV], l2T]]];
      ihHyp = ASSUME[ihHypT];

      (* appendCons: APPEND (CONS y l1') l2 = CONS y (APPEND l1' l2). *)
      (* At y, l1', (CONS xT l2T): *)
      appendConsAtLhs = HOL`Bool`SPEC[
        mkComb[mkComb[consC, xT], l2T],
        HOL`Bool`SPEC[l1pV, HOL`Bool`SPEC[yV,
          INSTTYPE[{mkVarType["A"] -> αP},
            HOL`Stdlib`List`appendConsThm]]]];
      (* ⊢ APPEND (CONS yV l1pV) (CONS xT l2T)
           = CONS yV (APPEND l1pV (CONS xT l2T)) *)

      (* At y, l1', l2T: *)
      appendConsAtRhs = HOL`Bool`SPEC[l2T,
        HOL`Bool`SPEC[l1pV, HOL`Bool`SPEC[yV,
          INSTTYPE[{mkVarType["A"] -> αP},
            HOL`Stdlib`List`appendConsThm]]]];
      (* ⊢ APPEND (CONS yV l1pV) l2T = CONS yV (APPEND l1pV l2T) *)

      (* PERM(CONS y (APPEND l1p (CONS x l2T)))
              (CONS y (CONS x (APPEND l1p l2T))) via permCons + IH *)
      permConsAt = HOL`Bool`SPEC[
        mkComb[mkComb[consC, xT],
          mkComb[mkComb[appendC, l1pV], l2T]],
        HOL`Bool`SPEC[
          mkComb[mkComb[appendC, l1pV],
            mkComb[mkComb[consC, xT], l2T]],
          HOL`Bool`SPEC[yV, permConsThm]]];
      (* ⊢ PERM (APPEND l1p (CONS x l2T)) (CONS x (APPEND l1p l2T))
           ⇒ PERM (CONS yV (APPEND l1p (CONS x l2T)))
                  (CONS yV (CONS x (APPEND l1p l2T))) *)
      transFirst = HOL`Bool`MP[permConsAt, ihHyp];
      (* (IH) ⊢ PERM (CONS yV (APPEND l1p (CONS x l2T)))
                     (CONS yV (CONS x (APPEND l1p l2T))) *)

      (* permSwap at y, x, (APPEND l1p l2T): *)
      permSwapAt = HOL`Bool`SPEC[
        mkComb[mkComb[appendC, l1pV], l2T],
        HOL`Bool`SPEC[xT, HOL`Bool`SPEC[yV, permSwapThm]]];
      (* ⊢ PERM (CONS yV (CONS xT (APPEND l1p l2T)))
                (CONS xT (CONS yV (APPEND l1p l2T))) *)

      (* Combine via permTransThm. *)
      transChainAt = HOL`Bool`SPEC[
        mkComb[mkComb[consC, xT],
          mkComb[mkComb[consC, yV],
            mkComb[mkComb[appendC, l1pV], l2T]]],
        HOL`Bool`SPEC[
          mkComb[mkComb[consC, yV],
            mkComb[mkComb[consC, xT],
              mkComb[mkComb[appendC, l1pV], l2T]]],
          HOL`Bool`SPEC[
            mkComb[mkComb[consC, yV],
              mkComb[mkComb[appendC, l1pV],
                mkComb[mkComb[consC, xT], l2T]]],
            permTransThm]]];
      (* ⊢ PERM l1 l2 ⇒ PERM l2 l3 ⇒ PERM l1 l3 (with the three lists above) *)
      transChain = HOL`Bool`MP[HOL`Bool`MP[transChainAt, transFirst],
        permSwapAt];
      (* (IH) ⊢ PERM (CONS yV (APPEND l1p (CONS x l2T)))
                     (CONS xT (CONS yV (APPEND l1p l2T))) *)

      (* Use appendConsAtLhs (SYM) to rewrite the first argument:    *)
      (*   CONS yV (APPEND l1p (CONS x l2T))                          *)
      (*     = APPEND (CONS yV l1p) (CONS x l2T)                      *)
      (* And appendConsAtRhs (SYM) to rewrite the second argument:    *)
      (*   CONS yV (APPEND l1p l2T) = APPEND (CONS yV l1p) l2T        *)
      finalPerm = HOL`Drule`SUBS[
        {HOL`Equal`SYM[appendConsAtLhs], HOL`Equal`SYM[appendConsAtRhs]},
        transChain];
      (* (IH) ⊢ PERM (APPEND (CONS yV l1p) (CONS x l2T))
                     (CONS x (APPEND (CONS yV l1p) l2T)) *)

      dischIH = HOL`Bool`DISCH[ihHypT, finalPerm];
      HOL`Bool`GEN[yV, HOL`Bool`GEN[l1pV, dischIH]]
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalAtL1 = HOL`Bool`MP[inductBeta, conjForall];
    (* (free xT, l2T) ⊢ ∀l1. PERM (APPEND l1 (CONS xT l2T))
                                  (CONS xT (APPEND l1 l2T)) *)
    (* SPEC down to a free l1, then GEN back in the order x l1 l2. *)
    Module[{l1FreeV, specL1, genL2, genL1, genX2},
      l1FreeV = mkVar["l1PACO", αPL];
      specL1 = HOL`Bool`SPEC[l1FreeV, finalAtL1];
      genL2 = HOL`Bool`GEN[l2T, specL1];
      genL1 = HOL`Bool`GEN[l1FreeV, genL2];
      genX2 = HOL`Bool`GEN[xT, genL1];
      genX2
    ]
  ];

(* ============================================================ *)
(* multEqZeroThm  (stage-3.d helper)                             *)
(*   ⊢ ∀x a. x * a = 0 ⇒ x = 0 ∨ a = 0.                          *)
(* Cases on x via numCasesThm. x = 0: DISJ1. x = SUC k:           *)
(*   SUC k * a = a + k * a (timesLeftSucThm), so a + k * a = 0;   *)
(*   addEqZeroLeftThm gives a = 0; DISJ2.                          *)
(* ============================================================ *)

multEqZeroThm =
  Module[{xV, aV, kV, hypH, casesX, zeroBranch, sucBranch, exKBody,
          body, dischHyp, gens},
    xV = mkVar["xMZ", numTy];
    aV = mkVar["aMZ", numTy];
    kV = mkVar["kMZ", numTy];

    hypH = ASSUME[mkEq[timesN[xV, aV], zeroN[]]];
    casesX = HOL`Bool`SPEC[xV, HOL`Stdlib`Num`numCasesThm];
    (* ⊢ x = 0 ∨ ∃m. x = SUC m *)

    zeroBranch = Module[{xEq0Hyp},
      xEq0Hyp = ASSUME[mkEq[xV, zeroN[]]];
      HOL`Bool`DISJ1[xEq0Hyp, mkEq[aV, zeroN[]]]
    ];

    sucBranch = Module[{exKHyp, xEqSucKHyp, sucMultEqZ, timesLeftAt,
                       addEqZ, aEq0, chosen},
      exKBody = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[kV, mkEq[xV, sucN[kV]]]];
      exKHyp = ASSUME[exKBody];
      xEqSucKHyp = ASSUME[mkEq[xV, sucN[kV]]];

      sucMultEqZ = HOL`Drule`SUBS[{xEqSucKHyp}, hypH];
      (* (xEqSucK, hypH) ⊢ SUC k * a = 0 *)
      timesLeftAt = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[kV,
        HOL`Stdlib`Num`timesLeftSucThm]];
      (* ⊢ SUC k * a = a + k * a *)
      addEqZ = TRANS[HOL`Equal`SYM[timesLeftAt], sucMultEqZ];
      (* (…) ⊢ a + k * a = 0 *)
      aEq0 = HOL`Bool`MP[
        HOL`Bool`SPEC[timesN[kV, aV],
          HOL`Bool`SPEC[aV, HOL`Stdlib`Num`addEqZeroLeftThm]],
        addEqZ];
      (* (…) ⊢ a = 0 *)
      chosen = HOL`Bool`CHOOSE[kV, exKHyp,
        HOL`Bool`DISJ2[aEq0, mkEq[xV, zeroN[]]]];
      chosen
    ];

    body = HOL`Bool`DISJCASES[casesX, zeroBranch, sucBranch];
    dischHyp = HOL`Bool`DISCH[mkEq[timesN[xV, aV], zeroN[]], body];
    gens = HOL`Bool`GEN[xV, HOL`Bool`GEN[aV, dischHyp]];
    gens
  ];

(* ============================================================ *)
(* multLeftCancelThm  (stage-3.d helper)                         *)
(*   ⊢ ∀x. ¬(x = 0) ⇒ ∀a b. x * a = x * b ⇒ a = b.               *)
(*                                                              *)
(* Fix x with x ≠ 0 outside; num induction on a.                  *)
(*   Base a = 0: x*b = 0 (from x*0=0 + hyp); multEqZeroThm with    *)
(*     ¬(x=0) gives b=0; SYM gives 0 = b.                          *)
(*   Step a = SUC a': IH ⊢ ∀b. x*a' = x*b ⇒ a' = b.                *)
(*     Cases on b (numCasesThm). b = 0: x*SUC a' = x*0 = 0,        *)
(*       x*SUC a' = x*a' + x by timesSucEq, so x*a' + x = 0;        *)
(*       addEqZeroRight gives x=0 — contradiction; CONTR.          *)
(*     b = SUC b': two timesSucEq + addRightCancel reduce to        *)
(*       x*a' = x*b'; IH yields a' = b'; APTERM[SUC] +              *)
(*       SUBS gives SUC a' = b.                                     *)
(* ============================================================ *)

multLeftCancelThm =
  Module[{xV, aV, aPV, bV, bPV, kCasesV, xNotZero, predLam, inductSpec,
          inductBeta, baseCase, indStep, conjForall, finalAtA,
          dischNotZ, gen},
    xV = mkVar["xMC", numTy];
    aV = mkVar["aMC", numTy];
    aPV = mkVar["aPMC", numTy];
    bV = mkVar["bMC", numTy];
    bPV = mkVar["bPMC", numTy];
    kCasesV = mkVar["kMCs", numTy];

    xNotZero = ASSUME[notTm[mkEq[xV, zeroN[]]]];

    (* predLam[a] = ∀b. x * a = x * b ⇒ a = b *)
    predLam = mkAbs[aV,
      mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[bV, impTm[mkEq[timesN[xV, aV], timesN[xV, bV]],
          mkEq[aV, bV]]]]];

    inductSpec = HOL`Bool`SPEC[predLam, HOL`Stdlib`Num`numInductionThm];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];
    (* ⊢ (∀b. x*0 = x*b ⇒ 0 = b)
       ∧ (∀a'. (∀b. x*a' = x*b ⇒ a' = b)
                ⇒ (∀b. x*SUC a' = x*b ⇒ SUC a' = b))
       ⇒ ∀a. ∀b. x*a = x*b ⇒ a = b *)

    baseCase = Module[{bLocal, eqHyp, x0Eq, eqVia0, symEq, bEq0Disj,
                      bEq0, zeroEqB, dischEq},
      bLocal = bV;
      eqHyp = ASSUME[mkEq[timesN[xV, zeroN[]], timesN[xV, bLocal]]];
      x0Eq = HOL`Bool`SPEC[xV, HOL`Stdlib`Num`timesZeroEqThm];
      (* ⊢ x * 0 = 0 *)
      eqVia0 = TRANS[HOL`Equal`SYM[x0Eq], eqHyp];
      (* (eqHyp) ⊢ 0 = x * bLocal *)
      symEq = HOL`Equal`SYM[eqVia0];
      (* (eqHyp) ⊢ x * bLocal = 0 *)
      bEq0Disj = HOL`Bool`MP[
        HOL`Bool`SPEC[bLocal, HOL`Bool`SPEC[xV, multEqZeroThm]],
        symEq];
      (* (eqHyp) ⊢ x = 0 ∨ bLocal = 0 *)
      bEq0 = HOL`Bool`DISJCASES[bEq0Disj,
        Module[{xEq0Hyp, fThm},
          xEq0Hyp = ASSUME[mkEq[xV, zeroN[]]];
          fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[xNotZero], xEq0Hyp];
          HOL`Bool`CONTR[mkEq[bLocal, zeroN[]], fThm]],
        ASSUME[mkEq[bLocal, zeroN[]]]];
      (* (eqHyp, ¬(x=0)) ⊢ bLocal = 0 *)
      zeroEqB = HOL`Equal`SYM[bEq0];
      (* (eqHyp, ¬(x=0)) ⊢ 0 = bLocal *)
      dischEq = HOL`Bool`DISCH[
        mkEq[timesN[xV, zeroN[]], timesN[xV, bLocal]], zeroEqB];
      HOL`Bool`GEN[bLocal, dischEq]
    ];

    indStep = Module[{aPL, ihHypT, ihHyp, bLocal, eqHyp, casesB,
                     zeroBranch, sucBranch, sucBody, dischEq, allB,
                     dischIH},
      aPL = aPV;
      ihHypT = mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[bV, impTm[mkEq[timesN[xV, aPL], timesN[xV, bV]],
          mkEq[aPL, bV]]]];
      ihHyp = ASSUME[ihHypT];

      bLocal = bV;
      eqHyp = ASSUME[mkEq[timesN[xV, sucN[aPL]], timesN[xV, bLocal]]];
      casesB = HOL`Bool`SPEC[bLocal, HOL`Stdlib`Num`numCasesThm];

      zeroBranch = Module[{bEq0Hyp, eqAt0, xT0Eq, eqIsZ, timesSucEq,
                          addEqZAtX, xEq0, fThm},
        bEq0Hyp = ASSUME[mkEq[bLocal, zeroN[]]];
        eqAt0 = HOL`Drule`SUBS[{bEq0Hyp}, eqHyp];
        (* (bEq0, eqHyp) ⊢ x * SUC aPL = x * 0 *)
        xT0Eq = HOL`Bool`SPEC[xV, HOL`Stdlib`Num`timesZeroEqThm];
        eqIsZ = TRANS[eqAt0, xT0Eq];
        (* (…) ⊢ x * SUC aPL = 0 *)
        timesSucEq = HOL`Bool`SPEC[aPL, HOL`Bool`SPEC[xV,
          HOL`Stdlib`Num`timesSucEqThm]];
        (* ⊢ x * SUC aPL = x * aPL + x *)
        addEqZAtX = TRANS[HOL`Equal`SYM[timesSucEq], eqIsZ];
        (* (…) ⊢ x * aPL + x = 0 *)
        xEq0 = HOL`Bool`MP[
          HOL`Bool`SPEC[xV, HOL`Bool`SPEC[timesN[xV, aPL],
            HOL`Stdlib`Num`addEqZeroRightThm]],
          addEqZAtX];
        (* (…) ⊢ x = 0 *)
        fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[xNotZero], xEq0];
        HOL`Bool`CONTR[mkEq[sucN[aPL], bLocal], fThm]
      ];

      sucBranch = Module[{exBpBody, exBpHyp, bEqSucBpHyp, eqAtSucBp,
                         timesSucAtA, timesSucAtBp, addCancAtRow,
                         midEq, cancled, ihAtBp, apEq, sucAEqSucBp,
                         finalEq, chosen},
        exBpBody = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[bPV, mkEq[bLocal, sucN[bPV]]]];
        exBpHyp = ASSUME[exBpBody];
        bEqSucBpHyp = ASSUME[mkEq[bLocal, sucN[bPV]]];

        eqAtSucBp = HOL`Drule`SUBS[{bEqSucBpHyp}, eqHyp];
        (* (bEqSucBp, eqHyp) ⊢ x * SUC aPL = x * SUC bPV *)
        timesSucAtA = HOL`Bool`SPEC[aPL, HOL`Bool`SPEC[xV,
          HOL`Stdlib`Num`timesSucEqThm]];
        (* ⊢ x * SUC aPL = x * aPL + x *)
        timesSucAtBp = HOL`Bool`SPEC[bPV, HOL`Bool`SPEC[xV,
          HOL`Stdlib`Num`timesSucEqThm]];
        (* ⊢ x * SUC bPV = x * bPV + x *)
        midEq = TRANS[HOL`Equal`SYM[timesSucAtA],
          TRANS[eqAtSucBp, timesSucAtBp]];
        (* (…) ⊢ x * aPL + x = x * bPV + x *)
        addCancAtRow = HOL`Bool`SPEC[timesN[xV, bPV],
          HOL`Bool`SPEC[timesN[xV, aPL], HOL`Bool`SPEC[xV,
            HOL`Stdlib`Num`addRightCancelThm]]];
        (* addRightCancelThm: ∀m n k. n + m = k + m ⇒ n = k.       *)
        (* Outermost ∀m → xV (the common right operand), then       *)
        (* ∀n → xV*aPL, then ∀k → xV*bPV.                            *)
        (* ⊢ x*aPL + x = x*bPV + x ⇒ x*aPL = x*bPV *)
        cancled = HOL`Bool`MP[addCancAtRow, midEq];
        (* (…) ⊢ x * aPL = x * bPV *)

        ihAtBp = HOL`Bool`SPEC[bPV, ihHyp];
        (* ⊢ x * aPL = x * bPV ⇒ aPL = bPV *)
        apEq = HOL`Bool`MP[ihAtBp, cancled];
        (* (…) ⊢ aPL = bPV *)
        sucAEqSucBp = HOL`Equal`APTERM[
          HOL`Stdlib`Num`sucConst[], apEq];
        (* (…) ⊢ SUC aPL = SUC bPV *)
        finalEq = HOL`Drule`SUBS[{HOL`Equal`SYM[bEqSucBpHyp]},
          sucAEqSucBp];
        (* (bEqSucBp, …) ⊢ SUC aPL = bLocal *)
        chosen = HOL`Bool`CHOOSE[bPV, exBpHyp, finalEq];
        (* (∃bp. b = SUC bp, …) ⊢ SUC aPL = bLocal *)
        chosen
      ];

      sucBody = HOL`Bool`DISJCASES[casesB, zeroBranch, sucBranch];
      dischEq = HOL`Bool`DISCH[
        mkEq[timesN[xV, sucN[aPL]], timesN[xV, bLocal]], sucBody];
      allB = HOL`Bool`GEN[bLocal, dischEq];
      dischIH = HOL`Bool`DISCH[ihHypT, allB];
      HOL`Bool`GEN[aPL, dischIH]
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalAtA = HOL`Bool`MP[inductBeta, conjForall];
    (* (¬(x=0)) ⊢ ∀a. ∀b. x*a = x*b ⇒ a = b *)
    dischNotZ = HOL`Bool`DISCH[notTm[mkEq[xV, zeroN[]]], finalAtA];
    gen = HOL`Bool`GEN[xV, dischNotZ];
    gen
  ];

(* ============================================================ *)
(* primeNotZeroThm  (stage-3.d helper)                            *)
(*   ⊢ ∀p. prime p ⇒ ¬(p = 0).                                    *)
(* From prime p extract SUC 0 < p. If p = 0, SUC 0 < 0 — but       *)
(* notLtZeroThm says ¬(n < 0).                                    *)
(* ============================================================ *)

primeNotZeroThm =
  Module[{pV, primeHyp, primeUnf, primeUnfApplied, oneLtP, pEq0Hyp,
          oneLtZero, fThm, notIntro, dischP, gen},
    pV = mkVar["pNZ", numTy];

    primeHyp = ASSUME[primeN[pV]];
    primeUnf = Module[{ap},
      ap = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, pV];
      TRANS[ap, BETACONV[concl[ap][[2]]]]];
    primeUnfApplied = EQMP[primeUnf, primeHyp];
    oneLtP = HOL`Bool`CONJUNCT1[primeUnfApplied];
    (* (prime p) ⊢ SUC 0 < p *)

    pEq0Hyp = ASSUME[mkEq[pV, zeroN[]]];
    oneLtZero = HOL`Drule`SUBS[{pEq0Hyp}, oneLtP];
    (* (prime p, p = 0) ⊢ SUC 0 < 0 *)
    fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[
      HOL`Bool`SPEC[oneN[], HOL`Stdlib`Num`notLtZeroThm]],
      oneLtZero];
    (* (prime p, p = 0) ⊢ F *)
    notIntro = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[pV, zeroN[]], fThm]];
    (* (prime p) ⊢ ¬(p = 0) *)
    dischP = HOL`Bool`DISCH[primeN[pV], notIntro];
    gen = HOL`Bool`GEN[pV, dischP];
    gen
  ];

(* ============================================================ *)
(* primesEqIfDividesThm  (stage-3.d helper)                       *)
(*   ⊢ ∀p q. prime p ⇒ prime q ⇒ divides p q ⇒ p = q.             *)
(*                                                              *)
(* From prime q: ∀d. d | q ⇒ d = SUC 0 ∨ d = q. SPEC at d = p     *)
(* gives p = SUC 0 ∨ p = q. From prime p: SUC 0 < p, so p ≠ SUC 0  *)
(* (ltImpliesNotEq + SYM), leaving p = q.                          *)
(* ============================================================ *)

primesEqIfDividesThm =
  Module[{pV, qV, primePHyp, primeQHyp, divHyp, primeUnfQ, primeQApp,
          oneLtP, primeUnfP, primePApp, allDClause, atP, mpDiv,
          oneEqPHyp, sucNeqP, sucEqPHyp, sucEqP, fThm, eqPCase,
          notSucEqPThm, divCase, body, dischDiv, dischPQ, dischPP, gens},
    pV = mkVar["pPED", numTy];
    qV = mkVar["qPED", numTy];

    primePHyp = ASSUME[primeN[pV]];
    primeQHyp = ASSUME[primeN[qV]];
    divHyp = ASSUME[dividesN[pV, qV]];

    primeUnfQ = Module[{ap},
      ap = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, qV];
      TRANS[ap, BETACONV[concl[ap][[2]]]]];
    primeQApp = EQMP[primeUnfQ, primeQHyp];
    (* (prime q) ⊢ SUC 0 < q ∧ (∀d. d|q ⇒ d = SUC 0 ∨ d = q) *)
    allDClause = HOL`Bool`CONJUNCT2[primeQApp];
    atP = HOL`Bool`SPEC[pV, allDClause];
    (* ⊢ p | q ⇒ p = SUC 0 ∨ p = q *)
    mpDiv = HOL`Bool`MP[atP, divHyp];
    (* (prime q, p|q) ⊢ p = SUC 0 ∨ p = q *)

    primeUnfP = Module[{ap},
      ap = HOL`Equal`APTHM[HOL`Stdlib`Num`primeDefThm, pV];
      TRANS[ap, BETACONV[concl[ap][[2]]]]];
    primePApp = EQMP[primeUnfP, primePHyp];
    oneLtP = HOL`Bool`CONJUNCT1[primePApp];
    (* (prime p) ⊢ SUC 0 < p *)

    notSucEqPThm = HOL`Bool`MP[
      HOL`Bool`SPEC[pV, HOL`Bool`SPEC[oneN[],
        HOL`Stdlib`Num`ltImpliesNotEqThm]],
      oneLtP];
    (* (prime p) ⊢ ¬(SUC 0 = p) *)

    eqPCase = Module[{pEqOneHyp, oneEqP, fThm2},
      pEqOneHyp = ASSUME[mkEq[pV, oneN[]]];
      oneEqP = HOL`Equal`SYM[pEqOneHyp];
      (* (p = SUC 0) ⊢ SUC 0 = p *)
      fThm2 = HOL`Bool`MP[HOL`Bool`NOTELIM[notSucEqPThm], oneEqP];
      HOL`Bool`CONTR[mkEq[pV, qV], fThm2]
    ];
    (* (prime p, p = SUC 0) ⊢ p = q *)

    divCase = ASSUME[mkEq[pV, qV]];
    (* (p = q) ⊢ p = q *)

    body = HOL`Bool`DISJCASES[mpDiv, eqPCase, divCase];
    (* (prime p, prime q, p|q) ⊢ p = q *)
    dischDiv = HOL`Bool`DISCH[dividesN[pV, qV], body];
    dischPQ = HOL`Bool`DISCH[primeN[qV], dischDiv];
    dischPP = HOL`Bool`DISCH[primeN[pV], dischPQ];
    gens = HOL`Bool`GEN[pV, HOL`Bool`GEN[qV, dischPP]];
    gens
  ];

(* ============================================================ *)
(* allMemImpThm  (stage-3.d helper)                               *)
(*   ⊢ ∀P l. ALL P l ⇒ ∀x. MEM x l ⇒ P x.                         *)
(* List induction on l (P free outside). NIL: MEM x NIL = F gives  *)
(* vacuous. CONS y l': from ALL P (CONS y l') = P y ∧ ALL P l';    *)
(*   MEM x (CONS y l') = (x = y ∨ MEM x l'); x=y branch uses        *)
(*   SUBS[x=y]→P x = P y from the ALL conjunct; MEM x l' branch     *)
(*   applies IH.                                                  *)
(* ============================================================ *)

allMemImpThm =
  Module[{αAM, αAML, predFnTy, pV, lV, xT, predLam, inductSpec,
          inductBeta, baseCase, indStep, conjForall, finalAtL,
          dischP, genP, allC, memC, nilC, consC, allAt, memAt},
    αAM = mkVarType["A"];
    αAML = HOL`Stdlib`List`listTy[αAM];
    predFnTy = tyFun[αAM, boolTy];
    pV = mkVar["pAM", predFnTy];
    lV = mkVar["lAM", αAML];
    xT = mkVar["xAM", αAM];

    allC = mkConst["ALL", tyFun[predFnTy, tyFun[αAML, boolTy]]];
    memC = mkConst["MEM", tyFun[αAM, tyFun[αAML, boolTy]]];
    nilC = mkConst["NIL", αAML];
    consC = mkConst["CONS", tyFun[αAM, tyFun[αAML, αAML]]];

    allAt[lt_] := mkComb[mkComb[allC, pV], lt];
    memAt[xt_, lt_] := mkComb[mkComb[memC, xt], lt];

    (* predLam[l] = ALL P l ⇒ ∀x. MEM x l ⇒ P x *)
    predLam = mkAbs[lV,
      impTm[allAt[lV],
        mkComb[mkConst["∀", tyFun[tyFun[αAM, boolTy], boolTy]],
          mkAbs[xT, impTm[memAt[xT, lV], mkComb[pV, xT]]]]]];
    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{mkVarType["A"] -> αAM},
        HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];

    baseCase = Module[{allNilHyp, memHyp, memNilAt, fThm, dischMem,
                      genX, dischAll},
      allNilHyp = ASSUME[allAt[nilC]];
      memHyp = ASSUME[memAt[xT, nilC]];
      memNilAt = HOL`Bool`SPEC[xT,
        INSTTYPE[{mkVarType["A"] -> αAM},
          HOL`Stdlib`List`memNilThm]];
      fThm = EQMP[memNilAt, memHyp];
      dischMem = HOL`Bool`DISCH[memAt[xT, nilC],
        HOL`Bool`CONTR[mkComb[pV, xT], fThm]];
      genX = HOL`Bool`GEN[xT, dischMem];
      dischAll = HOL`Bool`DISCH[allAt[nilC], genX];
      dischAll
    ];

    indStep = Module[{yV, lLoc, ihHypT, ihHyp, allConsHyp, allConsAt,
                     allConsConj, allHyp, allLLoc, pY, dischIH,
                     genCase, memConsHyp, memConsAt, memDisj, headCase,
                     tailCase, body, dischMem, genX, dischAll, dischIHOuter},
      yV   = mkVar["yAM", αAM];
      lLoc = mkVar["lAMI", αAML];

      ihHypT = impTm[allAt[lLoc],
        mkComb[mkConst["∀", tyFun[tyFun[αAM, boolTy], boolTy]],
          mkAbs[xT, impTm[memAt[xT, lLoc], mkComb[pV, xT]]]]];
      ihHyp = ASSUME[ihHypT];

      allConsHyp = ASSUME[allAt[mkComb[mkComb[consC, yV], lLoc]]];
      allConsAt = HOL`Bool`SPEC[lLoc, HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[pV,
          INSTTYPE[{mkVarType["A"] -> αAM},
            HOL`Stdlib`List`allConsThm]]]];
      (* ⊢ ALL P (CONS y l) = P y ∧ ALL P l *)
      allConsConj = EQMP[allConsAt, allConsHyp];
      pY = HOL`Bool`CONJUNCT1[allConsConj];
      allLLoc = HOL`Bool`CONJUNCT2[allConsConj];
      (* (ALL P (CONS y l)) ⊢ P y    and    ⊢ ALL P l *)

      memConsHyp = ASSUME[memAt[xT, mkComb[mkComb[consC, yV], lLoc]]];
      memConsAt = HOL`Bool`SPEC[lLoc, HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[xT,
          INSTTYPE[{mkVarType["A"] -> αAM},
            HOL`Stdlib`List`memConsThm]]]];
      memDisj = EQMP[memConsAt, memConsHyp];

      headCase = Module[{xEqYHyp, pXEqPY, pXFromY},
        xEqYHyp = ASSUME[mkEq[xT, yV]];
        pXEqPY = HOL`Equal`APTERM[pV, xEqYHyp];
        (* (x = y) ⊢ P x = P y *)
        pXFromY = EQMP[HOL`Equal`SYM[pXEqPY], pY];
        (* (x = y, ALL P (CONS y l)) ⊢ P x *)
        pXFromY
      ];

      tailCase = Module[{memXLHyp, ihAppliedAll, ihAtX, pXFromTail},
        memXLHyp = ASSUME[memAt[xT, lLoc]];
        ihAppliedAll = HOL`Bool`MP[ihHyp, allLLoc];
        (* (IH, ALL P (CONS y l)) ⊢ ∀x. MEM x l ⇒ P x *)
        ihAtX = HOL`Bool`SPEC[xT, ihAppliedAll];
        (* ⊢ MEM x l ⇒ P x *)
        pXFromTail = HOL`Bool`MP[ihAtX, memXLHyp];
        pXFromTail
      ];

      body = HOL`Bool`DISJCASES[memDisj, headCase, tailCase];
      dischMem = HOL`Bool`DISCH[memAt[xT, mkComb[mkComb[consC, yV], lLoc]], body];
      genX = HOL`Bool`GEN[xT, dischMem];
      dischAll = HOL`Bool`DISCH[allAt[mkComb[mkComb[consC, yV], lLoc]], genX];
      dischIHOuter = HOL`Bool`DISCH[ihHypT, dischAll];
      HOL`Bool`GEN[yV, HOL`Bool`GEN[lLoc, dischIHOuter]]
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalAtL = HOL`Bool`MP[inductBeta, conjForall];
    (* (free pV) ⊢ ∀l. ALL P l ⇒ ∀x. MEM x l ⇒ P x *)
    genP = HOL`Bool`GEN[pV, finalAtL];
    genP
  ];

(* ============================================================ *)
(* foldrEqOneNilThm  (stage-3.d helper)                          *)
(*   ⊢ ∀l. ALL prime l ⇒ FOLDR * (SUC 0) l = SUC 0 ⇒ l = NIL.    *)
(*                                                              *)
(* Cases on l. NIL: trivial. CONS y l': from ALL prime (CONS y l')*)
(* extract prime y, hence SUC 0 < y. Then y * FOLDR l' = SUC 0,   *)
(* so y | SUC 0, contradicting primeNotDivOne. (Hence the CONS    *)
(* case is vacuous via CONTR.)                                    *)
(* ============================================================ *)

foldrEqOneNilThm =
  Module[{lV, allHyp, foldrEqHyp, predLam, inductSpec, inductBeta,
          baseCase, indStep, conjForall, finalAtL},
    lV = mkVar["lFE", numListTy[]];

    predLam = mkAbs[lV,
      impTm[allTm[HOL`Stdlib`Num`primeConst[], lV],
        impTm[mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV],
                   oneN[]],
              mkEq[lV, nilNumTm[]]]]];

    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{mkVarType["A"] -> numTy},
        HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];

    baseCase = Module[{allNilHyp, foldrHyp, refl, dischFold, dischAll},
      allNilHyp = ASSUME[allTm[HOL`Stdlib`Num`primeConst[], nilNumTm[]]];
      foldrHyp = ASSUME[mkEq[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], nilNumTm[]],
        oneN[]]];
      refl = REFL[nilNumTm[]];
      dischFold = HOL`Bool`DISCH[concl[foldrHyp], refl];
      dischAll = HOL`Bool`DISCH[concl[allNilHyp], dischFold];
      dischAll
    ];

    indStep = Module[{yV, lLoc, ihHypT, ihHyp, allConsHyp, foldrEqHyp,
                    allConsAt, allConsConj, primeY, foldrConsAt,
                    foldrEqDecomp, divPart, divYOne, notDivYOne, fThm,
                    dischFold, dischAll, dischIHOuter},
      yV   = mkVar["yFE", numTy];
      lLoc = mkVar["lFEI", numListTy[]];

      ihHypT = impTm[allTm[HOL`Stdlib`Num`primeConst[], lLoc],
        impTm[mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lLoc],
                   oneN[]],
              mkEq[lLoc, nilNumTm[]]]];
      ihHyp = ASSUME[ihHypT];

      allConsHyp = ASSUME[allTm[HOL`Stdlib`Num`primeConst[],
        consNumApp[yV, lLoc]]];
      foldrEqHyp = ASSUME[mkEq[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], consNumApp[yV, lLoc]],
        oneN[]]];

      allConsAt = HOL`Bool`SPEC[lLoc, HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
          INSTTYPE[{mkVarType["A"] -> numTy},
            HOL`Stdlib`List`allConsThm]]]];
      allConsConj = EQMP[allConsAt, allConsHyp];
      primeY = HOL`Bool`CONJUNCT1[allConsConj];
      (* (ALL prime (CONS y l)) ⊢ prime y *)

      foldrConsAt = HOL`Bool`SPEC[lLoc, HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
          INSTTYPE[{mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
            HOL`Stdlib`List`foldrConsThm]]]]];
      (* ⊢ FOLDR * 1 (CONS y l) = y * FOLDR * 1 l *)
      foldrEqDecomp = TRANS[HOL`Equal`SYM[foldrConsAt], foldrEqHyp];
      (* (foldrEqHyp) ⊢ y * FOLDR * 1 l = 1 *)

      (* From y * FOLDR = 1: y | 1 (witness c = FOLDR * 1 l). *)
      divPart = Module[{exC, exTm, witness},
        witness = HOL`Equal`SYM[foldrEqDecomp];
        (* (foldrEqHyp) ⊢ 1 = y * FOLDR * 1 l *)
        exTm = mkComb[
          mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[mkVar["cFE", numTy],
            mkEq[oneN[], timesN[yV, mkVar["cFE", numTy]]]]];
        exC = HOL`Bool`EXISTS[exTm,
          foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lLoc], witness];
        EQMP[HOL`Equal`SYM[unfoldDivides[yV, oneN[]]], exC]
      ];
      divYOne = divPart;
      (* (foldrEqHyp) ⊢ divides y (SUC 0) *)

      notDivYOne = HOL`Bool`MP[
        HOL`Bool`SPEC[yV, primeNotDivOneThm], primeY];
      (* (ALL prime …) ⊢ ¬(divides y (SUC 0)) *)

      fThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notDivYOne], divYOne];
      (* (…) ⊢ F *)
      dischFold = HOL`Bool`DISCH[concl[foldrEqHyp],
        HOL`Bool`CONTR[mkEq[consNumApp[yV, lLoc], nilNumTm[]], fThm]];
      dischAll = HOL`Bool`DISCH[concl[allConsHyp], dischFold];
      dischIHOuter = HOL`Bool`DISCH[ihHypT, dischAll];
      HOL`Bool`GEN[yV, HOL`Bool`GEN[lLoc, dischIHOuter]]
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalAtL = HOL`Bool`MP[inductBeta, conjForall];
    finalAtL
  ];

(* ============================================================ *)
(* primeFactorsUniqueThm  (FTA stage 3 capstone)                 *)
(*                                                              *)
(*   ⊢ ∀l1 l2. ALL prime l1 ⇒ ALL prime l2                       *)
(*           ⇒ FOLDR * (SUC 0) l1 = FOLDR * (SUC 0) l2           *)
(*           ⇒ PERM l1 l2.                                       *)
(*                                                              *)
(* List induction on l1 (predicate quantifies ∀l2 inside).        *)
(*                                                              *)
(* NIL case: FOLDR NIL = 1, so FOLDR l2 = 1; foldrEqOneNilThm     *)
(*   gives l2 = NIL; permNilThm + APTERM(PERM NIL) closes.        *)
(*                                                              *)
(* CONS x l1' case: prime x ⇒ ¬(x = 0) (primeNotZeroThm).         *)
(*   x * FOLDR l1' = FOLDR l2, so x | FOLDR l2 (witness FOLDR l1').*)
(*   primeDivFoldrTimesThm ⇒ ∃y. MEM y l2 ∧ x | y.                *)
(*   allMemImpThm + ALL prime l2 + MEM y l2 ⇒ prime y.            *)
(*   primesEqIfDividesThm ⇒ x = y, hence MEM x l2.                *)
(*   memSplitThm ⇒ ∃l2a l2b. l2 = APPEND l2a (CONS x l2b).        *)
(*   permAppendConsThm + SUBS ⇒ PERM l2 (CONS x (APPEND l2a l2b)).*)
(*   permFoldrTimesThm transports FOLDR through.                  *)
(*   multLeftCancelThm cancels x ⇒                                *)
(*     FOLDR l1' = FOLDR (APPEND l2a l2b).                        *)
(*   ALL prime l2 splits via allAppend + allCons ⇒                *)
(*     ALL prime l2a ∧ ALL prime l2b ⇒ ALL prime (APPEND l2a l2b).*)
(*   IH at (APPEND l2a l2b) ⇒ PERM l1' (APPEND l2a l2b).          *)
(*   permConsThm at x ⇒ PERM (CONS x l1') (CONS x (APPEND l2a l2b)).*)
(*   permSymThm of the permAppendCons step + permTransThm assemble*)
(*     PERM (CONS x l1') l2.                                      *)
(* ============================================================ *)


primeFactorsUniqueThm =
  Module[{αTyL, βTyL, l1V, l2V, xV, l1pV, predLam, inductSpec, inductBeta,
          baseCase, indStep, conjForall, finalAtL1,
          allPrimePred, foldrAtL,
          permNilNum, permConsNum, permSymNum, permTransNum,
          permAppendConsNum},
    αTyL = mkVarType["A"]; βTyL = mkVarType["B"];

    l1V = mkVar["l1FU", numListTy[]];
    l2V = mkVar["l2FU", numListTy[]];
    xV  = mkVar["xFU", numTy];
    l1pV = mkVar["l1pFU", numListTy[]];

    allPrimePred[lt_] := allTm[HOL`Stdlib`Num`primeConst[], lt];
    foldrAtL[lt_] := foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lt];

    (* Num-instantiated PERM theorems. *)
    permNilNum         = INSTTYPE[{αPerm -> numTy}, permNilThm];
    permConsNum        = INSTTYPE[{αPerm -> numTy}, permConsThm];
    permSymNum         = INSTTYPE[{αPerm -> numTy}, permSymThm];
    permTransNum       = INSTTYPE[{αPerm -> numTy}, permTransThm];
    permAppendConsNum  = INSTTYPE[{αPerm -> numTy}, permAppendConsThm];

    (* predLam[l1] = ∀l2. ALL prime l1 ⇒ ALL prime l2
                          ⇒ FOLDR * 1 l1 = FOLDR * 1 l2
                          ⇒ PERM l1 l2 *)
    predLam = mkAbs[l1V,
      mkComb[mkConst["∀", tyFun[tyFun[numListTy[], boolTy], boolTy]],
        mkAbs[l2V,
          impTm[allPrimePred[l1V],
            impTm[allPrimePred[l2V],
              impTm[mkEq[foldrAtL[l1V], foldrAtL[l2V]],
                permNumTm[l1V, l2V]]]]]]];

    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{mkVarType["A"] -> numTy},
        HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];

    (* ============= NIL case ============= *)
    baseCase = Module[{l2Loc, allNilHyp, allL2Hyp, foldrEqHyp,
                       foldrNilAt, foldrL2EqOne, l2EqNil, permNilNil,
                       permLifted, dischFold, dischAllL2, dischAllNil,
                       genL2},
      l2Loc = l2V;
      allNilHyp = ASSUME[allPrimePred[nilNumTm[]]];
      allL2Hyp = ASSUME[allPrimePred[l2Loc]];
      foldrEqHyp = ASSUME[mkEq[foldrAtL[nilNumTm[]], foldrAtL[l2Loc]]];

      foldrNilAt = HOL`Bool`SPEC[oneN[],
        HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
          INSTTYPE[{αTyL -> numTy, βTyL -> numTy},
            HOL`Stdlib`List`foldrNilThm]]];
      (* ⊢ FOLDR * 1 NIL = SUC 0 *)
      foldrL2EqOne = TRANS[HOL`Equal`SYM[foldrEqHyp], foldrNilAt];
      (* (foldrEqHyp) ⊢ FOLDR * 1 l2 = SUC 0 *)

      l2EqNil = HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[l2Loc, foldrEqOneNilThm], allL2Hyp], foldrL2EqOne];
      (* (…) ⊢ l2 = NIL *)

      permNilNil = permNilNum;
      (* ⊢ PERM NIL NIL (at num) *)
      permLifted = EQMP[
        HOL`Equal`APTERM[mkComb[permNumConst[], nilNumTm[]],
          HOL`Equal`SYM[l2EqNil]],
        permNilNil];
      (* (…) ⊢ PERM NIL l2 *)

      dischFold = HOL`Bool`DISCH[concl[foldrEqHyp], permLifted];
      dischAllL2 = HOL`Bool`DISCH[concl[allL2Hyp], dischFold];
      dischAllNil = HOL`Bool`DISCH[concl[allNilHyp], dischAllL2];
      genL2 = HOL`Bool`GEN[l2Loc, dischAllNil];
      genL2
    ];

    (* ============= CONS x l1' case ============= *)
    indStep = Module[{l1pLoc, xLoc, ihHypT, ihHyp, ihAtl2, l2Loc,
                      allConsXl1pHyp, allL2Hyp, foldrEqHyp,
                      allConsXl1pUnf, primeXThm, allPrimeL1pThm,
                      xNotZero, foldrConsXl1pAt, foldrAtCons,
                      xTimesFoldrL1pEqFoldrL2,
                      divXFoldrL2, primeDivFoldrAt, primeDivFoldrAtL2,
                      exYBody, exYHyp, yV, yMemDivBodyTm, yMemDivHyp,
                      memYL2, divXY, primeY,
                      xEqY, memXL2,
                      memSplitAt, memSplitMP, l2aV, l2bV,
                      l2aExBodyTm, l2aExHyp, l2EqSplit,
                      permAppendConsAt, permL2AndExpanded, permL2Form,
                      permFoldrAt, foldrL2EqXTimesAppend,
                      foldrEqFromCons,
                      eqViaConcrete, allL2InAppendForm,
                      allAppendL2aXl2b, allConjL2aRest, allL2a,
                      allConsXl2bConj, primeXFromL2, allPrimeL2b,
                      allAppendL2aL2b, allAppendInst,
                      foldrCancelEq, foldrL1pEqFoldrAppend,
                      ihApplied, permL1pAppend, permConsXL1pXAppend,
                      permXAppendL2, permConsXl1pL2,
                      dischFoldFinal, dischAllL2Final, dischAllConsFinal,
                      genL2Final, dischIH, outerGens,
                      memYBody, memYAtCons, eqFromMemY,
                      memXL2Subst},
      l1pLoc = l1pV;
      xLoc   = xV;
      l2Loc  = l2V;

      (* IH at l1pLoc *)
      ihHypT = mkComb[mkConst["∀", tyFun[tyFun[numListTy[], boolTy], boolTy]],
        mkAbs[l2V,
          impTm[allPrimePred[l1pLoc],
            impTm[allPrimePred[l2V],
              impTm[mkEq[foldrAtL[l1pLoc], foldrAtL[l2V]],
                permNumTm[l1pLoc, l2V]]]]]];
      ihHyp = ASSUME[ihHypT];

      allConsXl1pHyp = ASSUME[allPrimePred[consNumApp[xLoc, l1pLoc]]];
      allL2Hyp = ASSUME[allPrimePred[l2Loc]];
      foldrEqHyp = ASSUME[mkEq[
        foldrAtL[consNumApp[xLoc, l1pLoc]], foldrAtL[l2Loc]]];

      (* prime x ∧ ALL prime l1' from ALL prime (CONS x l1') *)
      allConsXl1pUnf = EQMP[
        HOL`Bool`SPEC[l1pLoc, HOL`Bool`SPEC[xLoc,
          HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
            INSTTYPE[{αTyL -> numTy}, HOL`Stdlib`List`allConsThm]]]],
        allConsXl1pHyp];
      primeXThm     = HOL`Bool`CONJUNCT1[allConsXl1pUnf];
      allPrimeL1pThm = HOL`Bool`CONJUNCT2[allConsXl1pUnf];

      xNotZero = HOL`Bool`MP[
        HOL`Bool`SPEC[xLoc, primeNotZeroThm], primeXThm];
      (* (…) ⊢ ¬(x = 0) *)

      (* FOLDR (CONS x l1') = x * FOLDR l1' *)
      foldrConsXl1pAt = HOL`Bool`SPEC[l1pLoc, HOL`Bool`SPEC[xLoc,
        HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
          INSTTYPE[{αTyL -> numTy, βTyL -> numTy},
            HOL`Stdlib`List`foldrConsThm]]]]];

      xTimesFoldrL1pEqFoldrL2 = TRANS[HOL`Equal`SYM[foldrConsXl1pAt],
        foldrEqHyp];
      (* (foldrEqHyp) ⊢ x * FOLDR l1' = FOLDR l2 *)

      (* x | FOLDR l2: ∃c. FOLDR l2 = x * c with c = FOLDR l1'. *)
      divXFoldrL2 = Module[{cVlocal, exTm, witnessEq, exThm},
        cVlocal = mkVar["cDFL", numTy];
        exTm = mkComb[mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[cVlocal, mkEq[foldrAtL[l2Loc],
            timesN[xLoc, cVlocal]]]];
        witnessEq = HOL`Equal`SYM[xTimesFoldrL1pEqFoldrL2];
        (* (…) ⊢ FOLDR l2 = x * FOLDR l1' *)
        exThm = HOL`Bool`EXISTS[exTm, foldrAtL[l1pLoc], witnessEq];
        EQMP[HOL`Equal`SYM[unfoldDivides[xLoc, foldrAtL[l2Loc]]], exThm]
      ];
      (* (foldrEqHyp) ⊢ divides x (FOLDR l2) *)

      (* primeDivFoldrTimesThm: prime x ⇒ ∀l. divides x (FOLDR l) ⇒
                                ∃y. MEM y l ∧ divides x y. *)
      primeDivFoldrAt = HOL`Bool`MP[
        HOL`Bool`SPEC[xLoc, primeDivFoldrTimesThm], primeXThm];
      primeDivFoldrAtL2 = HOL`Bool`MP[
        HOL`Bool`SPEC[l2Loc, primeDivFoldrAt], divXFoldrL2];
      (* (…) ⊢ ∃y. MEM y l2 ∧ divides x y *)

      yV = mkVar["yFU", numTy];
      yMemDivBodyTm = andTm[memNumTm[yV, l2Loc], dividesN[xLoc, yV]];
      yMemDivHyp = ASSUME[yMemDivBodyTm];
      memYL2 = HOL`Bool`CONJUNCT1[yMemDivHyp];
      divXY  = HOL`Bool`CONJUNCT2[yMemDivHyp];

      (* prime y from allMemImp at p=prime *)
      primeY = Module[{allMemAt, allMemAtPrimeL2, ihAt, mpFirst, mpSecond},
        allMemAt = HOL`Bool`SPEC[l2Loc, HOL`Bool`SPEC[
          HOL`Stdlib`Num`primeConst[],
          INSTTYPE[{mkVarType["A"] -> numTy}, allMemImpThm]]];
        (* ⊢ ALL prime l2 ⇒ ∀x. MEM x l2 ⇒ prime x *)
        mpFirst = HOL`Bool`MP[allMemAt, allL2Hyp];
        mpSecond = HOL`Bool`MP[HOL`Bool`SPEC[yV, mpFirst], memYL2];
        mpSecond
      ];
      (* (…) ⊢ prime y *)

      xEqY = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[yV, HOL`Bool`SPEC[xLoc, primesEqIfDividesThm]],
        primeXThm], primeY], divXY];
      (* (…) ⊢ x = y *)

      (* MEM x l2 via SUBS x = y ↔ y = x in MEM y l2 *)
      memXL2 = HOL`Drule`SUBS[{HOL`Equal`SYM[xEqY]}, memYL2];
      (* (…) ⊢ MEM x l2 *)

      (* memSplitThm: MEM x l2 ⇒ ∃l1 l2. l2 = APPEND l1 (CONS x l2) *)
      memSplitMP = HOL`Bool`MP[
        HOL`Bool`SPEC[l2Loc, HOL`Bool`SPEC[xLoc,
          INSTTYPE[{mkVarType["A"] -> numTy}, memSplitThm]]], memXL2];
      (* (…) ⊢ ∃l1' l2'. l2 = APPEND l1' (CONS x l2') *)

      l2aV = mkVar["l2aFU", numListTy[]];
      l2bV = mkVar["l2bFU", numListTy[]];

      l2aExBodyTm = mkEq[l2Loc,
        appendNumTm[l2aV, consNumApp[xLoc, l2bV]]];

      (* The huge body that uses l2a, l2b to finish. *)
      Module[{innerBody},
        innerBody = Module[{l2EqSplitHyp,
                            permAppendConsAtV, permL2InCons,
                            permFoldrAtV, foldrL2EqXAppend,
                            xTimesFoldrL1pEqXTimesAppend,
                            foldrL1pEqAppend,
                            allL2InAppForm, allAppendAt,
                            allAppendConj, allL2a, allConsRest,
                            allConsAtV, allConsConj, allL2b,
                            allAppendL2aL2bThm,
                            ihAt, ihAllPrimeL1p, ihAllPrimeApp,
                            ihFoldrEq, permL1pAppendL2,
                            permConsXCong, permApendConsBacks,
                            permSymTrans, finalPerm,
                            outerExHyp},
          l2EqSplitHyp = ASSUME[l2aExBodyTm];

          (* permAppendCons: PERM (APPEND l2a (CONS x l2b))
                                  (CONS x (APPEND l2a l2b)) *)
          permAppendConsAtV = HOL`Bool`SPEC[l2bV,
            HOL`Bool`SPEC[l2aV,
              HOL`Bool`SPEC[xLoc, permAppendConsNum]]];

          (* Substitute l2 = APPEND l2a (CONS x l2b) into above
             to get PERM l2 (CONS x (APPEND l2a l2b)). *)
          permL2InCons = HOL`Drule`SUBS[
            {HOL`Equal`SYM[l2EqSplitHyp]}, permAppendConsAtV];

          (* permFoldrTimes: PERM a b ⇒ FOLDR * 1 a = FOLDR * 1 b *)
          permFoldrAtV = HOL`Bool`MP[
            HOL`Bool`SPEC[mkComb[mkComb[consNumConst[], xLoc],
              appendNumTm[l2aV, l2bV]],
              HOL`Bool`SPEC[l2Loc, permFoldrTimesThm]],
            permL2InCons];
          (* (…) ⊢ FOLDR l2 = FOLDR (CONS x (APPEND l2a l2b)) *)

          (* FOLDR (CONS x (APPEND l2a l2b)) = x * FOLDR (APPEND l2a l2b) *)
          foldrAtCons = HOL`Bool`SPEC[appendNumTm[l2aV, l2bV],
            HOL`Bool`SPEC[xLoc,
              HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[HOL`Stdlib`Num`timesConst[],
                INSTTYPE[{αTyL -> numTy, βTyL -> numTy},
                  HOL`Stdlib`List`foldrConsThm]]]]];

          foldrL2EqXAppend = TRANS[permFoldrAtV, foldrAtCons];
          (* (…) ⊢ FOLDR l2 = x * FOLDR (APPEND l2a l2b) *)

          xTimesFoldrL1pEqXTimesAppend = TRANS[
            xTimesFoldrL1pEqFoldrL2, foldrL2EqXAppend];
          (* (…) ⊢ x * FOLDR l1' = x * FOLDR (APPEND l2a l2b) *)

          (* multLeftCancelThm: ¬(x=0) ⇒ ∀a b. x*a = x*b ⇒ a = b *)
          foldrL1pEqAppend = HOL`Bool`MP[
            HOL`Bool`SPEC[foldrAtL[appendNumTm[l2aV, l2bV]],
              HOL`Bool`SPEC[foldrAtL[l1pLoc],
                HOL`Bool`MP[HOL`Bool`SPEC[xLoc, multLeftCancelThm],
                  xNotZero]]],
            xTimesFoldrL1pEqXTimesAppend];
          (* (…) ⊢ FOLDR l1' = FOLDR (APPEND l2a l2b) *)

          (* ALL prime l2 → ALL prime (APPEND l2a l2b) *)
          allL2InAppForm = HOL`Drule`SUBS[{l2EqSplitHyp}, allL2Hyp];
          (* (…) ⊢ ALL prime (APPEND l2a (CONS x l2b)) *)
          allAppendAt = HOL`Bool`SPEC[consNumApp[xLoc, l2bV],
            HOL`Bool`SPEC[l2aV, HOL`Bool`SPEC[
              HOL`Stdlib`Num`primeConst[],
              INSTTYPE[{mkVarType["A"] -> numTy},
                HOL`Stdlib`List`allAppendThm]]]];
          (* ⊢ ALL prime (APPEND l2a (CONS x l2b))
                = ALL prime l2a ∧ ALL prime (CONS x l2b) *)
          allAppendConj = EQMP[allAppendAt, allL2InAppForm];
          allL2a = HOL`Bool`CONJUNCT1[allAppendConj];
          allConsRest = HOL`Bool`CONJUNCT2[allAppendConj];
          (* (…) ⊢ ALL prime (CONS x l2b) *)
          allConsAtV = HOL`Bool`SPEC[l2bV, HOL`Bool`SPEC[xLoc,
            HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
              INSTTYPE[{mkVarType["A"] -> numTy},
                HOL`Stdlib`List`allConsThm]]]];
          allConsConj = EQMP[allConsAtV, allConsRest];
          allL2b = HOL`Bool`CONJUNCT2[allConsConj];

          (* Build ALL prime (APPEND l2a l2b) via SYM of allAppend at l2b *)
          allAppendL2aL2bThm = Module[{appAtV2, conjV},
            appAtV2 = HOL`Bool`SPEC[l2bV, HOL`Bool`SPEC[l2aV,
              HOL`Bool`SPEC[HOL`Stdlib`Num`primeConst[],
                INSTTYPE[{mkVarType["A"] -> numTy},
                  HOL`Stdlib`List`allAppendThm]]]];
            (* ⊢ ALL prime (APPEND l2a l2b)
                 = ALL prime l2a ∧ ALL prime l2b *)
            conjV = HOL`Bool`CONJ[allL2a, allL2b];
            EQMP[HOL`Equal`SYM[appAtV2], conjV]
          ];
          (* (…) ⊢ ALL prime (APPEND l2a l2b) *)

          (* Apply IH at l2 := APPEND l2a l2b *)
          ihAt = HOL`Bool`SPEC[appendNumTm[l2aV, l2bV], ihHyp];
          (* ⊢ ALL prime l1' ⇒ ALL prime (APPEND l2a l2b)
                ⇒ FOLDR l1' = FOLDR (APPEND l2a l2b) ⇒ PERM l1' (APPEND l2a l2b) *)
          permL1pAppendL2 = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`MP[ihAt,
            allPrimeL1pThm], allAppendL2aL2bThm], foldrL1pEqAppend];
          (* (…) ⊢ PERM l1' (APPEND l2a l2b) *)

          (* permCons at x: PERM (CONS x l1') (CONS x (APPEND l2a l2b)) *)
          permConsXCong = HOL`Bool`MP[
            HOL`Bool`SPEC[appendNumTm[l2aV, l2bV],
              HOL`Bool`SPEC[l1pLoc,
                HOL`Bool`SPEC[xLoc, permConsNum]]],
            permL1pAppendL2];
          (* (…) ⊢ PERM (CONS x l1') (CONS x (APPEND l2a l2b)) *)

          (* PERM l2 (CONS x (APPEND l2a l2b)) ⇒
             PERM (CONS x (APPEND l2a l2b)) l2 via permSym *)
          (* permSymNum: ∀l1 l2. PERM l1 l2 ⇒ PERM l2 l1. Need to apply  *)
          (* with l1 = l2Loc, l2 = CONS x (APPEND l2a l2b). Innermost   *)
          (* SPEC sets the outer ∀l1 → l2Loc.                            *)
          permSymTrans = HOL`Bool`MP[
            HOL`Bool`SPEC[
              mkComb[mkComb[consNumConst[], xLoc],
                appendNumTm[l2aV, l2bV]],
              HOL`Bool`SPEC[l2Loc, permSymNum]],
            permL2InCons];
          (* (…) ⊢ PERM (CONS x (APPEND l2a l2b)) l2 *)

          (* permTrans: PERM (CONS x l1') l2 *)
          finalPerm = HOL`Bool`MP[HOL`Bool`MP[
            HOL`Bool`SPEC[l2Loc, HOL`Bool`SPEC[
              mkComb[mkComb[consNumConst[], xLoc],
                appendNumTm[l2aV, l2bV]],
              HOL`Bool`SPEC[consNumApp[xLoc, l1pLoc], permTransNum]]],
            permConsXCong], permSymTrans];
          (* (…) ⊢ PERM (CONS x l1') l2 *)

          finalPerm
        ];

        (* CHOOSE l2bV from the inner ∃l2'. l2 = APPEND l2a (CONS x l2') *)
        Module[{outerL2bExBodyTm, l2bExHyp, chosenL2b, chosenL2a},
          outerL2bExBodyTm = existsListTm[l2bV, l2aExBodyTm];
          l2bExHyp = ASSUME[outerL2bExBodyTm];
          chosenL2b = HOL`Bool`CHOOSE[l2bV, l2bExHyp, innerBody];
          chosenL2a = HOL`Bool`CHOOSE[l2aV, memSplitMP, chosenL2b];
          (* (…) ⊢ PERM (CONS x l1') l2 *)

          (* Now CHOOSE yV from the ∃y. MEM y l2 ∧ divides x y *)
          Module[{chosenY, dischFoldFinal, dischAllL2Final,
                  dischAllConsFinal, genL2Final, dischIH, outerGens},
            chosenY = HOL`Bool`CHOOSE[yV, primeDivFoldrAtL2, chosenL2a];
            (* (foldrEqHyp, allConsXl1p, allL2, IH) ⊢ PERM (CONS x l1') l2 *)

            dischFoldFinal = HOL`Bool`DISCH[concl[foldrEqHyp], chosenY];
            dischAllL2Final = HOL`Bool`DISCH[concl[allL2Hyp], dischFoldFinal];
            dischAllConsFinal = HOL`Bool`DISCH[
              concl[allConsXl1pHyp], dischAllL2Final];
            genL2Final = HOL`Bool`GEN[l2Loc, dischAllConsFinal];
            dischIH = HOL`Bool`DISCH[ihHypT, genL2Final];
            outerGens = HOL`Bool`GEN[xLoc, HOL`Bool`GEN[l1pLoc, dischIH]];
            outerGens
          ]
        ]
      ]
    ];

    conjForall = HOL`Bool`CONJ[baseCase, indStep];
    finalAtL1 = HOL`Bool`MP[inductBeta, conjForall];
    (* ⊢ ∀l1. ∀l2. ALL prime l1 ⇒ ALL prime l2
                  ⇒ FOLDR * 1 l1 = FOLDR * 1 l2 ⇒ PERM l1 l2 *)
    finalAtL1
  ];

End[];
EndPackage[];
