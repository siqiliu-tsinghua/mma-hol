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

(* multEqZeroThm (m*n=0 ⇒ m=0∨n=0) now lives in Num.wl — see
   HOL`Stdlib`Num`multEqZeroThm; used below in multLeftCancelThm. *)
multLeftCancelThm::usage = "multLeftCancelThm — ⊢ ∀x. ¬(x = 0) ⇒ ∀a b. x * a = x * b ⇒ a = b. Left multiplicative cancellation in ℕ. (FTA stage 3.d helper.)";

(* gcd / divisibility / coprime number theory migrated from Rat.wl (2026-06). *)
dividesZeroImpZeroThm::usage = "dividesZeroImpZeroThm — ⊢ ∀n. divides 0 n ⇒ n = 0.";
dividesOneThm::usage         = "dividesOneThm — ⊢ ∀d. divides d (SUC 0) ⇒ d = SUC 0.";
gcdOneRightThm::usage        = "gcdOneRightThm — ⊢ ∀a. gcd a (SUC 0) = SUC 0.";
dividesMultBothLeftThm::usage = "dividesMultBothLeftThm — ⊢ ∀g h x. divides h x ⇒ divides (g * h) (g * x).";
gcdNonzeroFromRightThm::usage = "gcdNonzeroFromRightThm — ⊢ ∀a b. ¬ (b = 0) ⇒ ¬ (gcd a b = 0).";
coprimeReducedThm::usage = "coprimeReducedThm — ⊢ ∀a b. ¬ (gcd a b = 0) ⇒ gcd (exDiv a (gcd a b)) (exDiv b (gcd a b)) = SUC 0. Dividing both arguments by their gcd makes them coprime.";
dividesAntisymThm::usage = "dividesAntisymThm — ⊢ ∀a b. divides a b ⇒ divides b a ⇒ a = b.";
gcdZeroRightThm::usage   = "gcdZeroRightThm — ⊢ ∀a. gcd a 0 = a.";
gcdRecThm::usage         = "gcdRecThm — ⊢ ∀a b. ¬ (b = 0) ⇒ gcd a b = gcd b (a MOD b). Euclidean recurrence.";
bezoutNatThm::usage      = "bezoutNatThm — ⊢ ∀a b. ∃x y. a * x = b * y + gcd a b ∨ b * y = a * x + gcd a b. ℕ Bezout (disjunctive, subtraction-free).";
coprimeDividesProductThm::usage = "coprimeDividesProductThm — ⊢ ∀a b c. gcd a b = SUC 0 ⇒ divides a (b * c) ⇒ divides a c. ℕ Gauss / Euclid coprime-product lemma.";
gcdCommThm::usage = "gcdCommThm — ⊢ ∀a b. gcd a b = gcd b a.";
gcdZeroLeftThm::usage = "gcdZeroLeftThm — ⊢ ∀m. gcd 0 m = m.";
exDivSelfThm::usage = "exDivSelfThm — ⊢ ∀m. ¬ (m = 0) ⇒ exDiv m m = SUC 0.";
gcdSelfThm::usage = "gcdSelfThm — ⊢ ∀m. gcd m m = m.";
primeNotZeroThm::usage = "primeNotZeroThm — ⊢ ∀p. prime p ⇒ ¬(p = 0). (FTA stage 3.d helper.)";
primesEqIfDividesThm::usage = "primesEqIfDividesThm — ⊢ ∀p q. prime p ⇒ prime q ⇒ divides p q ⇒ p = q. Two primes are equal whenever one divides the other. (FTA stage 3.d helper.)";
allMemImpThm::usage = "allMemImpThm — ⊢ ∀P l. ALL P l ⇒ ∀x. MEM x l ⇒ P x. ALL is universally quantified MEM. (FTA stage 3.d helper.)";
foldrEqOneNilThm::usage = "foldrEqOneNilThm — ⊢ ∀l. ALL prime l ⇒ FOLDR * (SUC 0) l = SUC 0 ⇒ l = NIL. A product of primes equals 1 only for the empty list. (FTA stage 3.d helper.)";
primeFactorsUniqueThm::usage = "primeFactorsUniqueThm — ⊢ ∀l1 l2. ALL prime l1 ⇒ ALL prime l2 ⇒ FOLDR * (SUC 0) l1 = FOLDR * (SUC 0) l2 ⇒ PERM l1 l2. Uniqueness of prime factorization modulo permutation. FTA stage 3 capstone.";

(* gcd / prime / Euclid's lemma — migrated from Num.wl (2026-06). *)
gcdExistsThm::usage      = "gcdExistsThm — ⊢ ∀a b. ∃d. divides d a ∧ divides d b ∧ ∀e. (divides e a ∧ divides e b) ⇒ divides e d.";
gcdConst::usage          = "gcdConst[] — gcd : num → num → num. Greatest common divisor via Hilbert ε on the universal property; constructively exists by Euclid (gcdExistsThm).";
gcdDefThm::usage         = "gcdDefThm — ⊢ gcd = (λa b. ε d. divides d a ∧ divides d b ∧ ∀e. (divides e a ∧ divides e b) ⇒ divides e d).";
gcdSpecThm::usage        = "gcdSpecThm — ⊢ ∀a b. divides (gcd a b) a ∧ divides (gcd a b) b ∧ ∀e. (divides e a ∧ divides e b) ⇒ divides e (gcd a b).";
gcdDividesLeftThm::usage = "gcdDividesLeftThm — ⊢ ∀a b. divides (gcd a b) a.";
gcdDividesRightThm::usage= "gcdDividesRightThm — ⊢ ∀a b. divides (gcd a b) b.";
gcdUniversalThm::usage   = "gcdUniversalThm — ⊢ ∀a b e. divides e a ∧ divides e b ⇒ divides e (gcd a b).";
primeConst::usage        = "primeConst[] — prime : num → bool. prime p ⇔ SUC 0 < p ∧ ∀d. d divides p ⇒ d = SUC 0 ∨ d = p.";
primeDefThm::usage       = "primeDefThm — ⊢ prime = (λp. SUC 0 < p ∧ ∀d. divides d p ⇒ d = SUC 0 ∨ d = p).";
euclidLemmaThm::usage    = "euclidLemmaThm — ⊢ ∀p a b. prime p ⇒ divides p (a * b) ⇒ divides p a ∨ divides p b.";

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
primeN[p_] := mkComb[primeConst[], p];

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
(* gcd / prime / Euclid's lemma — migrated from Num.wl (2026-06) *)
(* per the "heavy divisibility theory lives in FTA" boundary.    *)
(* gcd is defined here (Hilbert-ε on its universal property),    *)
(* prime here, and Euclid's lemma here; only Rat (which imports  *)
(* FTA) and FTA's own factorization code consume them. The alias *)
(* block bridges the migrated proofs' Num term-builder vocab.    *)
(* ============================================================ *)

selectC[ty_]  := mkConst["@", tyFun[tyFun[ty, boolTy], ty]];
existsC[ty_]  := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];
forallC[ty_]  := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
notC[]        := mkConst["¬", tyFun[boolTy, boolTy]];
dividesTm[a_, b_] := dividesN[a, b];
timesTm[a_, b_]   := timesN[a, b];
leqTm[a_, b_]     := leqN[a, b];
ltTm[a_, b_]      := ltN[a, b];
divTm[a_, b_]     := mkComb[mkComb[divConst[], a], b];
modTm[a_, b_]     := mkComb[mkComb[modConst[], a], b];

(* ============================================================ *)
(* M7-3-o: gcd                                                  *)
(*                                                              *)
(* Approach: characterize gcd by its universal property among   *)
(* the divisibility preorder, then define via Hilbert ε.        *)
(* Existence (Euclid) drives strong induction on b.             *)
(* ============================================================ *)

(* gcdExistsThm                                                 *)
(*   ⊢ ∀a b. ∃d. divides d a ∧ divides d b ∧                    *)
(*               ∀e. (divides e a ∧ divides e b) ⇒ divides e d  *)
(*                                                              *)
(* Strong induction on b with predicate                          *)
(*   P b = ∀a. ∃d. divides d a ∧ divides d b ∧ universal.        *)
(* Case b = 0: witness d = a. divides a a (refl), divides a 0    *)
(* (zero); universal collapses to CONJUNCT1 (e | a from e|a∧e|0). *)
(* Case b = SUC b': bNotZero from sucNotZero, divisionPairThm    *)
(* gives a = b*q + r ∧ r < b. SIH at r and a'=b yields ∃d.       *)
(* divides d b ∧ divides d r ∧ ∀e. (e|b∧e|r)⇒e|d. Witness same d: *)
(*   d|a: d|b → d|b*q (dividesMultRight) → d|(b*q + r) (add) →    *)
(*        d|a (rewrite via a = b*q + r).                          *)
(*   d|b: directly from SIH.                                      *)
(*   ∀e. e|a∧e|b ⇒ e|d: e|b → e|b*q; e|a → e|(b*q+r); apply       *)
(*        dividesAddRight ⇒ e|r; then SIH's universal at e.       *)
(* ============================================================ *)

gcdExistsThm =
  Module[{aV, bV, dV, eV, kV, npV,
          gcdPredAt, gcdExistsAt, innerPredAt, inductionLam,
          sihTm, sihHyp,
          casesAtB, caseZeroB, caseSucB,
          merged, mpStrong, specBA, genB, genA,
          stepBody, abDiv, abMod},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    dV = mkVar["d", numTy];
    eV = mkVar["e", numTy];
    kV = mkVar["k", numTy];
    npV = mkVar["b'", numTy];
    abDiv = divTm[aV, bV];   (* a DIV b *)
    abMod = modTm[aV, bV];   (* a MOD b *)

    gcdPredAt[aTm_, bTm_, dTm_] := andTm[
      dividesTm[dTm, aTm],
      andTm[
        dividesTm[dTm, bTm],
        mkComb[forallC[numTy], mkAbs[eV, impTm[
          andTm[dividesTm[eV, aTm], dividesTm[eV, bTm]],
          dividesTm[eV, dTm]]]]]];

    gcdExistsAt[aTm_, bTm_] := mkComb[existsC[numTy],
      mkAbs[dV, gcdPredAt[aTm, bTm, dV]]];

    innerPredAt[bTm_] := mkComb[forallC[numTy],
      mkAbs[aV, gcdExistsAt[aV, bTm]]];

    inductionLam = mkAbs[bV, innerPredAt[bV]];

    sihTm = mkComb[forallC[numTy], mkAbs[kV, impTm[
      ltTm[kV, bV], innerPredAt[kV]]]];
    sihHyp = ASSUME[sihTm];
    (* sih: ⊢ ∀k. k < b ⇒ ∀a. ∃d. … *)

    casesAtB = HOL`Bool`SPEC[bV, numCasesThm];
    (* ⊢ b = 0 ∨ ∃b'. b = SUC b' *)

    (* --- Case A: b = 0. Witness d = a. --- *)
    caseZeroB = Module[{bEqZeroTm, bEqZeroHyp,
                        divAa, divA0, divDbEq, divAb,
                        eAndHypTm, eAndHyp, divEa, dischE, universalForb0,
                        predAtA, existsAtA},
      bEqZeroTm = mkEq[bV, zeroConst[]];
      bEqZeroHyp = ASSUME[bEqZeroTm];

      divAa = HOL`Bool`SPEC[aV, dividesReflThm];
      divA0 = HOL`Bool`SPEC[aV, dividesZeroThm];
      divDbEq = HOL`Equal`APTERM[mkComb[dividesConst[], aV],
                                  HOL`Equal`SYM[bEqZeroHyp]];
      (* (b=0) ⊢ divides a 0 = divides a b *)
      divAb = EQMP[divDbEq, divA0];
      (* (b=0) ⊢ divides a b *)

      eAndHypTm = andTm[dividesTm[eV, aV], dividesTm[eV, bV]];
      eAndHyp = ASSUME[eAndHypTm];
      divEa = HOL`Bool`CONJUNCT1[eAndHyp];
      (* (e|a ∧ e|b) ⊢ divides e a *)
      dischE = HOL`Bool`DISCH[eAndHypTm, divEa];
      universalForb0 = HOL`Bool`GEN[eV, dischE];
      (* ⊢ ∀e. (e|a ∧ e|b) ⇒ e|a *)

      predAtA = HOL`Bool`CONJ[divAa, HOL`Bool`CONJ[divAb, universalForb0]];
      (* (b=0) ⊢ gcdPredAt[a, b, a] *)
      existsAtA = HOL`Bool`EXISTS[gcdExistsAt[aV, bV], aV, predAtA];
      (* (b=0) ⊢ gcdExistsAt[a, b] *)
      existsAtA
    ];

    (* --- Case B: ∃b'. b = SUC b'. Apply Euclid step via SIH. --- *)
    caseSucB = Module[{exBpTm, exBpHyp, bEqSucTm, bEqSucHyp,
                       bEqZeroAlt, bEqZeroAltHyp, contradEq, sucNotZeroAtBp,
                       contradF, bNotZero,
                       divPairAt, divEq, modLtB,
                       sihAtR, sihAtRMpd, existsAtBR,
                       hypTripTm, hypTripHyp, divDb, divDrAndUniv,
                       divDr, univDbr,
                       divDbq, divDaProdEq, divDaProd, divDa,
                       eAndHypTm, eAndHyp, divEa, divEb,
                       divEbq, divEaToBqrEq, divEbqr,
                       divEr, hypEbAndEr, divEd,
                       dischE, genE,
                       predAtD, existsAtD,
                       chooseDStep, chooseBpStep},
      exBpTm = mkComb[existsC[numTy],
        mkAbs[npV, mkEq[bV, mkComb[sucConst[], npV]]]];
      exBpHyp = ASSUME[exBpTm];
      bEqSucTm = mkEq[bV, mkComb[sucConst[], npV]];
      bEqSucHyp = ASSUME[bEqSucTm];

      (* bNotZero: from b = SUC b' and sucNotZero. *)
      bEqZeroAlt = mkEq[bV, zeroConst[]];
      bEqZeroAltHyp = ASSUME[bEqZeroAlt];
      contradEq = TRANS[HOL`Equal`SYM[bEqSucHyp], bEqZeroAltHyp];
      (* (b=SUC b', b=0) ⊢ SUC b' = 0 *)
      sucNotZeroAtBp = HOL`Bool`SPEC[npV, sucNotZeroThm];
      contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[sucNotZeroAtBp], contradEq];
      bNotZero = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[bEqZeroAlt, contradF]];
      (* (b=SUC b') ⊢ ¬ (b = 0) *)

      divPairAt = HOL`Bool`MP[
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, divisionPairThm]],
        bNotZero];
      (* (b=SUC b') ⊢ a = b*(a DIV b) + (a MOD b) ∧ (a MOD b) < b *)
      divEq = HOL`Bool`CONJUNCT1[divPairAt];
      modLtB = HOL`Bool`CONJUNCT2[divPairAt];

      sihAtR = HOL`Bool`SPEC[abMod, sihHyp];
      sihAtRMpd = HOL`Bool`MP[sihAtR, modLtB];
      (* (sih, b=SUC b') ⊢ ∀a'. ∃d. divides d a' ∧ divides d r ∧
                                    ∀e. (e|a' ∧ e|r) ⇒ e|d *)
      existsAtBR = HOL`Bool`SPEC[bV, sihAtRMpd];
      (* (sih, b=SUC b') ⊢ ∃d. divides d b ∧ divides d r ∧
                              ∀e. (e|b ∧ e|r) ⇒ e|d *)

      hypTripTm = andTm[
        dividesTm[dV, bV],
        andTm[
          dividesTm[dV, abMod],
          mkComb[forallC[numTy], mkAbs[eV, impTm[
            andTm[dividesTm[eV, bV], dividesTm[eV, abMod]],
            dividesTm[eV, dV]]]]]];
      hypTripHyp = ASSUME[hypTripTm];
      divDb = HOL`Bool`CONJUNCT1[hypTripHyp];
      divDrAndUniv = HOL`Bool`CONJUNCT2[hypTripHyp];
      divDr = HOL`Bool`CONJUNCT1[divDrAndUniv];
      univDbr = HOL`Bool`CONJUNCT2[divDrAndUniv];

      (* d | a *)
      divDbq = HOL`Bool`MP[
        HOL`Bool`SPEC[abDiv,
          HOL`Bool`SPEC[bV,
            HOL`Bool`SPEC[dV, dividesMultRightThm]]],
        divDb];
      (* (hyp) ⊢ divides d (b * (a DIV b)) *)
      divDaProd = HOL`Bool`MP[
        HOL`Bool`MP[
          HOL`Bool`SPEC[abMod,
            HOL`Bool`SPEC[timesTm[bV, abDiv],
              HOL`Bool`SPEC[dV, dividesAddThm]]],
          divDbq],
        divDr];
      (* (hyp) ⊢ divides d (b*(a DIV b) + (a MOD b)) *)
      divDaProdEq = HOL`Equal`APTERM[mkComb[dividesConst[], dV],
                                       HOL`Equal`SYM[divEq]];
      (* (b=SUC b') ⊢ divides d (b*(a DIV b) + (a MOD b)) = divides d a *)
      divDa = EQMP[divDaProdEq, divDaProd];
      (* (hyp, b=SUC b') ⊢ divides d a *)

      (* Universal for case B *)
      eAndHypTm = andTm[dividesTm[eV, aV], dividesTm[eV, bV]];
      eAndHyp = ASSUME[eAndHypTm];
      divEa = HOL`Bool`CONJUNCT1[eAndHyp];
      divEb = HOL`Bool`CONJUNCT2[eAndHyp];

      divEbq = HOL`Bool`MP[
        HOL`Bool`SPEC[abDiv,
          HOL`Bool`SPEC[bV,
            HOL`Bool`SPEC[eV, dividesMultRightThm]]],
        divEb];
      (* (e|a ∧ e|b) ⊢ divides e (b * (a DIV b)) *)

      divEaToBqrEq = HOL`Equal`APTERM[mkComb[dividesConst[], eV], divEq];
      (* (b=SUC b') ⊢ divides e a = divides e (b*(a DIV b) + (a MOD b)) *)
      divEbqr = EQMP[divEaToBqrEq, divEa];
      (* (e|a ∧ e|b, b=SUC b') ⊢ divides e (b*(a DIV b) + (a MOD b)) *)

      divEr = HOL`Bool`MP[
        HOL`Bool`MP[
          HOL`Bool`SPEC[abMod,
            HOL`Bool`SPEC[timesTm[bV, abDiv],
              HOL`Bool`SPEC[eV, dividesAddRightThm]]],
          divEbq],
        divEbqr];
      (* (e|a ∧ e|b, b=SUC b') ⊢ divides e (a MOD b) *)

      hypEbAndEr = HOL`Bool`CONJ[divEb, divEr];
      divEd = HOL`Bool`MP[HOL`Bool`SPEC[eV, univDbr], hypEbAndEr];
      (* (hyp, e|a ∧ e|b, b=SUC b') ⊢ divides e d *)
      dischE = HOL`Bool`DISCH[eAndHypTm, divEd];
      genE = HOL`Bool`GEN[eV, dischE];
      (* (hyp, b=SUC b') ⊢ ∀e. (e|a ∧ e|b) ⇒ e|d *)

      predAtD = HOL`Bool`CONJ[divDa, HOL`Bool`CONJ[divDb, genE]];
      (* (hyp, b=SUC b') ⊢ gcdPredAt[a, b, d] *)
      existsAtD = HOL`Bool`EXISTS[gcdExistsAt[aV, bV], dV, predAtD];
      (* (hyp, b=SUC b') ⊢ gcdExistsAt[a, b] *)

      chooseDStep = HOL`Bool`CHOOSE[dV, existsAtBR, existsAtD];
      (* (sih, b=SUC b') ⊢ gcdExistsAt[a, b] *)
      chooseBpStep = HOL`Bool`CHOOSE[npV, exBpHyp, chooseDStep];
      (* (sih, ∃b'. b=SUC b') ⊢ gcdExistsAt[a, b] *)
      chooseBpStep
    ];

    merged = HOL`Bool`DISJCASES[casesAtB, caseZeroB, caseSucB];
    (* (sih) ⊢ gcdExistsAt[a, b] *)

    stepBody = HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[sihTm, HOL`Bool`GEN[aV, merged]]];
    (* ⊢ ∀b. (∀k. k < b ⇒ innerPredAt[k]) ⇒ innerPredAt[b] *)

    mpStrong = HOL`Bool`MP[
      HOL`Drule`CONVRULE[
        HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]],
        HOL`Bool`SPEC[inductionLam, strongInductionThm]],
      stepBody];
    (* ⊢ ∀b. innerPredAt[b] = ⊢ ∀b. ∀a. gcdExistsAt[a, b] *)

    (* Swap quantifier order to ∀a. ∀b. *)
    specBA = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, mpStrong]];
    genB = HOL`Bool`GEN[bV, specBA];
    genA = HOL`Bool`GEN[aV, genB]
  ];

(* ============================================================ *)
(* gcd : num → num → num                                        *)
(*   gcd = λa b. ε d. divides d a ∧ divides d b ∧               *)
(*                    ∀e. (divides e a ∧ divides e b) ⇒ e | d   *)
(* ============================================================ *)

gcdTy = tyFun[numTy, tyFun[numTy, numTy]];

gcdDefBody[] :=
  Module[{aV, bV, dV, eV, predBody, predLam},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    dV = mkVar["d", numTy];
    eV = mkVar["e", numTy];
    predBody = andTm[
      dividesTm[dV, aV],
      andTm[
        dividesTm[dV, bV],
        mkComb[forallC[numTy], mkAbs[eV, impTm[
          andTm[dividesTm[eV, aV], dividesTm[eV, bV]],
          dividesTm[eV, dV]]]]]];
    predLam = mkAbs[dV, predBody];
    mkAbs[aV, mkAbs[bV, mkComb[selectC[numTy], predLam]]]
  ];

gcdDefThm = newDefinition[mkEq[
  mkVar["gcd", gcdTy],
  gcdDefBody[]
]];

gcdConst[] := mkConst["gcd", gcdTy];
gcdTm[aTm_, bTm_] := mkComb[mkComb[gcdConst[], aTm], bTm];

unfoldGcd[aTm_, bTm_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[gcdDefThm, aTm];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, bTm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ============================================================ *)
(* gcdSpecThm                                                   *)
(*   ⊢ ∀a b. divides (gcd a b) a ∧ divides (gcd a b) b ∧        *)
(*           ∀e. (divides e a ∧ divides e b) ⇒ divides e (gcd a b) *)
(*                                                              *)
(* Two-step: selectOfExists on gcdExistsThm at the predicate λd. *)
(* yields predBody[@predLam/d]; rewrite @predLam → gcd a b via   *)
(* SYM[unfoldGcd] using DEPTHCONV[REWRCONV] (same trick as       *)
(* divisionPairThm).                                              *)
(* ============================================================ *)

gcdSpecThm =
  Module[{aV, bV, dV, eV,
          gcdPredAt, existsAtAB,
          predLam, atGcdAtAt, gcdUnfoldAB, atGcdResult,
          genB, genA},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    dV = mkVar["d", numTy];
    eV = mkVar["e", numTy];

    gcdPredAt[aTm_, bTm_, dTm_] := andTm[
      dividesTm[dTm, aTm],
      andTm[
        dividesTm[dTm, bTm],
        mkComb[forallC[numTy], mkAbs[eV, impTm[
          andTm[dividesTm[eV, aTm], dividesTm[eV, bTm]],
          dividesTm[eV, dTm]]]]]];

    existsAtAB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdExistsThm]];
    (* ⊢ ∃d. gcdPredAt[a, b, d] *)

    predLam = mkAbs[dV, gcdPredAt[aV, bV, dV]];
    atGcdAtAt = HOL`Stdlib`Num`selectOfExists[predLam, existsAtAB];
    (* ⊢ gcdPredAt[a, b, @d. gcdPredAt[a, b, d]] *)

    gcdUnfoldAB = unfoldGcd[aV, bV];
    (* ⊢ gcd a b = @d. gcdPredAt[a, b, d] *)
    atGcdResult = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[
        HOL`Drule`REWRCONV[HOL`Equal`SYM[gcdUnfoldAB]]],
      atGcdAtAt];
    (* ⊢ gcdPredAt[a, b, gcd a b] *)

    genB = HOL`Bool`GEN[bV, atGcdResult];
    genA = HOL`Bool`GEN[aV, genB]
  ];

(* ============================================================ *)
(* Three derived properties (CONJUNCT chains on gcdSpecThm).    *)
(* ============================================================ *)

gcdDividesLeftThm =
  Module[{aV, bV, specAB, conj1, genB, genA},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    specAB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdSpecThm]];
    conj1 = HOL`Bool`CONJUNCT1[specAB];
    genB = HOL`Bool`GEN[bV, conj1];
    genA = HOL`Bool`GEN[aV, genB]
  ];

gcdDividesRightThm =
  Module[{aV, bV, specAB, conj2, conj1, genB, genA},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    specAB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdSpecThm]];
    conj2 = HOL`Bool`CONJUNCT2[specAB];
    conj1 = HOL`Bool`CONJUNCT1[conj2];
    genB = HOL`Bool`GEN[bV, conj1];
    genA = HOL`Bool`GEN[aV, genB]
  ];

gcdUniversalThm =
  Module[{aV, bV, eV, specAB, conj2a, conj2b, hypTm, hypTh,
          specE, mpStep, dischHyp, genE, genB, genA},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    eV = mkVar["e", numTy];
    specAB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdSpecThm]];
    conj2a = HOL`Bool`CONJUNCT2[specAB];
    conj2b = HOL`Bool`CONJUNCT2[conj2a];
    (* ⊢ ∀e. (divides e a ∧ divides e b) ⇒ divides e (gcd a b) *)
    specE = HOL`Bool`SPEC[eV, conj2b];
    (* ⊢ (divides e a ∧ divides e b) ⇒ divides e (gcd a b) *)
    genE = HOL`Bool`GEN[eV, specE];
    genB = HOL`Bool`GEN[bV, genE];
    genA = HOL`Bool`GEN[aV, genB]
  ];

(* ============================================================ *)
(* prime : num → bool                                           *)
(*   prime p ⇔ SUC 0 < p ∧ ∀d. divides d p ⇒ d = SUC 0 ∨ d = p   *)
(* ============================================================ *)

primeTy = tyFun[numTy, boolTy];

primeDefBody[] :=
  Module[{pV, dV, suc0Tm},
    pV = mkVar["p", numTy];
    dV = mkVar["d", numTy];
    suc0Tm = mkComb[sucConst[], zeroConst[]];
    mkAbs[pV, andTm[
      ltTm[suc0Tm, pV],
      mkComb[forallC[numTy], mkAbs[dV, impTm[
        dividesTm[dV, pV],
        orTm[
          mkEq[dV, suc0Tm],
          mkEq[dV, pV]]]]]]]
  ];

primeDefThm = newDefinition[mkEq[
  mkVar["prime", primeTy],
  primeDefBody[]
]];

primeConst[] := mkConst["prime", primeTy];
primeTm[pTm_] := mkComb[primeConst[], pTm];

unfoldPrime[pTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[primeDefThm, pTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ============================================================ *)
(* M7-3-q: Euclid's lemma                                       *)
(*   ⊢ ∀p a b. prime p ⇒ divides p (a * b) ⇒                    *)
(*             divides p a ∨ divides p b                        *)
(*                                                              *)
(* Strong induction on a.  Under prime p:                       *)
(*   a = 0: trivial via dividesZero.                            *)
(*   a > 0: leqTotal(p, a) splits into                          *)
(*     A. p ≤ a: DIV a by p (uses pNotZero from prime).         *)
(*        a = p*q + r ∧ r < p. numCases on r:                    *)
(*          r = 0: a = p*q, so p|a (DISJ1).                      *)
(*          r > 0: r < a (via leqTrans), SIH at r gives          *)
(*                 p|r ∨ p|b; p|r contradicts via dividesLeq +   *)
(*                 leqAntisym + ltImpliesNotEq.                  *)
(*     B. a ≤ p: leqCaseEqLt gives a = p ∨ a < p.                 *)
(*          a = p: p|a via dividesRefl + rewrite.                *)
(*          a < p: DIV p by a (uses aNotZero from a = SUC a').    *)
(*                 p = a*q + r ∧ r < a. Derive p|r*b via the      *)
(*                 chain p|a*b → p|a*q*b → addRight → p|r*b.      *)
(*                 SIH at r; on p|r branch numCases on r:         *)
(*                   r = 0: a*q = p ⇒ a|p; primeUniv gives        *)
(*                          a = 1 ∨ a = p; a = p contradicts      *)
(*                          a<p; a = 1 ⇒ a*b = b ⇒ p|b.           *)
(*                   r > 0: contradiction as in case A.           *)
(* ============================================================ *)

euclidLemmaThm =
  Module[{pV, aV, bV, kV, qV, rV, apV, rpV, cV,
          primePTm, primePHyp, primePExpanded, suc0LtP, primeUniv,
          pNotZeroTm, pNotZero,
          predBodyAt, predLam, sihAtATm, sihAtAHyp,
          numCasesAtA, zeroCase, sucCase,
          stepInner, stepFull, strongSpec, mpStrong,
          specAB, dischPrime, genB, genA, genP},
    pV = mkVar["p", numTy];
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    kV = mkVar["k", numTy];
    qV = mkVar["q", numTy];
    rV = mkVar["r", numTy];
    apV = mkVar["a'", numTy];
    rpV = mkVar["r'", numTy];
    cV = mkVar["c", numTy];

    primePTm = primeTm[pV];
    primePHyp = ASSUME[primePTm];
    primePExpanded = EQMP[unfoldPrime[pV], primePHyp];
    suc0LtP = HOL`Bool`CONJUNCT1[primePExpanded];
    primeUniv = HOL`Bool`CONJUNCT2[primePExpanded];

    pNotZeroTm = mkComb[notC[], mkEq[pV, zeroConst[]]];
    pNotZero = Module[{pEqZeroTm, pEqZeroHyp, suc0LtRewrite,
                       notLtZeroAtSuc0, contradF, dischPEqZero},
      pEqZeroTm = mkEq[pV, zeroConst[]];
      pEqZeroHyp = ASSUME[pEqZeroTm];
      suc0LtRewrite = EQMP[
        HOL`Equal`APTERM[
          mkComb[ltConst[], mkComb[sucConst[], zeroConst[]]],
          pEqZeroHyp],
        suc0LtP];
      (* (prime p, p=0) ⊢ SUC 0 < 0 *)
      notLtZeroAtSuc0 = HOL`Bool`SPEC[
        mkComb[sucConst[], zeroConst[]], notLtZeroThm];
      contradF = HOL`Bool`MP[
        HOL`Bool`NOTELIM[notLtZeroAtSuc0], suc0LtRewrite];
      dischPEqZero = HOL`Bool`DISCH[pEqZeroTm, contradF];
      HOL`Bool`NOTINTRO[dischPEqZero]
    ];
    (* (prime p) ⊢ ¬ (p = 0) *)

    predBodyAt[aTm_] := mkComb[forallC[numTy], mkAbs[bV,
      impTm[dividesTm[pV, timesTm[aTm, bV]],
            orTm[dividesTm[pV, aTm], dividesTm[pV, bV]]]]];

    predLam = mkAbs[aV, predBodyAt[aV]];

    sihAtATm = mkComb[forallC[numTy], mkAbs[kV,
      impTm[ltTm[kV, aV], predBodyAt[kV]]]];
    sihAtAHyp = ASSUME[sihAtATm];
    (* (sih) ⊢ ∀k. k < a ⇒ ∀b. p|k*b ⇒ p|k ∨ p|b *)

    numCasesAtA = HOL`Bool`SPEC[aV, numCasesThm];
    (* ⊢ a = 0 ∨ ∃a'. a = SUC a' *)

    (* --- zeroCase: a = 0. p|0 trivially gives p|a (after rewrite). --- *)
    zeroCase = Module[{aEqZeroTm, aEqZeroHyp, dividesP0,
                       divEq, pDividesA, hypPDABTm, hypPDAB,
                       disj1Result, dischHyp, genBZero},
      aEqZeroTm = mkEq[aV, zeroConst[]];
      aEqZeroHyp = ASSUME[aEqZeroTm];
      dividesP0 = HOL`Bool`SPEC[pV, dividesZeroThm];
      divEq = HOL`Equal`APTERM[mkComb[dividesConst[], pV],
                               HOL`Equal`SYM[aEqZeroHyp]];
      (* (a=0) ⊢ divides p 0 = divides p a *)
      pDividesA = EQMP[divEq, dividesP0];
      (* (a=0) ⊢ divides p a *)
      hypPDABTm = dividesTm[pV, timesTm[aV, bV]];
      hypPDAB = ASSUME[hypPDABTm];
      disj1Result = HOL`Bool`DISJ1[pDividesA, dividesTm[pV, bV]];
      dischHyp = HOL`Bool`DISCH[hypPDABTm, disj1Result];
      genBZero = HOL`Bool`GEN[bV, dischHyp]
      (* (a=0) ⊢ predBodyAt[a] *)
    ];

    (* --- sucCase: ∃a'. a = SUC a'. Use Euclidean argument. --- *)
    sucCase = Module[{exApTm, exApHyp, aEqSucApTm, aEqSucApHyp,
                      aNotZero, hypPDABTm, hypPDAB,
                      leqTotalAtPA, caseA, caseB, merged,
                      dischHyp, genBSuc, chooseApSuc,
                      abDiv, abMod, paDiv, paMod},
      exApTm = mkComb[existsC[numTy],
        mkAbs[apV, mkEq[aV, mkComb[sucConst[], apV]]]];
      exApHyp = ASSUME[exApTm];
      aEqSucApTm = mkEq[aV, mkComb[sucConst[], apV]];
      aEqSucApHyp = ASSUME[aEqSucApTm];

      aNotZero = Module[{aEqZTm, aEqZH, chainEq, sucApNotZ, contradF, dischAZ},
        aEqZTm = mkEq[aV, zeroConst[]];
        aEqZH = ASSUME[aEqZTm];
        chainEq = TRANS[HOL`Equal`SYM[aEqSucApHyp], aEqZH];
        sucApNotZ = HOL`Bool`SPEC[apV, sucNotZeroThm];
        contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[sucApNotZ], chainEq];
        dischAZ = HOL`Bool`DISCH[aEqZTm, contradF];
        HOL`Bool`NOTINTRO[dischAZ]
      ];
      (* (a = SUC a') ⊢ ¬(a = 0) *)

      hypPDABTm = dividesTm[pV, timesTm[aV, bV]];
      hypPDAB = ASSUME[hypPDABTm];

      leqTotalAtPA = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[pV, leqTotalThm]];
      (* ⊢ p ≤ a ∨ a ≤ p *)

      abDiv = divTm[aV, pV];
      abMod = modTm[aV, pV];
      paDiv = divTm[pV, aV];
      paMod = modTm[pV, aV];

      (* === Case A: p ≤ a === *)
      caseA = Module[{pLeqATm, pLeqAHyp, divPairAt, divEq, rLtP,
                      rCases, rZeroBranch, rSucBranch, mergedR},
        pLeqATm = leqTm[pV, aV];
        pLeqAHyp = ASSUME[pLeqATm];

        divPairAt = HOL`Bool`MP[
          HOL`Bool`SPEC[pV, HOL`Bool`SPEC[aV, divisionPairThm]],
          pNotZero];
        (* (prime p) ⊢ a = p*(a DIV p) + (a MOD p) ∧ (a MOD p) < p *)
        divEq = HOL`Bool`CONJUNCT1[divPairAt];
        rLtP = HOL`Bool`CONJUNCT2[divPairAt];

        rCases = HOL`Bool`SPEC[abMod, numCasesThm];
        (* ⊢ (a MOD p) = 0 ∨ ∃r'. (a MOD p) = SUC r' *)

        (* sub r = 0: a = p*(a DIV p), so p|a. *)
        rZeroBranch = Module[{rEqZTm, rEqZHyp, divEqRZ, plusZAt,
                              aEqPq, pDivPq, pDivA, disj1Final},
          rEqZTm = mkEq[abMod, zeroConst[]];
          rEqZHyp = ASSUME[rEqZTm];
          divEqRZ = TRANS[divEq,
            HOL`Equal`APTERM[
              mkComb[plusConst[], timesTm[pV, abDiv]], rEqZHyp]];
          (* (prime p, r=0) ⊢ a = p*(a DIV p) + 0 *)
          plusZAt = HOL`Bool`SPEC[timesTm[pV, abDiv], plusZeroEqThm];
          aEqPq = TRANS[divEqRZ, plusZAt];
          (* (prime p, r=0) ⊢ a = p*(a DIV p) *)
          pDivPq = HOL`Bool`MP[
            HOL`Bool`SPEC[abDiv,
              HOL`Bool`SPEC[pV, HOL`Bool`SPEC[pV, dividesMultRightThm]]],
            HOL`Bool`SPEC[pV, dividesReflThm]];
          (* ⊢ divides p (p * (a DIV p)) *)
          pDivA = EQMP[
            HOL`Equal`APTERM[mkComb[dividesConst[], pV],
                             HOL`Equal`SYM[aEqPq]],
            pDivPq];
          (* (prime p, r=0) ⊢ divides p a *)
          disj1Final = HOL`Bool`DISJ1[pDivA, dividesTm[pV, bV]];
          disj1Final
          (* (prime p, r=0) ⊢ divides p a ∨ divides p b *)
        ];

        (* sub r = SUC r': r < a; SIH at r gives p|r ∨ p|b. *)
        rSucBranch = Module[{exRpTm, exRpHyp, rEqSucRpTm, rEqSucRpHyp,
                             rNotZero, sucRLeqP, leqTransAt, sucRLeqA, rLtA,
                             sihAtR, sihAtRMpd,
                             aBeqPqrBEq, pDivPqrB,
                             distribAt, pDivPqBplusRBeq, pDivPqBplusRB,
                             pDivPq, pDivPqB, addRightAt, pDivRB,
                             pDivROrB, pDivRBranch, pDivBBranch, disjFinal,
                             choseRp},
          exRpTm = mkComb[existsC[numTy],
            mkAbs[rpV, mkEq[abMod, mkComb[sucConst[], rpV]]]];
          exRpHyp = ASSUME[exRpTm];
          rEqSucRpTm = mkEq[abMod, mkComb[sucConst[], rpV]];
          rEqSucRpHyp = ASSUME[rEqSucRpTm];

          rNotZero = Module[{rEqZTm, rEqZH, chainEq, sucRpNotZ, contradF, dischRZ},
            rEqZTm = mkEq[abMod, zeroConst[]];
            rEqZH = ASSUME[rEqZTm];
            chainEq = TRANS[HOL`Equal`SYM[rEqSucRpHyp], rEqZH];
            sucRpNotZ = HOL`Bool`SPEC[rpV, sucNotZeroThm];
            contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[sucRpNotZ], chainEq];
            dischRZ = HOL`Bool`DISCH[rEqZTm, contradF];
            HOL`Bool`NOTINTRO[dischRZ]
          ];
          (* (r = SUC r') ⊢ ¬(r = 0) *)

          sucRLeqP = EQMP[unfoldLt[abMod, pV], rLtP];
          (* (prime p) ⊢ SUC (a MOD p) ≤ p *)
          leqTransAt = HOL`Bool`SPEC[aV,
            HOL`Bool`SPEC[pV,
              HOL`Bool`SPEC[mkComb[sucConst[], abMod], leqTransThm]]];
          (* ⊢ SUC r ≤ p ⇒ p ≤ a ⇒ SUC r ≤ a *)
          sucRLeqA = HOL`Bool`MP[HOL`Bool`MP[leqTransAt, sucRLeqP], pLeqAHyp];
          (* (prime p, p ≤ a) ⊢ SUC (a MOD p) ≤ a *)
          rLtA = EQMP[HOL`Equal`SYM[unfoldLt[abMod, aV]], sucRLeqA];
          (* (prime p, p ≤ a) ⊢ (a MOD p) < a *)

          sihAtR = HOL`Bool`SPEC[abMod, sihAtAHyp];
          sihAtRMpd = HOL`Bool`MP[sihAtR, rLtA];
          (* (sih, prime p, p ≤ a) ⊢ ∀b'. p|r*b' ⇒ p|r ∨ p|b' *)

          (* p | r*b chain:
             a*b = (p*q + r)*b via APTHM[APTERM[*, divEq], b].
             divides p (a*b) = divides p ((p*q+r)*b) via APTERM divides p.
             EQMP with hypPDAB.
             (p*q + r)*b = p*q*b + r*b via distribRight.
             APTERM + EQMP again.
             p|p*q*b via dividesMultRight twice on dividesRefl.
             dividesAddRightThm chain. *)
          aBeqPqrBEq = HOL`Equal`APTHM[
            HOL`Equal`APTERM[timesConst[], divEq], bV];
          (* (prime p) ⊢ a * b = (p*(a DIV p) + (a MOD p)) * b *)
          pDivPqrB = EQMP[
            HOL`Equal`APTERM[mkComb[dividesConst[], pV], aBeqPqrBEq],
            hypPDAB];
          (* (prime p, p|a*b) ⊢ divides p ((p*(a DIV p) + (a MOD p)) * b) *)

          distribAt = HOL`Bool`SPEC[bV,
            HOL`Bool`SPEC[abMod,
              HOL`Bool`SPEC[timesTm[pV, abDiv], timesDistribRightThm]]];
          (* ⊢ (p*q + r)*b = p*q*b + r*b *)
          pDivPqBplusRBeq = HOL`Equal`APTERM[
            mkComb[dividesConst[], pV], distribAt];
          pDivPqBplusRB = EQMP[pDivPqBplusRBeq, pDivPqrB];
          (* (prime p, p|a*b) ⊢ divides p (p*q*b + r*b) *)

          pDivPq = HOL`Bool`MP[
            HOL`Bool`SPEC[abDiv,
              HOL`Bool`SPEC[pV, HOL`Bool`SPEC[pV, dividesMultRightThm]]],
            HOL`Bool`SPEC[pV, dividesReflThm]];
          (* ⊢ divides p (p * (a DIV p)) *)
          pDivPqB = HOL`Bool`MP[
            HOL`Bool`SPEC[bV,
              HOL`Bool`SPEC[timesTm[pV, abDiv],
                HOL`Bool`SPEC[pV, dividesMultRightThm]]],
            pDivPq];
          (* ⊢ divides p (p*q*b) *)

          addRightAt = HOL`Bool`SPEC[timesTm[abMod, bV],
            HOL`Bool`SPEC[timesTm[timesTm[pV, abDiv], bV],
              HOL`Bool`SPEC[pV, dividesAddRightThm]]];
          (* ⊢ p|(p*q*b) ⇒ p|((p*q*b)+(r*b)) ⇒ p|r*b *)
          pDivRB = HOL`Bool`MP[HOL`Bool`MP[addRightAt, pDivPqB], pDivPqBplusRB];
          (* (prime p, p|a*b) ⊢ divides p (r * b) *)

          pDivROrB = HOL`Bool`MP[HOL`Bool`SPEC[bV, sihAtRMpd], pDivRB];
          (* (sih, prime p, p|a*b, p ≤ a) ⊢ divides p r ∨ divides p b *)

          pDivRBranch = Module[{pDivRHyp, pLeqR, rLeqSucR, sucRLeqP2,
                                rLeqP, pEqRR, notREqP, contradF},
            pDivRHyp = ASSUME[dividesTm[pV, abMod]];
            pLeqR = HOL`Bool`MP[
              HOL`Bool`MP[
                HOL`Bool`SPEC[abMod,
                  HOL`Bool`SPEC[pV, dividesLeqThm]],
                rNotZero],
              pDivRHyp];
            (* (prime p, r=SUC r', p|r) ⊢ p ≤ r *)
            rLeqSucR = HOL`Bool`SPEC[abMod, leqSucThm];
            (* ⊢ r ≤ SUC r *)
            rLeqP = HOL`Bool`MP[
              HOL`Bool`MP[
                HOL`Bool`SPEC[pV,
                  HOL`Bool`SPEC[mkComb[sucConst[], abMod],
                    HOL`Bool`SPEC[abMod, leqTransThm]]],
                rLeqSucR],
              sucRLeqP];
            (* (prime p) ⊢ r ≤ p *)
            pEqRR = HOL`Bool`MP[
              HOL`Bool`MP[
                HOL`Bool`SPEC[abMod, HOL`Bool`SPEC[pV, leqAntisymThm]],
                pLeqR],
              rLeqP];
            (* (..., p|r) ⊢ p = r *)
            notREqP = HOL`Bool`MP[
              HOL`Bool`SPEC[pV,
                HOL`Bool`SPEC[abMod, ltImpliesNotEqThm]],
              rLtP];
            (* (prime p) ⊢ ¬(r = p) *)
            contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[notREqP],
              HOL`Equal`SYM[pEqRR]];
            (* (...) ⊢ F *)
            HOL`Bool`CONTR[orTm[dividesTm[pV, aV], dividesTm[pV, bV]],
              contradF]
            (* (..., p|r) ⊢ divides p a ∨ divides p b *)
          ];

          pDivBBranch = Module[{pDivBHyp},
            pDivBHyp = ASSUME[dividesTm[pV, bV]];
            HOL`Bool`DISJ2[pDivBHyp, dividesTm[pV, aV]]
            (* (p|b) ⊢ divides p a ∨ divides p b *)
          ];

          disjFinal = HOL`Bool`DISJCASES[pDivROrB,
            pDivRBranch, pDivBBranch];
          (* (sih, prime p, p|a*b, p ≤ a, r=SUC r') ⊢ divides p a ∨ divides p b *)
          choseRp = HOL`Bool`CHOOSE[rpV, exRpHyp, disjFinal];
          (* (sih, prime p, p|a*b, p ≤ a, ∃r'. r=SUC r') ⊢ … *)
          choseRp
        ];

        mergedR = HOL`Bool`DISJCASES[rCases, rZeroBranch, rSucBranch];
        (* (sih, prime p, p ≤ a, p|a*b) ⊢ divides p a ∨ divides p b *)
        mergedR
      ];

      (* === Case B: a ≤ p === *)
      caseB = Module[{aLeqPTm, aLeqPHyp, leqCaseAt,
                      aEqPCase, aLtPCase, mergedB},
        aLeqPTm = leqTm[aV, pV];
        aLeqPHyp = ASSUME[aLeqPTm];

        leqCaseAt = HOL`Bool`MP[
          HOL`Bool`SPEC[pV, HOL`Bool`SPEC[aV, leqCaseEqLtThm]],
          aLeqPHyp];
        (* (a ≤ p) ⊢ a = p ∨ a < p *)

        (* Sub-case: a = p. p|a via refl + rewrite. *)
        aEqPCase = Module[{aEqPTm, aEqPHyp, pDivP, rewriteEq, pDivA, disj1},
          aEqPTm = mkEq[aV, pV];
          aEqPHyp = ASSUME[aEqPTm];
          pDivP = HOL`Bool`SPEC[pV, dividesReflThm];
          (* ⊢ divides p p *)
          rewriteEq = HOL`Equal`APTERM[mkComb[dividesConst[], pV],
                                       HOL`Equal`SYM[aEqPHyp]];
          (* (a=p) ⊢ divides p p = divides p a *)
          pDivA = EQMP[rewriteEq, pDivP];
          (* (a=p) ⊢ divides p a *)
          disj1 = HOL`Bool`DISJ1[pDivA, dividesTm[pV, bV]];
          disj1
          (* (a=p) ⊢ divides p a ∨ divides p b *)
        ];

        (* Sub-case: a < p. DIV p by a; SIH descent. *)
        aLtPCase = Module[{aLtPTm, aLtPHyp, divPairBAt, divEqB, rLtA,
                           pBeqRhsEq, pBeqRhsB, pDivPB, pDivRhs,
                           distribAtB,
                           assoc1, comm1, assoc2,
                           commApp1, assoc1Sym, aqBeqAbq,
                           pDivABq, pDivAQB,
                           addRightAtB, pDivRB,
                           sihAtR, sihAtRMpd, pDivROrB,
                           pDivRBranchB, pDivBBranchB, disjFinalB},
          aLtPTm = ltTm[aV, pV];
          aLtPHyp = ASSUME[aLtPTm];

          divPairBAt = HOL`Bool`MP[
            HOL`Bool`SPEC[aV, HOL`Bool`SPEC[pV, divisionPairThm]],
            aNotZero];
          (* (a=SUC a') ⊢ p = a*(p DIV a) + (p MOD a) ∧ (p MOD a) < a *)
          divEqB = HOL`Bool`CONJUNCT1[divPairBAt];
          rLtA = HOL`Bool`CONJUNCT2[divPairBAt];

          (* Derive p|r*b. p|a*b ⇒ p|(a*b)*q via mult; rewrite       *)
          (* (a*b)*q to (a*q)*b via the chain assoc → comm → assoc.   *)
          (* p|p*b refl+mult. Then dividesAddRightThm on the equation *)
          (* p*b = (a*q)*b + r*b yields p|r*b.                        *)
          pBeqRhsEq = HOL`Equal`APTHM[
            HOL`Equal`APTERM[timesConst[], divEqB], bV];
          (* (a=SUC a') ⊢ p * b = (a*(p DIV a) + (p MOD a)) * b *)
          distribAtB = HOL`Bool`SPEC[bV,
            HOL`Bool`SPEC[paMod,
              HOL`Bool`SPEC[timesTm[aV, paDiv], timesDistribRightThm]]];
          (* ⊢ (a*(p DIV a) + (p MOD a)) * b = a*(p DIV a)*b + (p MOD a)*b *)
          pBeqRhsB = TRANS[pBeqRhsEq, distribAtB];
          (* (a=SUC a') ⊢ p * b = a*(p DIV a)*b + (p MOD a)*b *)

          (* p | p*b *)
          pDivPB = HOL`Bool`MP[
            HOL`Bool`SPEC[bV,
              HOL`Bool`SPEC[pV, HOL`Bool`SPEC[pV, dividesMultRightThm]]],
            HOL`Bool`SPEC[pV, dividesReflThm]];
          (* ⊢ divides p (p * b) *)
          pDivRhs = EQMP[
            HOL`Equal`APTERM[mkComb[dividesConst[], pV], pBeqRhsB],
            pDivPB];
          (* (a=SUC a') ⊢ divides p (a*(p DIV a)*b + (p MOD a)*b) *)

          (* p | a*(p DIV a)*b from p|a*b. *)
          pDivABq = HOL`Bool`MP[
            HOL`Bool`SPEC[paDiv,
              HOL`Bool`SPEC[timesTm[aV, bV],
                HOL`Bool`SPEC[pV, dividesMultRightThm]]],
            hypPDAB];
          (* (p|a*b) ⊢ divides p ((a*b) * (p DIV a)) *)
          (* Now rewrite (a*b) * (p DIV a) = (a*(p DIV a))*b
             chain: (a*b)*q = a*(b*q) = a*(q*b) = (a*q)*b *)
          assoc1 = HOL`Bool`SPEC[paDiv,
            HOL`Bool`SPEC[bV,
              HOL`Bool`SPEC[aV, timesAssocThm]]];
          (* ⊢ (a*b)*(p DIV a) = a*(b*(p DIV a)) *)
          comm1 = HOL`Bool`SPEC[paDiv,
            HOL`Bool`SPEC[bV, timesCommThm]];
          (* ⊢ b*(p DIV a) = (p DIV a)*b *)
          commApp1 = HOL`Equal`APTERM[mkComb[timesConst[], aV], comm1];
          (* ⊢ a*(b*(p DIV a)) = a*((p DIV a)*b) *)
          assoc2 = HOL`Bool`SPEC[bV,
            HOL`Bool`SPEC[paDiv,
              HOL`Bool`SPEC[aV, timesAssocThm]]];
          (* ⊢ (a*(p DIV a))*b = a*((p DIV a)*b) *)
          assoc1Sym = HOL`Equal`SYM[assoc2];
          (* ⊢ a*((p DIV a)*b) = (a*(p DIV a))*b *)
          aqBeqAbq = TRANS[TRANS[assoc1, commApp1], assoc1Sym];
          (* ⊢ (a*b)*(p DIV a) = (a*(p DIV a))*b *)
          pDivAQB = EQMP[
            HOL`Equal`APTERM[mkComb[dividesConst[], pV], aqBeqAbq],
            pDivABq];
          (* (p|a*b) ⊢ divides p ((a*(p DIV a))*b) *)

          addRightAtB = HOL`Bool`SPEC[timesTm[paMod, bV],
            HOL`Bool`SPEC[timesTm[timesTm[aV, paDiv], bV],
              HOL`Bool`SPEC[pV, dividesAddRightThm]]];
          (* ⊢ p|(a*(p DIV a))*b ⇒ p|((a*(p DIV a))*b + (p MOD a)*b)
                                 ⇒ p|(p MOD a)*b *)
          pDivRB = HOL`Bool`MP[HOL`Bool`MP[addRightAtB, pDivAQB], pDivRhs];
          (* (a=SUC a', p|a*b) ⊢ divides p ((p MOD a)*b) *)

          sihAtR = HOL`Bool`SPEC[paMod, sihAtAHyp];
          sihAtRMpd = HOL`Bool`MP[sihAtR, rLtA];
          (* (sih, a=SUC a') ⊢ ∀b'. p|r*b' ⇒ p|r ∨ p|b' *)

          pDivROrB = HOL`Bool`MP[HOL`Bool`SPEC[bV, sihAtRMpd], pDivRB];
          (* (sih, a=SUC a', p|a*b) ⊢ divides p (p MOD a) ∨ divides p b *)

          pDivRBranchB = Module[{pDivRHyp, rCases2, rZBranch, rSBranch},
            pDivRHyp = ASSUME[dividesTm[pV, paMod]];
            rCases2 = HOL`Bool`SPEC[paMod, numCasesThm];

            (* r = 0: a*q = p, so a|p; primeUniv ⇒ a = 1 ∨ a = p.
               a=1 ⇒ a*b = b ⇒ p|b.
               a=p contradicts a<p. *)
            rZBranch = Module[{rEqZTm, rEqZH, divEqBRZ, plusZAt,
                               pEqAq, pEqAqSym, aDivPexBody, aDivPexists, aDivP,
                               primeUnivAtA, aEqDisj,
                               aEqSucZBranch, aEqPBranch, mergedADisj},
              rEqZTm = mkEq[paMod, zeroConst[]];
              rEqZH = ASSUME[rEqZTm];
              divEqBRZ = TRANS[divEqB,
                HOL`Equal`APTERM[
                  mkComb[plusConst[], timesTm[aV, paDiv]], rEqZH]];
              (* (a=SUC a', r=0) ⊢ p = a*(p DIV a) + 0 *)
              plusZAt = HOL`Bool`SPEC[timesTm[aV, paDiv], plusZeroEqThm];
              pEqAq = TRANS[divEqBRZ, plusZAt];
              (* (a=SUC a', r=0) ⊢ p = a * (p DIV a) *)

              aDivPexBody = mkComb[existsC[numTy],
                mkAbs[cV, mkEq[pV, timesTm[aV, cV]]]];
              aDivPexists = HOL`Bool`EXISTS[aDivPexBody, paDiv, pEqAq];
              (* (a=SUC a', r=0) ⊢ ∃c. p = a * c *)
              aDivP = EQMP[HOL`Equal`SYM[unfoldDivides[aV, pV]],
                aDivPexists];
              (* (a=SUC a', r=0) ⊢ divides a p *)

              primeUnivAtA = HOL`Bool`SPEC[aV, primeUniv];
              (* (prime p) ⊢ divides a p ⇒ a = SUC 0 ∨ a = p *)
              aEqDisj = HOL`Bool`MP[primeUnivAtA, aDivP];
              (* (prime p, a=SUC a', r=0) ⊢ a = SUC 0 ∨ a = p *)

              (* a = SUC 0 case: a*b = b ⇒ p|b *)
              aEqSucZBranch = Module[{aEqSucZHyp, abEqBRewrite, abEqBByOne,
                                      pDivBBuilt, disj2},
                aEqSucZHyp = ASSUME[mkEq[aV, mkComb[sucConst[], zeroConst[]]]];
                (* abEqBRewrite: a*b = SUC 0 * b *)
                abEqBRewrite = HOL`Equal`APTHM[
                  HOL`Equal`APTERM[timesConst[], aEqSucZHyp], bV];
                (* (a=SUC 0) ⊢ a*b = SUC 0 * b *)
                abEqBByOne = TRANS[abEqBRewrite,
                  HOL`Bool`SPEC[bV, oneTimesEqThm]];
                (* (a=SUC 0) ⊢ a*b = b *)
                pDivBBuilt = EQMP[
                  HOL`Equal`APTERM[mkComb[dividesConst[], pV], abEqBByOne],
                  hypPDAB];
                (* (a=SUC 0, p|a*b) ⊢ divides p b *)
                disj2 = HOL`Bool`DISJ2[pDivBBuilt, dividesTm[pV, aV]];
                disj2
                (* (a=SUC 0, p|a*b) ⊢ divides p a ∨ divides p b *)
              ];

              (* a = p case: contradicts a<p. *)
              aEqPBranch = Module[{aEqPHyp2, notAEqP, contradF},
                aEqPHyp2 = ASSUME[mkEq[aV, pV]];
                notAEqP = HOL`Bool`MP[
                  HOL`Bool`SPEC[pV,
                    HOL`Bool`SPEC[aV, ltImpliesNotEqThm]],
                  aLtPHyp];
                (* (a<p) ⊢ ¬(a = p) *)
                contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[notAEqP], aEqPHyp2];
                HOL`Bool`CONTR[
                  orTm[dividesTm[pV, aV], dividesTm[pV, bV]], contradF]
              ];

              mergedADisj = HOL`Bool`DISJCASES[aEqDisj,
                aEqSucZBranch, aEqPBranch];
              mergedADisj
              (* (sih, prime p, a=SUC a', r=0, p|a*b, a<p) ⊢ divides p a ∨ divides p b *)
            ];

            (* r = SUC r': same contradiction as case A. *)
            rSBranch = Module[{exRpTmB, exRpHypB, rEqSucRpTmB, rEqSucRpHypB,
                               rNotZeroB, pLeqRB, rLeqSucRB, sucRLeqAB,
                               sucRLeqPB, rLeqPB, pEqRRB, notREqPB,
                               contradFB, dischResult, choseRpB},
              exRpTmB = mkComb[existsC[numTy],
                mkAbs[rpV, mkEq[paMod, mkComb[sucConst[], rpV]]]];
              exRpHypB = ASSUME[exRpTmB];
              rEqSucRpTmB = mkEq[paMod, mkComb[sucConst[], rpV]];
              rEqSucRpHypB = ASSUME[rEqSucRpTmB];

              rNotZeroB = Module[{rEqZTm, rEqZH, chainEq, sucRpNZ, contradF, dischRZ},
                rEqZTm = mkEq[paMod, zeroConst[]];
                rEqZH = ASSUME[rEqZTm];
                chainEq = TRANS[HOL`Equal`SYM[rEqSucRpHypB], rEqZH];
                sucRpNZ = HOL`Bool`SPEC[rpV, sucNotZeroThm];
                contradF = HOL`Bool`MP[HOL`Bool`NOTELIM[sucRpNZ], chainEq];
                dischRZ = HOL`Bool`DISCH[rEqZTm, contradF];
                HOL`Bool`NOTINTRO[dischRZ]
              ];
              (* (r=SUC r') ⊢ ¬(r=0) *)

              pLeqRB = HOL`Bool`MP[
                HOL`Bool`MP[
                  HOL`Bool`SPEC[paMod, HOL`Bool`SPEC[pV, dividesLeqThm]],
                  rNotZeroB],
                pDivRHyp];
              (* (p|r, r=SUC r') ⊢ p ≤ (p MOD a) *)

              (* (p MOD a) < p via (p MOD a) < a < p chain.
                 sucRLeqAB = SUC r ≤ a (from r < a).
                 r ≤ SUC r (leqSuc), so r ≤ a (leqTrans).
                 a ≤ p (aLeqPHyp). So r ≤ p (leqTrans). *)
              sucRLeqAB = EQMP[unfoldLt[paMod, aV], rLtA];
              (* (a=SUC a') ⊢ SUC r ≤ a *)
              rLeqSucRB = HOL`Bool`SPEC[paMod, leqSucThm];
              (* ⊢ r ≤ SUC r *)
              (* r ≤ a via leqTrans *)
              Module[{rLeqA, leqTransSlow},
                leqTransSlow = HOL`Bool`SPEC[aV,
                  HOL`Bool`SPEC[mkComb[sucConst[], paMod],
                    HOL`Bool`SPEC[paMod, leqTransThm]]];
                rLeqA = HOL`Bool`MP[HOL`Bool`MP[leqTransSlow, rLeqSucRB], sucRLeqAB];
                rLeqPB = HOL`Bool`MP[
                  HOL`Bool`MP[
                    HOL`Bool`SPEC[pV,
                      HOL`Bool`SPEC[aV,
                        HOL`Bool`SPEC[paMod, leqTransThm]]],
                    rLeqA],
                  aLeqPHyp];
                (* (a=SUC a', a ≤ p) ⊢ r ≤ p *)
              ];

              pEqRRB = HOL`Bool`MP[
                HOL`Bool`MP[
                  HOL`Bool`SPEC[paMod, HOL`Bool`SPEC[pV, leqAntisymThm]],
                  pLeqRB],
                rLeqPB];
              (* (...) ⊢ p = (p MOD a) *)

              (* Need r < p, but we have r < a < p. Easiest: derive r < p chain.
                 Actually we want ¬(r = p). We have ¬(a = p) from a<p. Hmm.
                 Better: derive r < p directly via SUC r ≤ a ≤ p ⇒ SUC r ≤ p ⇒ r < p.
                 Then ltImpliesNotEq at r, p: ¬(r = p). *)
              Module[{sucRLeqPCycB, rLtPB},
                sucRLeqPCycB = HOL`Bool`MP[
                  HOL`Bool`MP[
                    HOL`Bool`SPEC[pV,
                      HOL`Bool`SPEC[aV,
                        HOL`Bool`SPEC[mkComb[sucConst[], paMod], leqTransThm]]],
                    sucRLeqAB],
                  aLeqPHyp];
                (* (a=SUC a', a ≤ p) ⊢ SUC r ≤ p *)
                rLtPB = EQMP[HOL`Equal`SYM[unfoldLt[paMod, pV]], sucRLeqPCycB];
                (* (a=SUC a', a ≤ p) ⊢ r < p *)
                notREqPB = HOL`Bool`MP[
                  HOL`Bool`SPEC[pV,
                    HOL`Bool`SPEC[paMod, ltImpliesNotEqThm]],
                  rLtPB]
                (* (a=SUC a', a ≤ p) ⊢ ¬(r = p) *)
              ];

              contradFB = HOL`Bool`MP[HOL`Bool`NOTELIM[notREqPB],
                HOL`Equal`SYM[pEqRRB]];
              (* (...) ⊢ F *)
              dischResult = HOL`Bool`CONTR[
                orTm[dividesTm[pV, aV], dividesTm[pV, bV]], contradFB];
              (* (...) ⊢ divides p a ∨ divides p b *)
              choseRpB = HOL`Bool`CHOOSE[rpV, exRpHypB, dischResult];
              choseRpB
            ];

            HOL`Bool`DISJCASES[rCases2, rZBranch, rSBranch]
            (* (...) ⊢ divides p a ∨ divides p b *)
          ];

          pDivBBranchB = Module[{pDivBHyp},
            pDivBHyp = ASSUME[dividesTm[pV, bV]];
            HOL`Bool`DISJ2[pDivBHyp, dividesTm[pV, aV]]
          ];

          disjFinalB = HOL`Bool`DISJCASES[pDivROrB,
            pDivRBranchB, pDivBBranchB];
          disjFinalB
          (* (sih, prime p, a=SUC a', a<p, p|a*b) ⊢ divides p a ∨ divides p b *)
        ];

        mergedB = HOL`Bool`DISJCASES[leqCaseAt,
          aEqPCase, aLtPCase];
        (* (sih, prime p, a=SUC a', a ≤ p, p|a*b) ⊢ divides p a ∨ divides p b *)
        mergedB
      ];

      merged = HOL`Bool`DISJCASES[leqTotalAtPA, caseA, caseB];
      (* (sih, prime p, a=SUC a', p|a*b) ⊢ divides p a ∨ divides p b *)
      dischHyp = HOL`Bool`DISCH[hypPDABTm, merged];
      genBSuc = HOL`Bool`GEN[bV, dischHyp];
      chooseApSuc = HOL`Bool`CHOOSE[apV, exApHyp, genBSuc];
      chooseApSuc
      (* (sih, prime p, ∃a'. a = SUC a') ⊢ predBodyAt[a] *)
    ];

    stepInner = HOL`Bool`DISJCASES[numCasesAtA, zeroCase, sucCase];
    (* (sih, prime p) ⊢ predBodyAt[a] *)

    stepFull = HOL`Bool`GEN[aV,
      HOL`Bool`DISCH[sihAtATm, stepInner]];
    (* (prime p) ⊢ ∀a. sihAtATm ⇒ predBodyAt[a] *)

    strongSpec = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]],
      HOL`Bool`SPEC[predLam, strongInductionThm]];
    mpStrong = HOL`Bool`MP[strongSpec, stepFull];
    (* (prime p) ⊢ ∀a. predBodyAt[a] *)

    specAB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, mpStrong]];
    (* (prime p) ⊢ divides p (a*b) ⇒ divides p a ∨ divides p b *)
    dischPrime = HOL`Bool`DISCH[primePTm, specAB];
    genB = HOL`Bool`GEN[bV, dischPrime];
    genA = HOL`Bool`GEN[aV, genB];
    genP = HOL`Bool`GEN[pV, genA]
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
        apP = HOL`Equal`APTHM[primeDefThm, nV];
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
        allTm[primeConst[], lV],
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
        allTm[primeConst[], lV],
        mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], nLocal]]];

      ihHypT = mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
        mkAbs[kV, impTm[ltN[kV, nLocal],
          impTm[notTm[mkEq[kV, zeroN[]]],
            existsListTm[lV, andTm[
              allTm[primeConst[], lV],
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

        allNilAtPrime = HOL`Bool`SPEC[primeConst[],
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
          apP = HOL`Equal`APTHM[primeDefThm, pV];
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
          allTm[primeConst[], lV],
          mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV], cV]];
        lHyp = ASSUME[lBody];
        allPrimeL = HOL`Bool`CONJUNCT1[lHyp];
        foldrLEqC = HOL`Bool`CONJUNCT2[lHyp];

        consPLTm = consNumApp[pV, lV];

        allConsAtPL = HOL`Bool`SPEC[lV, HOL`Bool`SPEC[pV,
          HOL`Bool`SPEC[primeConst[],
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
      apP = HOL`Equal`APTHM[primeDefThm, pV];
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
            euclidLemmaThm]]],
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

(* multEqZeroThm (∀m n. m*n=0 ⇒ m=0∨n=0) was a stage-3.d helper here;
   it is a fundamental ℕ fact and now lives in Num.wl. multLeftCancelThm
   below uses HOL`Stdlib`Num`multEqZeroThm. *)

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
        HOL`Bool`SPEC[bLocal, HOL`Bool`SPEC[xV, HOL`Stdlib`Num`multEqZeroThm]],
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
      ap = HOL`Equal`APTHM[primeDefThm, pV];
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
      ap = HOL`Equal`APTHM[primeDefThm, qV];
      TRANS[ap, BETACONV[concl[ap][[2]]]]];
    primeQApp = EQMP[primeUnfQ, primeQHyp];
    (* (prime q) ⊢ SUC 0 < q ∧ (∀d. d|q ⇒ d = SUC 0 ∨ d = q) *)
    allDClause = HOL`Bool`CONJUNCT2[primeQApp];
    atP = HOL`Bool`SPEC[pV, allDClause];
    (* ⊢ p | q ⇒ p = SUC 0 ∨ p = q *)
    mpDiv = HOL`Bool`MP[atP, divHyp];
    (* (prime q, p|q) ⊢ p = SUC 0 ∨ p = q *)

    primeUnfP = Module[{ap},
      ap = HOL`Equal`APTHM[primeDefThm, pV];
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
      impTm[allTm[primeConst[], lV],
        impTm[mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lV],
                   oneN[]],
              mkEq[lV, nilNumTm[]]]]];

    inductSpec = HOL`Bool`SPEC[predLam,
      INSTTYPE[{mkVarType["A"] -> numTy},
        HOL`Stdlib`List`listInductionThm]];
    inductBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], inductSpec];

    baseCase = Module[{allNilHyp, foldrHyp, refl, dischFold, dischAll},
      allNilHyp = ASSUME[allTm[primeConst[], nilNumTm[]]];
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

      ihHypT = impTm[allTm[primeConst[], lLoc],
        impTm[mkEq[foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], lLoc],
                   oneN[]],
              mkEq[lLoc, nilNumTm[]]]];
      ihHyp = ASSUME[ihHypT];

      allConsHyp = ASSUME[allTm[primeConst[],
        consNumApp[yV, lLoc]]];
      foldrEqHyp = ASSUME[mkEq[
        foldrTm[HOL`Stdlib`Num`timesConst[], oneN[], consNumApp[yV, lLoc]],
        oneN[]]];

      allConsAt = HOL`Bool`SPEC[lLoc, HOL`Bool`SPEC[yV,
        HOL`Bool`SPEC[primeConst[],
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

    allPrimePred[lt_] := allTm[primeConst[], lt];
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
          HOL`Bool`SPEC[primeConst[],
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
          primeConst[],
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
              primeConst[],
              INSTTYPE[{mkVarType["A"] -> numTy},
                HOL`Stdlib`List`allAppendThm]]]];
          (* ⊢ ALL prime (APPEND l2a (CONS x l2b))
                = ALL prime l2a ∧ ALL prime (CONS x l2b) *)
          allAppendConj = EQMP[allAppendAt, allL2InAppForm];
          allL2a = HOL`Bool`CONJUNCT1[allAppendConj];
          allConsRest = HOL`Bool`CONJUNCT2[allAppendConj];
          (* (…) ⊢ ALL prime (CONS x l2b) *)
          allConsAtV = HOL`Bool`SPEC[l2bV, HOL`Bool`SPEC[xLoc,
            HOL`Bool`SPEC[primeConst[],
              INSTTYPE[{mkVarType["A"] -> numTy},
                HOL`Stdlib`List`allConsThm]]]];
          allConsConj = EQMP[allConsAtV, allConsRest];
          allL2b = HOL`Bool`CONJUNCT2[allConsConj];

          (* Build ALL prime (APPEND l2a l2b) via SYM of allAppend at l2b *)
          allAppendL2aL2bThm = Module[{appAtV2, conjV},
            appAtV2 = HOL`Bool`SPEC[l2bV, HOL`Bool`SPEC[l2aV,
              HOL`Bool`SPEC[primeConst[],
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


(* ============================================================ *)
(* gcd / divisibility / coprime number theory (migrated from    *)
(* Rat.wl 2026-06). Pure ℕ facts that depend on multLeftCancel- *)
(* Thm / dividesPosThm (above) and Num's exDiv; only Rat        *)
(* consumes them and Rat imports FTA. The helper aliases below   *)
(* bridge the migrated proofs' term-builder vocabulary onto      *)
(* FTA/Num constructors.                                        *)
(* ============================================================ *)

plusTm[a_, b_]     := plusN[a, b];
ltTmR[a_, b_]      := ltN[a, b];
implTm[a_, b_]     := impTm[a, b];
orTmR[a_, b_]      := orTm[a, b];
plusC[]            := HOL`Stdlib`Num`plusConst[];
divTmR[a_, b_]     := mkComb[mkComb[HOL`Stdlib`Num`divConst[], a], b];
modTmR[a_, b_]     := mkComb[mkComb[HOL`Stdlib`Num`modConst[], a], b];
dividesHead[d_]    := mkComb[HOL`Stdlib`Num`dividesConst[], d];
exDivTm[nT_, gT_]  := mkComb[mkComb[HOL`Stdlib`Num`exDivConst[], nT], gT];
existsCR[ty_]      := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];
existsTmR[v_, body_] := mkComb[existsCR[typeOf[v]], mkAbs[v, body]];
forallTm[v_, body_]  := mkComb[mkConst["∀", tyFun[tyFun[typeOf[v], boolTy], boolTy]], mkAbs[v, body]];

(* ⊢ ∀n. divides 0 n ⇒ n = 0 *)
dividesZeroImpZeroThm =
  Module[{nV, cV, hyp, exThm, bodyAssume, zc, nEq0, chosen},
    nV = mkVar["n", numTy]; cV = mkVar["c", numTy];
    hyp = ASSUME[dividesTm[zeroN[], nV]];
    exThm = EQMP[unfoldDivides[zeroN[], nV], hyp];             (* ∃c. n = 0 * c *)
    bodyAssume = ASSUME[mkEq[nV, timesTm[zeroN[], cV]]];       (* n = 0 * c *)
    zc = HOL`Bool`SPEC[cV, HOL`Stdlib`Num`timesLeftZeroThm];   (* 0 * c = 0 *)
    nEq0 = TRANS[bodyAssume, zc];                              (* n = 0 *)
    chosen = HOL`Bool`CHOOSE[cV, exThm, nEq0];                 (* ⊢ n = 0 (hyp divides 0 n) *)
    HOL`Bool`GEN[nV, HOL`Bool`DISCH[dividesTm[zeroN[], nV], chosen]]
  ];

oneNotZeroThm = HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`sucNotZeroThm];  (* ¬(SUC 0 = 0) *)


(* ⊢ ∀d. divides d (SUC 0) ⇒ d = SUC 0 *)
(* d ≤ SUC 0 (dividesLeq) and SUC 0 ≤ d (d ≠ 0, since 0 ∤ SUC 0) → leqAntisym. *)
dividesOneThm =
  Module[{dV, hyp, leqStep, dEq0, hSubst, divZeroSuc, falseThm, dischFalse,
          notDEq0, posD, sucLeqD, dd},
    dV = mkVar["d", numTy];
    hyp = ASSUME[dividesTm[dV, oneN[]]];                       (* divides d (SUC 0) *)
    leqStep = HOL`Bool`MP[
      HOL`Bool`MP[
        HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[dV, HOL`Stdlib`Num`dividesLeqThm]],
        oneNotZeroThm],
      hyp];                                                    (* d ≤ SUC 0 *)
    dEq0 = ASSUME[mkEq[dV, zeroN[]]];                          (* d = 0 *)
    hSubst = HOL`Drule`SUBS[{dEq0}, hyp];                      (* divides 0 (SUC 0) *)
    divZeroSuc = HOL`Bool`MP[
      HOL`Bool`SPEC[oneN[], dividesZeroImpZeroThm], hSubst];   (* SUC 0 = 0 *)
    falseThm = HOL`Bool`MP[HOL`Bool`NOTELIM[oneNotZeroThm], divZeroSuc];  (* F *)
    dischFalse = HOL`Bool`DISCH[mkEq[dV, zeroN[]], falseThm];  (* (d=0) ⇒ F *)
    notDEq0 = HOL`Bool`NOTINTRO[dischFalse];                   (* ¬(d = 0) *)
    posD = HOL`Bool`MP[HOL`Bool`SPEC[dV, HOL`Stdlib`Num`ltZeroNotZeroThm], notDEq0]; (* 0 < d *)
    sucLeqD = EQMP[unfoldLt[zeroN[], dV], posD];               (* SUC 0 ≤ d *)
    dd = HOL`Bool`MP[
      HOL`Bool`MP[HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[dV, HOL`Stdlib`Num`leqAntisymThm]],
        leqStep],
      sucLeqD];                                                (* d = SUC 0 *)
    HOL`Bool`GEN[dV, HOL`Bool`DISCH[dividesTm[dV, oneN[]], dd]]
  ];

(* ⊢ ∀a. gcd a (SUC 0) = SUC 0 *)
gcdOneRightThm =
  Module[{aV, gdiv, eq},
    aV = mkVar["a", numTy];
    gdiv = HOL`Bool`SPEC[oneN[],
      HOL`Bool`SPEC[aV, gcdDividesRightThm]];  (* divides (gcd a 1) 1 *)
    eq = HOL`Bool`MP[HOL`Bool`SPEC[gcdTm[aV, oneN[]], dividesOneThm], gdiv];
    HOL`Bool`GEN[aV, eq]                                      (* gcd a 1 = 1 *)
  ];

(* ⊢ ∀g h x. divides h x ⇒ divides (g * h) (g * x) *)
dividesMultBothLeftThm =
  Module[{gV, hV, xV, cV, hyp, exTh, cBody, apG, assocSym, gxEq,
          existsTm, exC, chosen, folded},
    gV = mkVar["g", numTy]; hV = mkVar["h", numTy]; xV = mkVar["x", numTy];
    cV = mkVar["c", numTy];
    hyp = ASSUME[dividesTm[hV, xV]];                    (* divides h x *)
    exTh = EQMP[unfoldDivides[hV, xV], hyp];            (* ∃c. x = h * c *)
    cBody = ASSUME[mkEq[xV, timesTm[hV, cV]]];          (* x = h * c *)
    apG = HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], gV], cBody]; (* g*x = g*(h*c) *)
    assocSym = HOL`Equal`SYM[
      HOL`Bool`SPEC[cV, HOL`Bool`SPEC[hV, HOL`Bool`SPEC[gV,
        HOL`Stdlib`Num`timesAssocThm]]]];               (* g*(h*c) = (g*h)*c *)
    gxEq = TRANS[apG, assocSym];                        (* g*x = (g*h)*c *)
    existsTm = concl[unfoldDivides[timesTm[gV, hV], timesTm[gV, xV]]][[2]]; (* ∃c. g*x = (g*h)*c *)
    exC = HOL`Bool`EXISTS[existsTm, cV, gxEq];
    chosen = HOL`Bool`CHOOSE[cV, exTh, exC];            (* divides h x ⊢ ∃c. g*x=(g*h)*c *)
    folded = EQMP[
      HOL`Equal`SYM[unfoldDivides[timesTm[gV, hV], timesTm[gV, xV]]], chosen];
    HOL`Bool`GEN[gV, HOL`Bool`GEN[hV, HOL`Bool`GEN[xV,
      HOL`Bool`DISCH[dividesTm[hV, xV], folded]]]]
  ];

(* ⊢ ∀a b. ¬ (b = 0) ⇒ ¬ (gcd a b = 0) *)
gcdNonzeroFromRightThm =
  Module[{aV, bV, gTm, notB0, gB, posInst, notG0},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    gTm = gcdTm[aV, bV];
    notB0 = ASSUME[notTm[mkEq[bV, zeroN[]]]];           (* ¬(b = 0) *)
    gB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdDividesRightThm]]; (* divides (gcd a b) b *)
    posInst = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[gTm, HOL`Stdlib`FTA`dividesPosThm]];
                                                        (* ¬(b=0) ⇒ divides (gcd a b) b ⇒ ¬(gcd a b=0) *)
    notG0 = HOL`Bool`MP[HOL`Bool`MP[posInst, notB0], gB];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[notTm[mkEq[bV, zeroN[]]], notG0]]]
  ];

(* ⊢ ∀a b. ¬ (gcd a b = 0) ⇒ gcd (exDiv a (gcd a b)) (exDiv b (gcd a b)) = SUC 0 *)
coprimeReducedThm =
  Module[{aV, bV, gTm, notG0, gA, gB, aEq, bEq, qaTm, qbTm, hTm,
          hA, hB, ghDivA0, ghDivA, ghDivB0, ghDivB, ghDivG, exK, kV,
          kBody, assocHK, gEqGhk, gTimesOne, gOneEqGhk, cancelInst,
          suc0EqHk, existsH1, divH1, hEqOne, chosen},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    gTm = gcdTm[aV, bV];
    notG0 = ASSUME[notTm[mkEq[gTm, zeroN[]]]];          (* ¬(gcd a b = 0) *)
    gA = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdDividesLeftThm]];  (* divides (gcd a b) a *)
    gB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdDividesRightThm]]; (* divides (gcd a b) b *)
    aEq = HOL`Bool`MP[HOL`Bool`SPEC[aV, HOL`Bool`SPEC[gTm, exDivThm]], gA];  (* a = gcd a b * exDiv a (gcd a b) *)
    bEq = HOL`Bool`MP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[gTm, exDivThm]], gB];
    qaTm = exDivTm[aV, gTm]; qbTm = exDivTm[bV, gTm];
    hTm = gcdTm[qaTm, qbTm];
    hA = HOL`Bool`SPEC[qbTm, HOL`Bool`SPEC[qaTm, gcdDividesLeftThm]];  (* divides h qa *)
    hB = HOL`Bool`SPEC[qbTm, HOL`Bool`SPEC[qaTm, gcdDividesRightThm]]; (* divides h qb *)
    ghDivA0 = HOL`Bool`MP[
      HOL`Bool`SPEC[qaTm, HOL`Bool`SPEC[hTm, HOL`Bool`SPEC[gTm, dividesMultBothLeftThm]]], hA];
                                                        (* divides (gcd a b * h) (gcd a b * qa) *)
    ghDivA = HOL`Drule`SUBS[{HOL`Equal`SYM[aEq]}, ghDivA0];   (* divides (gcd a b * h) a *)
    ghDivB0 = HOL`Bool`MP[
      HOL`Bool`SPEC[qbTm, HOL`Bool`SPEC[hTm, HOL`Bool`SPEC[gTm, dividesMultBothLeftThm]]], hB];
    ghDivB = HOL`Drule`SUBS[{HOL`Equal`SYM[bEq]}, ghDivB0];   (* divides (gcd a b * h) b *)
    ghDivG = HOL`Bool`MP[
      HOL`Bool`SPEC[timesTm[gTm, hTm],
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdUniversalThm]]],
      HOL`Bool`CONJ[ghDivA, ghDivB]];                   (* divides (gcd a b * h) (gcd a b) *)
    exK = EQMP[unfoldDivides[timesTm[gTm, hTm], gTm], ghDivG];  (* ∃k. gcd a b = (gcd a b * h) * k *)
    kV = mkVar["k", numTy];
    kBody = ASSUME[mkEq[gTm, timesTm[timesTm[gTm, hTm], kV]]];  (* gcd a b = (gcd a b * h) * k *)
    assocHK = HOL`Bool`SPEC[kV, HOL`Bool`SPEC[hTm, HOL`Bool`SPEC[gTm,
      HOL`Stdlib`Num`timesAssocThm]]];                  (* (gcd a b * h) * k = gcd a b * (h * k) *)
    gEqGhk = TRANS[kBody, assocHK];                     (* gcd a b = gcd a b * (h * k) *)
    gTimesOne = TRANS[
      HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[gTm, HOL`Stdlib`Num`timesCommThm]],
      HOL`Bool`SPEC[gTm, HOL`Stdlib`Num`oneTimesEqThm]];  (* gcd a b * SUC 0 = gcd a b *)
    gOneEqGhk = TRANS[gTimesOne, gEqGhk];               (* gcd a b * SUC 0 = gcd a b * (h * k) *)
    cancelInst = HOL`Bool`SPEC[timesTm[hTm, kV], HOL`Bool`SPEC[oneN[],
      HOL`Bool`MP[HOL`Bool`SPEC[gTm, HOL`Stdlib`FTA`multLeftCancelThm], notG0]]];
                                                        (* gcd a b * SUC 0 = gcd a b * (h*k) ⇒ SUC 0 = h*k *)
    suc0EqHk = HOL`Bool`MP[cancelInst, gOneEqGhk];      (* SUC 0 = h * k *)
    existsH1 = concl[unfoldDivides[hTm, oneN[]]][[2]];  (* ∃k. SUC 0 = h * k *)
    divH1 = EQMP[HOL`Equal`SYM[unfoldDivides[hTm, oneN[]]],
      HOL`Bool`EXISTS[existsH1, kV, suc0EqHk]];         (* divides h (SUC 0) *)
    hEqOne = HOL`Bool`MP[HOL`Bool`SPEC[hTm, dividesOneThm], divH1];  (* h = SUC 0 *)
    chosen = HOL`Bool`CHOOSE[kV, exK, hEqOne];          (* ¬(gcd a b=0) ⊢ h = SUC 0 *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[notTm[mkEq[gTm, zeroN[]]], chosen]]]
  ];

(* ⊢ ∀a b. divides a b ⇒ divides b a ⇒ a = b *)
dividesAntisymThm =
  Module[{aV, bV, hAB, hBA, em, caseB0, caseBnz, result},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    hAB = ASSUME[dividesTm[aV, bV]];
    hBA = ASSUME[dividesTm[bV, aV]];
    em = HOL`Bool`EXCLUDEDMIDDLE[mkEq[bV, zeroN[]]];
    caseB0 = Module[{hB0, div0a, aEq0},
      hB0 = ASSUME[mkEq[bV, zeroN[]]];
      div0a = HOL`Drule`SUBS[{hB0}, hBA];                 (* divides 0 a *)
      aEq0 = HOL`Bool`MP[HOL`Bool`SPEC[aV, dividesZeroImpZeroThm], div0a];  (* a = 0 *)
      TRANS[aEq0, HOL`Equal`SYM[hB0]]];                   (* a = b *)
    caseBnz = Module[{hBnz, aLeqB, notA0, bLeqA},
      hBnz = ASSUME[notTm[mkEq[bV, zeroN[]]]];
      aLeqB = HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesLeqThm]], hBnz], hAB]; (* a ≤ b *)
      notA0 = Module[{hA0, div0b, bEq0, falseTh},
        hA0 = ASSUME[mkEq[aV, zeroN[]]];
        div0b = HOL`Drule`SUBS[{hA0}, hAB];               (* divides 0 b *)
        bEq0 = HOL`Bool`MP[HOL`Bool`SPEC[bV, dividesZeroImpZeroThm], div0b];  (* b = 0 *)
        falseTh = HOL`Bool`MP[HOL`Bool`NOTELIM[hBnz], bEq0];
        HOL`Bool`NOTINTRO[HOL`Bool`DISCH[mkEq[aV, zeroN[]], falseTh]]];      (* ¬(a = 0) *)
      bLeqA = HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`dividesLeqThm]], notA0], hBA]; (* b ≤ a *)
      HOL`Bool`MP[HOL`Bool`MP[
        HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`leqAntisymThm]], aLeqB], bLeqA]]; (* a = b *)
    result = HOL`Bool`DISJCASES[em, caseB0, caseBnz];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[dividesTm[aV, bV], HOL`Bool`DISCH[dividesTm[bV, aV], result]]]]
  ];

(* ⊢ ∀a. gcd a 0 = a *)
gcdZeroRightThm =
  Module[{aV, gTm, gDivA, aDivA, aDiv0, aDivG, eq},
    aV = mkVar["a", numTy];
    gTm = gcdTm[aV, zeroN[]];
    gDivA = HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[aV, gcdDividesLeftThm]];  (* divides (gcd a 0) a *)
    aDivA = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesReflThm];   (* divides a a *)
    aDiv0 = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesZeroThm];   (* divides a 0 *)
    aDivG = HOL`Bool`MP[
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[aV, gcdUniversalThm]]],
      HOL`Bool`CONJ[aDivA, aDiv0]];                            (* divides a (gcd a 0) *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[gTm, dividesAntisymThm]], gDivA], aDivG];  (* gcd a 0 = a *)
    HOL`Bool`GEN[aV, eq]
  ];

(*   `a` also occurs inside gcd a b.                                  *)
gcdRecThm =
  Module[{aV, bV, notB0, qTm, rTm, bqTm, divPair, aEq, g1, g2,
          g1DivA, g1DivB, g1DivBq, g1DivBqR, g1DivR, g1Divg2,
          g2DivB, g2DivR, g2DivBq, g2DivBqR, g2DivA, g2Divg1, eq},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    notB0 = ASSUME[notTm[mkEq[bV, zeroN[]]]];
    qTm = divTmR[aV, bV]; rTm = modTmR[aV, bV]; bqTm = timesTm[bV, qTm];
    divPair = HOL`Bool`MP[
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`divisionPairThm]], notB0];
    aEq = HOL`Bool`CONJUNCT1[divPair];                    (* a = b*q + r *)
    g1 = gcdTm[aV, bV]; g2 = gcdTm[bV, rTm];
    g1DivA = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdDividesLeftThm]];   (* g1 | a *)
    g1DivB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdDividesRightThm]];  (* g1 | b *)
    g1DivBq = HOL`Bool`MP[HOL`Bool`SPEC[qTm, HOL`Bool`SPEC[bV,
      HOL`Bool`SPEC[g1, HOL`Stdlib`Num`dividesMultRightThm]]], g1DivB];  (* g1 | (b*q) *)
    g1DivBqR = EQMP[HOL`Equal`APTERM[dividesHead[g1], aEq], g1DivA];     (* g1 | (b*q + r) *)
    g1DivR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bqTm,
      HOL`Bool`SPEC[g1, HOL`Stdlib`Num`dividesAddRightThm]]], g1DivBq], g1DivBqR];  (* g1 | r *)
    g1Divg2 = HOL`Bool`MP[HOL`Bool`SPEC[g1, HOL`Bool`SPEC[rTm,
      HOL`Bool`SPEC[bV, gcdUniversalThm]]],
      HOL`Bool`CONJ[g1DivB, g1DivR]];                     (* g1 | gcd b r *)
    g2DivB = HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bV, gcdDividesLeftThm]];   (* g2 | b *)
    g2DivR = HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bV, gcdDividesRightThm]];  (* g2 | r *)
    g2DivBq = HOL`Bool`MP[HOL`Bool`SPEC[qTm, HOL`Bool`SPEC[bV,
      HOL`Bool`SPEC[g2, HOL`Stdlib`Num`dividesMultRightThm]]], g2DivB];  (* g2 | (b*q) *)
    g2DivBqR = HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[rTm, HOL`Bool`SPEC[bqTm,
      HOL`Bool`SPEC[g2, HOL`Stdlib`Num`dividesAddThm]]], g2DivBq], g2DivR];  (* g2 | (b*q + r) *)
    g2DivA = EQMP[HOL`Equal`APTERM[dividesHead[g2], HOL`Equal`SYM[aEq]], g2DivBqR]; (* g2 | a *)
    g2Divg1 = HOL`Bool`MP[HOL`Bool`SPEC[g2, HOL`Bool`SPEC[bV,
      HOL`Bool`SPEC[aV, gcdUniversalThm]]],
      HOL`Bool`CONJ[g2DivA, g2DivB]];                     (* g2 | gcd a b *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[g2, HOL`Bool`SPEC[g1, dividesAntisymThm]], g1Divg2], g2Divg1];  (* g1 = g2 *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`DISCH[notTm[mkEq[bV, zeroN[]]], eq]]]
  ];

(*     g rewritten to gcd a b via gcdRec. No monus anywhere.             *)
bezoutNatThm =
  Module[{aV, bV, kV, xV, yV, aInner, disjAt, bezBody, pLam, specInd,
          specBeta, stepAnte, mainConcl},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; kV = mkVar["k", numTy];
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy]; aInner = mkVar["a", numTy];

    disjAt[aT_, nT_, xT_, yT_] := orTmR[
      mkEq[timesTm[aT, xT], plusTm[timesTm[nT, yT], gcdTm[aT, nT]]],
      mkEq[timesTm[nT, yT], plusTm[timesTm[aT, xT], gcdTm[aT, nT]]]];
    bezBody[aT_, nT_] := existsTmR[xV, existsTmR[yV, disjAt[aT, nT, xV, yV]]];

    pLam = mkAbs[bV, forallTm[aInner, bezBody[aInner, bV]]];
    specInd = HOL`Bool`ISPEC[pLam, HOL`Stdlib`Num`strongInductionThm];
    specBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specInd];

    stepAnte = Module[{nLoc, gN, exInnerTm, goalTm, ihHypTm, ihHyp,
                       em, case0, caseNZ, pnAtA, pnBody},
      nLoc = mkVar["b", numTy];
      gN = gcdTm[aInner, nLoc];
      exInnerTm[xT_] := existsTmR[yV, disjAt[aInner, nLoc, xT, yV]];
      goalTm = bezBody[aInner, nLoc];
      ihHypTm = forallTm[kV, implTm[ltTmR[kV, nLoc],
        forallTm[aInner, bezBody[aInner, kV]]]];
      ihHyp = ASSUME[ihHypTm];

      case0 = Module[{hN0, lhsStep1, a0eq, lhsStep2, addLeftZeroEq, lhsEq,
                      n0Eq, gcdAnEq, rhsStep1, rhsChain, firstDisjEq, disj, exY},
        hN0 = ASSUME[mkEq[nLoc, zeroN[]]];                      (* b = 0 *)
        lhsStep1 = HOL`Bool`SPEC[zeroN[], HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`timesSucEqThm]];
        a0eq = HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`timesZeroEqThm];
        lhsStep2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], a0eq], REFL[aInner]];
        addLeftZeroEq = HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`addLeftZeroThm];
        lhsEq = TRANS[lhsStep1, TRANS[lhsStep2, addLeftZeroEq]];  (* a*(SUC 0) = a *)
        n0Eq = HOL`Bool`SPEC[nLoc, HOL`Stdlib`Num`timesZeroEqThm];  (* b*0 = 0 *)
        gcdAnEq = TRANS[
          HOL`Equal`APTERM[mkComb[gcdConst[], aInner], hN0],
          HOL`Bool`SPEC[aInner, gcdZeroRightThm]];             (* gcd a b = a *)
        rhsStep1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], n0Eq], gcdAnEq];
        rhsChain = TRANS[rhsStep1, addLeftZeroEq];             (* b*0 + gcd a b = a *)
        firstDisjEq = TRANS[lhsEq, HOL`Equal`SYM[rhsChain]];   (* a*(SUC 0) = b*0 + gcd a b *)
        disj = HOL`Bool`DISJ1[firstDisjEq,
          mkEq[timesTm[nLoc, zeroN[]], plusTm[timesTm[aInner, oneN[]], gN]]];
        exY = HOL`Bool`EXISTS[exInnerTm[oneN[]], zeroN[], disj];
        HOL`Bool`EXISTS[goalTm, oneN[], exY]];

      caseNZ = Module[{hNnz, divPair, aEqDiv, rLtN, gRec, ihAtR, ihInst,
                       qN, rN, gR, bqTmN, x0V, y0V, bTimesQy0, rTimesY0,
                       bTimesX0, aTimesY0, ywit, bTimesYwit, step1, step2,
                       step2b, ay0Eq, distribLeftInst, distribN, caseA, caseB,
                       ihInnerYtm, gFromBody, chooseY, firstDisjTermA,
                       secondDisjTermA},
        hNnz = ASSUME[notTm[mkEq[nLoc, zeroN[]]]];
        divPair = HOL`Bool`MP[
          HOL`Bool`SPEC[nLoc, HOL`Bool`SPEC[aInner, HOL`Stdlib`Num`divisionPairThm]], hNnz];
        aEqDiv = HOL`Bool`CONJUNCT1[divPair];                  (* a = b*q + r *)
        rLtN = HOL`Bool`CONJUNCT2[divPair];                    (* (a MOD b) < b *)
        qN = divTmR[aInner, nLoc]; rN = modTmR[aInner, nLoc];
        gR = gcdTm[nLoc, rN]; bqTmN = timesTm[nLoc, qN];
        gRec = HOL`Bool`MP[
          HOL`Bool`SPEC[nLoc, HOL`Bool`SPEC[aInner, gcdRecThm]], hNnz];  (* gcd a b = gcd b r *)
        ihAtR = HOL`Bool`MP[HOL`Bool`SPEC[rN, ihHyp], rLtN];   (* ∀a. bezBody[a, r] *)
        ihInst = HOL`Bool`SPEC[nLoc, ihAtR];                   (* bezBody[b, r] *)
        x0V = mkVar["x0", numTy]; y0V = mkVar["y0", numTy];
        bTimesQy0 = timesTm[nLoc, timesTm[qN, y0V]];           (* b*(q*y0) *)
        rTimesY0  = timesTm[rN, y0V];                          (* r*y0 *)
        bTimesX0  = timesTm[nLoc, x0V];                        (* b*x0 *)
        aTimesY0  = timesTm[aInner, y0V];                      (* a*y0 *)
        ywit      = plusTm[timesTm[qN, y0V], x0V];             (* q*y0 + x0 *)
        bTimesYwit = timesTm[nLoc, ywit];                      (* b*(q*y0 + x0) *)
        firstDisjTermA  = mkEq[aTimesY0, plusTm[bTimesYwit, gN]];  (* a*y0 = b*Y + gcd a b *)
        secondDisjTermA = mkEq[bTimesYwit, plusTm[aTimesY0, gN]];  (* b*Y = a*y0 + gcd a b *)
        step1 = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], aEqDiv], y0V];
                                                               (* a*y0 = (b*q + r)*y0 *)
        step2 = HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[rN,
          HOL`Bool`SPEC[bqTmN, HOL`Stdlib`Num`timesDistribRightThm]]];
                                                               (* (b*q + r)*y0 = (b*q)*y0 + r*y0 *)
        step2b = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[],
            HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[qN, HOL`Bool`SPEC[nLoc, HOL`Stdlib`Num`timesAssocThm]]]],
          REFL[rTimesY0]];                                     (* (b*q)*y0 + r*y0 = b*(q*y0) + r*y0 *)
        ay0Eq = TRANS[step1, TRANS[step2, step2b]];            (* a*y0 = b*(q*y0) + r*y0 *)
        distribLeftInst = HOL`Bool`SPEC[x0V, HOL`Bool`SPEC[timesTm[qN, y0V],
          HOL`Bool`SPEC[nLoc, HOL`Stdlib`Num`timesDistribLeftThm]]];
        distribN = HOL`Equal`SYM[distribLeftInst];             (* b*(q*y0) + b*x0 = b*(q*y0+x0) *)

        caseA = Module[{hyp, e1, e2, e3, caseAeq, secondDisjProof, cdisj, exY},
          hyp = ASSUME[mkEq[bTimesX0, plusTm[rTimesY0, gR]]];  (* b*x0 = r*y0 + g *)
          e1 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], ay0Eq], REFL[gR]];
          e2 = HOL`Bool`SPEC[gR, HOL`Bool`SPEC[rTimesY0,
            HOL`Bool`SPEC[bTimesQy0, HOL`Stdlib`Num`addAssocThm]]];
          e3 = HOL`Kernel`MKCOMB[
            HOL`Equal`APTERM[plusC[], REFL[bTimesQy0]], HOL`Equal`SYM[hyp]];
          caseAeq = TRANS[e1, TRANS[e2, TRANS[e3, distribN]]];  (* (a*y0)+g = b*(q*y0+x0) *)
          secondDisjProof = TRANS[HOL`Equal`SYM[caseAeq],
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[aTimesY0]], HOL`Equal`SYM[gRec]]];
          cdisj = HOL`Bool`DISJ2[secondDisjProof, firstDisjTermA];
          exY = HOL`Bool`EXISTS[exInnerTm[y0V], ywit, cdisj];
          HOL`Bool`EXISTS[goalTm, y0V, exY]];

        caseB = Module[{hyp, f2, f3, caseBeqG, firstDisjProof, cdisj, exY},
          hyp = ASSUME[mkEq[rTimesY0, plusTm[bTimesX0, gR]]];  (* r*y0 = b*x0 + g *)
          f2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[bTimesQy0]], hyp];
          f3 = HOL`Equal`SYM[HOL`Bool`SPEC[gR, HOL`Bool`SPEC[bTimesX0,
            HOL`Bool`SPEC[bTimesQy0, HOL`Stdlib`Num`addAssocThm]]]];
          caseBeqG = TRANS[ay0Eq, TRANS[f2, TRANS[f3,
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], distribN], REFL[gR]]]]];
                                                               (* a*y0 = b*(q*y0+x0) + g *)
          firstDisjProof = TRANS[caseBeqG,
            HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[bTimesYwit]], HOL`Equal`SYM[gRec]]];
          cdisj = HOL`Bool`DISJ1[firstDisjProof, secondDisjTermA];
          exY = HOL`Bool`EXISTS[exInnerTm[y0V], ywit, cdisj];
          HOL`Bool`EXISTS[goalTm, y0V, exY]];

        ihInnerYtm = existsTmR[yV, disjAt[nLoc, rN, x0V, yV]];
        gFromBody = HOL`Bool`DISJCASES[
          ASSUME[disjAt[nLoc, rN, x0V, y0V]], caseA, caseB];
        chooseY = HOL`Bool`CHOOSE[y0V, ASSUME[ihInnerYtm], gFromBody];
        HOL`Bool`CHOOSE[x0V, ihInst, chooseY]];

      em = HOL`Bool`EXCLUDEDMIDDLE[mkEq[nLoc, zeroN[]]];
      pnAtA = HOL`Bool`DISJCASES[em, case0, caseNZ];           (* bezBody[a,b], hyp {ihHypTm} *)
      pnBody = HOL`Bool`GEN[aInner, pnAtA];                    (* ∀a. bezBody[a,b] *)
      HOL`Bool`GEN[nLoc, HOL`Bool`DISCH[ihHypTm, pnBody]]
    ];

    mainConcl = HOL`Bool`MP[specBeta, stepAnte];               (* ∀b. ∀a. bezBody[a,b] *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV,
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, mainConcl]]]]
  ];

(* (= a | (b*y0)*c) to peel c off with dividesAddRight.                    *)
coprimeDividesProductThm =
  Module[{aV, bV, cV, xV, yV, x0V, y0V, oneN1, gab, bc, ax0, by0, x0c, axc,
          by0c, disjAtXY, gcdEq1, aDivBc, bez, aDivA, aDivAxc, aDivBcy0,
          bycEq1, bycEq2, bycEq3, bycEq, aDivBy0c, disj1Tm, disj2Tm,
          disjBodyTm, case1, case2, innerProof, exYtm, chooseY, chooseX},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    x0V = mkVar["x0", numTy]; y0V = mkVar["y0", numTy];
    oneN1 = oneN[]; gab = gcdTm[aV, bV]; bc = timesTm[bV, cV];
    ax0 = timesTm[aV, x0V]; by0 = timesTm[bV, y0V];
    x0c = timesTm[x0V, cV]; axc = timesTm[aV, x0c]; by0c = timesTm[by0, cV];
    disjAtXY[xT_, yT_] := orTmR[
      mkEq[timesTm[aV, xT], plusTm[timesTm[bV, yT], gab]],
      mkEq[timesTm[bV, yT], plusTm[timesTm[aV, xT], gab]]];
    gcdEq1 = ASSUME[mkEq[gab, oneN1]];                  (* gcd a b = SUC 0 *)
    aDivBc = ASSUME[dividesTm[aV, bc]];                 (* divides a (b*c) *)
    bez = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, bezoutNatThm]];

    aDivA = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesReflThm];        (* divides a a *)
    aDivAxc = HOL`Bool`MP[HOL`Bool`SPEC[x0c, HOL`Bool`SPEC[aV,
      HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesMultRightThm]]], aDivA];  (* a | a*(x0*c) *)
    aDivBcy0 = HOL`Bool`MP[HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[bc,
      HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesMultRightThm]]], aDivBc]; (* a | (b*c)*y0 *)
    bycEq1 = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`timesAssocThm]]];
                                                        (* (b*y0)*c = b*(y0*c) *)
    bycEq2 = HOL`Equal`APTERM[mkComb[HOL`Stdlib`Num`timesConst[], bV],
      HOL`Bool`SPEC[cV, HOL`Bool`SPEC[y0V, HOL`Stdlib`Num`timesCommThm]]];  (* b*(y0*c) = b*(c*y0) *)
    bycEq3 = HOL`Equal`SYM[HOL`Bool`SPEC[y0V, HOL`Bool`SPEC[cV, HOL`Bool`SPEC[bV, HOL`Stdlib`Num`timesAssocThm]]]];
                                                        (* b*(c*y0) = (b*c)*y0 *)
    bycEq = TRANS[bycEq1, TRANS[bycEq2, bycEq3]];       (* (b*y0)*c = (b*c)*y0 *)
    aDivBy0c = EQMP[HOL`Equal`APTERM[dividesHead[aV], HOL`Equal`SYM[bycEq]], aDivBcy0]; (* a | (b*y0)*c *)

    disj1Tm = mkEq[ax0, plusTm[by0, gab]];
    disj2Tm = mkEq[by0, plusTm[ax0, gab]];
    disjBodyTm = orTmR[disj1Tm, disj2Tm];

    case1 = Module[{d1, caseEq1, l1, l2, l3, l4, axcEq, aDivBycC},
      d1 = ASSUME[disj1Tm];                             (* a*x0 = b*y0 + gab *)
      caseEq1 = TRANS[d1,
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[by0]], gcdEq1]];  (* a*x0 = b*y0 + SUC 0 *)
      l1 = HOL`Equal`SYM[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[x0V, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`timesAssocThm]]]];
                                                        (* a*(x0*c) = (a*x0)*c *)
      l2 = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], caseEq1], cV];
                                                        (* (a*x0)*c = (b*y0+SUC0)*c *)
      l3 = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[oneN1, HOL`Bool`SPEC[by0, HOL`Stdlib`Num`timesDistribRightThm]]];
                                                        (* (b*y0+SUC0)*c = (b*y0)*c + (SUC0)*c *)
      l4 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[by0c]],
        HOL`Bool`SPEC[cV, HOL`Stdlib`Num`oneTimesEqThm]];  (* (b*y0)*c + (SUC0)*c = (b*y0)*c + c *)
      axcEq = TRANS[l1, TRANS[l2, TRANS[l3, l4]]];      (* a*(x0*c) = (b*y0)*c + c *)
      aDivBycC = EQMP[HOL`Equal`APTERM[dividesHead[aV], axcEq], aDivAxc];  (* a | ((b*y0)*c + c) *)
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[by0c,
        HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesAddRightThm]]], aDivBy0c], aDivBycC]];  (* a | c *)

    case2 = Module[{d2, caseEq2, m1, m2, m3, byccEq, aDivAxcC},
      d2 = ASSUME[disj2Tm];                             (* b*y0 = a*x0 + gab *)
      caseEq2 = TRANS[d2,
        HOL`Kernel`MKCOMB[HOL`Equal`APTERM[plusC[], REFL[ax0]], gcdEq1]];  (* b*y0 = a*x0 + SUC 0 *)
      m1 = HOL`Equal`APTHM[HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], caseEq2], cV];
                                                        (* (b*y0)*c = (a*x0+SUC0)*c *)
      m2 = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[oneN1, HOL`Bool`SPEC[ax0, HOL`Stdlib`Num`timesDistribRightThm]]];
                                                        (* (a*x0+SUC0)*c = (a*x0)*c + (SUC0)*c *)
      m3 = HOL`Kernel`MKCOMB[
        HOL`Equal`APTERM[plusC[],
          HOL`Bool`SPEC[cV, HOL`Bool`SPEC[x0V, HOL`Bool`SPEC[aV, HOL`Stdlib`Num`timesAssocThm]]]],
        HOL`Bool`SPEC[cV, HOL`Stdlib`Num`oneTimesEqThm]];  (* (a*x0)*c + (SUC0)*c = a*(x0*c) + c *)
      byccEq = TRANS[m1, TRANS[m2, m3]];                (* (b*y0)*c = a*(x0*c) + c *)
      aDivAxcC = EQMP[HOL`Equal`APTERM[dividesHead[aV], byccEq], aDivBy0c];  (* a | (a*(x0*c) + c) *)
      HOL`Bool`MP[HOL`Bool`MP[HOL`Bool`SPEC[cV, HOL`Bool`SPEC[axc,
        HOL`Bool`SPEC[aV, HOL`Stdlib`Num`dividesAddRightThm]]], aDivAxc], aDivAxcC]];  (* a | c *)

    innerProof = HOL`Bool`DISJCASES[ASSUME[disjBodyTm], case1, case2];  (* a | c *)
    exYtm = existsTmR[yV, disjAtXY[x0V, yV]];
    chooseY = HOL`Bool`CHOOSE[y0V, ASSUME[exYtm], innerProof];
    chooseX = HOL`Bool`CHOOSE[x0V, bez, chooseY];      (* a | c, hyps {gcd a b=1, a|(b*c)} *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV,
      HOL`Bool`DISCH[mkEq[gab, oneN1],
        HOL`Bool`DISCH[dividesTm[aV, bc], chooseX]]]]]
  ];

(* ⊢ ∀a b. gcd a b = gcd b a *)
gcdCommThm =
  Module[{aV, bV, gAB, gBA, abDivA, abDivB, abDivBA, baDivA, baDivB, baDivAB, eq},
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    gAB = gcdTm[aV, bV]; gBA = gcdTm[bV, aV];
    abDivA = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdDividesLeftThm]];   (* gcd a b | a *)
    abDivB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdDividesRightThm]];  (* gcd a b | b *)
    abDivBA = HOL`Bool`MP[
      HOL`Bool`SPEC[gAB, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, gcdUniversalThm]]],
      HOL`Bool`CONJ[abDivB, abDivA]];                  (* gcd a b | gcd b a *)
    baDivB = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, gcdDividesLeftThm]];   (* gcd b a | b *)
    baDivA = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, gcdDividesRightThm]];  (* gcd b a | a *)
    baDivAB = HOL`Bool`MP[
      HOL`Bool`SPEC[gBA, HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, gcdUniversalThm]]],
      HOL`Bool`CONJ[baDivA, baDivB]];                  (* gcd b a | gcd a b *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[gBA, HOL`Bool`SPEC[gAB, dividesAntisymThm]], abDivBA], baDivAB];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, eq]]
  ];

(* ⊢ ∀m. gcd 0 m = m  (proper home Num.wl) *)
gcdZeroLeftThm =
  Module[{mV},
    mV = mkVar["m", numTy];
    HOL`Bool`GEN[mV, TRANS[
      HOL`Bool`SPEC[mV, HOL`Bool`SPEC[zeroN[], gcdCommThm]],   (* gcd 0 m = gcd m 0 *)
      HOL`Bool`SPEC[mV, gcdZeroRightThm]]]                     (* gcd m 0 = m *)
  ];

(* ⊢ ∀m. ¬ (m = 0) ⇒ exDiv m m = SUC 0  (proper home Num.wl) *)
exDivSelfThm =
  Module[{mV, notM0, mDivM, mEq, mTimesOne, cancelEq, suc0Eq},
    mV = mkVar["m", numTy];
    notM0 = ASSUME[notTm[mkEq[mV, zeroN[]]]];
    mDivM = HOL`Bool`SPEC[mV, HOL`Stdlib`Num`dividesReflThm];           (* divides m m *)
    mEq = HOL`Bool`MP[HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, exDivThm]], mDivM];  (* m = m * exDiv m m *)
    mTimesOne = TRANS[
      HOL`Bool`SPEC[oneN[], HOL`Bool`SPEC[mV, HOL`Stdlib`Num`timesCommThm]],
      HOL`Bool`SPEC[mV, HOL`Stdlib`Num`oneTimesEqThm]];                 (* m * SUC 0 = m *)
    cancelEq = TRANS[mTimesOne, mEq];                                   (* m * SUC 0 = m * exDiv m m *)
    suc0Eq = HOL`Bool`MP[
      HOL`Bool`SPEC[exDivTm[mV, mV], HOL`Bool`SPEC[oneN[],
        HOL`Bool`MP[HOL`Bool`SPEC[mV, HOL`Stdlib`FTA`multLeftCancelThm], notM0]]],
      cancelEq];                                                        (* SUC 0 = exDiv m m *)
    HOL`Bool`GEN[mV, HOL`Bool`DISCH[notTm[mkEq[mV, zeroN[]]], HOL`Equal`SYM[suc0Eq]]]
  ];

(* ⊢ ∀m. gcd m m = m  (proper home Num.wl) *)
gcdSelfThm =
  Module[{mV, gDivM, mDivG, eq},
    mV = mkVar["m", numTy];
    gDivM = HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, gcdDividesLeftThm]];  (* divides (gcd m m) m *)
    mDivG = HOL`Bool`MP[
      HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, HOL`Bool`SPEC[mV, gcdUniversalThm]]],
      HOL`Bool`CONJ[HOL`Bool`SPEC[mV, HOL`Stdlib`Num`dividesReflThm],
                    HOL`Bool`SPEC[mV, HOL`Stdlib`Num`dividesReflThm]]];   (* divides m (gcd m m) *)
    eq = HOL`Bool`MP[HOL`Bool`MP[
      HOL`Bool`SPEC[mV, HOL`Bool`SPEC[gcdTm[mV, mV], dividesAntisymThm]], gDivM], mDivG];
    HOL`Bool`GEN[mV, eq]
  ];

End[];
EndPackage[];
