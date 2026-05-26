(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Num`"];
Needs["HOL`Stdlib`FTA`"];

numTy = mkType["num", {}];

HOLTest`runTests["FTA: dividesPosThm — ⊢ ∀d n. ¬(n=0) ⇒ d|n ⇒ ¬(d=0)",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`dividesPosThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _], _, _]], _]]],
      "shape: ∀d n. …"];
]];

HOLTest`runTests["FTA: dividesTransThm — ⊢ ∀a b c. a|b ⇒ b|c ⇒ a|c",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`dividesTransThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _], _, _]], _]], _]]],
      "shape: ∀a b c. …"];
]];

HOLTest`runTests["FTA: notOneNorZeroLtThm — ⊢ ∀d. ¬(d=0) ⇒ ¬(d=1) ⇒ 1<d",
  HOLTest`assertEq[hyp[HOL`Stdlib`FTA`notOneNorZeroLtThm], {}, "no hyps"]];

HOLTest`runTests["FTA: primeOrCompositeThm — dichotomy",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`primeOrCompositeThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀n. 1<n ⇒ prime n ∨ ∃d. … *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], _],
          comb[comb[const["∨", _], comb[const["prime", _], _]],
            comb[const["∃", _], _]]], _]]],
      "shape: ∀n. 1<n ⇒ prime n ∨ ∃d. …"];
]];

HOLTest`runTests["FTA: primeDivExistsThm — every n>1 has a prime divisor",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`primeDivExistsThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], _],
          comb[const["∃", _], _]], _]]],
      "shape: ∀n. 1<n ⇒ ∃p. prime p ∧ p|n"];
]];

HOLTest`runTests["FTA: posAddLtThm — ⊢ ∀c d. ¬(d=0) ⇒ c < c + d",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`posAddLtThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _], _, _]], _]]],
      "shape: ∀c d. …"];
]];

HOLTest`runTests["FTA: ltMultIfOneLtThm — ⊢ ∀p c. 1<p ⇒ ¬(c=0) ⇒ c < p*c",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`ltMultIfOneLtThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _], _, _]], _]]],
      "shape: ∀p c. …"];
]];

HOLTest`runTests["FTA stage 2: primeFactorsExistsThm — ⊢ ∀n. ¬(n=0) ⇒ ∃l. ALL prime l ∧ FOLDR * 1 l = n",
  Module[{dThm, c, nLTy},
    dThm = HOL`Stdlib`FTA`primeFactorsExistsThm;
    c = concl[dThm];
    nLTy = HOL`Stdlib`List`listTy[numTy];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], comb[const["¬", _], _]],
          comb[const["∃", _], abs[bvar[0, _],
            comb[comb[const["∧", _], _], _], _]]], _]]],
      "shape: ∀n. ¬(n=0) ⇒ ∃l. ALL prime l ∧ FOLDR · l = n"];
]];

HOLTest`runTests["FTA stage 3.a: notLeqSucSelfThm — ⊢ ∀n. ¬(SUC n ≤ n)",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`notLeqSucSelfThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["¬", _],
          comb[comb[const["≤", _], comb[const["SUC", _], _]], _]], _]]],
      "shape: ∀n. ¬(SUC n ≤ n)"];
]];

HOLTest`runTests["FTA stage 3.a: primeNotDivOneThm — ⊢ ∀p. prime p ⇒ ¬(divides p (SUC 0))",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`primeNotDivOneThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], comb[const["prime", _], _]],
          comb[const["¬", _],
            comb[comb[const["divides", _], _], _]]], _]]],
      "shape: ∀p. prime p ⇒ ¬(divides p (SUC 0))"];
]];

HOLTest`runTests["FTA stage 3.a: primeDivFoldrTimesThm — Euclid's lemma on lists",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`primeDivFoldrTimesThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀p. prime p ⇒ ∀l. divides p (FOLDR * 1 l) ⇒ ∃y. MEM y l ∧ divides p y *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], comb[const["prime", _], _]],
          comb[const["∀", _], abs[bvar[0, _],
            comb[comb[const["⇒", _], _],
              comb[const["∃", _], abs[bvar[0, _], _, _]]],
            _]]], _]]],
      "shape: ∀p. prime p ⇒ ∀l. divides p (FOLDR…) ⇒ ∃y. MEM y l ∧ divides p y"];
]];

HOLTest`runTests["FTA stage 3.b: permNilThm — ⊢ PERM NIL NIL",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permNilThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["PERM", _], const["NIL", _]], const["NIL", _]]],
      "shape: PERM NIL NIL"];
]];

HOLTest`runTests["FTA stage 3.b: permConsThm — CONS congruence",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permConsThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀x l1 l2. PERM l1 l2 ⇒ PERM (CONS x l1) (CONS x l2) *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _], _, _]], _]], _]]],
      "shape: ∀x l1 l2. …"];
]];

HOLTest`runTests["FTA stage 3.b: permSwapThm — adjacent transposition",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permSwapThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀x y l. PERM (CONS x (CONS y l)) (CONS y (CONS x l)) *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _],
            comb[comb[const["PERM", _], _], _], _]], _]], _]]],
      "shape: ∀x y l. PERM (CONS x (CONS y l)) (CONS y (CONS x l))"];
]];

HOLTest`runTests["FTA stage 3.b: permTransThm — transitivity",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permTransThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀l1 l2 l3. PERM l1 l2 ⇒ PERM l2 l3 ⇒ PERM l1 l3 *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _], _, _]], _]], _]]],
      "shape: ∀l1 l2 l3. …"];
]];

HOLTest`runTests["FTA stage 3.b: permInductThm — induction principle",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permInductThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀P. closure ⇒ ∀l1 l2. PERM l1 l2 ⇒ P l1 l2 *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], _], _], _]]],
      "shape: ∀P. _ ⇒ _"];
]];

HOLTest`runTests["FTA stage 3.b: permReflThm — ⊢ ∀l. PERM l l",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permReflThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["PERM", _], _], _], _]]],
      "shape: ∀l. PERM l l"];
]];

HOLTest`runTests["FTA stage 3.b: permSymThm — ⊢ ∀l1 l2. PERM l1 l2 ⇒ PERM l2 l1",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permSymThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[comb[const["⇒", _], _], _], _]], _]]],
      "shape: ∀l1 l2. PERM l1 l2 ⇒ PERM l2 l1"];
]];

HOLTest`runTests["FTA stage 3.b: permFoldrTimesThm — PERM preserves FOLDR *",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permFoldrTimesThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀l1 l2. PERM l1 l2 ⇒ FOLDR * 1 l1 = FOLDR * 1 l2 *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[comb[const["⇒", _], comb[comb[const["PERM", _], _], _]],
            comb[comb[const["=", _], _], _]], _]], _]]],
      "shape: ∀l1 l2. PERM l1 l2 ⇒ FOLDR * 1 l1 = FOLDR * 1 l2"];
]];

HOLTest`runTests["FTA stage 3.b: permAllThm — PERM preserves ALL",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permAllThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀p l1 l2. PERM l1 l2 ⇒ ALL p l1 = ALL p l2 *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _], _, _]], _]], _]]],
      "shape: ∀p l1 l2. …"];
]];

HOLTest`runTests["FTA stage 3.c: memSplitThm — MEM x l ⇒ ∃l1 l2. l = APPEND l1 (CONS x l2)",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`memSplitThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀x l. MEM x l ⇒ ∃l1 l2. l = APPEND l1 (CONS x l2) *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[comb[const["⇒", _], comb[comb[const["MEM", _], _], _]],
            comb[const["∃", _], abs[bvar[0, _],
              comb[const["∃", _], abs[bvar[0, _], _, _]], _]]], _]], _]]],
      "shape: ∀x l. MEM x l ⇒ ∃l1 l2. _"];
]];

HOLTest`runTests["FTA stage 3.c: permAppendConsThm — PERM (APPEND l1 (CONS x l2)) (CONS x (APPEND l1 l2))",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`permAppendConsThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀x l1 l2. PERM (APPEND l1 (CONS x l2)) (CONS x (APPEND l1 l2)) *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[const["∀", _], abs[bvar[0, _],
            comb[comb[const["PERM", _], _], _], _]], _]], _]]],
      "shape: ∀x l1 l2. PERM _ _"];
]];

HOLTest`runTests["FTA stage 3.d: multEqZeroThm — ⊢ ∀x a. x*a = 0 ⇒ x = 0 ∨ a = 0",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`multEqZeroThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _], _, _]], _]]],
      "shape: ∀x a. …"];
]];

HOLTest`runTests["FTA stage 3.d: multLeftCancelThm — ⊢ ∀x. ¬(x=0) ⇒ ∀a b. x*a = x*b ⇒ a = b",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`multLeftCancelThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], comb[const["¬", _], _]], _], _]]],
      "shape: ∀x. ¬(_) ⇒ _"];
]];

HOLTest`runTests["FTA stage 3.d: primeNotZeroThm — ⊢ ∀p. prime p ⇒ ¬(p = 0)",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`primeNotZeroThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], comb[const["prime", _], _]],
          comb[const["¬", _], _]], _]]],
      "shape: ∀p. prime p ⇒ ¬(p = 0)"];
]];

HOLTest`runTests["FTA stage 3.d: primesEqIfDividesThm — ⊢ ∀p q. prime p ⇒ prime q ⇒ p|q ⇒ p = q",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`primesEqIfDividesThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _], _, _]], _]]],
      "shape: ∀p q. …"];
]];

HOLTest`runTests["FTA stage 3.d: allMemImpThm — ⊢ ∀P l. ALL P l ⇒ ∀x. MEM x l ⇒ P x",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`allMemImpThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _], _, _]], _]]],
      "shape: ∀P l. …"];
]];

HOLTest`runTests["FTA stage 3.d: foldrEqOneNilThm — ⊢ ∀l. ALL prime l ⇒ FOLDR * 1 l = 1 ⇒ l = NIL",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`foldrEqOneNilThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["⇒", _], _],
          comb[comb[const["⇒", _], _], _]], _]]],
      "shape: ∀l. _ ⇒ _ ⇒ _ = NIL"];
]];

HOLTest`runTests["FTA stage 3 capstone: primeFactorsUniqueThm — uniqueness modulo permutation",
  Module[{dThm, c},
    dThm = HOL`Stdlib`FTA`primeFactorsUniqueThm;
    c = concl[dThm];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
    (* ⊢ ∀l1 l2. ALL prime l1 ⇒ ALL prime l2
                ⇒ FOLDR * 1 l1 = FOLDR * 1 l2 ⇒ PERM l1 l2 *)
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[const["∀", _], abs[bvar[0, _],
          comb[comb[const["⇒", _], _],
            comb[comb[const["⇒", _], _],
              comb[comb[const["⇒", _], _],
                comb[comb[const["PERM", _], _], _]]]], _]], _]]],
      "shape: ∀l1 l2. … ⇒ PERM l1 l2"];
]];
