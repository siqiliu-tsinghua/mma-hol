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
