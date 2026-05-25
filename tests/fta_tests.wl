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
