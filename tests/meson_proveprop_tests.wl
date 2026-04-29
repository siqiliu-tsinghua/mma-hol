(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Parser`"];
Needs["HOL`Auto`PropTaut`"];
Needs["HOL`Auto`Meson`"];

mppParse[s_String] := HOL`Parser`parseTerm[s];

HOLTest`runTests["mesonProveProp: ⊢ p ⇒ p (smoke)",
  Module[{tm, th},
    tm = mppParse["p ⇒ p"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[isThm[th], True, "is a thm"];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ p ⇒ p"];
    HOLTest`assertEq[hyp[th], {}, "no hypotheses"];
  ]];

HOLTest`runTests["mesonProveProp: ⊢ p ∨ ¬p",
  Module[{tm, th},
    tm = mppParse["p ∨ ¬p"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ p ∨ ¬p"];
    HOLTest`assertEq[hyp[th], {}, "no hypotheses"];
  ]];

HOLTest`runTests["mesonProveProp: ⊢ ¬¬p ⇒ p",
  Module[{tm, th},
    tm = mppParse["¬¬p ⇒ p"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ ¬¬p ⇒ p"];
    HOLTest`assertEq[hyp[th], {}, "no hypotheses"];
  ]];

HOLTest`runTests["mesonProveProp: ⊢ ¬(p ∧ ¬p)",
  Module[{tm, th},
    tm = mppParse["¬(p ∧ ¬p)"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ ¬(p ∧ ¬p)"];
    HOLTest`assertEq[hyp[th], {}, "no hypotheses"];
  ]];

HOLTest`runTests["mesonProveProp: rejects non-tautology p",
  Module[{tm},
    tm = mppParse["p"];
    HOLTest`assertThrows[HOL`Auto`Meson`mesonProveProp[tm, {}], "meson",
      "non-tautology rejected"];
  ]];

(* === Premises (k>1 extension) === *)

HOLTest`runTests["mesonProveProp: ⊢ p ⇒ (p ⇒ q) ⇒ q",
  Module[{tm, th},
    tm = mppParse["p ⇒ (p ⇒ q) ⇒ q"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "MP form as goal"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
  ]];

HOLTest`runTests["mesonProveProp: ⊢ (p ⇒ q) ⇒ (q ⇒ r) ⇒ p ⇒ r",
  Module[{tm, th},
    tm = mppParse["(p ⇒ q) ⇒ (q ⇒ r) ⇒ p ⇒ r"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "transitivity of ⇒"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
  ]];

HOLTest`runTests["mesonProveProp: ⊢ ¬(p ∧ q) ⇒ ¬p ∨ ¬q (De Morgan)",
  Module[{tm, th},
    tm = mppParse["¬(p ∧ q) ⇒ ¬p ∨ ¬q"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "De Morgan ∧"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
  ]];

HOLTest`runTests["mesonProveProp: q from {⊢ p, ⊢ p ⇒ q} via ASSUMEd premises",
  Module[{p, q, pImpQ, thP, thPQ, th, expectedHyps},
    p     = mkVar["p", boolTy];
    q     = mkVar["q", boolTy];
    pImpQ = mppParse["p ⇒ q"];
    thP   = ASSUME[p];
    thPQ  = ASSUME[pImpQ];
    th    = HOL`Auto`Meson`mesonProveProp[q, {thP, thPQ}];
    HOLTest`assertEq[aconv[concl[th], q], True, "concl ≡ q"];
    expectedHyps = Sort[{p, pImpQ}];
    HOLTest`assertEq[Sort[hyp[th]], expectedHyps, "hyps = {p, p⇒q}"];
  ]];
