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

(* === k>1 start clause replay (M7-α-4-c-ext) === *)
(* ¬((p ∨ ¬p) ∧ (q ∨ ¬q)) clausifies to four 2-lit clauses with no    *)
(* unit clauses: {¬p,¬q}, {¬p,q}, {p,¬q}, {p,q}.  Search must pick a  *)
(* 2-lit start, which exercises the ASSUME-each-lit + DISJCASES fold. *)

HOLTest`runTests["mesonProveProp: k=2 start — ⊢ (p ∨ ¬p) ∧ (q ∨ ¬q)",
  Module[{tm, th},
    tm = mppParse["(p ∨ ¬p) ∧ (q ∨ ¬q)"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ (p ∨ ¬p) ∧ (q ∨ ¬q)"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
  ]];

(* Premise (a ∨ b) plus negated goal {¬a, ¬b} forces a 2-lit start    *)
(* even though units exist post-sort: search picks the unit ¬-goal    *)
(* clause first, but the chain can also drive through (a ∨ b).        *)
HOLTest`runTests["mesonProveProp: 2-lit premise + neg-goal — F from {⊢ a∨b, ⊢ ¬a, ⊢ ¬b}",
  Module[{a, b, aOrB, notA, notB, thAB, thNA, thNB, fGoal, th},
    a     = mkVar["a", boolTy];
    b     = mkVar["b", boolTy];
    aOrB  = mppParse["a ∨ b"];
    notA  = mppParse["¬a"];
    notB  = mppParse["¬b"];
    thAB  = ASSUME[aOrB];
    thNA  = ASSUME[notA];
    thNB  = ASSUME[notB];
    fGoal = mkConst["F", boolTy];
    th    = HOL`Auto`Meson`mesonProveProp[fGoal, {thAB, thNA, thNB}];
    HOLTest`assertEq[concl[th], fGoal, "concl ≡ F"];
    HOLTest`assertEq[Sort[hyp[th]], Sort[{aOrB, notA, notB}], "hyps = {a∨b, ¬a, ¬b}"];
  ]];

(* k=3 case (`(p∨¬p) ∧ (q∨¬q) ∧ (r∨¬r)` — 8 three-lit clauses post-CNF, *)
(* no units) is provable by mesonProveProp but the unguided IDS search  *)
(* explores combinatorially; deferred until α-5 adds equality / Brand    *)
(* mod and we have a chance to add subsumption / clause ordering.        *)

(* === First-order replay (M7-α-4-d-α). =============================== *)
(* These tests bypass the FOL clausifier (NNF/Skolem/CNF on theorems —    *)
(* α-4-d-β) and feed mesonProveProp pre-clausified premises with free    *)
(* logical variables. The σ produced by unification is INSTed at replay  *)
(* and any tagged-but-unbound vars are renamed back via untagThm before   *)
(* CCONTR discharges the negated goal.                                    *)

If[!MemberQ[HOL`Kernel`listConstants[], "mppP"],
  HOL`Kernel`newConstant["mppP", tyFun[indTy, boolTy]]];
If[!MemberQ[HOL`Kernel`listConstants[], "mppQ"],
  HOL`Kernel`newConstant["mppQ", tyFun[indTy, boolTy]]];
If[!MemberQ[HOL`Kernel`listConstants[], "mppR"],
  HOL`Kernel`newConstant["mppR", tyFun[indTy, boolTy]]];
If[!MemberQ[HOL`Kernel`listConstants[], "mppA"],
  HOL`Kernel`newConstant["mppA", indTy]];
If[!MemberQ[HOL`Kernel`listConstants[], "mppB"],
  HOL`Kernel`newConstant["mppB", indTy]];

mppNot[t_]   := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], t];
mppOr[u_, v_] :=
  mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], u], v];

HOLTest`runTests["mesonProveProp: FOL — Q(a) from {¬P(x)∨Q(x), P(a)}",
  Module[{P, Q, a, x, Px, Qx, Pa, Qa, premise1, premise2, th},
    P  = mkConst["mppP", tyFun[indTy, boolTy]];
    Q  = mkConst["mppQ", tyFun[indTy, boolTy]];
    a  = mkConst["mppA", indTy];
    x  = mkVar["x", indTy];
    Px = mkComb[P, x];   Qx = mkComb[Q, x];
    Pa = mkComb[P, a];   Qa = mkComb[Q, a];
    premise1 = ASSUME[mppOr[mppNot[Px], Qx]];
    premise2 = ASSUME[Pa];
    th = HOL`Auto`Meson`mesonProveProp[Qa, {premise1, premise2}];
    HOLTest`assertEq[concl[th], Qa, "concl ≡ Q(a)"];
    HOLTest`assertEq[Sort[hyp[th]],
      Sort[{mppOr[mppNot[Pa], Qa], Pa}],
      "hyps = {¬Pa∨Qa, Pa} (premise instantiated by σ={x→a})"];
    HOLTest`assertEq[
      Cases[concl[th], var[n_String, _] /; StringContainsQ[n, "@"], {0, Infinity}],
      {}, "no @-tagged vars leak into concl"];
    HOLTest`assertEq[
      Flatten[Cases[#, var[n_String, _] /; StringContainsQ[n, "@"], {0, Infinity}] & /@ hyp[th]],
      {}, "no @-tagged vars leak into hyps"];
  ]];

HOLTest`runTests["mesonProveProp: FOL — R(a) via two-step chain",
  Module[{P, Q, R, a, x, Px, Qx, Rx, Pa, Ra,
          premise1, premise2, premise3, th},
    P = mkConst["mppP", tyFun[indTy, boolTy]];
    Q = mkConst["mppQ", tyFun[indTy, boolTy]];
    R = mkConst["mppR", tyFun[indTy, boolTy]];
    a = mkConst["mppA", indTy];
    x = mkVar["x", indTy];
    Px = mkComb[P, x]; Qx = mkComb[Q, x]; Rx = mkComb[R, x];
    Pa = mkComb[P, a]; Ra = mkComb[R, a];
    premise1 = ASSUME[mppOr[mppNot[Px], Qx]];           (* P x ⇒ Q x *)
    premise2 = ASSUME[mppOr[mppNot[Qx], Rx]];           (* Q x ⇒ R x *)
    premise3 = ASSUME[Pa];
    th = HOL`Auto`Meson`mesonProveProp[Ra, {premise1, premise2, premise3}];
    HOLTest`assertEq[concl[th], Ra, "concl ≡ R(a)"];
    HOLTest`assertEq[
      Flatten[Cases[#, var[n_String, _] /; StringContainsQ[n, "@"], {0, Infinity}] & /@
              Append[hyp[th], concl[th]]],
      {}, "no @-tagged vars leak"];
  ]];

HOLTest`runTests["mesonProveProp: FOL — picks correct ground (Q(b) from {¬P(x)∨Q(x), P(a), P(b)})",
  Module[{P, Q, a, b, x, Px, Qx, Pa, Pb, Qb,
          premise1, premise2, premise3, th},
    P = mkConst["mppP", tyFun[indTy, boolTy]];
    Q = mkConst["mppQ", tyFun[indTy, boolTy]];
    a = mkConst["mppA", indTy];
    b = mkConst["mppB", indTy];
    x = mkVar["x", indTy];
    Px = mkComb[P, x]; Qx = mkComb[Q, x];
    Pa = mkComb[P, a]; Pb = mkComb[P, b]; Qb = mkComb[Q, b];
    premise1 = ASSUME[mppOr[mppNot[Px], Qx]];
    premise2 = ASSUME[Pa];
    premise3 = ASSUME[Pb];
    th = HOL`Auto`Meson`mesonProveProp[Qb, {premise1, premise2, premise3}];
    HOLTest`assertEq[concl[th], Qb, "concl ≡ Q(b)"];
    HOLTest`assertTrue[MemberQ[hyp[th], Pb], "Pb is among hyps (the ground used)"];
    HOLTest`assertEq[
      Flatten[Cases[#, var[n_String, _] /; StringContainsQ[n, "@"], {0, Infinity}] & /@
              Append[hyp[th], concl[th]]],
      {}, "no @-tagged vars leak"];
  ]];

(* === clausifyFOLThm: universal-quantifier goals (M7-α-4-d-β phase 1) === *)
(* The thm-layer FOL clausifier handles ∀ via SPEC fresh and ∧ via         *)
(* CONJUNCT1/2.  Negated goals like ¬((∀x. P x ⇒ Q x) ⇒ P a ⇒ Q a) become *)
(* (∀x. ¬P x ∨ Q x) ∧ P a ∧ ¬Q a after nnfThm; walkClausifyFOL produces   *)
(* clauses {¬P x' ∨ Q x'}, {P a}, {¬Q a} with x' a fresh free variable.    *)

HOLTest`runTests["mesonProveProp: FOL — (∀x. P x ⇒ Q x) ⇒ P a ⇒ Q a",
  Module[{tm, th},
    tm = HOL`Parser`parseTerm["(! x. mppP x ==> mppQ x) ==> mppP mppA ==> mppQ mppA"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ goal"];
    HOLTest`assertEq[hyp[th], {}, "no hyps (closed theorem)"];
    HOLTest`assertEq[
      Flatten[Cases[#, var[n_String, _] /; StringContainsQ[n, "@"], {0, Infinity}] & /@
              Append[hyp[th], concl[th]]],
      {}, "no @-tagged vars leak"];
  ]];

HOLTest`runTests["mesonProveProp: FOL — (∀x. P x) ⇒ P a (universal instantiation)",
  Module[{tm, th},
    tm = HOL`Parser`parseTerm["(! x. mppP x) ==> mppP mppA"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ goal"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
  ]];

HOLTest`runTests["mesonProveProp: FOL — (∀x. P x ∧ Q x) ⇒ P a ∧ Q a (∧ split under ∀)",
  Module[{tm, th},
    tm = HOL`Parser`parseTerm[
      "(! x. mppP x /\\ mppQ x) ==> mppP mppA /\\ mppQ mppA"];
    th = HOL`Auto`Meson`mesonProveProp[tm, {}];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ goal"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
  ]];

(* === clausifyFOLThm: ∃-Skolemization (M7-α-4-d-β phase 2) === *)

HOLTest`runTests["clausifyFOLThm: ∃-Skolem produces a fresh constant clause",
  Module[{th, clauses, c, freeVarsInBody},
    th      = ASSUME[HOL`Parser`parseTerm["? x. mppP x"]];
    clauses = HOL`Auto`Meson`clausifyFOLThm[th];
    HOLTest`assertEq[Length[clauses], 1, "exactly one clause"];
    c = concl[clauses[[1]]];
    HOLTest`assertTrue[MatchQ[c, comb[const["mppP", _], const[_String, _]]],
      "clause is mppP applied to a constant (the Skolem)"];
    freeVarsInBody = freesIn[c];
    HOLTest`assertEq[freeVarsInBody, {},
      "Skolem clause is closed (no free vars in nullary case)"];
  ]];

HOLTest`runTests[
  "mesonProveProp: FOL — F from {⊢ ∃x. P x, ⊢ ∀x. ¬P x} (Skolem + SPEC)",
  Module[{premise1, premise2, goal, th},
    premise1 = ASSUME[HOL`Parser`parseTerm["? x. mppP x"]];
    premise2 = ASSUME[HOL`Parser`parseTerm["! x. ~ mppP x"]];
    goal     = mkConst["F", boolTy];
    th = HOL`Auto`Meson`mesonProveProp[goal, {premise1, premise2}];
    HOLTest`assertEq[concl[th], goal, "concl ≡ F"];
    HOLTest`assertEq[Length[hyp[th]], 2, "two hyps (∃ premise, ∀ premise)"];
    HOLTest`assertEq[
      Flatten[Cases[#, var[n_String, _] /; StringContainsQ[n, "@"], {0, Infinity}] & /@
              Append[hyp[th], concl[th]]],
      {}, "no @-tagged vars leak"];
  ]];

If[!MemberQ[HOL`Kernel`listConstants[], "mppR2"],
  HOL`Kernel`newConstant["mppR2", tyFun[indTy, tyFun[indTy, boolTy]]]];

HOLTest`runTests["mesonProveProp: FOL — goal with ∃ premise + ∀ rule",
  Module[{premise1, premise2, goal, th},
    (* Premise 1: ∃x. P x  (someone has property P)                       *)
    (* Premise 2: ∀x. P x ⇒ Q x (P implies Q)                              *)
    (* Goal: ∃x. Q x  (someone has Q)                                     *)
    (* ¬goal becomes ∀x. ¬Q x via NNF — no NOT_EXISTS_THM yet, so test this *)
    (* indirectly by giving the negated form of the goal as a premise.    *)
    premise1 = ASSUME[HOL`Parser`parseTerm["? x. mppP x"]];
    premise2 = ASSUME[HOL`Parser`parseTerm["! x. mppP x ==> mppQ x"]];
    goal     = mkConst["F", boolTy];
    (* Add a third premise: ∀x. ¬Q x (the negated goal in NNF form).      *)
    th = HOL`Auto`Meson`mesonProveProp[goal,
      {premise1, premise2,
       ASSUME[HOL`Parser`parseTerm["! x. ~ mppQ x"]]}];
    HOLTest`assertEq[concl[th], goal, "concl ≡ F"];
    HOLTest`assertEq[Length[hyp[th]], 3, "three premise hyps"];
  ]];

HOLTest`runTests["clausifyFOLThm: ∃ under ∀ becomes Skolem-applied function",
  Module[{R, x, y, Rxy, existsBody, forallTerm, th, clauses, c},
    R = mkConst["mppR2", tyFun[indTy, tyFun[indTy, boolTy]]];
    x = mkVar["x", indTy]; y = mkVar["y", indTy];
    Rxy = mkComb[mkComb[R, x], y];
    existsBody = mkComb[mkConst["∃", tyFun[tyFun[indTy, boolTy], boolTy]],
                        mkAbs[y, Rxy]];
    forallTerm = mkComb[mkConst["∀", tyFun[tyFun[indTy, boolTy], boolTy]],
                        mkAbs[x, existsBody]];
    th = HOL`Auto`Meson`specWithFreshName[ASSUME[forallTerm]];
    clauses = HOL`Auto`Meson`clausifyFOLThm[th];
    HOLTest`assertEq[Length[clauses], 1, "exactly one clause"];
    c = concl[clauses[[1]]];
    (* clause should be mppR2 x_fresh (sk x_fresh): a binary application *)
    (* with the Skolem function applied to the universal-scope variable.  *)
    HOLTest`assertTrue[
      MatchQ[c,
        comb[comb[const["mppR2", _], var[_String, _]],
             comb[const[_String, _], var[_String, _]]]],
      "clause shape is mppR2 x_fresh (sk x_fresh)"];
    HOLTest`assertEq[
      Cases[c, var[_String, _], {0, Infinity}] // DeleteDuplicates // Length,
      1, "exactly one free var (the universal-scope variable)"];
  ]];
