(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Drule`"];
Needs["HOL`Tactics`"];
Needs["HOL`Parser`"];
Needs["HOL`Auto`Meson`"];

(* === M7-α-1 skeleton tests === *)

HOLTest`runTests["meson: skeleton — public symbols exist",
  Module[{},
    HOLTest`assertEq[mesonMaxDepth, 50, "default depth cap is 50"];
  ]];

HOLTest`runTests["meson: skeleton — MESON[{}] signs to tactic failure",
  Module[{p, g},
    p = mkVar["p", boolTy];
    g = goal[{}, p];
    HOLTest`assertThrows[MESON[{}][g], "tactic",
      "MESON skeleton fails as a tactic (signs to noTac)"];
  ]];

HOLTest`runTests["meson: skeleton — mesonProve throws meson-tag",
  Module[{p},
    p = mkVar["p", boolTy];
    HOLTest`assertThrows[mesonProve[p, {}], "meson",
      "mesonProve skeleton throws meson tag"];
  ]];

(* === M7-α-2 preprocessing tests === *)

(* Local builders for expected outputs.  Use the same below-kernel
   structural builders as Meson.wl uses internally so === comparisons
   line up. *)

bbb = tyFun[boolTy, tyFun[boolTy, boolTy]];
bb  = tyFun[boolTy, boolTy];
andC = const["∧", bbb];
orC  = const["∨", bbb];
impC = const["⇒", bbb];
notC = const["¬", bb];
mkAndS[p_, q_] := comb[comb[andC, p], q];
mkOrS[p_, q_]  := comb[comb[orC, p], q];
mkImpS[p_, q_] := comb[comb[impC, p], q];
mkNotS[p_]     := comb[notC, p];

HOLTest`runTests["meson: NNF — atom unchanged",
  Module[{p},
    p = mkVar["p", boolTy];
    HOLTest`assertEq[mesonNNF[p], p, "atom passes through"];
  ]];

HOLTest`runTests["meson: NNF — double negation",
  Module[{p, t},
    p = mkVar["p", boolTy];
    t = mkNotS[mkNotS[p]];
    HOLTest`assertEq[mesonNNF[t], p, "¬¬p ↦ p"];
  ]];

HOLTest`runTests["meson: NNF — De Morgan",
  Module[{p, q, andT, orT, expected1, expected2},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    andT = mkAndS[p, q]; orT = mkOrS[p, q];
    HOLTest`assertEq[mesonNNF[mkNotS[andT]],
      mkOrS[mkNotS[p], mkNotS[q]], "¬(p ∧ q) ↦ ¬p ∨ ¬q"];
    HOLTest`assertEq[mesonNNF[mkNotS[orT]],
      mkAndS[mkNotS[p], mkNotS[q]], "¬(p ∨ q) ↦ ¬p ∧ ¬q"];
  ]];

HOLTest`runTests["meson: NNF — ⇒ expanded",
  Module[{p, q, t},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    t = mkImpS[p, q];
    HOLTest`assertEq[mesonNNF[t], mkOrS[mkNotS[p], q],
      "p ⇒ q ↦ ¬p ∨ q"];
    HOLTest`assertEq[mesonNNF[mkNotS[t]], mkAndS[p, mkNotS[q]],
      "¬(p ⇒ q) ↦ p ∧ ¬q"];
  ]];

HOLTest`runTests["meson: NNF — ⇔ (= at bool) expanded",
  Module[{p, q, t},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    t = mkEq[p, q];
    HOLTest`assertEq[mesonNNF[t],
      mkAndS[mkOrS[mkNotS[p], q], mkOrS[mkNotS[q], p]],
      "p ⇔ q ↦ (¬p ∨ q) ∧ (¬q ∨ p)"];
  ]];

HOLTest`runTests["meson: NNF — ¬∀ ↦ ∃¬",
  Module[{t, nnf},
    t = parseTerm["¬ (∀x:bool. x)"];
    nnf = mesonNNF[t];
    HOLTest`assertTrue[
      MatchQ[nnf, comb[const["∃", _], abs[bvar[0, _], comb[const["¬", _], bvar[0, _]], _]]],
      "¬(∀x. x) ↦ ∃x. ¬x"];
  ]];

HOLTest`runTests["meson: NNF — ¬∃ ↦ ∀¬",
  Module[{t, nnf},
    t = parseTerm["¬ (∃x:bool. x)"];
    nnf = mesonNNF[t];
    HOLTest`assertTrue[
      MatchQ[nnf, comb[const["∀", _], abs[bvar[0, _], comb[const["¬", _], bvar[0, _]], _]]],
      "¬(∃x. x) ↦ ∀x. ¬x"];
  ]];

HOLTest`runTests["meson: Skolemize — ∀ to fresh free var",
  Module[{t, sk},
    mesonResetState[];
    t = parseTerm["∀x:bool. x"];
    sk = mesonSkolemize[t];
    HOLTest`assertTrue[MatchQ[sk, var[_String, _]],
      "∀x:bool. x skolemizes to a free var"];
  ]];

HOLTest`runTests["meson: Skolemize — ∃ to fresh constant",
  Module[{t, sk},
    mesonResetState[];
    t = parseTerm["∃x:bool. x"];
    sk = mesonSkolemize[t];
    HOLTest`assertTrue[MatchQ[sk, const[_String, _]],
      "∃x:bool. x skolemizes to a fresh constant"];
    HOLTest`assertTrue[StringStartsQ[sk[[1]], "?sk"],
      "Skolem name starts with ?sk"];
  ]];

HOLTest`runTests["meson: Skolemize — ∀x. ∃y. P (Skolem function)",
  Module[{t, sk},
    mesonResetState[];
    t = parseTerm["∀x:bool. ∃y:bool. x"];
    sk = mesonSkolemize[t];
    HOLTest`assertTrue[MatchQ[sk, var["x", _]],
      "body 'x' after skolemize: x is a free var (universal), y witness applied to x but body is just x"];
  ]];

HOLTest`runTests["meson: Skolemize — ∀x. ∃y. y (Skolem function applied to x)",
  Module[{t, sk},
    mesonResetState[];
    t = parseTerm["∀x:bool. ∃y:bool. y"];
    sk = mesonSkolemize[t];
    (* sk should be (sk_const x) — i.e., comb[const["?sk_n", bool->bool], var["x", bool]] *)
    HOLTest`assertTrue[
      MatchQ[sk, comb[const[skName_String /; StringStartsQ[skName, "?sk"], _], var["x", _]]],
      "∀x. ∃y. y ↦ sk(x) where sk : bool → bool"];
  ]];

HOLTest`runTests["meson: CNF — atom",
  Module[{p, cs},
    p = mkVar["p", boolTy];
    cs = mesonCNF[p];
    HOLTest`assertEq[cs, {mClause[{mLit[True, p]}]}, "atom → single unit clause"];
  ]];

HOLTest`runTests["meson: CNF — ∨ stays one clause",
  Module[{p, q, cs},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    cs = mesonCNF[mkOrS[p, q]];
    HOLTest`assertEq[cs, {mClause[{mLit[True, p], mLit[True, q]}]},
      "p ∨ q → one binary clause"];
  ]];

HOLTest`runTests["meson: CNF — ∧ splits into two clauses",
  Module[{p, q, cs},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    cs = mesonCNF[mkAndS[p, q]];
    HOLTest`assertEq[cs, {mClause[{mLit[True, p]}], mClause[{mLit[True, q]}]},
      "p ∧ q → two unit clauses"];
  ]];

HOLTest`runTests["meson: CNF — distribution",
  Module[{p, q, r, cs, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy]; r = mkVar["r", boolTy];
    (* (p ∧ q) ∨ r → (p ∨ r) ∧ (q ∨ r) *)
    cs = mesonCNF[mkOrS[mkAndS[p, q], r]];
    expected = {
      mClause[{mLit[True, p], mLit[True, r]}],
      mClause[{mLit[True, q], mLit[True, r]}]};
    HOLTest`assertEq[cs, expected, "(p ∧ q) ∨ r distributes correctly"];
  ]];

HOLTest`runTests["meson: factor — drops tautology",
  Module[{p, c, factored},
    p = mkVar["p", boolTy];
    c = mClause[{mLit[True, p], mLit[False, p]}];
    factored = mesonFactor[{c}];
    HOLTest`assertEq[factored, {}, "p ∨ ¬p tautology dropped"];
  ]];

HOLTest`runTests["meson: factor — dedups within clause",
  Module[{p, c, factored},
    p = mkVar["p", boolTy];
    c = mClause[{mLit[True, p], mLit[True, p]}];
    factored = mesonFactor[{c}];
    HOLTest`assertEq[factored, {mClause[{mLit[True, p]}]},
      "duplicate literal removed"];
  ]];

HOLTest`runTests["meson: clausify — full pipeline on a non-tautology",
  Module[{t, cs},
    mesonResetState[];
    t = parseTerm["p ∧ (q ∨ r)"];
    cs = mesonClausify[t];
    HOLTest`assertEq[Length[cs], 2,
      "p ∧ (q ∨ r) clausifies to 2 clauses: {p} and {q,r}"];
    HOLTest`assertTrue[AllTrue[cs, MatchQ[#, mClause[{__mLit}]] &],
      "every clause is an mClause of mLits"];
  ]];

HOLTest`runTests["meson: clausify — tautology produces empty clause set",
  Module[{t, cs},
    mesonResetState[];
    t = parseTerm["p ∨ (¬ p)"];
    cs = mesonClausify[t];
    HOLTest`assertEq[cs, {},
      "p ∨ ¬p factored away as tautology"];
  ]];
