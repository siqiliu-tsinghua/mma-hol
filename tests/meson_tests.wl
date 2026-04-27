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

(* === M7-α-3 search engine tests === *)

(* Register a test predicate P : bool → bool — Skolem fresh names use ?sk*
   so 'P' doesn't collide with anything the search engine will introduce. *)
If[!MemberQ[HOL`Kernel`listConstants[], "P"],
  HOL`Kernel`newConstant["P", tyFun[boolTy, boolTy]]];

HOLTest`runTests["meson: unify — same atom is identity",
  Module[{p, σ},
    p = mkVar["p", boolTy];
    σ = mesonUnify[p, p, <||>];
    HOLTest`assertEq[σ, <||>, "var === var: empty σ"];
  ]];

HOLTest`runTests["meson: unify — var with const binds",
  Module[{x, c, σ},
    x = mkVar["x", boolTy];
    c = mkConst["T", boolTy];
    σ = mesonUnify[x, c, <||>];
    HOLTest`assertEq[σ, <|"x" -> c|>, "x ↦ T"];
  ]];

HOLTest`runTests["meson: unify — type mismatch fails",
  Module[{x, c, σ},
    x = mkVar["x", boolTy];
    c = mkConst["T", boolTy];  (* T is bool *)
    (* Try to unify x:bool with const at a different type *)
    σ = mesonUnify[x, mkVar["y", tyVar["a"]], <||>];
    HOLTest`assertEq[σ, mesonUnifyFailed, "x:bool ≁ y:'a fails"];
  ]];

HOLTest`runTests["meson: unify — different consts fail",
  Module[{σ},
    σ = mesonUnify[mkConst["T", boolTy], mkConst["F", boolTy], <||>];
    HOLTest`assertEq[σ, mesonUnifyFailed, "T ≁ F"];
  ]];

HOLTest`runTests["meson: unify — comb propagates",
  Module[{p, x, y, q, σ},
    (* Unify p(x) with p(c)  →  x ↦ c *)
    p = mkConst["P", tyFun[boolTy, boolTy]];
    x = mkVar["x", boolTy];
    σ = mesonUnify[mkComb[p, x], mkComb[p, mkConst["T", boolTy]], <||>];
    HOLTest`assertEq[σ, <|"x" -> mkConst["T", boolTy]|>, "P x ≃ P T → x ↦ T"];
  ]];

HOLTest`runTests["meson: unify — occurs check",
  Module[{x, p, σ},
    x = mkVar["x", boolTy];
    p = mkConst["P", tyFun[boolTy, boolTy]];
    (* Try x ≃ P x (occurs) *)
    σ = mesonUnify[x, mkComb[p, x], <||>];
    HOLTest`assertEq[σ, mesonUnifyFailed, "x ≁ P x (occurs check)"];
  ]];

HOLTest`runTests["meson: refute — propositional contradiction {p}, {¬p}",
  Module[{p, clauses, result},
    p = mkVar["p", boolTy];
    clauses = {mClause[{mLit[True, p]}], mClause[{mLit[False, p]}]};
    result = mesonRefute[clauses, 5];
    HOLTest`assertTrue[result =!= mesonRefuteFailed,
      "{p} ∧ {¬p} is unsatisfiable"];
  ]];

HOLTest`runTests["meson: refute — modus ponens contradiction",
  Module[{p, q, np, nq, clauses, result},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    (* {p ∨ ¬q}, {q}, {¬p}: i.e., (q ⇒ p) ∧ q ∧ ¬p *)
    clauses = {
      mClause[{mLit[True, p], mLit[False, q]}],
      mClause[{mLit[True, q]}],
      mClause[{mLit[False, p]}]};
    result = mesonRefute[clauses, 5];
    HOLTest`assertTrue[result =!= mesonRefuteFailed,
      "(q ⇒ p) ∧ q ∧ ¬p is unsatisfiable"];
  ]];

HOLTest`runTests["meson: refute — satisfiable returns failure within bound",
  Module[{p, q, clauses, result},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    (* {p}, {q}: both consistent, no refutation *)
    clauses = {mClause[{mLit[True, p]}], mClause[{mLit[True, q]}]};
    result = mesonRefute[clauses, 3];
    HOLTest`assertEq[result, mesonRefuteFailed,
      "satisfiable set has no refutation"];
  ]];

HOLTest`runTests["meson: refute — first-order contradiction via unification",
  Module[{px0, npxv, result, clauses},
    mesonResetState[];
    (* Goal: (∀x. P x) ⇒ P 0.  Negate: (∀x. P x) ∧ ¬P 0.
       Clausify gives {P x_logical}, {¬P 0_const}. Unify x ↦ 0_const. *)
    clauses = mesonClausify[
      parseTerm["(∀x:bool. P x) ∧ (¬ (P T))"]];
    result = mesonRefute[clauses, 5];
    HOLTest`assertTrue[result =!= mesonRefuteFailed,
      "(∀x:bool. P x) ∧ ¬P T refutes by unifying x ↦ T"];
  ]];

HOLTest`runTests["meson: refute — depth bound respected",
  Module[{p, np, clauses, resultZero, resultOne},
    p = mkVar["p", boolTy];
    clauses = {mClause[{mLit[True, p]}], mClause[{mLit[False, p]}]};
    (* At depth 0: starting clause has 1 literal needing extension;
       extension uses 1 step → needs depth ≥ 1. Actually since the
       second clause is unit, after one extension new subgoals = {}
       so depth 1 should suffice. depth 0 cannot extend at all. *)
    resultZero = mesonRefute[clauses, 0];
    resultOne  = mesonRefute[clauses, 1];
    HOLTest`assertEq[resultZero, mesonRefuteFailed,
      "depth 0 can't refute even simple contradictions"];
    HOLTest`assertTrue[resultOne =!= mesonRefuteFailed,
      "depth 1 suffices for unit-clause contradiction"];
  ]];
