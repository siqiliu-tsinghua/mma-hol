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

HOLTest`runTests["meson: MESON[{}] on a non-tautology fails with meson-tag",
  Module[{p, g},
    p = mkVar["p", boolTy];
    g = goal[{}, p];
    HOLTest`assertThrows[MESON[{}][g], "meson",
      "MESON on bare bool var rejects (no refutation)"];
  ]];

HOLTest`runTests["meson: mesonProve on a non-tautology fails with meson-tag",
  Module[{p},
    p = mkVar["p", boolTy];
    HOLTest`assertThrows[mesonProve[p, {}], "meson",
      "mesonProve rejects bare bool var"];
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

(* Register test predicates / propositions — Skolem fresh names use ?sk*
   so these names don't collide with anything the search engine will introduce.
   p_atm, q_atm are propositional constants used to test the propositional
   refutation cases without collateral var-unification. *)
If[!MemberQ[HOL`Kernel`listConstants[], "P"],
  HOL`Kernel`newConstant["P", tyFun[boolTy, boolTy]]];
If[!MemberQ[HOL`Kernel`listConstants[], "p_atm"],
  HOL`Kernel`newConstant["p_atm", boolTy]];
If[!MemberQ[HOL`Kernel`listConstants[], "q_atm"],
  HOL`Kernel`newConstant["q_atm", boolTy]];

HOLTest`runTests["meson: unify — same atom is identity",
  Module[{p, σ},
    p = mkVar["p", boolTy];
    σ = mesonUnify[p, p, <||>];
    HOLTest`assertEq[σ, <||>, "var === var: empty σ"];
  ]];

HOLTest`runTests["meson: unify — α-var with const binds",
  Module[{x, c, σ},
    x = mkVar["x", tyVar["a"]];
    c = mkVar["c", tyVar["a"]];
    σ = mesonUnify[x, c, <||>];
    HOLTest`assertEq[σ, <|"x" -> c|>, "x ↦ c (logical α-var binds)"];
  ]];

HOLTest`runTests["meson: unify — bool-typed vars are rigid",
  Module[{p, q, σ},
    p = mkVar["p", boolTy];
    q = mkVar["q", boolTy];
    σ = mesonUnify[p, q, <||>];
    HOLTest`assertEq[σ, mesonUnifyFailed, "p:bool ≁ q:bool (atomic props)"];
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

HOLTest`runTests["meson: unify — comb propagates (FOL with α-var)",
  Module[{p, x, c, σ},
    (* Unify P(x) with P(c) where x:α (logical), c:α — binds x ↦ c. *)
    p = mkConst["=", tyFun[tyVar["a"], tyFun[tyVar["a"], boolTy]]];
    x = mkVar["x", tyVar["a"]];
    c = mkVar["c", tyVar["a"]];
    σ = mesonUnify[mkComb[mkComb[p, x], c], mkComb[mkComb[p, c], c], <||>];
    HOLTest`assertEq[σ, <|"x" -> c|>, "= x c ≃ = c c → x ↦ c"];
  ]];

HOLTest`runTests["meson: unify — occurs check (α-var)",
  Module[{x, p, c, σ},
    x = mkVar["x", tyVar["a"]];
    p = mkConst["=", tyFun[tyVar["a"], tyFun[tyVar["a"], boolTy]]];
    c = mkVar["c", tyVar["a"]];
    (* Try x ≃ (= x c)  — type-mismatched, but more importantly occurs *)
    σ = mesonUnify[x, mkComb[mkComb[p, x], c], <||>];
    HOLTest`assertEq[σ, mesonUnifyFailed, "x ≁ = x c (type mismatch / occurs)"];
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
  Module[{aTy, pConst, xVar, cVar, pxAtom, pcAtom, clauses, result},
    mesonResetState[];
    (* Build {P x}, {¬P c} directly with x:'a logical, c:'a rigid.
       (Bool-typed vars are now rigid; FOL needs non-bool.) *)
    aTy    = tyVar["a"];
    pConst = mkVar["P", tyFun[aTy, boolTy]];  (* free pred-var, rigid *)
    xVar   = mkVar["x", aTy];                 (* logical *)
    cVar   = mkVar["c", aTy];                 (* logical too — but
                                                 since c never gets a
                                                 σ binding from unify
                                                 chain, x ↦ c happens *)
    pxAtom = mkComb[pConst, xVar];
    pcAtom = mkComb[pConst, cVar];
    clauses = {
      mClause[{mLit[True, pxAtom]}],
      mClause[{mLit[False, pcAtom]}]};
    result = mesonRefute[clauses, 5];
    HOLTest`assertTrue[result =!= mesonRefuteFailed,
      "{P x:'a} ∧ {¬P c:'a} refutes via x ↦ c"];
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

(* === M7-α-4-a proof-tree shape tests === *)

HOLTest`runTests["meson: trace — root is mProof start with tag slot",
  Module[{p, clauses, tree},
    p = mkVar["p", boolTy];
    clauses = {mClause[{mLit[True, p]}], mClause[{mLit[False, p]}]};
    tree = mesonRefute[clauses, 5];
    HOLTest`assertTrue[
      MatchQ[tree, mProof["start", _mClause, _String, _List]],
      "refutation tree's root is mProof[\"start\", clause, tag, subTrees]"];
  ]];

HOLTest`runTests["meson: trace — unit refutation has extension with empty subTrees",
  Module[{p, clauses, tree},
    p = mkVar["p", boolTy];
    clauses = {mClause[{mLit[True, p]}], mClause[{mLit[False, p]}]};
    tree = mesonRefute[clauses, 5];
    (* tree = mProof["start", c, tag, {mProof["extension", lit, c', cTag, litC, σ, {}]}] *)
    HOLTest`assertTrue[
      MatchQ[tree,
        mProof["start", _, _String,
          {mProof["extension", _mLit, _mClause, _String, _mLit, _Association, {}]}]],
      "{p}, {¬p}: start[c, tag, [extension(lit, c', cTag, litC, σ, [])]]"];
  ]];

HOLTest`runTests["meson: trace — extension records original (un-renamed) clause",
  Module[{p, clauses, tree, ext, sourceClause},
    p = mkVar["p", boolTy];
    clauses = {mClause[{mLit[True, p]}], mClause[{mLit[False, p]}]};
    tree = mesonRefute[clauses, 5];
    ext = tree[[4, 1]];
    sourceClause = ext[[3]];
    HOLTest`assertTrue[MemberQ[clauses, sourceClause],
      "the extension's clause field is one of the input clauses (un-renamed)"];
  ]];

HOLTest`runTests["meson: trace — multi-step proof for modus ponens contradiction",
  Module[{p, q, clauses, tree, depth},
    (* Constants here, not vars — vars would unify across atoms and
       collapse the refutation to one step. *)
    p = mkConst["p_atm", boolTy]; q = mkConst["q_atm", boolTy];
    (* {p ∨ ¬q}, {q}, {¬p} *)
    clauses = {
      mClause[{mLit[True, p], mLit[False, q]}],
      mClause[{mLit[True, q]}],
      mClause[{mLit[False, p]}]};
    tree = mesonRefute[clauses, 5];
    depth = Length[Cases[tree, mProof["extension", __], {0, Infinity}]];
    HOLTest`assertTrue[depth >= 2,
      "modus ponens refutation uses at least 2 extensions"];
  ]];

HOLTest`runTests["meson: trace — empty starting clause produces mProof empty",
  Module[{clauses, tree},
    (* Pathological: an empty clause among inputs is a direct refutation. *)
    clauses = {mClause[{}]};
    tree = mesonRefute[clauses, 5];
    HOLTest`assertTrue[MatchQ[tree, mProof["empty", _mClause]],
      "empty clause in input produces mProof[\"empty\", c]"];
  ]];
