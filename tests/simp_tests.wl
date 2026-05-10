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
Needs["HOL`Auto`PropTaut`"];
Needs["HOL`Auto`Meson`"];
Needs["HOL`Auto`Simp`"];

(* ===== simpPrepareRule: strip ∀ + EQT-coerce ===== *)

HOLTest`runTests["simp: prepareRule strips one ∀",
  Module[{alpha, x, eqTh, ruleThm, c},
    alpha = mkVarType["a"];
    x = mkVar["x", alpha];
    eqTh = GEN[x, REFL[x]];          (* ⊢ ∀x. x = x *)
    ruleThm = HOL`Auto`Simp`simpPrepareRule[eqTh];
    c = concl[ruleThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _], _]],
      "result is an equation"];
]];

HOLTest`runTests["simp: prepareRule EQT-coerces a non-equation",
  Module[{p, th, ruleThm, T},
    p = mkVar["p", boolTy];
    th = ASSUME[p];                  (* p ⊢ p *)
    ruleThm = HOL`Auto`Simp`simpPrepareRule[th];
    T = mkConst["T", boolTy];
    HOLTest`assertEq[concl[ruleThm], mkEq[p, T],
      "non-eq concl becomes p = T"];
    HOLTest`assertEq[hyp[ruleThm], {p}, "hyp preserved"];
]];

HOLTest`runTests["simp: prepareRule strips nested ∀",
  Module[{alpha, x, y, refl, gen1, gen2, ruleThm, c},
    alpha = mkVarType["a"];
    x = mkVar["x", alpha];
    y = mkVar["y", alpha];
    refl = REFL[x];                  (* ⊢ x = x *)
    gen1 = GEN[x, refl];             (* ⊢ ∀x. x = x *)
    gen2 = GEN[y, gen1];             (* ⊢ ∀y. ∀x. x = x *)
    ruleThm = HOL`Auto`Simp`simpPrepareRule[gen2];
    c = concl[ruleThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], _], _]],
      "after stripping both ∀'s, concl is an equation"];
]];

(* ===== simpConv: identity / single rule / fixpoint ===== *)

HOLTest`runTests["simp: simpConv with no rules is BETA-only",
  Module[{x, redex, eqTh},
    x = mkVar["x", boolTy];
    redex = mkComb[mkAbs[x, x], x];     (* (λx. x) x *)
    eqTh = HOL`Auto`Simp`simpConv[{}][redex];
    HOLTest`assertEq[concl[eqTh][[2]], x,
      "(λx. x) x β-reduces to x"];
]];

HOLTest`runTests["simp: simpConv applies a ∀-quantified rule",
  Module[{p, q, notC, schemaTh, eqTh, target, res, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    schemaTh = HOL`Auto`PropTaut`propTaut[
      mkEq[mkComb[notC, mkComb[notC, p]], p]];   (* ⊢ ¬¬p = p *)
    eqTh = GEN[p, schemaTh];                      (* ⊢ ∀p. ¬¬p = p *)
    target = mkComb[notC, mkComb[notC, q]];       (* ¬¬q *)
    res = HOL`Auto`Simp`simpConv[{eqTh}][target];
    expected = q;
    HOLTest`assertEq[concl[res][[2]], expected,
      "∀-stripped ¬¬p = p drops the double negation"];
]];

HOLTest`runTests["simp: simpConv iterates to fixpoint (¬¬¬¬x → x)",
  Module[{p, x, notC, schemaTh, eqTh, target, res},
    p = mkVar["p", boolTy]; x = mkVar["x", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    schemaTh = HOL`Auto`PropTaut`propTaut[
      mkEq[mkComb[notC, mkComb[notC, p]], p]];
    eqTh = GEN[p, schemaTh];                      (* ⊢ ∀p. ¬¬p = p *)
    (* target = ¬¬¬¬x: requires two iterations of ¬¬p = p. *)
    target = mkComb[notC, mkComb[notC,
              mkComb[notC, mkComb[notC, x]]]];
    res = HOL`Auto`Simp`simpConv[{eqTh}][target];
    HOLTest`assertEq[concl[res][[2]], x,
      "fixpoint reduces ¬¬¬¬x to x in two passes"];
]];

HOLTest`runTests["simp: simpConv terminates on cyclic rules p↔q",
  Module[{p, q, fwd, bwd, res, rhs},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    fwd = ASSUME[mkEq[p, q]];
    bwd = ASSUME[mkEq[q, p]];
    res = HOL`Auto`Simp`simpConv[{fwd, bwd}][p];
    rhs = concl[res][[2]];
    HOLTest`assertTrue[rhs === p || rhs === q,
      "fixpoint terminates with rhs ∈ {p, q}"];
]];

(* ===== simpConv with HO Miller match (under ∀) ===== *)

HOLTest`runTests["simp: simpConv applies HO Miller rule",
  Module[{alpha, x, y, P, Pty, Q, f, forallTy, lhs, rhs, eqTh,
          target, res, expected},
    alpha    = mkVarType["a"];
    Pty      = tyFun[alpha, boolTy];
    forallTy = tyFun[Pty, boolTy];
    x        = mkVar["x", alpha];
    y        = mkVar["y", alpha];
    P        = mkVar["P", Pty];
    Q        = mkVar["Q", boolTy];
    f        = mkVar["f", Pty];
    lhs = mkComb[mkConst["∀", forallTy],
            mkAbs[x, mkComb[P, x]]];
    rhs = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];           (* (lhs=Q) ⊢ (∀x. P x) = Q *)
    target = mkComb[mkConst["∀", forallTy],
              mkAbs[y, mkComb[f, y]]];
    res = HOL`Auto`Simp`simpConv[{eqTh}][target];
    expected = Q;
    HOLTest`assertEq[concl[res][[2]], expected,
      "(∀y. f y) simplifies to Q via Miller-matched rule"];
]];

(* ===== simpProve: closes goals reduced to T ===== *)

HOLTest`runTests["simp: simpProve closes ⊢ p when p = T is given",
  Module[{p, eqTh, th, ruleConcl},
    p = mkVar["p", boolTy];
    eqTh = ASSUME[mkEq[p, mkConst["T", boolTy]]];
    ruleConcl = concl[eqTh];                 (* p = T, the ASSUMEd hyp *)
    th = HOL`Auto`Simp`simpProve[p, {eqTh}];
    HOLTest`assertEq[concl[th], p,
      "simpProve unwraps ⊢ p = T to ⊢ p"];
    HOLTest`assertTrue[MemberQ[hyp[th], ruleConcl],
      "simpProve preserves the rule's hyp p = T"];
]];

HOLTest`runTests["simp: simpProve fails when target doesn't reduce to T",
  Module[{p, q, eqTh},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    eqTh = ASSUME[mkEq[p, q]];                (* not a = T form *)
    HOLTest`assertThrows[HOL`Auto`Simp`simpProve[p, {eqTh}], "simp",
      "not reducing to T raises a simp error"];
]];

(* ===== SIMP tactic via prove ===== *)

HOLTest`runTests["simp: SIMP tactic closes a goal that reduces to T",
  Module[{p, eqTh, th},
    p = mkVar["p", boolTy];
    eqTh = ASSUME[mkEq[p, mkConst["T", boolTy]]];
    th = HOL`Tactics`prove[p, HOL`Auto`Simp`SIMP[{eqTh}]];
    HOLTest`assertEq[concl[th], p,
      "SIMP[{p = T}] closes goal p"];
]];

(* ===== β-1.5: built-in propositional simpset ===== *)

HOLTest`runTests["simp: basicSimpset reduces T ∧ p to p with no user rules",
  Module[{p, T, andC, target, res},
    p = mkVar["p", boolTy];
    T = mkConst["T", boolTy];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[andC, T], p];          (* T ∧ p *)
    res = HOL`Auto`Simp`simpConv[{}][target];
    HOLTest`assertEq[concl[res][[2]], p,
      "T ∧ p simplifies to p"];
]];

HOLTest`runTests["simp: basicSimpset reduces ¬¬¬¬x without user rules",
  Module[{x, notC, target, res},
    x = mkVar["x", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    target = mkComb[notC, mkComb[notC,
              mkComb[notC, mkComb[notC, x]]]];   (* ¬¬¬¬x *)
    res = HOL`Auto`Simp`simpConv[{}][target];
    HOLTest`assertEq[concl[res][[2]], x,
      "¬¬¬¬x reduces to x via two ¬¬p = p rewrites"];
]];

HOLTest`runTests["simp: basicSimpset closes p ⇒ p",
  Module[{p, impC, target, th},
    p = mkVar["p", boolTy];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[impC, p], p];          (* p ⇒ p *)
    th = HOL`Auto`Simp`simpProve[target, {}];
    HOLTest`assertEq[concl[th], target,
      "simpProve discharges p ⇒ p via basicSimpset"];
    HOLTest`assertEq[hyp[th], {}, "no hyps in the result"];
]];

HOLTest`runTests["simp: basicSimpset closes nested propositional formula",
  Module[{p, T, F, andC, orC, notC, target, th},
    p = mkVar["p", boolTy];
    T = mkConst["T", boolTy];
    F = mkConst["F", boolTy];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    orC  = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    (* ¬F ∧ (T ∨ p) = T ∧ T = T *)
    target = mkComb[mkComb[andC, mkComb[notC, F]],
              mkComb[mkComb[orC, T], p]];
    th = HOL`Auto`Simp`simpProve[target, {}];
    HOLTest`assertEq[concl[th], target,
      "¬F ∧ (T ∨ p) simplifies to T and is proved"];
]];

HOLTest`runTests["simp: basicSimpset enables conditional rule with F ⇒ p antecedent",
  Module[{p, q, F, impC, notC, lhs, ruleAnt, rule, target, res},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    F = mkConst["F", boolTy];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    lhs = mkComb[notC, p];
    ruleAnt = mkComb[mkComb[impC, F], p];          (* F ⇒ p — a tautology *)
    (* ⊢ (F ⇒ p) ⇒ (¬p = q): the antecedent is provable via basicSimpset's *)
    (* `F ⇒ p = T`, so the recursive simpProve discharges it.              *)
    rule = ASSUME[mkComb[mkComb[impC, ruleAnt], mkEq[lhs, q]]];
    target = mkComb[notC, p];
    res = HOL`Auto`Simp`simpConv[{rule}][target];
    HOLTest`assertEq[concl[res][[2]], q,
      "basic F ⇒ p = T discharges antecedent → ¬p rewrites to q"];
]];

HOLTest`runTests["simp: user rule wins over basic when both match",
  Module[{p, T, andC, lhs, userRule, target, res},
    p = mkVar["p", boolTy];
    T = mkConst["T", boolTy];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    lhs = mkComb[mkComb[andC, T], p];
    (* User rule: T ∧ p = T (overrides basic T ∧ p = p). User goes first. *)
    userRule = ASSUME[mkEq[lhs, T]];
    target = lhs;
    res = HOL`Auto`Simp`simpConv[{userRule}][target];
    HOLTest`assertEq[concl[res][[2]], T,
      "user rule overrides basic for T ∧ p"];
]];

(* ===== β-2: conditional rewriting ===== *)

HOLTest`runTests["simp: condRewr discharges T antecedent (TRUTH path)",
  Module[{p, q, T, notC, impC, lhs, rule, target, res},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    T = mkConst["T", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    lhs = mkComb[notC, p];
    (* rule : ⊢ T ⇒ (¬p = q) — the antecedent T is auto-discharged. *)
    rule = ASSUME[mkComb[mkComb[impC, T], mkEq[lhs, q]]];
    target = mkComb[notC, p];
    res = HOL`Auto`Simp`simpConv[{rule}][target];
    HOLTest`assertEq[concl[res][[2]], q,
      "T-antecedent rule rewrites ¬p to q"];
]];

HOLTest`runTests["simp: condRewr discharges via fact-as-hypothesis (direct lookup)",
  Module[{A, p, q, notC, impC, notA, lhs, rule, fact, target, res},
    A = mkVar["A", boolTy]; p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notA = mkComb[notC, A];
    lhs  = mkComb[notC, p];
    (* rule : ⊢ ¬A ⇒ (¬p = q); fact : ⊢ ¬A. Direct lookup discharges ¬A. *)
    rule = ASSUME[mkComb[mkComb[impC, notA], mkEq[lhs, q]]];
    fact = ASSUME[notA];
    target = mkComb[notC, p];
    res = HOL`Auto`Simp`simpConv[{rule, fact}][target];
    HOLTest`assertEq[concl[res][[2]], q,
      "¬A-antecedent rule fires when ⊢ ¬A is supplied"];
]];

HOLTest`runTests["simp: condRewr leaves target alone when antecedent unprovable",
  Module[{A, p, q, notC, impC, notA, lhs, rule, target, res},
    A = mkVar["A", boolTy]; p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notA = mkComb[notC, A];
    lhs  = mkComb[notC, p];
    rule = ASSUME[mkComb[mkComb[impC, notA], mkEq[lhs, q]]];
    target = mkComb[notC, p];
    (* Without ⊢ ¬A in the simpset, prover cannot discharge — rule is   *)
    (* skipped, target survives unchanged.                              *)
    res = HOL`Auto`Simp`simpConv[{rule}][target];
    HOLTest`assertEq[concl[res][[2]], target,
      "unprovable antecedent ⇒ rule skipped, target unchanged"];
]];

HOLTest`runTests["simp: condRewr discharges multiple preconditions in order",
  Module[{A, B, p, q, notC, impC, notA, notB, lhs, rule, factA, factB,
          target, res},
    A = mkVar["A", boolTy]; B = mkVar["B", boolTy];
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notA = mkComb[notC, A]; notB = mkComb[notC, B];
    lhs  = mkComb[notC, p];
    (* ⊢ ¬A ⇒ ¬B ⇒ (¬p = q) *)
    rule = ASSUME[mkComb[mkComb[impC, notA],
            mkComb[mkComb[impC, notB], mkEq[lhs, q]]]];
    factA = ASSUME[notA];
    factB = ASSUME[notB];
    target = mkComb[notC, p];
    res = HOL`Auto`Simp`simpConv[{rule, factA, factB}][target];
    HOLTest`assertEq[concl[res][[2]], q,
      "two preconditions both discharged via direct lookup"];
]];

HOLTest`runTests["simp: condRewr does not fire on F antecedent",
  Module[{p, q, F, notC, impC, lhs, rule, target, res},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    F = mkConst["F", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    lhs = mkComb[notC, p];
    (* ⊢ F ⇒ (¬p = q) — antecedent is the literal constant F, not a    *)
    (* free var, so the prover cannot trivially over-match it via any *)
    (* EQT-coerced fact rewrite. The rule must be skipped.            *)
    rule = ASSUME[mkComb[mkComb[impC, F], mkEq[lhs, q]]];
    target = mkComb[notC, p];
    res = HOL`Auto`Simp`simpConv[{rule}][target];
    HOLTest`assertEq[concl[res][[2]], target,
      "F antecedent → rule never fires, target preserved"];
]];

HOLTest`runTests["simp: condRewr through ∀-stripped rule",
  Module[{p, q, x, notC, impC, T, lhs, ruleSchema, ruleQuant, target, res},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    x = mkVar["x", boolTy];
    T = mkConst["T", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    lhs = mkComb[notC, x];
    (* ⊢ T ⇒ (¬x = q) — close over x via GEN, then prepareRule strips ∀x.*)
    ruleSchema = ASSUME[mkComb[mkComb[impC, T], mkEq[lhs, q]]];
    (* The hyp `T ⇒ ¬x = q` contains x; GEN[x, ...] would fail. Use a    *)
    (* hyp-free schema: build ⊢ T ⇒ (¬p = T) via propTaut.               *)
    Module[{schemaThm, genThm, target2, resB},
      schemaThm = HOL`Auto`PropTaut`propTaut[
        mkComb[mkComb[impC, T],
          mkEq[mkComb[notC, mkComb[notC, p]], p]]];
      (* schemaThm : ⊢ T ⇒ (¬¬p = p) — propositional tautology *)
      genThm = GEN[p, schemaThm];   (* ⊢ ∀p. T ⇒ ¬¬p = p *)
      target2 = mkComb[notC, mkComb[notC, q]];   (* ¬¬q *)
      resB = HOL`Auto`Simp`simpConv[{genThm}][target2];
      HOLTest`assertEq[concl[resB][[2]], q,
        "∀-stripped conditional rule rewrites ¬¬q to q"];
    ];
]];

HOLTest`runTests["simp: SIMP tactic leaves residual goal when not T",
  Module[{p, q, eqTh, g, r, sg},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    eqTh = ASSUME[mkEq[p, q]];
    g = HOL`Tactics`goal[{}, p];
    r = HOL`Auto`Simp`SIMP[{eqTh}][g];
    sg = r[[1]];
    HOLTest`assertEq[Length[sg], 1, "exactly one subgoal"];
    HOLTest`assertEq[sg[[1]], HOL`Tactics`goal[{}, q],
      "subgoal is the simplified concl"];
]];
