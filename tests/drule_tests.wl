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

HOLTest`runTests["drule: ALLCONV", Module[{x, th},
  x = mkVar["x", boolTy];
  th = ALLCONV[x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "ALLCONV[x] = REFL[x]"];
  HOLTest`assertEq[hyp[th], {}, "ALLCONV no hyps"];
]];

HOLTest`runTests["drule: NOCONV fails with conv tag", Module[{x},
  x = mkVar["x", boolTy];
  HOLTest`assertThrows[NOCONV[x], "conv", "NOCONV throws conv"];
]];

HOLTest`runTests["drule: THENC two ALLCONV", Module[{x, th},
  x = mkVar["x", boolTy];
  th = THENC[ALLCONV, ALLCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "THENC[ALLCONV, ALLCONV][x]"];
]];

HOLTest`runTests["drule: ORELSEC falls back", Module[{x, th},
  x = mkVar["x", boolTy];
  th = ORELSEC[NOCONV, ALLCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "ORELSEC tries second"];
]];

HOLTest`runTests["drule: ORELSEC first succeeds", Module[{x, th, c1},
  x = mkVar["x", boolTy];
  c1 = Function[t, REFL[t]];
  th = ORELSEC[c1, NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "ORELSEC picks first when it works"];
]];

HOLTest`runTests["drule: TRYCONV on failure", Module[{x, th},
  x = mkVar["x", boolTy];
  th = TRYCONV[NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "TRYCONV falls back to REFL"];
]];

HOLTest`runTests["drule: REPEATC on NOCONV", Module[{x, th},
  x = mkVar["x", boolTy];
  th = REPEATC[NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "REPEATC NOCONV = REFL"];
]];

HOLTest`runTests["drule: REPEATC one-shot BETA", Module[{x, y, redex, th},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  redex = mkComb[mkAbs[x, x], y];
  th = REPEATC[BETACONV][redex];
  HOLTest`assertEq[concl[th], mkEq[redex, y], "REPEATC reduces one β"];
]];

HOLTest`runTests["drule: SUBCONV comb", Module[{f, x, y, redex, th, fTy},
  fTy = tyFun[boolTy, boolTy];
  f = mkVar["f", fTy];
  x = mkVar["x", boolTy];
  y = mkVar["y", boolTy];
  redex = mkComb[f, mkComb[mkAbs[x, x], y]];
  (* SUBCONV[BETACONV][f ((λx. x) y)] should β-reduce the argument only. *)
  th = SUBCONV[BETACONV][redex];
  HOLTest`assertEq[concl[th], mkEq[redex, mkComb[f, y]], "SUBCONV reduces comb arg"];
]];

HOLTest`runTests["drule: SUBCONV abs", Module[{x, y, inner, outer, th, expected},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  inner = mkComb[mkAbs[x, x], y];
  outer = mkAbs[x, inner];
  (* SUBCONV[BETACONV][λx. (λx. x) y] reduces the inner β under the abs. *)
  th = SUBCONV[BETACONV][outer];
  expected = mkAbs[x, y];
  HOLTest`assertEq[concl[th][[2]], expected, "SUBCONV descends into abs"];
]];

HOLTest`runTests["drule: SUBCONV atomic fails", Module[{x},
  x = mkVar["x", boolTy];
  HOLTest`assertThrows[SUBCONV[ALLCONV][x], "conv",
    "SUBCONV on atom fails"];
]];

HOLTest`runTests["drule: DEPTHCONV nested β", Module[{x, y, inner, outer, th},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  inner = mkAbs[x, mkComb[mkAbs[x, x], x]];
  outer = mkComb[inner, y];
  th = DEPTHCONV[BETACONV][outer];
  HOLTest`assertEq[concl[th], mkEq[outer, y], "DEPTHCONV reduces nested β to y"];
]];

HOLTest`runTests["drule: DEPTHCONV no match returns REFL", Module[{x, th},
  x = mkVar["x", boolTy];
  th = DEPTHCONV[NOCONV][x];
  HOLTest`assertEq[concl[th], mkEq[x, x], "DEPTHCONV NOCONV = REFL"];
]];

HOLTest`runTests["drule: REWRCONV identity on var", Module[{p, q, eqTh, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  eqTh = ASSUME[mkEq[p, q]];
  th = REWRCONV[eqTh][p];
  HOLTest`assertEq[concl[th], mkEq[p, q], "REWRCONV[p=q][p] = p=q"];
  HOLTest`assertEq[hyp[th], {mkEq[p, q]}, "preserves hyp"];
]];

HOLTest`runTests["drule: REWRCONV type-var instantiation",
  Module[{alpha, x, eqTh, bx, th},
    alpha = mkVarType["a"];
    x = mkVar["x", alpha];
    eqTh = REFL[x];
    bx = mkVar["x", boolTy];
    th = REWRCONV[eqTh][bx];
    HOLTest`assertEq[concl[th], mkEq[bx, bx], "REWRCONV instantiates type a := bool"];
]];

HOLTest`runTests["drule: REWRCONV rejects mismatch", Module[{p, q, r, eqTh},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  r = mkConst["T", boolTy];
  eqTh = ASSUME[mkEq[mkComb[mkAbs[p, p], p], q]];
  (* lhs = (λp. p) p : bool ; target = T : bool — lhs shape is a comb, T is a const. *)
  HOLTest`assertThrows[REWRCONV[eqTh][r], "conv", "REWRCONV rejects shape mismatch"];
]];

HOLTest`runTests["drule: REWRCONV rejects non-eq",
  Module[{p, th},
    p = mkVar["p", boolTy];
    th = ASSUME[p];
    HOLTest`assertThrows[REWRCONV[th][p], "conv", "REWRCONV demands equation"];
]];

HOLTest`runTests["drule: CONVRULE lifts", Module[{x, y, redex, th, rewTh},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  redex = mkComb[mkAbs[x, x], y];
  th = ASSUME[redex];
  rewTh = CONVRULE[BETACONV, th];
  HOLTest`assertEq[concl[rewTh], y, "CONVRULE β-reduces concl"];
  HOLTest`assertEq[hyp[rewTh], {redex}, "CONVRULE preserves hyps"];
]];

HOLTest`runTests["drule: ONCEREWRITERULE",
  Module[{p, q, notP, eqTh, andC, target, th, rewritten, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notP = mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
    eqTh = ASSUME[mkEq[notP, q]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[andC, notP], notP];
    th = ASSUME[target];
    rewritten = ONCEREWRITERULE[eqTh, th];
    expected = mkComb[mkComb[andC, q], notP];
    HOLTest`assertEq[concl[rewritten], expected,
      "ONCEREWRITERULE rewrites leftmost ¬p only"];
]];

HOLTest`runTests["drule: REWRITERULE rewrites all",
  Module[{p, q, notP, eqTh, andC, target, th, rewritten, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notP = mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
    eqTh = ASSUME[mkEq[notP, q]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[andC, notP], notP];
    th = ASSUME[target];
    rewritten = REWRITERULE[eqTh, th];
    expected = mkComb[mkComb[andC, q], q];
    HOLTest`assertEq[concl[rewritten], expected,
      "REWRITERULE rewrites both ¬p occurrences"];
]];

HOLTest`runTests["drule: productiveEqThm — true for distinct LHS/RHS",
  Module[{p, q, eqTh},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    eqTh = ASSUME[mkEq[p, q]];
    HOLTest`assertEq[productiveEqThm[eqTh], True,
      "p = q is productive (lhs ≠ rhs)"];
  ]];

HOLTest`runTests["drule: productiveEqThm — false for reflexive equation",
  Module[{p, eqTh},
    p = mkVar["p", boolTy];
    eqTh = REFL[p];
    HOLTest`assertEq[productiveEqThm[eqTh], False,
      "p = p is non-productive (lhs aconv rhs)"];
  ]];

HOLTest`runTests["drule: REWRITERULE silently drops non-productive rules",
  Module[{p, q, eqTh, th, rewritten},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    eqTh = REFL[p];                  (* ⊢ p = p *)
    th   = ASSUME[mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q]];
    rewritten = REWRITERULE[eqTh, th];
    HOLTest`assertEq[concl[rewritten], concl[th],
      "non-productive rule leaves concl unchanged"];
  ]];

HOLTest`runTests["drule: REWRITERULE list form filters productive rules",
  Module[{p, q, notP, andC, refl, swap, target, th, rewritten, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notP = mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    refl   = REFL[notP];                (* non-productive: ¬p = ¬p *)
    swap   = ASSUME[mkEq[notP, q]];     (* productive: ¬p → q *)
    target = mkComb[mkComb[andC, notP], notP];
    th     = ASSUME[target];
    rewritten = REWRITERULE[{refl, swap}, th];
    expected  = mkComb[mkComb[andC, q], q];
    HOLTest`assertEq[concl[rewritten], expected,
      "list form: refl dropped, swap applied to both ¬p's"];
  ]];

HOLTest`runTests["drule: REWRITERULE cycle detection terminates p↔q",
  Module[{p, q, fwd, bwd, th, rewritten},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    fwd = ASSUME[mkEq[p, q]];        (* p → q *)
    bwd = ASSUME[mkEq[q, p]];        (* q → p *)
    th  = ASSUME[p];
    rewritten = REWRITERULE[{fwd, bwd}, th];
    (* Cycle detection breaks before infinite loop; result's concl is   *)
    (* either p or q (whichever the loop settles on first revisit). The *)
    (* essential property is that this terminates and returns a valid   *)
    (* theorem.                                                         *)
    HOLTest`assertTrue[
      concl[rewritten] === p || concl[rewritten] === q,
      "cycle terminates with concl ∈ {p, q}"];
  ]];

HOLTest`runTests["drule: fixpointConvRule terminates on cycling conv",
  Module[{p, q, fwd, bwd, conv, th, rewritten},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    fwd = ASSUME[mkEq[p, q]];
    bwd = ASSUME[mkEq[q, p]];
    conv = HOL`Drule`DEPTHCONV[
      HOL`Drule`ORELSEC[REWRCONV[fwd], REWRCONV[bwd]]];
    th = ASSUME[p];
    rewritten = HOL`Drule`fixpointConvRule[conv, th];
    HOLTest`assertTrue[
      concl[rewritten] === p || concl[rewritten] === q,
      "fixpointConvRule terminates under cycle"];
  ]];

HOLTest`runTests["drule: SUBS empty list is identity",
  Module[{p, th, res},
    p = mkVar["p", boolTy];
    th = ASSUME[p];
    res = SUBS[{}, th];
    HOLTest`assertEq[concl[res], p, "SUBS[{}, th] keeps concl"];
    HOLTest`assertEq[hyp[res], {p}, "SUBS[{}, th] keeps hyps"];
]];

HOLTest`runTests["drule: SUBS replaces all occurrences",
  Module[{p, q, notP, eqTh, andC, target, th, res, expected},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    notP = mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
    eqTh = ASSUME[mkEq[notP, q]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[andC, notP], notP];
    th = ASSUME[target];
    res = SUBS[{eqTh}, th];
    expected = mkComb[mkComb[andC, q], q];
    HOLTest`assertEq[concl[res], expected, "both ¬p replaced"];
    HOLTest`assertEq[hyp[res], Sort[{target, mkEq[notP, q]}],
      "SUBS merges eqTh hyp with th hyp"];
]];

HOLTest`runTests["drule: SUBS does not descend into rewritten subterm",
  Module[{p, q, notC, eqTh, target, th, res},
    (* ⊢ p = ¬ p ; rewriting concl ⊢ p must yield ⊢ ¬ p, not ⊢ ¬ ¬ p *)
    p = mkVar["p", boolTy];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    eqTh = ASSUME[mkEq[p, mkComb[notC, p]]];
    th = ASSUME[p];
    res = SUBS[{eqTh}, th];
    HOLTest`assertEq[concl[res], mkComb[notC, p],
      "single pass: ¬ p, not ¬ ¬ p"];
]];

HOLTest`runTests["drule: SUBS no match leaves theorem alone",
  Module[{p, q, r, eqTh, th, res},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy]; r = mkVar["r", boolTy];
    eqTh = ASSUME[mkEq[q, r]];   (* q = r ; q does not appear in concl *)
    th = ASSUME[p];
    res = SUBS[{eqTh}, th];
    HOLTest`assertEq[concl[res], p, "concl unchanged"];
    HOLTest`assertEq[hyp[res], {p}, "no eqTh hyp added on no-match"];
]];

HOLTest`runTests["drule: SUBS sequential equations",
  Module[{a, b, c, eq1, eq2, andC, target, th, res, expected},
    a = mkVar["a", boolTy]; b = mkVar["b", boolTy]; c = mkVar["c", boolTy];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    eq1 = ASSUME[mkEq[a, b]];
    eq2 = ASSUME[mkEq[b, c]];
    target = mkComb[mkComb[andC, a], a];
    th = ASSUME[target];
    res = SUBS[{eq1, eq2}, th];
    expected = mkComb[mkComb[andC, c], c];
    HOLTest`assertEq[concl[res], expected,
      "a→b then b→c yields c on both sides"];
]];

HOLTest`runTests["drule: SUBS with type instantiation",
  Module[{alpha, x, eqTh, p, q, andC, target, th, res, expected},
    alpha = mkVarType["a"];
    x = mkVar["x", alpha];
    eqTh = REFL[x];   (* polymorphic ⊢ x = x at α *)
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    target = mkComb[mkComb[andC, p], q];
    th = ASSUME[target];
    res = SUBS[{eqTh}, th];
    (* ⊢ x = x with α := bool reduces concl unchanged but exercises path. *)
    HOLTest`assertEq[concl[res], target, "polymorphic refl no-op"];
]];

(* ===== TODO.C: higher-order Miller-pattern matching ===== *)

HOLTest`runTests["drule: REWRCONV HO Miller match under ∀",
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
    (* eqTh : ⊢ (∀x. P x) = Q  — schema where P is a higher-order var *)
    lhs = mkComb[mkConst["∀", forallTy],
            mkAbs[x, mkComb[P, x]]];
    rhs = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];
    (* Target: (∀y. f y), uses f instead of P *)
    target = mkComb[mkConst["∀", forallTy],
              mkAbs[y, mkComb[f, y]]];
    res = REWRCONV[eqTh][target];
    expected = mkEq[target, Q];
    HOLTest`assertTrue[aconv[concl[res], expected],
      "HO Miller: (∀y. f y) rewrites to Q"];
]];

HOLTest`runTests["drule: REWRCONV HO Miller against compound body",
  Module[{alpha, x, y, P, Pty, Q, gtC, zeroC, intC, forallTy,
          lhs, rhs, eqTh, target, res, expected},
    alpha    = mkVarType["a"];
    Pty      = tyFun[alpha, boolTy];
    forallTy = tyFun[Pty, boolTy];
    intC     = mkVarType["int"];
    x        = mkVar["x", alpha];
    P        = mkVar["P", Pty];
    Q        = mkVar["Q", boolTy];
    lhs = mkComb[mkConst["∀", forallTy],
            mkAbs[x, mkComb[P, x]]];
    rhs = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];
    (* Target: (∀y:int. y > 0). Use a synthetic > and 0 we declare here. *)
    (* Avoid touching the kernel: use free vars to stand in for > and 0. *)
    Module[{gt, zero, yi, body, fty},
      yi   = mkVar["y", intC];
      gt   = mkVar["gt", tyFun[intC, tyFun[intC, boolTy]]];
      zero = mkVar["zero", intC];
      body = mkComb[mkComb[gt, yi], zero];
      target = mkComb[
        mkConst["∀", tyFun[tyFun[intC, boolTy], boolTy]],
        mkAbs[yi, body]];
      res = REWRCONV[eqTh][target];
      expected = mkEq[target, Q];
      HOLTest`assertTrue[aconv[concl[res], expected],
        "HO Miller: (∀y. y > 0) rewrites to Q"];
    ];
]];

HOLTest`runTests["drule: REWRCONV closed-bvar guard rejects capturing FO match",
  Module[{alpha, intC, x, y, P, Q, f, forallTy, lhs, rhs, eqTh, target},
    alpha    = mkVarType["a"];
    intC     = mkVarType["int"];
    forallTy = tyFun[tyFun[alpha, boolTy], boolTy];
    x        = mkVar["x", alpha];
    P        = mkVar["P", boolTy];   (* P : bool, no x dependence *)
    Q        = mkVar["Q", boolTy];
    (* eqTh : ⊢ (∀x. P) = Q  — P is a bool-typed free var inside the abs.   *)
    (* No Miller pattern (P has no args), so the matcher must fall back to *)
    (* first-order. The closed-bvar check then refuses to bind P to a body *)
    (* that references the abstracted x.                                    *)
    lhs = mkComb[mkConst["∀", forallTy], mkAbs[x, P]];
    rhs = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];
    f = mkVar["f", tyFun[intC, boolTy]];
    y = mkVar["y", intC];
    target = mkComb[
      mkConst["∀", tyFun[tyFun[intC, boolTy], boolTy]],
      mkAbs[y, mkComb[f, y]]];
    HOLTest`assertThrows[REWRCONV[eqTh][target], "conv",
      "FO match into context-bvar body is rejected"];
]];

HOLTest`runTests["drule: REWRCONV vacuous binder still rewrites when target is closed",
  Module[{alpha, x, y, P, Q, T, forallTy, lhs, rhs, eqTh,
          target, res, expected},
    alpha    = mkVarType["a"];
    forallTy = tyFun[tyFun[alpha, boolTy], boolTy];
    x        = mkVar["x", alpha];
    y        = mkVar["y", alpha];
    P        = mkVar["P", boolTy];
    Q        = mkVar["Q", boolTy];
    T        = mkConst["T", boolTy];
    lhs  = mkComb[mkConst["∀", forallTy], mkAbs[x, P]];
    rhs  = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];
    target = mkComb[mkConst["∀", forallTy], mkAbs[y, T]];
    res = REWRCONV[eqTh][target];
    expected = mkEq[target, Q];
    HOLTest`assertTrue[aconv[concl[res], expected],
      "(∀y. T) (P-body has no bvar use) rewrites to Q"];
]];

HOLTest`runTests["drule: REWRCONV HO Miller with two args",
  Module[{alpha, beta, x, y, R, Rty, Q, Sf, forallA, forallAB, lhs, rhs,
          eqTh, target, res, expected},
    alpha    = mkVarType["a"];
    beta     = mkVarType["b"];
    Rty      = tyFun[alpha, tyFun[beta, boolTy]];
    forallA  = tyFun[tyFun[alpha, boolTy], boolTy];
    forallAB = tyFun[tyFun[beta, boolTy], boolTy];
    x        = mkVar["x", alpha];
    y        = mkVar["y", beta];
    R        = mkVar["R", Rty];
    Q        = mkVar["Q", boolTy];
    Sf       = mkVar["Sf", Rty];
    (* Pattern: (∀x:α. ∀y:β. R x y).  Schema rule rewrites to Q.       *)
    lhs = mkComb[mkConst["∀", forallA],
            mkAbs[x,
              mkComb[mkConst["∀", forallAB],
                mkAbs[y, mkComb[mkComb[R, x], y]]]]];
    rhs = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];
    (* Target: (∀x. ∀y. Sf x y) using a different binary predicate Sf. *)
    target = mkComb[mkConst["∀", forallA],
              mkAbs[x,
                mkComb[mkConst["∀", forallAB],
                  mkAbs[y, mkComb[mkComb[Sf, x], y]]]]];
    res = REWRCONV[eqTh][target];
    expected = mkEq[target, Q];
    HOLTest`assertTrue[aconv[concl[res], expected],
      "two-arg Miller: (∀x. ∀y. Sf x y) rewrites to Q"];
]];

HOLTest`runTests["drule: REWRCONV HO Miller rejects inconsistent P bindings",
  Module[{alpha, x, y, P, Pty, Q, f, g, andC, forallTy, lhs, rhs,
          eqTh, target},
    alpha    = mkVarType["a"];
    Pty      = tyFun[alpha, boolTy];
    forallTy = tyFun[Pty, boolTy];
    x        = mkVar["x", alpha];
    y        = mkVar["y", alpha];
    P        = mkVar["P", Pty];
    Q        = mkVar["Q", boolTy];
    f        = mkVar["f", Pty];
    g        = mkVar["g", Pty];
    andC     = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    (* lhs: (∀x. P x) ∧ (∀y. P y) — same P twice.                     *)
    lhs = mkComb[mkComb[andC,
            mkComb[mkConst["∀", forallTy], mkAbs[x, mkComb[P, x]]]],
            mkComb[mkConst["∀", forallTy], mkAbs[y, mkComb[P, y]]]];
    rhs = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];
    (* Target: (∀x. f x) ∧ (∀y. g y). Match must fail since P would   *)
    (* need to bind to both f and g.                                  *)
    target = mkComb[mkComb[andC,
              mkComb[mkConst["∀", forallTy], mkAbs[x, mkComb[f, x]]]],
              mkComb[mkConst["∀", forallTy], mkAbs[y, mkComb[g, y]]]];
    HOLTest`assertThrows[REWRCONV[eqTh][target], "conv",
      "Miller binding consistency forces match failure"];
]];

HOLTest`runTests["drule: REWRCONV HO match shows up under DEPTHCONV / REWRITERULE",
  Module[{alpha, x, y, P, Pty, Q, f, forallTy, andC, lhs, rhs, eqTh,
          target, th, res, expected},
    alpha    = mkVarType["a"];
    Pty      = tyFun[alpha, boolTy];
    forallTy = tyFun[Pty, boolTy];
    x        = mkVar["x", alpha];
    y        = mkVar["y", alpha];
    P        = mkVar["P", Pty];
    Q        = mkVar["Q", boolTy];
    f        = mkVar["f", Pty];
    andC     = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    lhs = mkComb[mkConst["∀", forallTy], mkAbs[x, mkComb[P, x]]];
    rhs = Q;
    eqTh = ASSUME[mkEq[lhs, rhs]];
    (* (∀y. f y) ∧ (∀y. f y) ⊢ same — REWRITERULE rewrites both copies. *)
    target = mkComb[mkConst["∀", forallTy], mkAbs[y, mkComb[f, y]]];
    th = ASSUME[mkComb[mkComb[andC, target], target]];
    res = REWRITERULE[eqTh, th];
    expected = mkComb[mkComb[andC, Q], Q];
    HOLTest`assertEq[concl[res], expected,
      "REWRITERULE applies HO rule under both ∧ branches"];
]];
