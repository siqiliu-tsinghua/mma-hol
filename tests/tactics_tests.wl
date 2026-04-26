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

andTm[p_, q_] := mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
orTm[p_, q_]  := mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
impTm[p_, q_] := mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];
forallTm[v : var[_, ty_], body_] :=
  mkComb[mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];
existsTm[v : var[_, ty_], body_] :=
  mkComb[mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]], mkAbs[v, body]];

HOLTest`runTests["tactics: allTac is identity",
  Module[{p, g, r},
    p = mkVar["p", boolTy];
    g = goal[{}, p];
    r = allTac[g];
    HOLTest`assertEq[r[[1]], {g}, "single subgoal == input"];
    HOLTest`assertEq[r[[2]][{ASSUME[p]}], ASSUME[p], "just is identity"];
]];

HOLTest`runTests["tactics: noTac fails", Module[{p},
  p = mkVar["p", boolTy];
  HOLTest`assertThrows[noTac[goal[{}, p]], "tactic", "noTac fires"];
]];

HOLTest`runTests["tactics: conjTac splits", Module[{p, q, g, r},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  g = goal[{}, andTm[p, q]];
  r = conjTac[g];
  HOLTest`assertEq[r[[1]], {goal[{}, p], goal[{}, q]},
    "two subgoals: prove p, prove q"];
  HOLTest`assertEq[concl[r[[2]][{ASSUME[p], ASSUME[q]}]], andTm[p, q],
    "just rebuilds p ∧ q"];
]];

HOLTest`runTests["tactics: conjTac rejects non-∧", Module[{p, g},
  p = mkVar["p", boolTy];
  g = goal[{}, p];
  HOLTest`assertThrows[conjTac[g], "tactic", "rejects non-∧"];
]];

HOLTest`runTests["tactics: disj1Tac", Module[{p, q, g, r, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  g = goal[{}, orTm[p, q]];
  r = disj1Tac[g];
  HOLTest`assertEq[r[[1]], {goal[{}, p]}, "subgoal: prove p"];
  th = r[[2]][{ASSUME[p]}];
  HOLTest`assertEq[concl[th], orTm[p, q], "rebuilds p ∨ q"];
]];

HOLTest`runTests["tactics: disj2Tac", Module[{p, q, g, r, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  g = goal[{}, orTm[p, q]];
  r = disj2Tac[g];
  HOLTest`assertEq[r[[1]], {goal[{}, q]}, "subgoal: prove q"];
  th = r[[2]][{ASSUME[q]}];
  HOLTest`assertEq[concl[th], orTm[p, q], "rebuilds p ∨ q"];
]];

HOLTest`runTests["tactics: genTac strips ∀", Module[{p, target, g, r, x, th},
  p = mkVar["p", boolTy];
  target = forallTm[p, p];
  g = goal[{}, target];
  r = genTac[g];
  HOLTest`assertEq[Length[r[[1]]], 1, "one subgoal"];
  x = r[[1, 1, 2]];
  HOLTest`assertEq[x, p, "opened with the binder's preferred name"];
  th = r[[2]][{REFL[p]}];
  HOLTest`assertEq[concl[th], forallTm[p, mkEq[p, p]],
    "just rebuilds ∀ on a stronger body"];
]];

HOLTest`runTests["tactics: genTac rejects non-∀", Module[{p},
  p = mkVar["p", boolTy];
  HOLTest`assertThrows[genTac[goal[{}, p]], "tactic", "rejects non-∀"];
]];

HOLTest`runTests["tactics: existsTac", Module[{alpha, x, c, target, g, r, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  c = mkVar["c", alpha];
  target = existsTm[x, mkEq[x, c]];
  g = goal[{}, target];
  r = existsTac[c][g];
  HOLTest`assertEq[r[[1]], {goal[{}, mkEq[c, c]]}, "subgoal: c = c"];
  th = r[[2]][{REFL[c]}];
  HOLTest`assertEq[concl[th], target, "just rebuilds ∃"];
]];

HOLTest`runTests["tactics: existsTac type check",
  Module[{alpha, x, c, target, badWit},
    alpha = mkVarType["a"];
    x = mkVar["x", alpha];
    c = mkVar["c", alpha];
    target = existsTm[x, mkEq[x, c]];
    badWit = mkConst["T", boolTy];
    HOLTest`assertThrows[existsTac[badWit][goal[{}, target]], "tactic",
      "rejects wrong-type witness"];
]];

HOLTest`runTests["tactics: dischTac", Module[{p, q, g, r, th, asm},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  g = goal[{}, impTm[p, q]];
  r = dischTac[g];
  HOLTest`assertEq[Length[r[[1]]], 1, "one subgoal"];
  HOLTest`assertEq[r[[1, 1, 2]], q, "concl is q"];
  asm = r[[1, 1, 1, 1]];
  HOLTest`assertEq[concl[asm], p, "asm concl is p"];
  HOLTest`assertEq[hyp[asm], {p}, "asm has hyp p"];
  th = r[[2]][{ASSUME[q]}];
  HOLTest`assertEq[concl[th], impTm[p, q], "rebuilds p ⇒ q"];
]];

HOLTest`runTests["tactics: acceptTac closes matching goal",
  Module[{p, th, r},
    p = mkVar["p", boolTy];
    th = ASSUME[p];
    r = acceptTac[th][goal[{}, p]];
    HOLTest`assertEq[r[[1]], {}, "no subgoals"];
    HOLTest`assertEq[r[[2]][{}], th, "just returns the theorem"];
]];

HOLTest`runTests["tactics: acceptTac rejects mismatch",
  Module[{p, q, th},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    th = ASSUME[p];
    HOLTest`assertThrows[acceptTac[th][goal[{}, q]], "tactic",
      "acceptTac rejects when concl doesn't match"];
]];

HOLTest`runTests["tactics: popAssum applies ttac to last asm",
  Module[{p, q, g, r, th},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    g = goal[{ASSUME[p], ASSUME[q]}, q];
    r = popAssum[acceptTac][g];
    HOLTest`assertEq[r[[1]], {}, "popAssum[acceptTac] closes"];
    th = r[[2]][{}];
    HOLTest`assertEq[concl[th], q, "produces ⊢ q"];
]];

HOLTest`runTests["tactics: popAssum rejects empty asms",
  Module[{p},
    p = mkVar["p", boolTy];
    HOLTest`assertThrows[popAssum[acceptTac][goal[{}, p]], "tactic",
      "empty assumption list"];
]];

HOLTest`runTests["tactics: rewriteTac discharges T",
  Module[{p, eqTh, target, g, r, th},
    p = mkVar["p", boolTy];
    eqTh = ASSUME[mkEq[p, mkConst["T", boolTy]]];
    target = p;
    g = goal[{}, target];
    r = rewriteTac[{eqTh}][g];
    HOLTest`assertEq[r[[1]], {}, "auto-discharges to T"];
    th = r[[2]][{}];
    HOLTest`assertEq[concl[th], p, "produces ⊢ p"];
]];

HOLTest`runTests["tactics: THEN propagates failure",
  Module[{p, q, target, tac},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    target = andTm[p, q];
    tac = THEN[conjTac, acceptTac[ASSUME[andTm[p, q]]]];
    HOLTest`assertThrows[tac[goal[{}, target]], "tactic",
      "THEN: ACCEPT can't match every branch"];
]];

HOLTest`runTests["tactics: THENL branches",
  Module[{p, q, target, asm, tac, th},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    target = andTm[p, q];
    asm = ASSUME[target];
    tac = THENL[conjTac, {
      acceptTac[CONJUNCT1[asm]],
      acceptTac[CONJUNCT2[asm]]
    }];
    th = prove[target, tac];
    HOLTest`assertEq[concl[th], target, "THENL closes both branches"];
    HOLTest`assertEq[hyp[th], {target}, "preserves the asm hyp"];
]];

HOLTest`runTests["tactics: THENL rejects size mismatch",
  Module[{p, q, target, tac},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    target = andTm[p, q];
    tac = THENL[conjTac, {allTac}];
    HOLTest`assertThrows[tac[goal[{}, target]], "tactic",
      "THENL: 2 subgoals, 1 tactic"];
]];

HOLTest`runTests["tactics: ORELSE falls back",
  Module[{p, target, tac, th},
    p = mkVar["p", boolTy];
    target = p;
    tac = ORELSE[conjTac, acceptTac[ASSUME[p]]];
    th = prove[target, tac];
    HOLTest`assertEq[concl[th], p, "ORELSE picks acceptTac"];
]];

HOLTest`runTests["tactics: REPEAT exhausts",
  Module[{p, target, tac, th},
    p = mkVar["p", boolTy];
    target = forallTm[mkVar["a", boolTy],
      forallTm[mkVar["b", boolTy], p]];
    tac = THEN[REPEAT[genTac], acceptTac[ASSUME[p]]];
    th = prove[target, tac];
    HOLTest`assertEq[concl[th], target,
      "REPEAT[genTac] strips both ∀, then accept closes"];
]];

(* M5 acceptance: classical propositional theorems via tactics *)

HOLTest`runTests["tactics M5 acceptance: ⊢ T via acceptTac[TRUTH]",
  Module[{tConst, th},
    tConst = mkConst["T", boolTy];
    th = prove[tConst, acceptTac[TRUTH]];
    HOLTest`assertEq[concl[th], tConst, "⊢ T"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
]];

HOLTest`runTests["tactics M5 acceptance: ⊢ ∀p. p ⇒ p",
  Module[{p, target, tac, th},
    p = mkVar["p", boolTy];
    target = forallTm[p, impTm[p, p]];
    tac = THEN[genTac, THEN[dischTac, popAssum[acceptTac]]];
    th = prove[target, tac];
    HOLTest`assertEq[concl[th], target, "⊢ ∀p. p ⇒ p"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
]];

HOLTest`runTests["tactics M5 acceptance: ⊢ ∀p q. p ∧ q ⇒ q ∧ p",
  Module[{p, q, target, tac, th},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    target = forallTm[p, forallTm[q, impTm[andTm[p, q], andTm[q, p]]]];
    tac = THEN[genTac, THEN[genTac, THEN[dischTac,
      popAssum[Function[asm,
        THENL[conjTac, {
          acceptTac[CONJUNCT2[asm]],
          acceptTac[CONJUNCT1[asm]]
        }]
      ]]
    ]]];
    th = prove[target, tac];
    HOLTest`assertEq[concl[th], target, "⊢ ∀p q. p ∧ q ⇒ q ∧ p"];
    HOLTest`assertEq[hyp[th], {}, "closed theorem"];
]];

HOLTest`runTests["tactics M5 acceptance: ⊢ ∀p q. p ⇒ q ⇒ p ∧ q",
  Module[{p, q, target, tac, th},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    target = forallTm[p, forallTm[q, impTm[p, impTm[q, andTm[p, q]]]]];
    tac = THEN[REPEAT[genTac], THEN[dischTac, THEN[dischTac,
      popAssum[Function[qAsm,
        popAssum[Function[pAsm,
          THENL[conjTac, {acceptTac[pAsm], acceptTac[qAsm]}]
        ]]
      ]]
    ]]];
    th = prove[target, tac];
    HOLTest`assertEq[concl[th], target, "⊢ ∀p q. p ⇒ q ⇒ p ∧ q"];
    HOLTest`assertEq[hyp[th], {}, "closed"];
]];

HOLTest`runTests["tactics: prove rejects unfinished tactic",
  Module[{p, q, target},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    target = andTm[p, q];
    HOLTest`assertThrows[prove[target, conjTac], "tactic",
      "prove demands zero subgoals"];
]];

HOLTest`runTests["tactics: goalstack closure round-trip",
  Module[{gs, p, q, target, th},
    gs = makeGoalstack[];
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    target = forallTm[p, forallTm[q, impTm[andTm[p, q], andTm[q, p]]]];
    gs["g"][target];
    gs["e"][genTac];
    gs["e"][genTac];
    gs["e"][dischTac];
    gs["e"][popAssum[Function[a,
      THENL[conjTac, {
        acceptTac[CONJUNCT2[a]],
        acceptTac[CONJUNCT1[a]]
      }]
    ]]];
    th = gs["finished"][];
    HOLTest`assertEq[concl[th], target, "stepwise proof matches"];
    HOLTest`assertEq[hyp[th], {}, "closed"];
]];

HOLTest`runTests["tactics: goalstack b[] undoes",
  Module[{gs, p, target, after1Top, after2Top},
    gs = makeGoalstack[];
    p = mkVar["p", boolTy];
    target = forallTm[p, p];
    gs["g"][target];
    gs["e"][genTac];
    after1Top = gs["top"][];
    gs["e"][allTac];
    gs["b"][];
    after2Top = gs["top"][];
    HOLTest`assertEq[after2Top, after1Top, "b[] returns to previous state"];
]];

HOLTest`runTests["tactics: goalstack finished[] rejects open goals",
  Module[{gs, p, target},
    gs = makeGoalstack[];
    p = mkVar["p", boolTy];
    target = forallTm[p, p];
    gs["g"][target];
    HOLTest`assertThrows[gs["finished"][], "tactic", "still open"];
]];
