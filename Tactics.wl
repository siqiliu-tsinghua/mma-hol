(* ::Package:: *)

BeginPackage["HOL`Tactics`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
                              "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`"}];

goal::usage      = "goal[asms_List, concl_] — a goalstate node: asms is a list of assumption thms, concl is the term to prove.";
tacResult::usage = "tacResult[subgoals_List, just_] — what every tactic returns: residual subgoals + a justification taking that many proven thms back to a thm of the original goal.";

allTac::usage    = "allTac[g] — identity tactic.";
noTac::usage     = "noTac[g] — always fails with tactic-tagged error.";
conjTac::usage   = "conjTac[g] — splits a ∧ goal into two subgoals.";
disj1Tac::usage  = "disj1Tac[g] — reduces ⊢ p ∨ q to ⊢ p.";
disj2Tac::usage  = "disj2Tac[g] — reduces ⊢ p ∨ q to ⊢ q.";
genTac::usage    = "genTac[g] — strips a leading ∀, opening a fresh variable.";
existsTac::usage = "existsTac[w][g] — to prove ∃x. P[x], reduces to ⊢ P[w].";
dischTac::usage  = "dischTac[g] — to prove p ⇒ q, ASSUMEs p and reduces to ⊢ q.";
assumeTac::usage = "assumeTac[th][g] — adds th to the goal's assumption list.";
acceptTac::usage = "acceptTac[th][g] — closes the goal if concl[th] === goal.concl.";
popAssum::usage  = "popAssum[ttac][g] — pops the most recent assumption and applies the thm-tactic ttac to it on the smaller goal.";
rewriteTac::usage = "rewriteTac[eqThs][g] — rewrites concl using eqThs (DEPTHCONV); auto-discharges if the result is T.";

THEN::usage   = "THEN[t1, t2][g] — apply t1, then t2 to every resulting subgoal.";
THENL::usage  = "THENL[t1, ts][g] — apply t1, then ts[[i]] to subgoal i; lengths must match.";
ORELSE::usage = "ORELSE[t1, t2][g] — try t1; on tactic-tagged failure, try t2.";
REPEAT::usage = "REPEAT[t][g] — apply t repeatedly while it succeeds.";
TRY::usage    = "TRY[t][g] — try t, fall back to allTac.";

prove::usage = "prove[tm, tac] — apply tac to goal[{}, tm]; throws if any subgoal remains, else returns the discharged theorem.";

makeGoalstack::usage = "makeGoalstack[] — returns an Association of {g, e, b, top, finished} closures over private mutable state. Apply g[tm] to start a proof, e[tac] to apply a tactic to the first subgoal, b[] to undo, top[] to inspect, finished[] to extract the theorem when no subgoals remain.";

Begin["`Private`"];

freshName[preferred_String, forbidden_List] :=
  Module[{i, cand},
    If[! MemberQ[forbidden, preferred], Return[preferred]];
    cand = "z"; i = 0;
    While[MemberQ[forbidden, cand],
      i++; cand = "z" <> ToString[i]];
    cand
  ];

allFreeNames[asms_List, c_] :=
  DeleteDuplicates[Join[
    Flatten[Map[Function[t, Map[First, freesIn[concl[t]]]], asms]],
    Map[First, freesIn[c]]
  ]];

splitByLengths[list_List, lens_List] :=
  Module[{cum},
    cum = Prepend[Accumulate[lens], 0];
    Table[list[[cum[[i]] + 1 ;; cum[[i + 1]]]], {i, Length[lens]}]
  ];

threadOver[r_, t_] :=
  Module[{sgs, just, subres, innerCounts, allSub, justList, finalJust},
    sgs = r[[1]]; just = r[[2]];
    subres = Map[t, sgs];
    innerCounts = Map[Length[#[[1]]] &, subres];
    allSub = Flatten[Map[#[[1]] &, subres], 1];
    justList = Map[#[[2]] &, subres];
    finalJust = Function[{thList},
      Module[{p, m},
        p = splitByLengths[thList, innerCounts];
        m = MapThread[#1[#2] &, {justList, p}];
        just[m]
      ]
    ];
    tacResult[allSub, finalJust]
  ];

threadByList[r_, ts_List] :=
  Module[{sgs, just, subres, innerCounts, allSub, justList, finalJust},
    sgs = r[[1]]; just = r[[2]];
    If[Length[sgs] =!= Length[ts],
      HOL`Error`holError["tactic", "THENL: subgoal count mismatch",
        <|"got" -> Length[sgs], "expected" -> Length[ts]|>]];
    subres = MapThread[#1[#2] &, {ts, sgs}];
    innerCounts = Map[Length[#[[1]]] &, subres];
    allSub = Flatten[Map[#[[1]] &, subres], 1];
    justList = Map[#[[2]] &, subres];
    finalJust = Function[{thList},
      Module[{p, m},
        p = splitByLengths[thList, innerCounts];
        m = MapThread[#1[#2] &, {justList, p}];
        just[m]
      ]
    ];
    tacResult[allSub, finalJust]
  ];

SetAttributes[tryTactic, HoldFirst];
tryTactic[expr_] :=
  Module[{r},
    r = Catch[expr, HOL`Error`holErrorTag];
    Which[
      MatchQ[r, _Failure] && r[[2, "tag"]] === "tactic", $tacFailed,
      MatchQ[r, _Failure], Throw[r, HOL`Error`holErrorTag],
      True, r
    ]
  ];

HOL`Tactics`allTac[g_goal] :=
  tacResult[{g}, Function[{thList}, thList[[1]]]];

HOL`Tactics`noTac[g_goal] :=
  HOL`Error`holError["tactic", "noTac", <|"goal" -> g|>];

HOL`Tactics`THEN[t1_, t2_][g_goal] := threadOver[t1[g], t2];

HOL`Tactics`THENL[t1_, ts_List][g_goal] := threadByList[t1[g], ts];

HOL`Tactics`ORELSE[t1_, t2_][g_goal] :=
  Module[{r},
    r = tryTactic[t1[g]];
    If[r === $tacFailed, t2[g], r]
  ];

HOL`Tactics`REPEAT[t_][g_goal] :=
  Module[{r},
    r = tryTactic[t[g]];
    If[r === $tacFailed,
      HOL`Tactics`allTac[g],
      threadOver[r, HOL`Tactics`REPEAT[t]]
    ]
  ];

HOL`Tactics`TRY[t_][g_goal] :=
  HOL`Tactics`ORELSE[t, HOL`Tactics`allTac][g];

HOL`Tactics`conjTac[goal[asms_, c_]] :=
  Module[{p, q},
    If[! MatchQ[c, comb[comb[const["∧", _], _], _]],
      HOL`Error`holError["tactic", "conjTac: goal not ∧", <|"goal" -> c|>]];
    p = c[[1, 2]]; q = c[[2]];
    tacResult[
      {goal[asms, p], goal[asms, q]},
      Function[{thList}, CONJ[thList[[1]], thList[[2]]]]
    ]
  ];

HOL`Tactics`disj1Tac[goal[asms_, c_]] :=
  Module[{p, q},
    If[! MatchQ[c, comb[comb[const["∨", _], _], _]],
      HOL`Error`holError["tactic", "disj1Tac: goal not ∨", <|"goal" -> c|>]];
    p = c[[1, 2]]; q = c[[2]];
    tacResult[{goal[asms, p]},
      Function[{thList}, DISJ1[thList[[1]], q]]]
  ];

HOL`Tactics`disj2Tac[goal[asms_, c_]] :=
  Module[{p, q},
    If[! MatchQ[c, comb[comb[const["∨", _], _], _]],
      HOL`Error`holError["tactic", "disj2Tac: goal not ∨", <|"goal" -> c|>]];
    p = c[[1, 2]]; q = c[[2]];
    tacResult[{goal[asms, q]},
      Function[{thList}, DISJ2[thList[[1]], p]]]
  ];

HOL`Tactics`genTac[goal[asms_, c_]] :=
  Module[{lamTm, xTy, origin, forbidden, name, v, openTh, opened},
    If[! MatchQ[c, comb[const["∀", _], abs[bvar[0, _], _, _String]]],
      HOL`Error`holError["tactic", "genTac: goal not ∀", <|"goal" -> c|>]];
    lamTm = c[[2]];
    xTy = lamTm[[1, 2]];
    origin = lamTm[[3]];
    forbidden = allFreeNames[asms, c];
    name = freshName[origin, forbidden];
    v = mkVar[name, xTy];
    openTh = BETA[comb[abs[bvar[0, xTy], lamTm[[2]], origin], v]];
    opened = concl[openTh][[2]];
    tacResult[{goal[asms, opened]},
      Function[{thList}, GEN[v, thList[[1]]]]]
  ];

HOL`Tactics`existsTac[w_][goal[asms_, c_]] :=
  Module[{P, xTy, betaTh, opened},
    If[! MatchQ[c, comb[const["∃", _], abs[bvar[0, _], _, _String]]],
      HOL`Error`holError["tactic", "existsTac: goal not ∃", <|"goal" -> c|>]];
    P = c[[2]];
    xTy = typeOf[P] /. tyApp["fun", {a_, _}] :> a;
    If[typeOf[w] =!= xTy,
      HOL`Error`holError["tactic", "existsTac: witness type mismatch",
        <|"binderType" -> xTy, "witnessType" -> typeOf[w]|>]];
    betaTh = BETACONV[mkComb[P, w]];
    opened = concl[betaTh][[2]];
    tacResult[{goal[asms, opened]},
      Function[{thList}, EXISTS[c, w, thList[[1]]]]]
  ];

HOL`Tactics`dischTac[goal[asms_, c_]] :=
  Module[{p, q, asTh},
    If[! MatchQ[c, comb[comb[const["⇒", _], _], _]],
      HOL`Error`holError["tactic", "dischTac: goal not ⇒", <|"goal" -> c|>]];
    p = c[[1, 2]]; q = c[[2]];
    asTh = ASSUME[p];
    tacResult[{goal[Append[asms, asTh], q]},
      Function[{thList}, DISCH[p, thList[[1]]]]]
  ];

HOL`Tactics`assumeTac[th_][goal[asms_, c_]] :=
  tacResult[{goal[Append[asms, th], c]},
    Function[{thList}, thList[[1]]]];

HOL`Tactics`acceptTac[th_][goal[asms_, c_]] :=
  If[concl[th] === c,
    tacResult[{}, Function[{thList}, th]],
    HOL`Error`holError["tactic", "acceptTac: theorem doesn't match goal",
      <|"thmConcl" -> concl[th], "goal" -> c|>]
  ];

HOL`Tactics`popAssum[ttac_][goal[asms_, c_]] :=
  If[asms === {},
    HOL`Error`holError["tactic", "popAssum: empty assumptions", <||>],
    Module[{popped, rest},
      popped = Last[asms];
      rest = Most[asms];
      ttac[popped][goal[rest, c]]
    ]
  ];

HOL`Tactics`rewriteTac[eqThs_List][goal[asms_, c_]] :=
  Module[{combinedConv, eqRes, newConcl, tConst},
    tConst = mkConst["T", boolTy];
    combinedConv = If[Length[eqThs] === 0,
      ALLCONV,
      DEPTHCONV[Fold[ORELSEC, NOCONV, REWRCONV /@ eqThs]]
    ];
    eqRes = combinedConv[c];
    newConcl = concl[eqRes][[2]];
    Which[
      newConcl === c,
        tacResult[{goal[asms, c]}, Function[{thList}, thList[[1]]]],
      newConcl === tConst,
        tacResult[{}, Function[{ignored}, EQMP[SYM[eqRes], TRUTH]]],
      True,
        tacResult[{goal[asms, newConcl]},
          Function[{thList}, EQMP[SYM[eqRes], thList[[1]]]]]
    ]
  ];

HOL`Tactics`prove[tm_, tac_] :=
  Module[{g, r},
    g = goal[{}, tm];
    r = tac[g];
    If[Length[r[[1]]] =!= 0,
      HOL`Error`holError["tactic", "prove: tactic produced subgoals",
        <|"remaining" -> Length[r[[1]]]|>]];
    r[[2]][{}]
  ];

HOL`Tactics`makeGoalstack[] :=
  Module[{state},
    Module[{startG, applyE, backB, viewTop, finishF, threadFirst},
      state = {};
      threadFirst[tacResult[sgList_, just_], tac_] :=
        Module[{firstSg, restSgs, r, innerSgs, innerJust, k, newSgs, newJust},
          firstSg = First[sgList];
          restSgs = Rest[sgList];
          r = tac[firstSg];
          innerSgs = r[[1]]; innerJust = r[[2]];
          k = Length[innerSgs];
          newSgs = Join[innerSgs, restSgs];
          newJust = Function[{thList},
            Module[{firstChunk, rest, firstThm},
              firstChunk = thList[[1 ;; k]];
              rest = thList[[k + 1 ;;]];
              firstThm = innerJust[firstChunk];
              just[Prepend[rest, firstThm]]
            ]
          ];
          tacResult[newSgs, newJust]
        ];
      startG[tm_] := Module[{init},
        init = tacResult[{goal[{}, tm]},
          Function[{thList}, thList[[1]]]];
        state = {init};
        "started"
      ];
      applyE[tac_] := Module[{cur, newRes},
        If[state === {},
          HOL`Error`holError["tactic", "goalstack: empty stack", <||>]];
        cur = First[state];
        If[Length[cur[[1]]] === 0,
          HOL`Error`holError["tactic", "goalstack: no remaining subgoals", <||>]];
        newRes = threadFirst[cur, tac];
        state = Prepend[state, newRes];
        "advanced"
      ];
      backB[] := If[Length[state] > 1,
        state = Rest[state]; "backed",
        "no history"
      ];
      viewTop[] := If[state === {}, None, First[state]];
      finishF[] := Module[{cur},
        If[state === {},
          HOL`Error`holError["tactic", "goalstack: empty", <||>]];
        cur = First[state];
        If[Length[cur[[1]]] =!= 0,
          HOL`Error`holError["tactic", "goalstack: not yet proved",
            <|"remaining" -> Length[cur[[1]]]|>]];
        cur[[2]][{}]
      ];
      <|"g" -> startG, "e" -> applyE, "b" -> backB,
        "top" -> viewTop, "finished" -> finishF|>
    ]
  ];

End[];
EndPackage[];
