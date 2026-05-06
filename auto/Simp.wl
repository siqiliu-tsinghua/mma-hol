(* ::Package:: *)

(* M7-β SIMP — simplification tactic over rewriting + β.

   β-1: strip ∀ from each input thm via specWithFreshName, EQT-coerce
   non-(equational|conditional) concl into ⊢ p = T; DEPTHCONV[ORELSEC[
   rule-convs, BETACONV]] to fixpoint with cycle detection.

   β-2: support conditional rules `⊢ P1 ⇒ … ⇒ Pn ⇒ lhs = rhs`. After
   matching the equation's LHS against a target, INST σ into the whole
   theorem, beta-reduce, then prove each σ(Pi) by recursive simpProve
   (depth-limited to prevent loops) and MP it in. Built on `matchPattern`
   from Drule.wl which uses the same depth-aware HO Miller matcher
   REWRCONV uses.

   Trust boundary: rule normalization runs in untrusted code; every rule
   ends as a kernel-validated theorem (SPEC / EQTINTRO / user-supplied),
   so a bug in normalization can only mean "rule discarded", never "false
   theorem". *)

BeginPackage["HOL`Auto`Simp`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Tactics`", "HOL`Auto`Meson`"
}];

simpConv::usage =
  "simpConv[thms_List][t_] — runs the user thms (∀-stripped, =T-coerced "<>
  "for non-rule concl's) plus BETACONV at every subterm, iterating to "  <>
  "fixpoint with cycle detection. Conditional rules `P1 ⇒ … ⇒ lhs = rhs` "<>
  "discharge their preconditions by recursive simpProve (depth-limited).";

simpProve::usage =
  "simpProve[t_, thms_List] — if simpConv reduces t to T, returns Γ ⊢ t " <>
  "via EQTELIM. Throws \"simp\" otherwise.";

SIMP::usage =
  "SIMP[thms_List][g_goal] — tactic that runs simpConv on the goal's "   <>
  "conclusion. If the result is T, closes via TRUTH; else replaces the " <>
  "goal with the simplified concl.";

simpPrepareRule::usage =
  "simpPrepareRule[th] — strip leading ∀'s via specWithFreshName; if "   <>
  "the resulting concl is neither an equation nor a conditional rule, "  <>
  "EQT-coerce to ⊢ p = T. Returns the prepared rule theorem.";

Begin["`Private`"];

(* ------------- shape predicates ------------- *)

isEquation[t_] :=
  MatchQ[t, comb[comb[const["=", _], _], _]];

isImp[t_] :=
  MatchQ[t, comb[comb[const["⇒", _], _], _]];

isForall[t_] :=
  MatchQ[t, comb[const["∀", _], abs[bvar[0, _], _, _]]];

(* Strip implications until the conseq is no longer an implication.       *)
(* Returns {antecedents-in-order, finalConseq}.                          *)
stripImps[t_] :=
  Module[{cur = t, ants = {}, a, c},
    While[isImp[cur],
      a = cur[[1, 2]];
      c = cur[[2]];
      AppendTo[ants, a];
      cur = c
    ];
    {ants, cur}
  ];

isConditionalRule[t_] :=
  isImp[t] && isEquation[stripImps[t][[2]]];

(* Productivity: the underlying equation's LHS is not aconv RHS.         *)
(* Eq-rule: check the concl directly. Conditional: check the final        *)
(* equation slot. Anything else returns False (filtered out).            *)
productiveSimpRule[ruleTh_] :=
  Module[{c, eqPart, lhs, rhs},
    c = concl[ruleTh];
    eqPart = If[isImp[c], stripImps[c][[2]], c];
    If[!isEquation[eqPart], Return[False]];
    lhs = eqPart[[1, 2]]; rhs = eqPart[[2]];
    !aconv[lhs, rhs]
  ];

(* ------------- rule preparation ------------- *)

HOL`Auto`Simp`simpPrepareRule[th_] :=
  Module[{cur = th, c},
    While[isForall[concl[cur]],
      cur = HOL`Auto`Meson`specWithFreshName[cur]];
    c = concl[cur];
    If[isEquation[c] || isConditionalRule[c],
      cur,
      HOL`Bool`EQTINTRO[cur]]
  ];

(* ------------- fixpoint CONV iterator ------------- *)

fixpointConv[conv_, t_] :=
  Module[{cur, rhs, next, newRhs, seen},
    cur = conv[t];
    rhs = concl[cur][[2]];
    seen = <|t -> True, rhs -> True|>;
    While[True,
      next = conv[rhs];
      newRhs = concl[next][[2]];
      If[newRhs === rhs, Break[]];
      If[KeyExistsQ[seen, newRhs], Break[]];
      cur = TRANS[cur, next];
      rhs = newRhs;
      seen[newRhs] = True
    ];
    cur
  ];

(* ------------- conditional rewrite ------------- *)

(* Match the final equation's LHS, INST σ into the entire conditional   *)
(* rule, beta-reduce, then for each surviving antecedent (in order)      *)
(* invoke `prover` to obtain ⊢ ant[σ] and MP it through.                 *)
condRewrConv[ruleTh_, prover_][t_] :=
  Module[{c, ants, eqPart, lhs, matchRes, tsubst, tysubst,
          thAfterTy, tsubstKeyed, thFinal, betaConv, antTm, antThm,
          currentConcl, k},
    c = concl[ruleTh];
    {ants, eqPart} = stripImps[c];
    If[!isEquation[eqPart],
      Throw[HOL`Error`holError["conv",
        "condRewrConv: rule does not end in an equation",
        <|"concl" -> c|>], HOL`Error`holErrorTag]];
    lhs = eqPart[[1, 2]];
    matchRes = HOL`Drule`matchPattern[lhs, t];
    If[MissingQ[matchRes],
      Throw[HOL`Error`holError["conv",
        "condRewrConv: lhs does not match target",
        <|"lhs" -> lhs, "target" -> t|>], HOL`Error`holErrorTag]];
    {tsubst, tysubst} = matchRes;
    thAfterTy = If[Length[tysubst] > 0,
      INSTTYPE[Normal[tysubst], ruleTh], ruleTh];
    tsubstKeyed = Map[instType[tysubst, #[[1]]] -> #[[2]] &, Normal[tsubst]];
    thFinal = If[Length[tsubstKeyed] > 0,
      INST[tsubstKeyed, thAfterTy], thAfterTy];
    (* Beta-reduce HO redexes introduced by INST before discharging      *)
    (* antecedents — the prover should see beta-normal terms.            *)
    betaConv = HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]];
    thFinal = HOL`Drule`CONVRULE[betaConv, thFinal];
    Do[
      currentConcl = concl[thFinal];
      If[!isImp[currentConcl], Break[]];
      antTm = currentConcl[[1, 2]];
      antThm = prover[antTm];   (* throws on failure → ORELSEC catches *)
      thFinal = HOL`Bool`MP[thFinal, antThm];
      , {k, 1, Length[ants]}];
    thFinal
  ];

(* ------------- per-rule dispatcher ------------- *)

simpRuleConv[ruleTh_, prover_][t_] :=
  Module[{c},
    c = concl[ruleTh];
    Which[
      isEquation[c],         HOL`Drule`REWRCONV[ruleTh][t],
      isConditionalRule[c],  condRewrConv[ruleTh, prover][t],
      True,
        Throw[HOL`Error`holError["conv",
          "simpRuleConv: rule is neither equation nor conditional",
          <|"concl" -> c|>], HOL`Error`holErrorTag]
    ]
  ];

combineSimpConvs[{}]         := BETACONV;
combineSimpConvs[{conv_}]    := HOL`Drule`ORELSEC[conv, BETACONV];
combineSimpConvs[{conv_, rest__}] :=
  HOL`Drule`ORELSEC[conv, combineSimpConvs[{rest}]];

(* ------------- depth-limited driver ------------- *)

(* Each conditional discharge through `prover` re-enters simpConvImpl at *)
(* depth - 1; once depth hits 0 the prover is replaced by a stub that   *)
(* always fails, blocking further conditional rule firings. This caps    *)
(* recursion in the presence of mutually-conditional rule sets.          *)
$simpDepthLimit = 4;

(* The prover discharges antecedents in conditional rules. Tries:        *)
(*   1. direct lookup of antTm against original-thm concls (avoids       *)
(*      bare-var LHS over-matching that would happen if we always went   *)
(*      through simpConv → REWRCONV);                                    *)
(*   2. T-shortcut → TRUTH;                                              *)
(*   3. recursive simpProve at depth - 1.                                *)
(* When depth has hit zero only the lookup paths are tried — recursive   *)
(* simpProve is disabled.                                                *)
makeProver[origThms_List, depth_Integer] :=
  Function[{antTm},
    Module[{direct, T},
      direct = SelectFirst[origThms, aconv[concl[#], antTm] &, Missing[]];
      T = mkConst["T", boolTy];
      Which[
        !MissingQ[direct], direct,
        antTm === T,       HOL`Bool`TRUTH,
        depth > 0,         simpProveImpl[origThms, depth - 1, antTm],
        True,
          Throw[HOL`Error`holError["simp",
            "simp: cannot discharge antecedent (depth exhausted)",
            <|"target" -> antTm|>], HOL`Error`holErrorTag]
      ]
    ]
  ];

simpConvImpl[thms_List, depth_Integer][t_] :=
  Module[{prepared, productive, prover, ruleConvs, baseConv, depthConv},
    prepared = HOL`Auto`Simp`simpPrepareRule /@ thms;
    productive = Select[prepared, productiveSimpRule];
    prover = makeProver[thms, depth];
    ruleConvs = simpRuleConv[#, prover] & /@ productive;
    baseConv  = combineSimpConvs[ruleConvs];
    depthConv = HOL`Drule`DEPTHCONV[baseConv];
    fixpointConv[depthConv, t]
  ];

simpProveImpl[thms_List, depth_Integer, t_] :=
  Module[{eqTh, rhs, T},
    eqTh = simpConvImpl[thms, depth][t];
    rhs = concl[eqTh][[2]];
    T = mkConst["T", boolTy];
    If[rhs =!= T,
      Throw[HOL`Error`holError["simp",
        "simpProve: simplification did not reach T",
        <|"target" -> t, "simplified" -> rhs|>], HOL`Error`holErrorTag]];
    HOL`Bool`EQTELIM[eqTh]
  ];

HOL`Auto`Simp`simpConv[thms_List][t_] :=
  simpConvImpl[thms, $simpDepthLimit][t];

HOL`Auto`Simp`simpProve[t_, thms_List] :=
  simpProveImpl[thms, $simpDepthLimit, t];

HOL`Auto`Simp`SIMP[thms_List][g : HOL`Tactics`goal[asms_, conclTm_]] :=
  Module[{eqTh, rhs, T, just},
    eqTh = HOL`Auto`Simp`simpConv[thms][conclTm];
    rhs = concl[eqTh][[2]];
    T = mkConst["T", boolTy];
    If[rhs === T,
      just = Function[{ths}, HOL`Bool`EQTELIM[eqTh]];
      HOL`Tactics`tacResult[{}, just],
      just = Function[{ths},
        EQMP[HOL`Equal`SYM[eqTh], First[ths]]];
      HOL`Tactics`tacResult[
        {HOL`Tactics`goal[asms, rhs]}, just]
    ]
  ];

End[];
EndPackage[];
