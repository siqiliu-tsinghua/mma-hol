(* ::Package:: *)

(* M7-β SIMP — simplification tactic over rewriting + β.

   MVP (β-1): strip ∀ from each input thm via specWithFreshName, EQT-coerce
   non-equations into ⊢ p = T, then apply DEPTHCONV[ORELSEC[REWRCONV-rules,
   BETACONV]] iteratively to fixpoint with cycle detection. No conditional
   rewriting yet (β-2 will lift `⊢ P ⇒ lhs = rhs` rules).

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
  "simpConv[thms_List][t_] — runs the user thms (∀-stripped, =T-coerced) "<>
  "plus BETACONV at every subterm, iterating to fixpoint with cycle "    <>
  "detection. Returns Γ ⊢ t = t'.";

simpProve::usage =
  "simpProve[t_, thms_List] — if simpConv reduces t to T, returns Γ ⊢ t " <>
  "via EQTELIM. Throws otherwise.";

SIMP::usage =
  "SIMP[thms_List][g_goal] — tactic that runs simpConv on the goal's "   <>
  "conclusion. If the result is T, closes via TRUTH; else replaces the " <>
  "goal with the simplified concl.";

simpPrepareRule::usage =
  "simpPrepareRule[th] — strip leading ∀'s via specWithFreshName and "   <>
  "EQT-coerce a non-equational concl. Returns the prepared rule "        <>
  "theorem suitable for REWRCONV.";

Begin["`Private`"];

simpFail[msg_String] :=
  HOL`Error`holError["simp", msg, <||>];
simpFail[msg_String, extra_Association] :=
  HOL`Error`holError["simp", msg, extra];

isEquation[t_] :=
  MatchQ[t, comb[comb[const["=", _], _], _]];

isForall[t_] :=
  MatchQ[t, comb[const["∀", _], abs[bvar[0, _], _, _]]];

HOL`Auto`Simp`simpPrepareRule[th_] :=
  Module[{cur = th, c},
    While[isForall[concl[cur]],
      cur = HOL`Auto`Meson`specWithFreshName[cur]];
    c = concl[cur];
    If[isEquation[c], cur, HOL`Bool`EQTINTRO[cur]]
  ];

(* Fixed-point CONV iterator with cycle detection. Each step produces      *)
(* ⊢ rhs_n = rhs_{n+1}; we TRANS-chain into the running ⊢ t = rhs_n. Stop  *)
(* when rhs_{n+1} === rhs_n (stable) or when rhs_{n+1} is a previously     *)
(* seen rhs (cycle). DEPTHCONV always succeeds (returns REFL on no-match), *)
(* so we don't need to catch conv failures.                                *)
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

(* Right-associated ORELSEC: try each rule in order, fall through to     *)
(* BETACONV. Don't wrap BETACONV in TRYCONV — TRYCONV always succeeds,   *)
(* which would block ORELSEC from ever reaching the user rules.          *)
combineSimpConvs[{}]         := BETACONV;
combineSimpConvs[{conv_}]    := HOL`Drule`ORELSEC[conv, BETACONV];
combineSimpConvs[{conv_, rest__}] :=
  HOL`Drule`ORELSEC[conv, combineSimpConvs[{rest}]];

HOL`Auto`Simp`simpConv[thms_List][t_] :=
  Module[{prepared, productive, baseConv, depthConv},
    prepared = HOL`Auto`Simp`simpPrepareRule /@ thms;
    productive = Select[prepared, HOL`Drule`productiveEqThm];
    baseConv = combineSimpConvs[HOL`Drule`REWRCONV /@ productive];
    depthConv = HOL`Drule`DEPTHCONV[baseConv];
    fixpointConv[depthConv, t]
  ];

HOL`Auto`Simp`simpProve[t_, thms_List] :=
  Module[{eqTh, rhs, T},
    eqTh = HOL`Auto`Simp`simpConv[thms][t];
    rhs = concl[eqTh][[2]];
    T = mkConst["T", boolTy];
    If[rhs =!= T,
      simpFail["simpProve: simplification did not reach T",
        <|"target" -> t, "simplified" -> rhs|>]];
    HOL`Bool`EQTELIM[eqTh]
  ];

HOL`Auto`Simp`SIMP[thms_List][g : HOL`Tactics`goal[asms_, conclTm_]] :=
  Module[{eqTh, rhs, T, simpThm, just},
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
