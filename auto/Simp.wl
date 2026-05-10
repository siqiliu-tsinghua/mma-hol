(* ::Package:: *)

(* M7-β SIMP — simplification tactic over rewriting + β.

   β-1: strip ∀ from each input thm via specWithFreshName, EQT-coerce
   non-(equational|conditional) concl into ⊢ p = T; iterate to fixpoint
   with cycle detection.

   β-1.5: built-in basicSimpset of 19 propositional schemas (T∧p=p,
   ¬¬p=p, p⇒p=T, …) proved once via propTaut and cached.

   β-2: support conditional rules `⊢ P1 ⇒ … ⇒ Pn ⇒ lhs = rhs`. After
   matching the equation's LHS against a target, INST σ into the whole
   theorem, beta-reduce, then prove each σ(Pi) by recursive simpProve
   (depth-limited to prevent loops) and MP it in.

   β-3: context-aware congruence descent at ⇒ / ∧ / ∨ positions. The
   simplification of `q` under `(p ⇒ q)` (resp. `(p ∧ q)`) runs with
   the simplified left-hand p' added to the assumption context; under
   `(p ∨ q)` the right-hand context is `¬p'`. ctxAsms appear in the
   inner simpFixpointConv as: (1) ctxRewrConv exact-match rewriters
   that turn an aconv-equal subterm into ⊢ subterm = T, and (2) facts
   for the prover's direct lookup when discharging conditional-rule
   antecedents. Each congruence is realised via a propTaut-derived
   schema lemma plus DISCH/CONJ/INST/MP plumbing.

   Trust boundary: rule normalization runs in untrusted code; every
   rule ends as a kernel-validated theorem (SPEC / EQTINTRO /
   user-supplied), so a bug in normalization can only mean "rule
   discarded", never "false theorem". *)

BeginPackage["HOL`Auto`Simp`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Tactics`", "HOL`Auto`PropTaut`", "HOL`Auto`Meson`"
}];

simpConv::usage =
  "simpConv[thms_List][t_] — runs the user thms (∀-stripped, =T-coerced "<>
  "for non-rule concl's) plus BETACONV at every subterm; iterates to "   <>
  "fixpoint with cycle detection. Conditional rules `P1 ⇒ … ⇒ lhs = rhs` "<>
  "discharge their preconditions by recursive simpProve. Descends with " <>
  "context-aware congruence at ⇒ / ∧ / ∨.";

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

basicSimpset::usage =
  "basicSimpset[] — list of propositional simplification theorems "      <>
  "(T∧p=p, ¬¬p=p, p⇒p=T, …) proved once via propTaut and cached. SIMP " <>
  "and simpProve prepend this list AFTER the user's thms so user rules " <>
  "are tried first; combineSimpConvs preserves the order via right-"     <>
  "associated ORELSEC.";

Begin["`Private`"];

(* ============================================================ *)
(* shape predicates                                             *)
(* ============================================================ *)

isEquation[t_] :=
  MatchQ[t, comb[comb[const["=", _], _], _]];

isImp[t_] :=
  MatchQ[t, comb[comb[const["⇒", _], _], _]];

isAndForm[t_] :=
  MatchQ[t, comb[comb[const["∧", _], _], _]];

isOrForm[t_] :=
  MatchQ[t, comb[comb[const["∨", _], _], _]];

isForall[t_] :=
  MatchQ[t, comb[const["∀", _], abs[bvar[0, _], _, _]]];

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

productiveSimpRule[ruleTh_] :=
  Module[{c, eqPart, lhs, rhs},
    c = concl[ruleTh];
    eqPart = If[isImp[c], stripImps[c][[2]], c];
    If[!isEquation[eqPart], Return[False]];
    lhs = eqPart[[1, 2]]; rhs = eqPart[[2]];
    !aconv[lhs, rhs]
  ];

(* ============================================================ *)
(* rule preparation                                             *)
(* ============================================================ *)

HOL`Auto`Simp`simpPrepareRule[th_] :=
  Module[{cur = th, c},
    While[isForall[concl[cur]],
      cur = HOL`Auto`Meson`specWithFreshName[cur]];
    c = concl[cur];
    If[isEquation[c] || isConditionalRule[c],
      cur,
      HOL`Bool`EQTINTRO[cur]]
  ];

(* ============================================================ *)
(* canonical bool constants (factored to keep schema code tight)*)
(* ============================================================ *)

andConst[] := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
orConst[]  := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
impConst[] := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notConst[] := mkConst["¬", tyFun[boolTy, boolTy]];
eqConst[]  := mkConst["=", tyFun[boolTy, tyFun[boolTy, boolTy]]];
tConst[]   := mkConst["T", boolTy];
fConst[]   := mkConst["F", boolTy];

mkAnd[a_, b_] := mkComb[mkComb[andConst[], a], b];
mkOr[a_, b_]  := mkComb[mkComb[orConst[], a], b];
mkImp[a_, b_] := mkComb[mkComb[impConst[], a], b];
mkNot[a_]     := mkComb[notConst[], a];

(* ============================================================ *)
(* built-in propositional simpset (β-1.5)                       *)
(* ============================================================ *)

computeBasicSimpset[] :=
  Module[{p, T, F, schemas},
    p = mkVar["p", boolTy];
    T = tConst[]; F = fConst[];
    schemas = {
      mkEq[mkAnd[T, p], p],            (* T ∧ p = p     *)
      mkEq[mkAnd[p, T], p],            (* p ∧ T = p     *)
      mkEq[mkAnd[F, p], F],            (* F ∧ p = F     *)
      mkEq[mkAnd[p, F], F],            (* p ∧ F = F     *)
      mkEq[mkAnd[p, p], p],            (* p ∧ p = p     *)
      mkEq[mkOr[T, p], T],             (* T ∨ p = T     *)
      mkEq[mkOr[p, T], T],             (* p ∨ T = T     *)
      mkEq[mkOr[F, p], p],             (* F ∨ p = p     *)
      mkEq[mkOr[p, F], p],             (* p ∨ F = p     *)
      mkEq[mkOr[p, p], p],             (* p ∨ p = p     *)
      mkEq[mkImp[T, p], p],            (* T ⇒ p = p     *)
      mkEq[mkImp[F, p], T],            (* F ⇒ p = T     *)
      mkEq[mkImp[p, T], T],            (* p ⇒ T = T     *)
      mkEq[mkImp[p, p], T],            (* p ⇒ p = T     *)
      mkEq[mkNot[T], F],               (* ¬T = F        *)
      mkEq[mkNot[F], T],               (* ¬F = T        *)
      mkEq[mkNot[mkNot[p]], p],        (* ¬¬p = p       *)
      mkEq[mkComb[mkComb[eqConst[], T], p], p],   (* (T = p) = p *)
      mkEq[mkComb[mkComb[eqConst[], p], T], p]    (* (p = T) = p *)
    };
    Map[HOL`Auto`PropTaut`propTaut, schemas]
  ];

HOL`Auto`Simp`basicSimpset[] := HOL`Auto`Simp`basicSimpset[] = computeBasicSimpset[];

(* ============================================================ *)
(* congruence schema lemmas (β-3) — propTaut, lazy-cached       *)
(* ============================================================ *)

computeImpCongLemma[] :=
  Module[{p1, p2, q1, q2},
    p1 = mkVar["p1", boolTy]; p2 = mkVar["p2", boolTy];
    q1 = mkVar["q1", boolTy]; q2 = mkVar["q2", boolTy];
    HOL`Auto`PropTaut`propTaut[
      mkImp[
        mkAnd[mkEq[p1, p2], mkImp[p2, mkEq[q1, q2]]],
        mkEq[mkImp[p1, q1], mkImp[p2, q2]]]]
  ];

computeAndCongLemma[] :=
  Module[{p1, p2, q1, q2},
    p1 = mkVar["p1", boolTy]; p2 = mkVar["p2", boolTy];
    q1 = mkVar["q1", boolTy]; q2 = mkVar["q2", boolTy];
    HOL`Auto`PropTaut`propTaut[
      mkImp[
        mkAnd[mkEq[p1, p2], mkImp[p2, mkEq[q1, q2]]],
        mkEq[mkAnd[p1, q1], mkAnd[p2, q2]]]]
  ];

computeOrCongLemma[] :=
  Module[{p1, p2, q1, q2},
    p1 = mkVar["p1", boolTy]; p2 = mkVar["p2", boolTy];
    q1 = mkVar["q1", boolTy]; q2 = mkVar["q2", boolTy];
    HOL`Auto`PropTaut`propTaut[
      mkImp[
        mkAnd[mkEq[p1, p2], mkImp[mkNot[p2], mkEq[q1, q2]]],
        mkEq[mkOr[p1, q1], mkOr[p2, q2]]]]
  ];

impCongLemma[] := impCongLemma[] = computeImpCongLemma[];
andCongLemma[] := andCongLemma[] = computeAndCongLemma[];
orCongLemma[]  := orCongLemma[]  = computeOrCongLemma[];

(* ============================================================ *)
(* fresh-name picker for abs descent                            *)
(* ============================================================ *)

pickFreshNm[preferred_String, forbidden_List] :=
  Module[{i, cand},
    If[!MemberQ[forbidden, preferred], Return[preferred]];
    cand = "z"; i = 0;
    While[MemberQ[forbidden, cand],
      i++; cand = "z" <> ToString[i]];
    cand
  ];

(* ============================================================ *)
(* per-rule conv dispatch                                       *)
(* ============================================================ *)

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
    betaConv = HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]];
    thFinal = HOL`Drule`CONVRULE[betaConv, thFinal];
    Do[
      currentConcl = concl[thFinal];
      If[!isImp[currentConcl], Break[]];
      antTm = currentConcl[[1, 2]];
      antThm = prover[antTm];
      thFinal = HOL`Bool`MP[thFinal, antThm];
      , {k, 1, Length[ants]}];
    thFinal
  ];

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

(* Exact-match assumption rewrite: turns ⊢ asm = T into a conv that *)
(* fires only when the target is α-equal to asm. Uses ASSUME[asm]   *)
(* internally so the resulting equation carries asm as a hypothesis. *)
ctxRewrConv[asm_][t_] :=
  If[aconv[t, asm],
    HOL`Bool`EQTINTRO[ASSUME[asm]],
    Throw[HOL`Error`holError["conv",
      "ctxRewrConv: target not α-equal to context assumption",
      <|"target" -> t, "asm" -> asm|>], HOL`Error`holErrorTag]];

combineSimpConvs[{}]         := BETACONV;
combineSimpConvs[{conv_}]    := HOL`Drule`ORELSEC[conv, BETACONV];
combineSimpConvs[{conv_, rest__}] :=
  HOL`Drule`ORELSEC[conv, combineSimpConvs[{rest}]];

(* ============================================================ *)
(* prover for conditional-rule antecedents                      *)
(* ============================================================ *)

$simpDepthLimit = 4;

makeProver[origThms_List, ctxAsms_List, depth_Integer] :=
  Function[{antTm},
    Module[{allFacts, direct, T},
      allFacts = Join[origThms, ASSUME /@ ctxAsms];
      direct = SelectFirst[allFacts, aconv[concl[#], antTm] &, Missing[]];
      T = tConst[];
      Which[
        !MissingQ[direct], direct,
        antTm === T,       HOL`Bool`TRUTH,
        depth > 0,         simpProveImpl[origThms, ctxAsms, depth - 1, antTm],
        True,
          Throw[HOL`Error`holError["simp",
            "simp: cannot discharge antecedent (depth exhausted)",
            <|"target" -> antTm|>], HOL`Error`holErrorTag]
      ]
    ]
  ];

(* ============================================================ *)
(* baseConv: assemble conv stack for one (rules, ctx, depth)    *)
(* ============================================================ *)

buildBaseConv[ruleThms_List, ctxAsms_List, depth_Integer] :=
  Module[{prepared, productive, prover, ruleConvs, ctxConvs},
    prepared = HOL`Auto`Simp`simpPrepareRule /@ ruleThms;
    productive = Select[prepared, productiveSimpRule];
    prover = makeProver[ruleThms, ctxAsms, depth];
    ruleConvs = simpRuleConv[#, prover] & /@ productive;
    ctxConvs = ctxRewrConv /@ ctxAsms;
    (* Order: ctx-rewrites first (cheap aconv), then user/basic rules,    *)
    (* then BETACONV at the deepest fallback.                             *)
    combineSimpConvs[Join[ctxConvs, ruleConvs]]
  ];

(* ============================================================ *)
(* congruence descents (β-3)                                    *)
(* ============================================================ *)

doImpCong[ruleThms_, ctxAsms_, depth_][t_] :=
  Module[{p1Tm, q1Tm, eq1, p2Tm, eq2, q2Tm, dischEq2, conjAx,
          p1V, p2V, q1V, q2V, instLemma},
    p1Tm = t[[1, 2]]; q1Tm = t[[2]];
    eq1 = simpFixpointConv[ruleThms, ctxAsms, depth][p1Tm];
    p2Tm = concl[eq1][[2]];
    eq2 = simpFixpointConv[ruleThms, Append[ctxAsms, p2Tm], depth][q1Tm];
    q2Tm = concl[eq2][[2]];
    dischEq2 = HOL`Bool`DISCH[p2Tm, eq2];
    conjAx = HOL`Bool`CONJ[eq1, dischEq2];
    p1V = mkVar["p1", boolTy]; p2V = mkVar["p2", boolTy];
    q1V = mkVar["q1", boolTy]; q2V = mkVar["q2", boolTy];
    instLemma = INST[
      {p1V -> p1Tm, p2V -> p2Tm, q1V -> q1Tm, q2V -> q2Tm},
      impCongLemma[]];
    HOL`Bool`MP[instLemma, conjAx]
  ];

doAndCong[ruleThms_, ctxAsms_, depth_][t_] :=
  Module[{p1Tm, q1Tm, eq1, p2Tm, eq2, q2Tm, dischEq2, conjAx,
          p1V, p2V, q1V, q2V, instLemma},
    p1Tm = t[[1, 2]]; q1Tm = t[[2]];
    eq1 = simpFixpointConv[ruleThms, ctxAsms, depth][p1Tm];
    p2Tm = concl[eq1][[2]];
    eq2 = simpFixpointConv[ruleThms, Append[ctxAsms, p2Tm], depth][q1Tm];
    q2Tm = concl[eq2][[2]];
    dischEq2 = HOL`Bool`DISCH[p2Tm, eq2];
    conjAx = HOL`Bool`CONJ[eq1, dischEq2];
    p1V = mkVar["p1", boolTy]; p2V = mkVar["p2", boolTy];
    q1V = mkVar["q1", boolTy]; q2V = mkVar["q2", boolTy];
    instLemma = INST[
      {p1V -> p1Tm, p2V -> p2Tm, q1V -> q1Tm, q2V -> q2Tm},
      andCongLemma[]];
    HOL`Bool`MP[instLemma, conjAx]
  ];

doOrCong[ruleThms_, ctxAsms_, depth_][t_] :=
  Module[{p1Tm, q1Tm, eq1, p2Tm, notP2, eq2, q2Tm, dischEq2, conjAx,
          p1V, p2V, q1V, q2V, instLemma},
    p1Tm = t[[1, 2]]; q1Tm = t[[2]];
    eq1 = simpFixpointConv[ruleThms, ctxAsms, depth][p1Tm];
    p2Tm = concl[eq1][[2]];
    notP2 = mkNot[p2Tm];
    eq2 = simpFixpointConv[ruleThms, Append[ctxAsms, notP2], depth][q1Tm];
    q2Tm = concl[eq2][[2]];
    dischEq2 = HOL`Bool`DISCH[notP2, eq2];
    conjAx = HOL`Bool`CONJ[eq1, dischEq2];
    p1V = mkVar["p1", boolTy]; p2V = mkVar["p2", boolTy];
    q1V = mkVar["q1", boolTy]; q2V = mkVar["q2", boolTy];
    instLemma = INST[
      {p1V -> p1Tm, p2V -> p2Tm, q1V -> q1Tm, q2V -> q2Tm},
      orCongLemma[]];
    HOL`Bool`MP[instLemma, conjAx]
  ];

(* ============================================================ *)
(* one-pass descent: congruence dispatch, else MKCOMB / ABS     *)
(* ============================================================ *)

descendOnce[ruleThms_, ctxAsms_, depth_][t_] :=
  Which[
    isImp[t],     doImpCong[ruleThms, ctxAsms, depth][t],
    isAndForm[t], doAndCong[ruleThms, ctxAsms, depth][t],
    isOrForm[t],  doOrCong[ruleThms, ctxAsms, depth][t],
    MatchQ[t, comb[_, _]],
      Module[{f = t[[1]], x = t[[2]], fEq, xEq},
        fEq = simpFixpointConv[ruleThms, ctxAsms, depth][f];
        xEq = simpFixpointConv[ruleThms, ctxAsms, depth][x];
        MKCOMB[fEq, xEq]
      ],
    MatchQ[t, abs[bvar[0, _], _, _]],
      Module[{bty, body, origin, forbidden, name, v, openTh, opened, innerEq},
        bty = t[[1, 2]]; body = t[[2]]; origin = t[[3]];
        forbidden = First /@ freesIn[body];
        name = pickFreshNm[origin, forbidden];
        v = mkVar[name, bty];
        openTh = BETA[mkComb[abs[bvar[0, bty], body, name], v]];
        opened = concl[openTh][[2]];
        innerEq = simpFixpointConv[ruleThms, ctxAsms, depth][opened];
        ABS[v, innerEq]
      ],
    True, REFL[t]
  ];

(* ============================================================ *)
(* one step + fixpoint                                          *)
(* ============================================================ *)

simpStepConv[baseConv_, ruleThms_, ctxAsms_, depth_][t_] :=
  Module[{topTh, rhs1, descTh},
    topTh = HOL`Drule`TRYCONV[HOL`Drule`REPEATC[baseConv]][t];
    rhs1 = concl[topTh][[2]];
    descTh = descendOnce[ruleThms, ctxAsms, depth][rhs1];
    TRANS[topTh, descTh]
  ];

simpFixpointConv[ruleThms_, ctxAsms_, depth_][t_] :=
  Module[{baseConv, stepConv, cur, rhs, next, newRhs, seen},
    baseConv = buildBaseConv[ruleThms, ctxAsms, depth];
    stepConv = simpStepConv[baseConv, ruleThms, ctxAsms, depth];
    cur = stepConv[t];
    rhs = concl[cur][[2]];
    seen = <|t -> True, rhs -> True|>;
    While[True,
      next = stepConv[rhs];
      newRhs = concl[next][[2]];
      If[newRhs === rhs, Break[]];
      If[KeyExistsQ[seen, newRhs], Break[]];
      cur = TRANS[cur, next];
      rhs = newRhs;
      seen[newRhs] = True
    ];
    cur
  ];

simpProveImpl[thms_List, ctxAsms_List, depth_Integer, t_] :=
  Module[{eqTh, rhs, T},
    eqTh = simpFixpointConv[thms, ctxAsms, depth][t];
    rhs = concl[eqTh][[2]];
    T = tConst[];
    If[rhs =!= T,
      Throw[HOL`Error`holError["simp",
        "simpProve: simplification did not reach T",
        <|"target" -> t, "simplified" -> rhs|>], HOL`Error`holErrorTag]];
    HOL`Bool`EQTELIM[eqTh]
  ];

(* ============================================================ *)
(* public API                                                   *)
(* ============================================================ *)

withBasic[thms_List] := Join[thms, HOL`Auto`Simp`basicSimpset[]];

HOL`Auto`Simp`simpConv[thms_List][t_] :=
  simpFixpointConv[withBasic[thms], {}, $simpDepthLimit][t];

HOL`Auto`Simp`simpProve[t_, thms_List] :=
  simpProveImpl[withBasic[thms], {}, $simpDepthLimit, t];

HOL`Auto`Simp`SIMP[thms_List][g : HOL`Tactics`goal[asms_, conclTm_]] :=
  Module[{eqTh, rhs, T, just},
    eqTh = HOL`Auto`Simp`simpConv[thms][conclTm];
    rhs = concl[eqTh][[2]];
    T = tConst[];
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
