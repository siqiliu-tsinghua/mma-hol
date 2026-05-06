(* ::Package:: *)

BeginPackage["HOL`Drule`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
                            "HOL`Equal`", "HOL`Bool`"}];

ALLCONV::usage   = "ALLCONV[t] — identity conversion: returns REFL[t].";
NOCONV::usage    = "NOCONV[t] — always fails with a conv-tagged error.";
THENC::usage     = "THENC[c1, c2][t] — run c1, then c2 on the RHS; chain with TRANS.";
ORELSEC::usage   = "ORELSEC[c1, c2][t] — run c1; on conv failure run c2.";
TRYCONV::usage   = "TRYCONV[c][t] — run c, or return REFL[t] on conv failure.";
REPEATC::usage   = "REPEATC[c][t] — apply c repeatedly, TRANS-chained, until it fails.";
SUBCONV::usage   = "SUBCONV[c][t] — apply c to immediate subterms (comb sides / under abs).";
DEPTHCONV::usage = "DEPTHCONV[c][t] — bottom-up depth-first traversal, REPEATC-applying c at each level.";
REWRCONV::usage  = "REWRCONV[eqTh][t] — given eqTh : Γ ⊢ lhs = rhs, first-order match t against lhs and return Γ' ⊢ t = rhs'.";
CONVRULE::usage  = "CONVRULE[c, th] — from Γ ⊢ p, apply c to p to get ⊢ p = p', then EQMP to Γ ⊢ p'.";
ONCEREWRITERULE::usage = "ONCEREWRITERULE[eqTh, th] — rewrite the first applicable subterm in concl[th] using eqTh.";
REWRITERULE::usage     = "REWRITERULE[eqTh, th] / REWRITERULE[{eqTh, …}, th] — rewrite concl[th] bottom-up using each productive rule (LHS not aconv RHS), iterating to fixpoint with cycle detection.";
fixpointConvRule::usage = "fixpointConvRule[conv, th] — apply CONVRULE[conv, ⋅] iteratively to th until concl is stable, or until a previously-seen concl recurs (cycle); returns the last computed theorem either way.";
productiveEqThm::usage  = "productiveEqThm[eqTh] — True iff eqTh is an equation whose LHS is NOT α-equivalent to its RHS. Non-productive rules (LHS aconv RHS) are silently dropped by REWRITERULE to avoid pointless / cycle-prone rewrites.";
SUBS::usage      = "SUBS[{eq1, …, eqn}, th] — substitute lhs→rhs in concl[th] for each eqi, top-down, all matching positions, no descent into rewritten subterms.";
matchPattern::usage = "matchPattern[pat, tgt] returns {tsubst, tysubst} (Associations) such that pat[σ] α-equals tgt under HO Miller-pattern matching. Returns Missing[] when no match exists.";

Begin["`Private`"];

convFail[msg_String] := HOL`Error`holError["conv", msg, <||>];
convFail[msg_String, extra_Association] := HOL`Error`holError["conv", msg, extra];

SetAttributes[tryConv, HoldFirst];
tryConv[body_] :=
  Module[{res},
    res = Catch[body, HOL`Error`holErrorTag];
    If[MatchQ[res, _Failure], $convFailed, res]
  ];

HOL`Drule`ALLCONV[t_] := REFL[t];

HOL`Drule`NOCONV[t_] := convFail["NOCONV", <|"term" -> t|>];

HOL`Drule`THENC[c1_, c2_][t_] :=
  Module[{th1, rhs, th2},
    th1 = c1[t];
    rhs = concl[th1][[2]];
    th2 = c2[rhs];
    TRANS[th1, th2]
  ];

HOL`Drule`ORELSEC[c1_, c2_][t_] :=
  Module[{res},
    res = tryConv[c1[t]];
    If[res === $convFailed, c2[t], res]
  ];

HOL`Drule`TRYCONV[c_][t_] :=
  Module[{res},
    res = tryConv[c[t]];
    If[res === $convFailed, REFL[t], res]
  ];

HOL`Drule`REPEATC[c_][t_] :=
  Module[{res, rhs},
    res = tryConv[c[t]];
    If[res === $convFailed, Return[REFL[t]]];
    rhs = concl[res][[2]];
    If[aconv[rhs, t], Return[res]];
    TRANS[res, HOL`Drule`REPEATC[c][rhs]]
  ];

pickFreshName[preferred_String, forbidden_List] :=
  Module[{i, cand},
    If[! MemberQ[forbidden, preferred], Return[preferred]];
    cand = "z"; i = 0;
    While[MemberQ[forbidden, cand],
      i++; cand = "z" <> ToString[i]];
    cand
  ];

HOL`Drule`SUBCONV[c_][comb[f_, x_]] :=
  MKCOMB[HOL`Drule`TRYCONV[c][f], HOL`Drule`TRYCONV[c][x]];

HOL`Drule`SUBCONV[c_][abs[bvar[0, bty_], body_, origin_String]] :=
  Module[{forbidden, name, v, openTh, opened, convTh},
    forbidden = Map[First, freesIn[body]];
    name = pickFreshName[origin, forbidden];
    v = mkVar[name, bty];
    openTh = BETA[comb[abs[bvar[0, bty], body, name], v]];
    opened = concl[openTh][[2]];
    convTh = HOL`Drule`TRYCONV[c][opened];
    ABS[v, convTh]
  ];

HOL`Drule`SUBCONV[c_][t : (var[_, _] | const[_, _])] :=
  convFail["SUBCONV: atomic term has no subterms", <|"term" -> t|>];

HOL`Drule`DEPTHCONV[c_][t_] :=
  Module[{subTh, rhs, topTh},
    subTh = tryConv[HOL`Drule`SUBCONV[HOL`Drule`DEPTHCONV[c]][t]];
    If[subTh === $convFailed,
      HOL`Drule`TRYCONV[HOL`Drule`REPEATC[c]][t],
      rhs = concl[subTh][[2]];
      topTh = HOL`Drule`TRYCONV[HOL`Drule`REPEATC[c]][rhs];
      TRANS[subTh, topTh]
    ]
  ];

$matchFail   = "matchFail$"   <> ToString[Unique[]];
$millerFail  = "millerFail$"  <> ToString[Unique[]];

tryTypeMatch[tyVar[n_String], tgt_, acc_] :=
  Module[{existing},
    existing = Lookup[acc, tyVar[n], Missing[]];
    If[MissingQ[existing],
      Append[acc, tyVar[n] -> tgt],
      If[existing === tgt, acc, $matchFail]
    ]
  ];
tryTypeMatch[tyApp[name_, args_List], tyApp[name2_, args2_List], acc_] :=
  If[name =!= name2 || Length[args] =!= Length[args2], $matchFail,
    Fold[
      Function[{a, pair},
        If[a === $matchFail, $matchFail, tryTypeMatch[pair[[1]], pair[[2]], a]]],
      acc, Transpose[{args, args2}]
    ]
  ];
tryTypeMatch[_, _, _] := $matchFail;

(* True iff t (interpreted at top depth 0 of a fresh walk) contains any   *)
(* bvar that references one of the `dep` matching-context binders we     *)
(* descended through. Used to reject first-order bindings that would     *)
(* capture an outer binder under INST.                                   *)
hasContextBvar[t_, dep_Integer] := hasContextBvarWalk[t, dep, 0];
hasContextBvarWalk[bvar[k_Integer, _], dep_Integer, d_Integer] :=
  k - d >= 0 && k - d < dep;
hasContextBvarWalk[var[_, _], _, _]   := False;
hasContextBvarWalk[const[_, _], _, _] := False;
hasContextBvarWalk[comb[f_, x_], dep_, d_] :=
  hasContextBvarWalk[f, dep, d] || hasContextBvarWalk[x, dep, d];
hasContextBvarWalk[abs[_, body_, _], dep_, d_] :=
  hasContextBvarWalk[body, dep, d + 1];

collectAppSpine[t_] :=
  Module[{cur, args},
    cur = t; args = {};
    While[MatchQ[cur, comb[_, _]],
      args = Prepend[args, cur[[2]]];
      cur  = cur[[1]]];
    {cur, args}
  ];

(* Miller args criterion: non-empty, all bvars at distinct levels in     *)
(* [0, depth).                                                           *)
isMillerArgs[args_List, depth_Integer] :=
  Module[{ks},
    If[args === {}, Return[False]];
    If[!AllTrue[args,
        MatchQ[#, bvar[_Integer, _]] && 0 <= #[[1]] < depth &],
      Return[False]];
    ks = #[[1]] & /@ args;
    DuplicateFreeQ[ks]
  ];

(* Walk t, replacing each bvar referencing matching-context level ki     *)
(* (ki ∈ keys[mapping]) with mapping[ki] (a fresh free var). Tracks      *)
(* descent depth so a bvar[k] inside d-deep abstractions corresponds to  *)
(* context level k - d. Returns $millerFail if any context bvar is       *)
(* outside the mapping — that bvar can't be abstracted by the Miller    *)
(* pattern's args, so the HO match must fail.                            *)
millerSubstWalk[bvar[k_Integer, ty_], mapping_, dep_, d_] :=
  Module[{level = k - d, fv},
    If[level < 0 || level >= dep,
      bvar[k, ty],
      fv = Lookup[mapping, level, $millerFail];
      fv
    ]
  ];
millerSubstWalk[v : var[_, _], _, _, _]   := v;
millerSubstWalk[c : const[_, _], _, _, _] := c;
millerSubstWalk[comb[f_, x_], m_, dep_, d_] :=
  Module[{r1, r2},
    r1 = millerSubstWalk[f, m, dep, d];
    If[r1 === $millerFail, Return[$millerFail]];
    r2 = millerSubstWalk[x, m, dep, d];
    If[r2 === $millerFail, $millerFail, comb[r1, r2]]
  ];
millerSubstWalk[abs[bv_, body_, o_], m_, dep_, d_] :=
  Module[{r},
    r = millerSubstWalk[body, m, dep, d + 1];
    If[r === $millerFail, $millerFail, abs[bv, r, o]]
  ];

pickHOFvName[forbidden_List, i_Integer] :=
  Module[{cand, j},
    cand = "ho$" <> ToString[i];
    j = 0;
    While[MemberQ[forbidden, cand],
      j++; cand = "ho$" <> ToString[i] <> "$" <> ToString[j]];
    cand
  ];

(* Miller HO match. Pattern was `comb[head, a1, …, an]` where head =     *)
(* var[Pname, Pty] and ai = bvar[ki, ti] are distinct in-scope binders.  *)
(* Bind P ↦ λfv1…λfvn. tgt' where tgt' replaces the bvars at levels {ki}*)
(* with fresh fv-vars. The substitute is closed-bvar by construction;    *)
(* INST + post-beta restores the intended rewrite at the original        *)
(* application site. Fails if tgt references a context binder not in     *)
(* {ki}.                                                                  *)
tryHOMatch[var[Pname_String, Pty_], args_List, tgt_, {tsubst_, tysubst_}, depth_Integer] :=
  Module[{argLevels, argTypes, substArgTypes, tgtType, expectedPty, tysubst2,
          existingNames, freshNames, fvVars, mapping, tgtSubbed,
          body, key, existing, allNames},
    argLevels = #[[1]] & /@ args;
    argTypes  = #[[2]] & /@ args;
    (* Apply the in-progress type substitution to arg types: an outer abs *)
    (* descent may have already bound the bvar's tyvars (e.g., α := int).  *)
    substArgTypes = Map[typeSubst[tysubst, #] &, argTypes];
    tgtType   = typeOf[tgt];
    expectedPty = Fold[tyFun[#2, #1] &, tgtType, Reverse[substArgTypes]];
    tysubst2 = tryTypeMatch[Pty, expectedPty, tysubst];
    If[tysubst2 === $matchFail, Return[$matchFail]];
    existingNames = First /@ freesIn[tgt];
    allNames = existingNames;
    freshNames = Table[
      Module[{nm = pickHOFvName[allNames, i]},
        AppendTo[allNames, nm]; nm], {i, 1, Length[args]}];
    fvVars = Table[
      var[freshNames[[i]], typeSubst[tysubst2, argTypes[[i]]]],
      {i, 1, Length[args]}];
    mapping = Association[
      Table[argLevels[[i]] -> fvVars[[i]], {i, 1, Length[args]}]];
    tgtSubbed = millerSubstWalk[tgt, mapping, depth, 0];
    If[tgtSubbed === $millerFail, Return[$matchFail]];
    body = Fold[mkAbs[#2, #1] &, tgtSubbed, Reverse[fvVars]];
    key = var[Pname, Pty];
    existing = Lookup[tsubst, key, Missing[]];
    If[MissingQ[existing],
      {Append[tsubst, key -> body], tysubst2},
      If[aconv[existing, body], {tsubst, tysubst2}, $matchFail]
    ]
  ];

tryTermMatch[bvar[k_Integer, ty_], bvar[k_Integer, ty2_], {tsubst_, tysubst_}, _] :=
  Module[{tys2},
    tys2 = tryTypeMatch[ty, ty2, tysubst];
    If[tys2 === $matchFail, $matchFail, {tsubst, tys2}]
  ];
tryTermMatch[bvar[_, _], _, _, _] := $matchFail;

tryTermMatch[var[n_String, ty_], tgt_, {tsubst_, tysubst_}, depth_Integer] :=
  Module[{tysubst2, key, existing},
    tysubst2 = tryTypeMatch[ty, typeOf[tgt], tysubst];
    If[tysubst2 === $matchFail, Return[$matchFail]];
    If[hasContextBvar[tgt, depth], Return[$matchFail]];
    key = var[n, ty];
    existing = Lookup[tsubst, key, Missing[]];
    If[MissingQ[existing],
      {Append[tsubst, key -> tgt], tysubst2},
      If[aconv[existing, tgt], {tsubst, tysubst2}, $matchFail]
    ]
  ];

tryTermMatch[const[n_String, ty_], const[n_String, ty2_], {ts_, tys_}, _] :=
  Module[{tys2},
    tys2 = tryTypeMatch[ty, ty2, tys];
    If[tys2 === $matchFail, $matchFail, {ts, tys2}]
  ];

tryTermMatch[combTerm : comb[_, _], tgt_, subst_, depth_Integer] :=
  Module[{head, args},
    {head, args} = collectAppSpine[combTerm];
    If[MatchQ[head, var[_String, _]] && isMillerArgs[args, depth],
      tryHOMatch[head, args, tgt, subst, depth],
      tryStructComb[combTerm, tgt, subst, depth]
    ]
  ];

tryStructComb[comb[f_, x_], comb[f2_, x2_], subst_, depth_Integer] :=
  Module[{r1},
    r1 = tryTermMatch[f, f2, subst, depth];
    If[r1 === $matchFail, $matchFail,
      tryTermMatch[x, x2, r1, depth]]
  ];
tryStructComb[_, _, _, _] := $matchFail;

tryTermMatch[abs[bv_, body_, _], abs[bv2_, body2_, _], subst_, depth_Integer] :=
  Module[{r1},
    r1 = tryTermMatch[bv, bv2, subst, depth];
    If[r1 === $matchFail, $matchFail,
      tryTermMatch[body, body2, r1, depth + 1]]
  ];

tryTermMatch[_, _, _, _] := $matchFail;

HOL`Drule`REWRCONV[eqTh_][t_] :=
  Module[{c, lhs, matchRes, tsubst, tysubst, thAfterTy, tsubstKeyed, thFinal,
          betaConv},
    c = concl[eqTh];
    If[! MatchQ[c, comb[comb[const["=", _], _], _]],
      convFail["REWRCONV: theorem is not an equation", <|"concl" -> c|>]];
    lhs = c[[1, 2]];
    matchRes = tryTermMatch[lhs, t, {<||>, <||>}, 0];
    If[matchRes === $matchFail,
      convFail["REWRCONV: term does not match LHS",
        <|"lhs" -> lhs, "target" -> t|>]];
    {tsubst, tysubst} = matchRes;
    thAfterTy = If[Length[tysubst] > 0,
      INSTTYPE[Normal[tysubst], eqTh], eqTh];
    tsubstKeyed = Map[instType[tysubst, #[[1]]] -> #[[2]] &, Normal[tsubst]];
    thFinal = If[Length[tsubstKeyed] > 0,
      INST[tsubstKeyed, thAfterTy], thAfterTy];
    (* HO substitutes introduce (λfv. body) ai redexes wherever P was    *)
    (* applied to its Miller args; reduce them so the resulting equation *)
    (* has shape ⊢ t' = rhs', with t' α-equal to the input target.        *)
    betaConv = HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]];
    HOL`Drule`CONVRULE[betaConv, thFinal]
  ];

HOL`Drule`CONVRULE[c_, th_] :=
  Module[{eqTh}, eqTh = c[concl[th]]; EQMP[eqTh, th]];

HOL`Drule`matchPattern[pat_, tgt_] :=
  Module[{r},
    r = tryTermMatch[pat, tgt, {<||>, <||>}, 0];
    If[r === $matchFail, Missing[], r]
  ];

HOL`Drule`ONCEREWRITERULE[eqTh_, th_] :=
  HOL`Drule`CONVRULE[onceDepthConv[HOL`Drule`REWRCONV[eqTh]], th];

onceDepthConv[c_][t_] :=
  Module[{topRes, leftRes, rightRes, bty, forbidden, name, v, openTh,
          opened, convTh},
    topRes = tryConv[c[t]];
    If[topRes =!= $convFailed, Return[topRes]];
    Which[
      MatchQ[t, comb[_, _]],
        leftRes = tryConv[
          MKCOMB[onceDepthConv[c][t[[1]]], REFL[t[[2]]]]];
        If[leftRes =!= $convFailed, Return[leftRes]];
        rightRes = tryConv[
          MKCOMB[REFL[t[[1]]], onceDepthConv[c][t[[2]]]]];
        If[rightRes =!= $convFailed, Return[rightRes]];
        convFail["ONCE_DEPTH_CONV: no subterm matched",
          <|"term" -> t|>],
      MatchQ[t, abs[bvar[0, _], _, _]],
        bty = t[[1, 2]];
        forbidden = Map[First, freesIn[t[[2]]]];
        name = pickFreshName[t[[3]], forbidden];
        v = mkVar[name, bty];
        openTh = BETA[comb[abs[bvar[0, bty], t[[2]], name], v]];
        opened = concl[openTh][[2]];
        convTh = tryConv[onceDepthConv[c][opened]];
        If[convTh === $convFailed,
          convFail["ONCE_DEPTH_CONV: no subterm matched under abs"],
          ABS[v, convTh]],
      True,
        convFail["ONCE_DEPTH_CONV: atomic, no match",
          <|"term" -> t|>]
    ]
  ];

HOL`Drule`productiveEqThm[eqTh_] :=
  Module[{c, lhs, rhs},
    c = concl[eqTh];
    If[! MatchQ[c, comb[comb[const["=", _], _], _]], Return[False]];
    lhs = c[[1, 2]]; rhs = c[[2]];
    ! aconv[lhs, rhs]
  ];

HOL`Drule`fixpointConvRule[conv_, th_] :=
  Module[{cur, prev, seen},
    cur  = th;
    seen = <|concl[cur] -> True|>;
    While[True,
      prev = cur;
      cur  = HOL`Drule`CONVRULE[conv, cur];
      If[concl[cur] === concl[prev], Break[]];
      If[KeyExistsQ[seen, concl[cur]], Break[]];
      seen[concl[cur]] = True
    ];
    cur
  ];

combineRewrConvs[{conv_}] := conv;
combineRewrConvs[{conv_, rest__}] :=
  HOL`Drule`ORELSEC[conv, combineRewrConvs[{rest}]];

(* Single-equation form delegates to the list form for productivity     *)
(* filtering and cycle-aware iteration.                                 *)
HOL`Drule`REWRITERULE[eqTh_, th_] /; !ListQ[eqTh] :=
  HOL`Drule`REWRITERULE[{eqTh}, th];

HOL`Drule`REWRITERULE[eqThs_List, th_] :=
  Module[{productive, conv},
    productive = Select[eqThs, HOL`Drule`productiveEqThm];
    If[productive === {}, Return[th]];
    conv = HOL`Drule`DEPTHCONV[
      combineRewrConvs[Map[HOL`Drule`REWRCONV, productive]]];
    HOL`Drule`fixpointConvRule[conv, th]
  ];

topDownAllConv[c_][t_] :=
  Module[{topRes, leftRes, rightRes, bty, forbidden, name, v, openTh,
          opened, innerConv},
    topRes = tryConv[c[t]];
    If[topRes =!= $convFailed, Return[topRes]];
    Which[
      MatchQ[t, comb[_, _]],
        leftRes  = topDownAllConv[c][t[[1]]];
        rightRes = topDownAllConv[c][t[[2]]];
        MKCOMB[leftRes, rightRes],
      MatchQ[t, abs[bvar[0, _], _, _]],
        bty = t[[1, 2]];
        forbidden = Map[First, freesIn[t[[2]]]];
        name = pickFreshName[t[[3]], forbidden];
        v = mkVar[name, bty];
        openTh = BETA[comb[abs[bvar[0, bty], t[[2]], name], v]];
        opened = concl[openTh][[2]];
        innerConv = topDownAllConv[c][opened];
        ABS[v, innerConv],
      True,
        REFL[t]
    ]
  ];

literalRewrConv[eqTh_][t_] :=
  Module[{c, lhs},
    c = concl[eqTh];
    If[! MatchQ[c, comb[comb[const["=", _], _], _]],
      convFail["SUBS: theorem is not an equation", <|"concl" -> c|>]];
    lhs = c[[1, 2]];
    If[t === lhs, eqTh,
      convFail["SUBS: term does not equal LHS",
        <|"lhs" -> lhs, "target" -> t|>]]
  ];

HOL`Drule`SUBS[{}, th_] := th;
HOL`Drule`SUBS[eqThs_List, th_] :=
  Fold[
    HOL`Drule`CONVRULE[topDownAllConv[literalRewrConv[#2]], #1] &,
    th, eqThs
  ];

End[];
EndPackage[];
