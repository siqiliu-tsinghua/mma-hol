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

$matchFail = "matchFail$" <> ToString[Unique[]];

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

tryTermMatch[bvar[k_Integer, ty_], tgt_, {tsubst_, tysubst_}] :=
  If[MatchQ[tgt, bvar[k, _]] && tgt[[2]] === typeSubst[tysubst, ty],
    {tsubst, tysubst}, $matchFail];
tryTermMatch[var[n_String, ty_], tgt_, {tsubst_, tysubst_}] :=
  Module[{tysubst2, existing, key},
    tysubst2 = tryTypeMatch[ty, typeOf[tgt], tysubst];
    If[tysubst2 === $matchFail, $matchFail,
      key = var[n, ty];
      existing = Lookup[tsubst, key, Missing[]];
      If[MissingQ[existing],
        {Append[tsubst, key -> tgt], tysubst2},
        If[aconv[existing, tgt], {tsubst, tysubst2}, $matchFail]
      ]
    ]
  ];
tryTermMatch[const[n_String, ty_], const[n_String, ty2_], {ts_, tys_}] :=
  Module[{tys2},
    tys2 = tryTypeMatch[ty, ty2, tys];
    If[tys2 === $matchFail, $matchFail, {ts, tys2}]
  ];
tryTermMatch[comb[f_, x_], comb[f2_, x2_], subst_] :=
  Module[{r1},
    r1 = tryTermMatch[f, f2, subst];
    If[r1 === $matchFail, $matchFail, tryTermMatch[x, x2, r1]]
  ];
tryTermMatch[abs[bv_, body_, _], abs[bv2_, body2_, _], subst_] :=
  Module[{r1},
    r1 = tryTermMatch[bv, bv2, subst];
    If[r1 === $matchFail, $matchFail, tryTermMatch[body, body2, r1]]
  ];
tryTermMatch[_, _, _] := $matchFail;

HOL`Drule`REWRCONV[eqTh_][t_] :=
  Module[{c, lhs, matchRes, tsubst, tysubst, thAfterTy, tsubstKeyed, thFinal, finalLhs},
    c = concl[eqTh];
    If[! MatchQ[c, comb[comb[const["=", _], _], _]],
      convFail["REWRCONV: theorem is not an equation", <|"concl" -> c|>]];
    lhs = c[[1, 2]];
    matchRes = tryTermMatch[lhs, t, {<||>, <||>}];
    If[matchRes === $matchFail,
      convFail["REWRCONV: term does not match LHS",
        <|"lhs" -> lhs, "target" -> t|>]];
    {tsubst, tysubst} = matchRes;
    thAfterTy = If[Length[tysubst] > 0,
      INSTTYPE[Normal[tysubst], eqTh], eqTh];
    tsubstKeyed = Map[instType[tysubst, #[[1]]] -> #[[2]] &, Normal[tsubst]];
    thFinal = If[Length[tsubstKeyed] > 0,
      INST[tsubstKeyed, thAfterTy], thAfterTy];
    thFinal
  ];

HOL`Drule`CONVRULE[c_, th_] :=
  Module[{eqTh}, eqTh = c[concl[th]]; EQMP[eqTh, th]];

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
