(* ::Package:: *)

BeginPackage["HOL`Bool`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
                           "HOL`Bootstrap`", "HOL`Equal`"}];

TRUTH::usage     = "TRUTH — ⊢ T, derived once from tDef + REFL.";
EQTINTRO::usage  = "EQTINTRO[th] — from Γ ⊢ p, derive Γ ⊢ p = T.";
EQTELIM::usage   = "EQTELIM[th] — from Γ ⊢ p = T, derive Γ ⊢ p.";
GEN::usage       = "GEN[x, th] — from Γ ⊢ p with x not free in Γ, derive Γ ⊢ ∀x. p.";
SPEC::usage      = "SPEC[t, th] — from Γ ⊢ ∀(λx. p), derive Γ ⊢ p[t/x]. Requires typeOf[t] === binder-type exactly; for the polymorphic case use ISPEC.";
ISPEC::usage     = "ISPEC[t, th] — `intelligent SPEC`. Like SPEC but first runs one-way type matching from the outer ∀-binder's type to typeOf[t] and INSTTYPEs th accordingly. Use this whenever th is polymorphic (e.g., selectAx) and t is at a concrete type instance from another file that uses different tyvar names (Bootstrap uses tyVar[\"a\"]/\"b\" while stdlib typically uses tyVar[\"A\"]/\"B\").";
CONJ::usage      = "CONJ[thp, thq] — from Γ₁ ⊢ p and Γ₂ ⊢ q, derive Γ₁∪Γ₂ ⊢ p ∧ q.";
CONJUNCT1::usage = "CONJUNCT1[th] — from Γ ⊢ p ∧ q, derive Γ ⊢ p.";
CONJUNCT2::usage = "CONJUNCT2[th] — from Γ ⊢ p ∧ q, derive Γ ⊢ q.";
MP::usage        = "MP[thImp, thP] — from Γ₁ ⊢ p ⇒ q and Γ₂ ⊢ p, derive Γ₁∪Γ₂ ⊢ q.";
DISCH::usage     = "DISCH[p, th] — from Γ ⊢ q, derive (Γ\\{p}) ⊢ p ⇒ q.";
UNDISCH::usage   = "UNDISCH[th] — from Γ ⊢ p ⇒ q, derive Γ∪{p} ⊢ q.";
NOTINTRO::usage  = "NOTINTRO[th] — from Γ ⊢ p ⇒ F, derive Γ ⊢ ¬ p.";
NOTELIM::usage   = "NOTELIM[th] — from Γ ⊢ ¬ p, derive Γ ⊢ p ⇒ F.";
CONTR::usage     = "CONTR[p, thF] — from Γ ⊢ F and p:bool, derive Γ ⊢ p.";
EXISTS::usage    = "EXISTS[∃x. P x, t, th] — from Γ ⊢ P[t/x], derive Γ ⊢ ∃x. P x.";
CHOOSE::usage    = "CHOOSE[v, existsTh, bodyTh] — from Γ₁ ⊢ ∃x. P x and (Γ₂, P[v/x]) ⊢ q with v fresh, derive Γ₁∪Γ₂ ⊢ q.";
orDef::usage     = "orDef — ⊢ ∨ = (λp q. ∀r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r).";
DISJ1::usage     = "DISJ1[thp, q] — from Γ ⊢ p, derive Γ ⊢ p ∨ q.";
DISJ2::usage     = "DISJ2[thq, p] — from Γ ⊢ q, derive Γ ⊢ p ∨ q.";
DISJCASES::usage = "DISJCASES[thOr, thPR, thQR] — from Γ ⊢ p ∨ q, (Δ₁,p) ⊢ r, (Δ₂,q) ⊢ r, derive Γ∪Δ₁∪Δ₂ ⊢ r.";
EXCLUDEDMIDDLE::usage = "EXCLUDEDMIDDLE[t] — for t:bool, derive ⊢ t ∨ ¬ t via Diaconescu on SELECT_AX.";
CCONTR::usage    = "CCONTR[p, thF] — from Γ ⊢ F with ¬ p possibly in Γ, derive (Γ\\{¬p}) ⊢ p.";

condConst::usage = "condConst[ty] — COND : bool → ty → ty → ty. The conditional; COND b t e selects t when b is T, e when b is F.";
condDefThm::usage = "condDefThm — ⊢ COND = (λt a b. @x. ((t = T) ⇒ (x = a)) ∧ ((t = F) ⇒ (x = b))).";
condTThm::usage = "condTThm — ⊢ ∀a b. COND T a b = a.";
condFThm::usage = "condFThm — ⊢ ∀a b. COND F a b = b.";

Begin["`Private`"];

destEqTh[th_] :=
  Module[{c},
    c = concl[th];
    If[! MatchQ[c, comb[comb[const["=", _], _], _]],
      HOL`Error`holError["rule", "Bool: conclusion is not an equation",
        <|"concl" -> c|>]];
    {c[[1, 2]], c[[2]]}
  ];

rhsOfConcl[th_] := destEqTh[th][[2]];

Module[{x, body, sym},
  x = mkVar["x", boolTy];
  body = mkAbs[x, x];
  sym = SYM[tDef];
  HOL`Bool`TRUTH = EQMP[sym, REFL[body]];
];

HOL`Bool`EQTELIM[th_] := EQMP[SYM[th], HOL`Bool`TRUTH];

HOL`Bool`EQTINTRO[th_] := DEDUCTANTISYM[th, HOL`Bool`TRUTH];

HOL`Bool`GEN[x : var[_String, xTy_], th_] :=
  Module[{p, eqth, absth, fdefInst, lamTm, aptm, betaTh, unfoldEq},
    p = concl[th];
    eqth = HOL`Bool`EQTINTRO[th];
    absth = ABS[x, eqth];
    fdefInst = INSTTYPE[{tyVar["a"] -> xTy}, forallDef];
    lamTm = mkAbs[x, p];
    aptm = APTHM[fdefInst, lamTm];
    betaTh = BETACONV[rhsOfConcl[aptm]];
    unfoldEq = TRANS[aptm, betaTh];
    EQMP[SYM[unfoldEq], absth]
  ];
HOL`Bool`GEN[other_, _] :=
  HOL`Error`holError["rule", "GEN: first arg must be a non-reserved var",
    <|"got" -> other|>];

HOL`Bool`SPEC[t_, th_] :=
  Module[{c, lamTm, bv, xTy, fdefInst, aptm, betaTh, unfoldEq,
          step1, step2, leftBeta, rightBeta, chain},
    c = concl[th];
    If[! MatchQ[c, comb[const["∀", _], abs[bvar[0, _], _, _String]]],
      HOL`Error`holError["rule", "SPEC: expected ⊢ ∀(λx. p)",
        <|"concl" -> c|>]];
    lamTm = c[[2]];
    bv = First[destAbs[lamTm]];
    xTy = typeOf[bv];
    If[typeOf[t] =!= xTy,
      HOL`Error`holError["rule", "SPEC: term type does not match binder",
        <|"binderType" -> xTy, "termType" -> typeOf[t]|>]];
    fdefInst = INSTTYPE[{tyVar["a"] -> xTy}, forallDef];
    aptm = APTHM[fdefInst, lamTm];
    betaTh = BETACONV[rhsOfConcl[aptm]];
    unfoldEq = TRANS[aptm, betaTh];
    step1 = EQMP[unfoldEq, th];
    step2 = APTHM[step1, t];
    leftBeta  = BETACONV[destEqTh[step2][[1]]];
    rightBeta = BETACONV[destEqTh[step2][[2]]];
    chain = TRANS[TRANS[SYM[leftBeta], step2], rightBeta];
    HOL`Bool`EQTELIM[chain]
  ];

(* ============================================================ *)
(* ISPEC — intelligent SPEC                                     *)
(*                                                              *)
(* One-way tyvar matching from the ∀-binder's type to typeOf[t],*)
(* then INSTTYPE the theorem before delegating to SPEC. Lets    *)
(* polymorphic axioms (like selectAx) be specialised against    *)
(* concrete types whose tyvar names don't agree with Bootstrap's*)
(* "a"/"b" — see the SPEC failure that hit stdlib/Pair when     *)
(* selectAx's tyVar["a"] needed to align with αTy = tyVar["A"]. *)
(* ============================================================ *)

$ispecTyFail = "ispecTyFail$" <> ToString[Unique[]];

ispecTyMatch[tyVar[n_String], target_, acc_] :=
  Module[{existing = Lookup[acc, tyVar[n], Missing[]]},
    If[MissingQ[existing],
      Append[acc, tyVar[n] -> target],
      If[existing === target, acc, $ispecTyFail]
    ]
  ];
ispecTyMatch[tyApp[n_, args1_List], tyApp[m_, args2_List], acc_] :=
  If[n =!= m || Length[args1] =!= Length[args2], $ispecTyFail,
    Fold[
      Function[{a, pr},
        If[a === $ispecTyFail, $ispecTyFail,
          ispecTyMatch[pr[[1]], pr[[2]], a]]],
      acc, Transpose[{args1, args2}]
    ]
  ];
ispecTyMatch[_, _, _] := $ispecTyFail;

HOL`Bool`ISPEC[t_, th_] :=
  Module[{c, bv, xTy, tTy, match, instTh},
    c = concl[th];
    If[! MatchQ[c, comb[const["∀", _], abs[bvar[0, _], _, _String]]],
      HOL`Error`holError["rule", "ISPEC: expected ⊢ ∀(λx. p)",
        <|"concl" -> c|>]];
    bv = First[destAbs[c[[2]]]];
    xTy = typeOf[bv];
    tTy = typeOf[t];
    match = ispecTyMatch[xTy, tTy, <||>];
    If[match === $ispecTyFail,
      HOL`Error`holError["rule",
        "ISPEC: cannot one-way match binder type to term type",
        <|"binderType" -> xTy, "termType" -> tTy|>]];
    instTh = If[Length[match] > 0,
      HOL`Kernel`INSTTYPE[Normal[match], th], th];
    HOL`Bool`SPEC[t, instTh]
  ];

boolBinConst[name_] := mkConst[name, tyFun[boolTy, tyFun[boolTy, boolTy]]];

unfoldBinop[defTh_, p_, q_] :=
  Module[{s1, b1, t1, s2, b2},
    s1 = APTHM[defTh, p];
    b1 = BETACONV[rhsOfConcl[s1]];
    t1 = TRANS[s1, b1];
    s2 = APTHM[t1, q];
    b2 = BETACONV[rhsOfConcl[s2]];
    TRANS[s2, b2]
  ];

unfoldAnd[p_, q_]     := unfoldBinop[andDef, p, q];
unfoldImplies[p_, q_] := unfoldBinop[impliesDef, p, q];

proveHyp[th1_, th2_] := EQMP[DEDUCTANTISYM[th1, th2], th1];

collectFreeNames[tms___] :=
  DeleteDuplicates[Flatten[Map[Function[t, Map[First, freesIn[t]]], {tms}]]];

freshName[prefix_String, forbidden_List] :=
  Module[{i, cand},
    cand = prefix; i = 0;
    While[MemberQ[forbidden, cand], i++; cand = prefix <> ToString[i]];
    cand
  ];

HOL`Bool`CONJ[thp_, thq_] :=
  Module[{p, q, fName, fVar, pEqT, qEqT, fpqEqFTT, absth, unfoldTh},
    p = concl[thp];
    q = concl[thq];
    fName = freshName["f",
      collectFreeNames[p, q, Sequence @@ hyp[thp], Sequence @@ hyp[thq]]];
    fVar = mkVar[fName, tyFun[boolTy, tyFun[boolTy, boolTy]]];
    pEqT = HOL`Bool`EQTINTRO[thp];
    qEqT = HOL`Bool`EQTINTRO[thq];
    fpqEqFTT = MKCOMB[MKCOMB[REFL[fVar], pEqT], qEqT];
    absth = ABS[fVar, fpqEqFTT];
    unfoldTh = unfoldAnd[p, q];
    EQMP[SYM[unfoldTh], absth]
  ];

conjunctImpl[th_, selectLeft_] :=
  Module[{c, pT, qT, pv, qv, sel, unfoldTh, eq0, eq1, tConst,
          betaL1, inner1L, betaL2, applyQL, betaL3, chainL, lhsRed,
          betaR1, inner1R, betaR2, applyQR, betaR3, chainR, rhsRed,
          equation},
    c = concl[th];
    If[! MatchQ[c, comb[comb[const["∧", _], _], _]],
      HOL`Error`holError["rule", "CONJUNCT: expected p ∧ q", <|"concl" -> c|>]];
    pT = c[[1, 2]]; qT = c[[2]];
    pv = mkVar["pSel", boolTy];
    qv = mkVar["qSel", boolTy];
    sel = If[selectLeft, mkAbs[pv, mkAbs[qv, pv]], mkAbs[pv, mkAbs[qv, qv]]];
    unfoldTh = unfoldAnd[pT, qT];
    eq0 = EQMP[unfoldTh, th];
    eq1 = APTHM[eq0, sel];
    betaL1 = BETACONV[destEqTh[eq1][[1]]];
    inner1L = mkComb[sel, pT];
    betaL2 = BETACONV[inner1L];
    applyQL = APTHM[betaL2, qT];
    betaL3 = BETACONV[destEqTh[applyQL][[2]]];
    chainL = TRANS[applyQL, betaL3];
    lhsRed = TRANS[betaL1, chainL];
    tConst = mkConst["T", boolTy];
    betaR1 = BETACONV[destEqTh[eq1][[2]]];
    inner1R = mkComb[sel, tConst];
    betaR2 = BETACONV[inner1R];
    applyQR = APTHM[betaR2, tConst];
    betaR3 = BETACONV[destEqTh[applyQR][[2]]];
    chainR = TRANS[applyQR, betaR3];
    rhsRed = TRANS[betaR1, chainR];
    equation = TRANS[TRANS[SYM[lhsRed], eq1], rhsRed];
    HOL`Bool`EQTELIM[equation]
  ];

HOL`Bool`CONJUNCT1[th_] := conjunctImpl[th, True];
HOL`Bool`CONJUNCT2[th_] := conjunctImpl[th, False];

HOL`Bool`MP[thImp_, thP_] :=
  Module[{c, p, q, unfoldEq, step1, andTh},
    c = concl[thImp];
    If[! MatchQ[c, comb[comb[const["⇒", _], _], _]],
      HOL`Error`holError["rule", "MP: expected ⊢ p ⇒ q", <|"concl" -> c|>]];
    p = c[[1, 2]]; q = c[[2]];
    unfoldEq = unfoldImplies[p, q];
    step1 = EQMP[unfoldEq, thImp];
    andTh = EQMP[SYM[step1], thP];
    HOL`Bool`CONJUNCT2[andTh]
  ];

HOL`Bool`DISCH[p_, th_] :=
  Module[{q, andTh, projTh, equivTh, unfoldEq},
    If[typeOf[p] =!= boolTy,
      HOL`Error`holError["rule", "DISCH: hypothesis must be :bool",
        <|"got" -> typeOf[p]|>]];
    q = concl[th];
    andTh = HOL`Bool`CONJ[ASSUME[p], th];
    projTh = HOL`Bool`CONJUNCT1[ASSUME[concl[andTh]]];
    equivTh = DEDUCTANTISYM[andTh, projTh];
    unfoldEq = unfoldImplies[p, q];
    EQMP[SYM[unfoldEq], equivTh]
  ];

HOL`Bool`UNDISCH[th_] :=
  Module[{c, p},
    c = concl[th];
    If[! MatchQ[c, comb[comb[const["⇒", _], _], _]],
      HOL`Error`holError["rule", "UNDISCH: expected ⊢ p ⇒ q", <|"concl" -> c|>]];
    p = c[[1, 2]];
    HOL`Bool`MP[th, ASSUME[p]]
  ];

impTmInt[a_, b_] :=
  mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];

Module[{p, q, r, orTy, impBool, forallBool, pImpR, qImpR, qImpRThenR,
        innerImpl, outerForall, innerLam, outerLam, def},
  orTy = tyFun[boolTy, tyFun[boolTy, boolTy]];
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy]; r = mkVar["r", boolTy];
  impBool = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  forallBool = mkConst["∀", tyFun[tyFun[boolTy, boolTy], boolTy]];
  pImpR = mkComb[mkComb[impBool, p], r];
  qImpR = mkComb[mkComb[impBool, q], r];
  qImpRThenR = mkComb[mkComb[impBool, qImpR], r];
  innerImpl = mkComb[mkComb[impBool, pImpR], qImpRThenR];
  outerForall = mkComb[forallBool, mkAbs[r, innerImpl]];
  innerLam = mkAbs[q, outerForall];
  outerLam = mkAbs[p, innerLam];
  def = mkEq[mkVar["∨", orTy], outerLam];
  HOL`Bool`orDef = newDefinition[def];
];

unfoldOr[p_, q_] := unfoldBinop[HOL`Bool`orDef, p, q];

unfoldNot[p_] :=
  Module[{s1, b1},
    s1 = APTHM[notDef, p];
    b1 = BETACONV[rhsOfConcl[s1]];
    TRANS[s1, b1]
  ];

HOL`Bool`NOTINTRO[th_] :=
  Module[{c, p, unfoldEq},
    c = concl[th];
    If[! MatchQ[c, comb[comb[const["⇒", _], _], const["F", _]]],
      HOL`Error`holError["rule", "NOTINTRO: expected ⊢ p ⇒ F",
        <|"concl" -> c|>]];
    p = c[[1, 2]];
    unfoldEq = unfoldNot[p];
    EQMP[SYM[unfoldEq], th]
  ];

HOL`Bool`NOTELIM[th_] :=
  Module[{c, p, unfoldEq},
    c = concl[th];
    If[! MatchQ[c, comb[const["¬", _], _]],
      HOL`Error`holError["rule", "NOTELIM: expected ⊢ ¬ p",
        <|"concl" -> c|>]];
    p = c[[2]];
    unfoldEq = unfoldNot[p];
    EQMP[unfoldEq, th]
  ];

HOL`Bool`CONTR[p_, thF_] :=
  Module[{c, forAllAll},
    If[typeOf[p] =!= boolTy,
      HOL`Error`holError["rule", "CONTR: target must be :bool",
        <|"got" -> typeOf[p]|>]];
    c = concl[thF];
    If[c =!= mkConst["F", boolTy],
      HOL`Error`holError["rule", "CONTR: second arg must conclude F",
        <|"concl" -> c|>]];
    forAllAll = EQMP[fDef, thF];
    HOL`Bool`SPEC[p, forAllAll]
  ];

HOL`Bool`EXISTS[existTm_, witness_, th_] :=
  Module[{P, xTy, pWit, betaPw, bodyAsPw, qVar, xVar, forbidden,
          innerForall, specTh, mpTh, dischTh, genTh,
          defInst, s1, b1, unfoldEq},
    If[! MatchQ[existTm, comb[const["∃", _], abs[bvar[0, _], _, _String]]],
      HOL`Error`holError["rule", "EXISTS: expected ∃x. p",
        <|"got" -> existTm|>]];
    P = existTm[[2]];
    xTy = typeOf[P] /. tyApp["fun", {a_, _}] :> a;
    If[typeOf[witness] =!= xTy,
      HOL`Error`holError["rule", "EXISTS: witness type mismatch",
        <|"binderType" -> xTy, "witnessType" -> typeOf[witness]|>]];
    pWit = mkComb[P, witness];
    betaPw = BETACONV[pWit];
    bodyAsPw = EQMP[SYM[betaPw], th];
    forbidden = collectFreeNames[existTm, witness, Sequence @@ hyp[th]];
    qVar = mkVar[freshName["q", forbidden], boolTy];
    xVar = mkVar[freshName["x", Append[forbidden, qVar[[1]]]], xTy];
    innerForall = mkComb[
      mkConst["∀", tyFun[tyFun[xTy, boolTy], boolTy]],
      mkAbs[xVar, impTmInt[mkComb[P, xVar], qVar]]];
    specTh = HOL`Bool`SPEC[witness, ASSUME[innerForall]];
    mpTh = HOL`Bool`MP[specTh, bodyAsPw];
    dischTh = HOL`Bool`DISCH[innerForall, mpTh];
    genTh = HOL`Bool`GEN[qVar, dischTh];
    defInst = INSTTYPE[{tyVar["a"] -> xTy}, existsDef];
    s1 = APTHM[defInst, P];
    b1 = BETACONV[rhsOfConcl[s1]];
    unfoldEq = TRANS[s1, b1];
    EQMP[SYM[unfoldEq], genTh]
  ];

HOL`Bool`CHOOSE[v : var[vName_String, _], existsTh_, bodyTh_] :=
  Module[{c, P, xTy, qRes, defInst, s1, b1, unfoldEq, step1, specTh,
          pv, betaPv, assPv, bodyFromPv, withHyp, dischTh, genTh},
    c = concl[existsTh];
    If[! MatchQ[c, comb[const["∃", _], abs[bvar[0, _], _, _String]]],
      HOL`Error`holError["rule", "CHOOSE: exists th must conclude ∃x. p",
        <|"concl" -> c|>]];
    P = c[[2]];
    xTy = typeOf[P] /. tyApp["fun", {a_, _}] :> a;
    If[typeOf[v] =!= xTy,
      HOL`Error`holError["rule", "CHOOSE: v type must match ∃ binder",
        <|"expected" -> xTy, "got" -> typeOf[v]|>]];
    qRes = concl[bodyTh];
    If[MemberQ[Map[First, freesIn[qRes]], vName],
      HOL`Error`holError["rule", "CHOOSE: v must not be free in conclusion",
        <|"v" -> v, "concl" -> qRes|>]];
    If[AnyTrue[hyp[existsTh], MemberQ[Map[First, freesIn[#]], vName] &],
      HOL`Error`holError["rule", "CHOOSE: v must not be free in exists-hypotheses",
        <|"v" -> v|>]];
    defInst = INSTTYPE[{tyVar["a"] -> xTy}, existsDef];
    s1 = APTHM[defInst, P];
    b1 = BETACONV[rhsOfConcl[s1]];
    unfoldEq = TRANS[s1, b1];
    step1 = EQMP[unfoldEq, existsTh];
    specTh = HOL`Bool`SPEC[qRes, step1];
    pv = mkComb[P, v];
    betaPv = BETACONV[pv];
    assPv = ASSUME[pv];
    bodyFromPv = EQMP[betaPv, assPv];
    withHyp = proveHyp[bodyFromPv, bodyTh];
    dischTh = HOL`Bool`DISCH[pv, withHyp];
    genTh = HOL`Bool`GEN[v, dischTh];
    HOL`Bool`MP[specTh, genTh]
  ];
HOL`Bool`CHOOSE[other_, _, _] :=
  HOL`Error`holError["rule", "CHOOSE: first arg must be a var",
    <|"got" -> other|>];

HOL`Bool`DISJ1[thp_, qTm_] :=
  Module[{p, r, pImpR, qImpR, mpTh, inner1, inner2, genTh},
    If[typeOf[qTm] =!= boolTy,
      HOL`Error`holError["rule", "DISJ1: q must be :bool",
        <|"got" -> typeOf[qTm]|>]];
    p = concl[thp];
    r = mkVar[freshName["r",
      collectFreeNames[p, qTm, Sequence @@ hyp[thp]]], boolTy];
    pImpR = impTmInt[p, r];
    qImpR = impTmInt[qTm, r];
    mpTh = HOL`Bool`MP[ASSUME[pImpR], thp];
    inner1 = HOL`Bool`DISCH[qImpR, mpTh];
    inner2 = HOL`Bool`DISCH[pImpR, inner1];
    genTh = HOL`Bool`GEN[r, inner2];
    EQMP[SYM[unfoldOr[p, qTm]], genTh]
  ];

HOL`Bool`DISJ2[thq_, pTm_] :=
  Module[{q, r, pImpR, qImpR, mpTh, inner1, inner2, genTh},
    If[typeOf[pTm] =!= boolTy,
      HOL`Error`holError["rule", "DISJ2: p must be :bool",
        <|"got" -> typeOf[pTm]|>]];
    q = concl[thq];
    r = mkVar[freshName["r",
      collectFreeNames[q, pTm, Sequence @@ hyp[thq]]], boolTy];
    pImpR = impTmInt[pTm, r];
    qImpR = impTmInt[q, r];
    mpTh = HOL`Bool`MP[ASSUME[qImpR], thq];
    inner1 = HOL`Bool`DISCH[qImpR, mpTh];
    inner2 = HOL`Bool`DISCH[pImpR, inner1];
    genTh = HOL`Bool`GEN[r, inner2];
    EQMP[SYM[unfoldOr[pTm, q]], genTh]
  ];

HOL`Bool`DISJCASES[thOr_, thPR_, thQR_] :=
  Module[{c, p, q, rTgt, unfoldTh, step1, specTh, pImp, qImp, step3},
    c = concl[thOr];
    If[! MatchQ[c, comb[comb[const["∨", _], _], _]],
      HOL`Error`holError["rule", "DISJCASES: expected p ∨ q",
        <|"concl" -> c|>]];
    p = c[[1, 2]]; q = c[[2]];
    rTgt = concl[thPR];
    If[concl[thQR] =!= rTgt,
      HOL`Error`holError["rule", "DISJCASES: branches must share conclusion",
        <|"left" -> rTgt, "right" -> concl[thQR]|>]];
    unfoldTh = unfoldOr[p, q];
    step1 = EQMP[unfoldTh, thOr];
    specTh = HOL`Bool`SPEC[rTgt, step1];
    pImp = HOL`Bool`DISCH[p, thPR];
    qImp = HOL`Bool`DISCH[q, thQR];
    step3 = HOL`Bool`MP[specTh, pImp];
    HOL`Bool`MP[step3, qImp]
  ];

orTmInt[a_, b_] :=
  mkComb[mkComb[mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
notTmInt[p_] := mkComb[mkConst["¬", tyFun[boolTy, boolTy]], p];
selectCty[ty_] := mkConst["@", tyFun[tyFun[ty, boolTy], ty]];

selectAp[P_, w_, wth_] :=
  Module[{xTy, axInst, specP, specW, pWbeta, pSelbeta, thApp, mpStep},
    xTy = typeOf[P] /. tyApp["fun", {a_, _}] :> a;
    axInst = INSTTYPE[{tyVar["a"] -> xTy}, selectAx];
    specP = HOL`Bool`SPEC[P, axInst];
    specW = HOL`Bool`SPEC[w, specP];
    pWbeta = BETACONV[mkComb[P, w]];
    thApp = EQMP[SYM[pWbeta], wth];
    mpStep = HOL`Bool`MP[specW, thApp];
    pSelbeta = BETACONV[mkComb[P, mkComb[selectCty[xTy], P]]];
    EQMP[pSelbeta, mpStep]
  ];

HOL`Bool`EXCLUDEDMIDDLE[t_] :=
  Module[{xName, xv, tConst, fConst, Uabs, Vabs, selBool, u, v,
          uEqTOrT, vEqFOrT, assT, thA, thB, bodyEq, UeqV, tEqUV,
          tImpUV, assUT, assVF, assTHyp, mpUV, symUT, transTv,
          transTF, fromTEqF, dischTF, notTThm, notT,
          innerBranch1, innerBranch2, outerBranch1, outerBranch2},
    If[typeOf[t] =!= boolTy,
      HOL`Error`holError["rule", "EXCLUDEDMIDDLE: target must be :bool",
        <|"got" -> typeOf[t]|>]];
    tConst = mkConst["T", boolTy];
    fConst = mkConst["F", boolTy];
    xName = freshName["x", collectFreeNames[t]];
    xv = mkVar[xName, boolTy];
    Uabs = mkAbs[xv, orTmInt[mkEq[xv, tConst], t]];
    Vabs = mkAbs[xv, orTmInt[mkEq[xv, fConst], t]];
    selBool = selectCty[boolTy];
    u = mkComb[selBool, Uabs];
    v = mkComb[selBool, Vabs];
    uEqTOrT = selectAp[Uabs, tConst, HOL`Bool`DISJ1[REFL[tConst], t]];
    vEqFOrT = selectAp[Vabs, fConst, HOL`Bool`DISJ1[REFL[fConst], t]];
    assT = ASSUME[t];
    thA = HOL`Bool`DISJ2[assT, mkEq[xv, tConst]];
    thB = HOL`Bool`DISJ2[assT, mkEq[xv, fConst]];
    bodyEq = DEDUCTANTISYM[thA, thB];
    UeqV = ABS[xv, bodyEq];
    tEqUV = APTERM[selBool, UeqV];
    tImpUV = HOL`Bool`DISCH[t, tEqUV];
    assUT = ASSUME[mkEq[u, tConst]];
    assVF = ASSUME[mkEq[v, fConst]];
    assTHyp = ASSUME[t];
    mpUV = HOL`Bool`MP[tImpUV, assTHyp];
    symUT = SYM[assUT];
    transTv = TRANS[symUT, mpUV];
    transTF = TRANS[transTv, assVF];
    fromTEqF = EQMP[transTF, HOL`Bool`TRUTH];
    dischTF = HOL`Bool`DISCH[t, fromTEqF];
    notTThm = HOL`Bool`NOTINTRO[dischTF];
    notT = notTmInt[t];
    innerBranch1 = HOL`Bool`DISJ2[notTThm, t];
    innerBranch2 = HOL`Bool`DISJ1[ASSUME[t], notT];
    outerBranch1 = HOL`Bool`DISJCASES[vEqFOrT, innerBranch1, innerBranch2];
    outerBranch2 = HOL`Bool`DISJ1[ASSUME[t], notT];
    HOL`Bool`DISJCASES[uEqTOrT, outerBranch1, outerBranch2]
  ];

HOL`Bool`CCONTR[p_, thF_] :=
  Module[{c, emTh, pBranch, notPBranch},
    If[typeOf[p] =!= boolTy,
      HOL`Error`holError["rule", "CCONTR: target must be :bool",
        <|"got" -> typeOf[p]|>]];
    c = concl[thF];
    If[c =!= mkConst["F", boolTy],
      HOL`Error`holError["rule", "CCONTR: second arg must conclude F",
        <|"concl" -> c|>]];
    emTh = HOL`Bool`EXCLUDEDMIDDLE[p];
    pBranch = ASSUME[p];
    notPBranch = HOL`Bool`CONTR[p, thF];
    HOL`Bool`DISJCASES[emTh, pBranch, notPBranch]
  ];

(* ============================================================ *)
(* COND : the conditional (bool.ml COND + COND_CLAUSES).        *)
(*   COND = λt a b. @x. ((t=T) ⇒ x=a) ∧ ((t=F) ⇒ x=b).          *)
(* Below the SIMP layer, so the clauses are proved with raw     *)
(* Bool/Equal rules + selectAx.                                  *)
(* ============================================================ *)

conjTmInt[a_, b_] :=
  mkComb[mkComb[mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];

Module[{aTy, tV, aV, bV, xV, tConst, fConst, condTy, selTm, predLam,
        condBody},
  aTy = mkVarType["A"];
  tV = mkVar["t", boolTy]; aV = mkVar["a", aTy]; bV = mkVar["b", aTy];
  xV = mkVar["x", aTy];
  tConst = mkConst["T", boolTy]; fConst = mkConst["F", boolTy];
  condTy = tyFun[boolTy, tyFun[aTy, tyFun[aTy, aTy]]];
  predLam = mkAbs[xV,
    conjTmInt[
      impTmInt[mkEq[tV, tConst], mkEq[xV, aV]],
      impTmInt[mkEq[tV, fConst], mkEq[xV, bV]]]];
  selTm = mkComb[mkConst["@", tyFun[tyFun[aTy, boolTy], aTy]], predLam];
  condBody = mkAbs[tV, mkAbs[aV, mkAbs[bV, selTm]]];
  HOL`Bool`condDefThm = newDefinition[mkEq[mkVar["COND", condTy], condBody]];
];

HOL`Bool`condConst[ty_] :=
  mkConst["COND", tyFun[boolTy, tyFun[ty, tyFun[ty, ty]]]];

(* ⊢ COND t a b = @x. ((t=T)⇒x=a) ∧ ((t=F)⇒x=b) for given t,a,b. *)
unfoldCond[tTm_, aTm_, bTm_] :=
  Module[{ap1, e1, ap2, e2, ap3},
    ap1 = APTHM[HOL`Bool`condDefThm, tTm];
    e1 = TRANS[ap1, BETACONV[rhsOfConcl[ap1]]];
    ap2 = APTHM[e1, aTm];
    e2 = TRANS[ap2, BETACONV[rhsOfConcl[ap2]]];
    ap3 = APTHM[e2, bTm];
    TRANS[ap3, BETACONV[rhsOfConcl[ap3]]]
  ];

(* Given uf : ⊢ COND … = @P, a witness w, predAtW : ⊢ P w, and    *)
(* uniqGen : ⊢ ∀x. P x ⇒ x = w, derive ⊢ COND … = w via selectAx. *)
epsEqWitness[uf_, wTm_, predAtW_, uniqGen_] :=
  Module[{selP, predLam, atSel, pOfSel, specUniq},
    selP = rhsOfConcl[uf];
    predLam = selP[[2]];
    atSel = HOL`Bool`SPEC[wTm, HOL`Bool`ISPEC[predLam, HOL`Bootstrap`selectAx]];
    pOfSel = HOL`Bool`MP[atSel, predAtW];
    specUniq = HOL`Bool`SPEC[selP, uniqGen];
    TRANS[uf, HOL`Bool`MP[specUniq, pOfSel]]
  ];

(* condTThm : ⊢ ∀a b. COND T a b = a *)
HOL`Bool`condTThm =
  Module[{aTy, aV, bV, xx, tConst, fConst, uf, predLam, betaPa,
          c1, hTF, fF, c2, predAtA, Pxx, betaPxx, unf, xxEqA, uniqGen,
          condEqA},
    aTy = mkVarType["A"];
    aV = mkVar["a", aTy]; bV = mkVar["b", aTy]; xx = mkVar["xx", aTy];
    tConst = mkConst["T", boolTy]; fConst = mkConst["F", boolTy];
    uf = unfoldCond[tConst, aV, bV];
    predLam = rhsOfConcl[uf][[2]];
    (* predAtA : ⊢ P a *)
    betaPa = BETACONV[mkComb[predLam, aV]];
    c1 = HOL`Bool`DISCH[mkEq[tConst, tConst], REFL[aV]];
    hTF = ASSUME[mkEq[tConst, fConst]];
    fF = EQMP[hTF, HOL`Bool`TRUTH];
    c2 = HOL`Bool`DISCH[mkEq[tConst, fConst], HOL`Bool`CONTR[mkEq[aV, bV], fF]];
    predAtA = EQMP[SYM[betaPa], HOL`Bool`CONJ[c1, c2]];
    (* uniqGen : ⊢ ∀x. P x ⇒ x = a *)
    Pxx = mkComb[predLam, xx];
    betaPxx = BETACONV[Pxx];
    unf = EQMP[betaPxx, ASSUME[Pxx]];
    xxEqA = HOL`Bool`MP[HOL`Bool`CONJUNCT1[unf], REFL[tConst]];
    uniqGen = HOL`Bool`GEN[xx, HOL`Bool`DISCH[Pxx, xxEqA]];
    condEqA = epsEqWitness[uf, aV, predAtA, uniqGen];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, condEqA]]
  ];

(* condFThm : ⊢ ∀a b. COND F a b = b *)
HOL`Bool`condFThm =
  Module[{aTy, aV, bV, xx, tConst, fConst, uf, predLam, betaPb,
          hFT, fF, c1, c2, predAtB, Pxx, betaPxx, unf, xxEqB, uniqGen,
          condEqB},
    aTy = mkVarType["A"];
    aV = mkVar["a", aTy]; bV = mkVar["b", aTy]; xx = mkVar["xx", aTy];
    tConst = mkConst["T", boolTy]; fConst = mkConst["F", boolTy];
    uf = unfoldCond[fConst, aV, bV];
    predLam = rhsOfConcl[uf][[2]];
    (* predAtB : ⊢ P b *)
    betaPb = BETACONV[mkComb[predLam, bV]];
    hFT = ASSUME[mkEq[fConst, tConst]];
    fF = EQMP[SYM[hFT], HOL`Bool`TRUTH];
    c1 = HOL`Bool`DISCH[mkEq[fConst, tConst], HOL`Bool`CONTR[mkEq[bV, aV], fF]];
    c2 = HOL`Bool`DISCH[mkEq[fConst, fConst], REFL[bV]];
    predAtB = EQMP[SYM[betaPb], HOL`Bool`CONJ[c1, c2]];
    (* uniqGen : ⊢ ∀x. P x ⇒ x = b *)
    Pxx = mkComb[predLam, xx];
    betaPxx = BETACONV[Pxx];
    unf = EQMP[betaPxx, ASSUME[Pxx]];
    xxEqB = HOL`Bool`MP[HOL`Bool`CONJUNCT2[unf], REFL[fConst]];
    uniqGen = HOL`Bool`GEN[xx, HOL`Bool`DISCH[Pxx, xxEqB]];
    condEqB = epsEqWitness[uf, bV, predAtB, uniqGen];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, condEqB]]
  ];

End[];
EndPackage[];
