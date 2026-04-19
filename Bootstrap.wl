(* ::Package:: *)

BeginPackage["HOL`Bootstrap`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`"}];

tDef::usage       = "tDef — ⊢ T = ((λx:bool. x) = (λx:bool. x)).";
forallDef::usage  = "forallDef — ⊢ ∀ = (λP. P = (λx. T)).";
andDef::usage     = "andDef — ⊢ ∧ = (λp q. (λf. f p q) = (λf. f T T)).";
impliesDef::usage = "impliesDef — ⊢ ⇒ = (λp q. (p ∧ q) = p).";
existsDef::usage  = "existsDef — ⊢ ∃ = (λP. ∀q. (∀x. P x ⇒ q) ⇒ q).";
fDef::usage       = "fDef — ⊢ F = (∀p:bool. p).";
notDef::usage     = "notDef — ⊢ ¬ = (λp. p ⇒ F).";
oneOneDef::usage  = "oneOneDef — ⊢ ONE_ONE = (λf. ∀x1 x2. f x1 = f x2 ⇒ x1 = x2).";
ontoDef::usage    = "ontoDef — ⊢ ONTO = (λf. ∀y. ∃x. y = f x).";

etaAx::usage      = "etaAx — ⊢ ∀t. (λx. t x) = t.";
selectAx::usage   = "selectAx — ⊢ ∀P x. P x ⇒ P (@ P).";
infinityAx::usage = "infinityAx — ⊢ ∃f:ind→ind. ONE_ONE f ∧ ¬ (ONTO f).";

Begin["`Private`"];

bool = HOL`Kernel`boolTy;
ind  = HOL`Kernel`indTy;
alpha = tyVar["a"];
beta  = tyVar["b"];

tyArrow[t1_, t2_] := tyApp["fun", {t1, t2}];

cEq[ty_] := mkConst["=", tyArrow[ty, tyArrow[ty, bool]]];
eqTm[s_, t_] := mkEq[s, t];

app[f_, x_] := mkComb[f, x];
app[f_, x_, y__] := Fold[mkComb, f, {x, y}];

lam[v_, body_] := mkAbs[v, body];
lams[{v_}, body_] := lam[v, body];
lams[{v_, rest__}, body_] := lam[v, lams[{rest}, body]];

(* --- T --- *)
Module[{x, body, rhs, lhs},
  x   = mkVar["x", bool];
  body = lam[x, x];
  rhs  = eqTm[body, body];
  lhs  = mkVar["T", bool];
  HOL`Bootstrap`tDef = newDefinition[eqTm[lhs, rhs]];
];

constT = mkConst["T", bool];

(* --- ∀ --- *)
(* ∀ ≡ λP. P = (λx:α. T)   :  (α→bool) → bool *)
Module[{P, x, inner, body, lhs, ty},
  ty  = tyArrow[tyArrow[alpha, bool], bool];
  P   = mkVar["P", tyArrow[alpha, bool]];
  x   = mkVar["x", alpha];
  inner = lam[x, constT];
  body  = lam[P, eqTm[P, inner]];
  lhs   = mkVar["∀", ty];
  HOL`Bootstrap`forallDef = newDefinition[eqTm[lhs, body]];
];

forallC[ty_] :=
  mkConst["∀", tyArrow[tyArrow[ty, bool], bool]];

(* forall v. body  =  ∀ (λv. body) *)
forallQ[v : var[_, ty_], body_] := app[forallC[ty], lam[v, body]];
forallQs[vs_List, body_] := Fold[forallQ[#2, #1] &, body, Reverse[vs]];

(* --- ∧ --- *)
(* ∧ ≡ λp q. (λf:bool→bool→bool. f p q) = (λf. f T T)   :  bool→bool→bool *)
Module[{p, q, f, fAtBool, fppq, fTT, body, lhs, ty},
  ty = tyArrow[bool, tyArrow[bool, bool]];
  p = mkVar["p", bool];
  q = mkVar["q", bool];
  fAtBool = tyArrow[bool, tyArrow[bool, bool]];
  f = mkVar["f", fAtBool];
  fppq = lam[f, app[f, p, q]];
  fTT  = lam[f, app[f, constT, constT]];
  body = lams[{p, q}, eqTm[fppq, fTT]];
  lhs  = mkVar["∧", ty];
  HOL`Bootstrap`andDef = newDefinition[eqTm[lhs, body]];
];

andC := mkConst["∧", tyArrow[bool, tyArrow[bool, bool]]];
andTm[a_, b_] := app[andC, a, b];

(* --- ⇒ --- *)
(* ⇒ ≡ λp q. (p ∧ q) = p    :  bool→bool→bool *)
Module[{p, q, body, lhs, ty},
  ty = tyArrow[bool, tyArrow[bool, bool]];
  p = mkVar["p", bool];
  q = mkVar["q", bool];
  body = lams[{p, q}, eqTm[andTm[p, q], p]];
  lhs  = mkVar["⇒", ty];
  HOL`Bootstrap`impliesDef = newDefinition[eqTm[lhs, body]];
];

impliesC := mkConst["⇒", tyArrow[bool, tyArrow[bool, bool]]];
impliesTm[a_, b_] := app[impliesC, a, b];

(* --- ∃ --- *)
(* ∃ ≡ λP:α→bool. ∀q:bool. (∀x:α. P x ⇒ q) ⇒ q    :  (α→bool) → bool *)
Module[{P, q, x, innerForall, body, lhs, ty},
  ty = tyArrow[tyArrow[alpha, bool], bool];
  P = mkVar["P", tyArrow[alpha, bool]];
  q = mkVar["q", bool];
  x = mkVar["x", alpha];
  innerForall = forallQ[x, impliesTm[app[P, x], q]];
  body = lam[P, forallQ[q, impliesTm[innerForall, q]]];
  lhs  = mkVar["∃", ty];
  HOL`Bootstrap`existsDef = newDefinition[eqTm[lhs, body]];
];

existsC[ty_] := mkConst["∃", tyArrow[tyArrow[ty, bool], bool]];
existsQ[v : var[_, ty_], body_] := app[existsC[ty], lam[v, body]];

(* --- F --- *)
(* F ≡ ∀p:bool. p    :  bool *)
Module[{p, body, lhs},
  p = mkVar["p", bool];
  body = forallQ[p, p];
  lhs  = mkVar["F", bool];
  HOL`Bootstrap`fDef = newDefinition[eqTm[lhs, body]];
];

constF = mkConst["F", bool];

(* --- ¬ --- *)
(* ¬ ≡ λp:bool. p ⇒ F    :  bool→bool *)
Module[{p, body, lhs, ty},
  ty = tyArrow[bool, bool];
  p = mkVar["p", bool];
  body = lam[p, impliesTm[p, constF]];
  lhs  = mkVar["¬", ty];
  HOL`Bootstrap`notDef = newDefinition[eqTm[lhs, body]];
];

notC := mkConst["¬", tyArrow[bool, bool]];
notTm[t_] := app[notC, t];

(* --- @ (Hilbert's epsilon) — primitive constant, not a definition --- *)
(* @ : (α → bool) → α *)
newConstant["@", tyArrow[tyArrow[alpha, bool], alpha]];

selectC[ty_] := mkConst["@", tyArrow[tyArrow[ty, bool], ty]];

(* --- ONE_ONE --- *)
(* ONE_ONE ≡ λf:α→β. ∀x1 x2. f x1 = f x2 ⇒ x1 = x2   :  (α→β) → bool *)
Module[{f, x1, x2, body, lhs, ty, fnTy},
  fnTy = tyArrow[alpha, beta];
  ty = tyArrow[fnTy, bool];
  f  = mkVar["f", fnTy];
  x1 = mkVar["x1", alpha];
  x2 = mkVar["x2", alpha];
  body = lam[f,
    forallQs[{x1, x2},
      impliesTm[
        eqTm[app[f, x1], app[f, x2]],
        eqTm[x1, x2]]]];
  lhs = mkVar["ONE_ONE", ty];
  HOL`Bootstrap`oneOneDef = newDefinition[eqTm[lhs, body]];
];

oneOneC[a_, b_] :=
  mkConst["ONE_ONE", tyArrow[tyArrow[a, b], bool]];
oneOneTm[f : var[_, tyApp["fun", {a_, b_}]]] := app[oneOneC[a, b], f];
oneOneTm[f_] := app[oneOneC[alpha, beta], f];

(* --- ONTO --- *)
(* ONTO ≡ λf:α→β. ∀y. ∃x. y = f x    :  (α→β) → bool *)
Module[{f, y, x, body, lhs, ty, fnTy},
  fnTy = tyArrow[alpha, beta];
  ty = tyArrow[fnTy, bool];
  f = mkVar["f", fnTy];
  y = mkVar["y", beta];
  x = mkVar["x", alpha];
  body = lam[f,
    forallQ[y, existsQ[x, eqTm[y, app[f, x]]]]];
  lhs = mkVar["ONTO", ty];
  HOL`Bootstrap`ontoDef = newDefinition[eqTm[lhs, body]];
];

ontoC[a_, b_] :=
  mkConst["ONTO", tyArrow[tyArrow[a, b], bool]];

(* --- Axioms --- *)

(* ETA_AX: ∀t:α→β. (λx:α. t x) = t *)
Module[{t, x, lhs, body, fnTy},
  fnTy = tyArrow[alpha, beta];
  t = mkVar["t", fnTy];
  x = mkVar["x", alpha];
  lhs = lam[x, app[t, x]];
  body = forallQ[t, eqTm[lhs, t]];
  HOL`Bootstrap`etaAx = newAxiom[body];
];

(* SELECT_AX: ∀P:α→bool. ∀x:α. P x ⇒ P (@ P) *)
Module[{P, x, sel, body, predTy},
  predTy = tyArrow[alpha, bool];
  P = mkVar["P", predTy];
  x = mkVar["x", alpha];
  sel = app[selectC[alpha], P];
  body = forallQs[{P, x},
    impliesTm[app[P, x], app[P, sel]]];
  HOL`Bootstrap`selectAx = newAxiom[body];
];

(* INFINITY_AX: ∃f:ind→ind. ONE_ONE f ∧ ¬ (ONTO f) *)
Module[{f, body, fnTy},
  fnTy = tyArrow[ind, ind];
  f = mkVar["f", fnTy];
  body = existsQ[f,
    andTm[
      app[oneOneC[ind, ind], f],
      notTm[app[ontoC[ind, ind], f]]]];
  HOL`Bootstrap`infinityAx = newAxiom[body];
];

lockAxioms[];

End[];
EndPackage[];
