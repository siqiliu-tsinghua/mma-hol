(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Printer`"];

HOLTest`runTests["printer: registry", Module[{spec},
  spec = HOL`Printer`lookupOperator["∧"];
  HOLTest`assertTrue[AssociationQ[spec], "lookup ∧ returns assoc"];
  HOLTest`assertEq[spec["kind"], "infix", "∧ kind"];
  HOLTest`assertEq[spec["assoc"], "right", "∧ right-assoc"];
  HOLTest`assertEq[HOL`Printer`lookupOperator["nope"],
    Missing["NotRegistered", "nope"], "missing key"];
]];

HOLTest`runTests["printer: atoms", Module[{alpha, x},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  HOLTest`assertEq[formatTerm[x], "x", "var prints as name"];
  HOLTest`assertEq[formatTerm[mkConst["T", boolTy]], "T",
    "non-operator const prints as bare name"];
  HOLTest`assertEq[
    formatTerm[mkConst["=", tyFun[alpha, tyFun[alpha, boolTy]]]],
    "(=)", "registered infix const prints with parens"];
]];

HOLTest`runTests["printer: applications", Module[{alpha, beta, gamma, f, g, x, y, fxy, gx, fGxy, ggx},
  alpha = mkVarType["a"]; beta = mkVarType["b"]; gamma = mkVarType["c"];
  f = mkVar["f", tyFun[alpha, tyFun[beta, gamma]]];
  g = mkVar["g", tyFun[alpha, alpha]];
  x = mkVar["x", alpha]; y = mkVar["y", beta];
  fxy = mkComb[mkComb[f, x], y];
  HOLTest`assertEq[formatTerm[fxy], "f x y", "left-assoc app"];
  gx = mkComb[g, x];
  fGxy = mkComb[mkComb[f, gx], y];
  HOLTest`assertEq[formatTerm[fGxy], "f (g x) y",
    "function arg parenthesized"];
  ggx = mkComb[g, gx];
  HOLTest`assertEq[formatTerm[ggx], "g (g x)",
    "right arg with app needs parens"];
]];

HOLTest`runTests["printer: equality (infix)", Module[{alpha, xa, ya, p, q, r, eqXY, eqQR},
  alpha = mkVarType["a"];
  xa = mkVar["x", alpha]; ya = mkVar["y", alpha];
  eqXY = mkEq[xa, ya];
  HOLTest`assertEq[formatTerm[eqXY], "x = y", "= renders infix"];
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy]; r = mkVar["r", boolTy];
  eqQR = mkEq[q, r];
  HOLTest`assertEq[formatTerm[mkEq[p, eqQR]], "p = q = r",
    "= right-assoc, right child no parens"];
  HOLTest`assertEq[formatTerm[mkEq[mkEq[p, q], r]], "(p = q) = r",
    "= left child needs parens"];
]];

HOLTest`runTests["printer: ∧ ∨ ⇒ precedence", Module[
    {p, q, r, andC, orC, impC, pq, qr, pOrQ},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy]; r = mkVar["r", boolTy];
  andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  orC  = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];

  pq = mkComb[mkComb[andC, p], q];
  HOLTest`assertEq[formatTerm[pq], "p ∧ q", "p ∧ q"];

  qr = mkComb[mkComb[andC, q], r];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[andC, p], qr]],
    "p ∧ q ∧ r", "∧ right-assoc chain (no parens)"];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[andC, pq], r]],
    "(p ∧ q) ∧ r", "∧ left-assoc structure forces parens"];

  pOrQ = mkComb[mkComb[orC, p], q];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[andC, pOrQ], r]],
    "(p ∨ q) ∧ r", "∨ inside ∧ needs parens (looser child)"];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[orC, p], pq]],
    "p ∨ p ∧ q", "∧ inside ∨ no parens (tighter child)"];

  HOLTest`assertEq[formatTerm[mkComb[mkComb[impC, p], q]],
    "p ⇒ q", "p ⇒ q"];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[impC, pq], r]],
    "p ∧ q ⇒ r", "∧ inside ⇒ no parens"];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[impC, p], mkComb[mkComb[impC, q], r]]],
    "p ⇒ q ⇒ r", "⇒ right-assoc chain"];
]];

HOLTest`runTests["printer: ¬ prefix", Module[{p, q, andC, notC, np, ppq},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  notC = mkConst["¬", tyFun[boolTy, boolTy]];
  np = mkComb[notC, p];
  HOLTest`assertEq[formatTerm[np], "¬ p", "¬ p"];
  HOLTest`assertEq[formatTerm[mkComb[notC, np]], "¬ ¬ p",
    "double prefix no parens"];

  ppq = mkComb[mkComb[andC, p], q];
  HOLTest`assertEq[formatTerm[mkComb[notC, ppq]], "¬ (p ∧ q)",
    "looser child of prefix gets parens"];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[andC, np], q]],
    "¬ p ∧ q", "¬ tighter than ∧"];
]];

HOLTest`runTests["printer: λ binder", Module[{alpha, x, y, f, lam, lam2},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  lam = mkAbs[x, x];
  HOLTest`assertEq[formatTerm[lam], "λx. x", "λx. x"];
  f = mkVar["f", tyFun[alpha, tyFun[alpha, alpha]]];
  lam2 = mkAbs[x, mkAbs[y, mkComb[mkComb[f, x], y]]];
  HOLTest`assertEq[formatTerm[lam2], "λx y. f x y", "λ-chain collapses"];
]];

HOLTest`runTests["printer: ∀ ∃ binder chain", Module[
    {alpha, x, y, z, forallC, existsC, body, q, q2, q3, mixed},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha]; z = mkVar["z", alpha];
  forallC = mkConst["∀", tyFun[tyFun[alpha, boolTy], boolTy]];
  existsC = mkConst["∃", tyFun[tyFun[alpha, boolTy], boolTy]];
  body = mkConst["T", boolTy];

  q = mkComb[forallC, mkAbs[x, body]];
  HOLTest`assertEq[formatTerm[q], "∀x. T", "∀x. T"];

  q2 = mkComb[forallC, mkAbs[x, mkComb[forallC, mkAbs[y, body]]]];
  HOLTest`assertEq[formatTerm[q2], "∀x y. T", "∀ chain length 2"];

  q3 = mkComb[forallC, mkAbs[x,
        mkComb[forallC, mkAbs[y,
          mkComb[forallC, mkAbs[z, body]]]]]];
  HOLTest`assertEq[formatTerm[q3], "∀x y z. T", "∀ chain length 3"];

  mixed = mkComb[forallC, mkAbs[x, mkComb[existsC, mkAbs[y, body]]]];
  HOLTest`assertEq[formatTerm[mixed], "∀x. ∃y. T",
    "∀ then ∃ stays separate (different binder)"];
]];

HOLTest`runTests["printer: name collision", Module[
    {alpha, xAlpha, xBool, lam, forallC, P, inner, term},
  alpha = mkVarType["a"];
  xAlpha = mkVar["x", alpha];
  xBool  = mkVar["x", boolTy];
  lam = mkAbs[xAlpha, xBool];
  HOLTest`assertEq[formatTerm[lam], "λx'. x",
    "binder origin collides with free-var name → primed"];

  forallC = mkConst["∀", tyFun[tyFun[alpha, boolTy], boolTy]];
  P = mkVar["P", tyFun[tyFun[alpha, alpha], boolTy]];
  inner = mkAbs[xAlpha, xAlpha];
  term = mkComb[forallC, mkAbs[xAlpha, mkComb[P, inner]]];
  HOLTest`assertEq[formatTerm[term],
    "∀x. P (λx'. x')",
    "inner λ binder origin clashes with enclosing ∀'s display name → primed"];
]];

HOLTest`runTests["printer: binder paren on left of infix", Module[
    {alpha, x, lam, eq},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  lam = mkAbs[x, x];
  eq = mkEq[lam, lam];
  HOLTest`assertEq[formatTerm[eq], "(λx. x) = λx. x",
    "binder parens on left arg of =, none on right (binder body extends right)"];
]];

HOLTest`runTests["printer: ASCII mode", Module[
    {alpha, p, q, andC, orC, impC, notC, x, y, lam, forallC, body},
  alpha = mkVarType["a"];
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  orC  = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  notC = mkConst["¬", tyFun[boolTy, boolTy]];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  lam = mkAbs[x, x];
  forallC = mkConst["∀", tyFun[tyFun[alpha, boolTy], boolTy]];
  body = mkConst["T", boolTy];

  HOLTest`assertEq[formatTerm[mkComb[mkComb[andC, p], q], "ASCII"],
    "p /\\ q", "∧ → /\\"];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[orC, p], q], "ASCII"],
    "p \\/ q", "∨ → \\/"];
  HOLTest`assertEq[formatTerm[mkComb[mkComb[impC, p], q], "ASCII"],
    "p ==> q", "⇒ → ==>"];
  HOLTest`assertEq[formatTerm[mkComb[notC, p], "ASCII"], "~ p",
    "¬ → ~"];
  HOLTest`assertEq[formatTerm[lam, "ASCII"], "\\x. x", "λ → \\"];
  HOLTest`assertEq[formatTerm[mkComb[forallC, mkAbs[x, body]], "ASCII"],
    "!x. T", "∀ → !"];
]];

HOLTest`runTests["printer: formatThm", Module[{p, q, andC, pq, refl, hypTh},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  pq = mkComb[mkComb[andC, p], q];

  refl = REFL[p];
  HOLTest`assertEq[formatThm[refl], "⊢ p = p", "no-hyps thm"];
  HOLTest`assertEq[formatThm[refl, "ASCII"], "|- p = p",
    "no-hyps thm ASCII"];

  hypTh = ASSUME[pq];
  HOLTest`assertEq[formatThm[hypTh], "[p ∧ q] ⊢ p ∧ q", "single hyp"];
]];

HOLTest`runTests["printer: tDef capstone", Module[{},
  HOLTest`assertEq[formatThm[tDef],
    "⊢ T = (λx. x) = λx. x",
    "tDef rendered: left arg of inner = parenthesized, right arg unparenthesized"];
]];

HOLTest`runTests["printer: invalid mode rejected", Module[{p},
  p = mkVar["p", boolTy];
  HOLTest`assertThrows[formatTerm[p, "Pirate"], "printer",
    "formatTerm rejects unknown mode"];
  HOLTest`assertThrows[formatThm[REFL[p], "Pirate"], "printer",
    "formatThm rejects unknown mode"];
]];

HOLTest`runTests["printer: app vs infix interaction", Module[
    {alpha, f, g, x, y, fx, gy, eqfg, h, hEq},
  alpha = mkVarType["a"];
  f = mkVar["f", tyFun[alpha, alpha]];
  g = mkVar["g", tyFun[alpha, alpha]];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];

  fx = mkComb[f, x]; gy = mkComb[g, y];
  eqfg = mkEq[fx, gy];
  HOLTest`assertEq[formatTerm[eqfg], "f x = g y",
    "f x = g y: = looser than app, no inner parens"];

  h = mkVar["h", tyFun[boolTy, alpha]];
  hEq = mkComb[h, mkEq[x, y]];
  HOLTest`assertEq[formatTerm[hEq], "h (x = y)",
    "h (x = y): = inside app needs parens"];
]];
