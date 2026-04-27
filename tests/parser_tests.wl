(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Printer`"];
Needs["HOL`Parser`"];

HOLTest`runTests["parser: types — atoms", Module[{},
  HOLTest`assertEq[parseType["bool"], boolTy, "bool"];
  HOLTest`assertEq[parseType["ind"], indTy, "ind"];
  HOLTest`assertEq[parseType["'a"], tyVar["a"], "type variable 'a"];
  HOLTest`assertEq[parseType["'foo"], tyVar["foo"], "longer type variable name"];
]];

HOLTest`runTests["parser: types — function arrow (right-assoc)", Module[{},
  HOLTest`assertEq[parseType["bool -> bool"],
    tyFun[boolTy, boolTy], "bool -> bool"];
  HOLTest`assertEq[parseType["'a -> 'b"],
    tyFun[tyVar["a"], tyVar["b"]], "'a -> 'b"];
  HOLTest`assertEq[parseType["'a -> 'b -> 'c"],
    tyFun[tyVar["a"], tyFun[tyVar["b"], tyVar["c"]]],
    "right-assoc"];
  HOLTest`assertEq[parseType["('a -> 'b) -> 'c"],
    tyFun[tyFun[tyVar["a"], tyVar["b"]], tyVar["c"]],
    "left grouping with parens"];
]];

HOLTest`runTests["parser: types — errors", Module[{},
  HOLTest`assertThrows[parseType["nope"], "parser",
    "unknown nullary constructor"];
  HOLTest`assertThrows[parseType["fun"], "parser",
    "fun has arity 2, parser only handles arity 0 inline"];
  HOLTest`assertThrows[parseType["'"], "parser",
    "lone apostrophe rejected"];
]];

HOLTest`runTests["parser: term atoms", Module[{t},
  t = parseTerm["x"];
  HOLTest`assertTrue[MatchQ[t, var["x", _]], "free var x"];
  t = parseTerm["T"];
  HOLTest`assertEq[t, mkConst["T", boolTy],
    "constant T resolved via kernel registry"];
]];

HOLTest`runTests["parser: applications", Module[{t, alpha, beta},
  alpha = tyVar["a"]; beta = tyVar["b"];
  t = parseTerm["f x"];
  HOLTest`assertTrue[MatchQ[t, comb[var["f", _], var["x", _]]],
    "f x"];
  HOLTest`assertEq[typeOf[t[[1]]],
    tyFun[typeOf[t[[2]]], typeOf[t]],
    "type of f matches arg + return"];
  t = parseTerm["f x y"];
  HOLTest`assertTrue[
    MatchQ[t, comb[comb[var["f", _], var["x", _]], var["y", _]]],
    "left-assoc: f x y = (f x) y"];
  t = parseTerm["f (g x)"];
  HOLTest`assertTrue[
    MatchQ[t, comb[var["f", _], comb[var["g", _], var["x", _]]]],
    "f (g x) parens preserve nesting"];
]];

HOLTest`runTests["parser: equality", Module[{t},
  t = parseTerm["x = y"];
  HOLTest`assertTrue[
    MatchQ[t, comb[comb[const["=", _], var["x", τ_]], var["y", τ_]]],
    "x = y forces same type"];
  HOLTest`assertEq[typeOf[t], boolTy, "x = y has type bool"];
]];

HOLTest`runTests["parser: ∧ ∨ ⇒ ¬", Module[{t, p, q, r, andC, orC, impC, notC},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy]; r = mkVar["r", boolTy];
  andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  orC  = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  notC = mkConst["¬", tyFun[boolTy, boolTy]];

  HOLTest`assertEq[parseTerm["p ∧ q"],
    mkComb[mkComb[andC, p], q], "p ∧ q"];
  HOLTest`assertEq[parseTerm["p ∨ q"],
    mkComb[mkComb[orC, p], q], "p ∨ q"];
  HOLTest`assertEq[parseTerm["p ⇒ q"],
    mkComb[mkComb[impC, p], q], "p ⇒ q"];
  HOLTest`assertEq[parseTerm["¬ p"],
    mkComb[notC, p], "¬ p"];
  HOLTest`assertEq[parseTerm["¬ ¬ p"],
    mkComb[notC, mkComb[notC, p]], "¬ ¬ p"];

  HOLTest`assertEq[parseTerm["p ∧ q ∧ r"],
    mkComb[mkComb[andC, p], mkComb[mkComb[andC, q], r]],
    "∧ right-assoc"];
  HOLTest`assertEq[parseTerm["p ∨ q ∧ r"],
    mkComb[mkComb[orC, p], mkComb[mkComb[andC, q], r]],
    "∧ tighter than ∨"];
  HOLTest`assertEq[parseTerm["¬ p ∧ q"],
    mkComb[mkComb[andC, mkComb[notC, p]], q],
    "¬ tighter than ∧"];
  HOLTest`assertEq[parseTerm["¬ (p ∧ q)"],
    mkComb[notC, mkComb[mkComb[andC, p], q]],
    "parens override prefix tightness"];
]];

HOLTest`runTests["parser: ASCII operator aliases", Module[{p, q, andC, orC, impC, notC},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  orC  = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  notC = mkConst["¬", tyFun[boolTy, boolTy]];

  HOLTest`assertEq[parseTerm["p /\\ q"],
    mkComb[mkComb[andC, p], q], "/\\ → ∧"];
  HOLTest`assertEq[parseTerm["p \\/ q"],
    mkComb[mkComb[orC, p], q], "\\/ → ∨"];
  HOLTest`assertEq[parseTerm["p ==> q"],
    mkComb[mkComb[impC, p], q], "==> → ⇒"];
  HOLTest`assertEq[parseTerm["~ p"],
    mkComb[notC, p], "~ → ¬"];
]];

HOLTest`runTests["parser: λ binder", Module[{t, alpha, x, lam},
  alpha = tyVar["a"];
  t = parseTerm["λx. x"];
  HOLTest`assertTrue[MatchQ[t, abs[bvar[0, _], bvar[0, _], "x"]],
    "λx. x has identity shape"];

  t = parseTerm["\\x. x"];
  HOLTest`assertTrue[MatchQ[t, abs[bvar[0, _], bvar[0, _], "x"]],
    "ASCII \\x. x"];

  t = parseTerm["λx y. x"];
  HOLTest`assertTrue[
    MatchQ[t, abs[bvar[0, _], abs[bvar[0, _], bvar[1, _], "y"], "x"]],
    "λx y. x — chain expands to nested abs, body uses bvar[1] for x"];

  t = parseTerm["λx:bool. x"];
  HOLTest`assertEq[t, mkAbs[mkVar["x", boolTy], mkVar["x", boolTy]],
    "type annotation on binder"];
]];

HOLTest`runTests["parser: ∀ ∃ binder", Module[{t, alpha, x, p, body, forallC, existsC},
  alpha = tyVar["a"];
  x = mkVar["x", alpha];

  t = parseTerm["∀x. T"];
  HOLTest`assertTrue[
    MatchQ[t, comb[const["∀", _], abs[bvar[0, _], const["T", _], "x"]]],
    "∀x. T shape"];

  t = parseTerm["∀x y. T"];
  HOLTest`assertTrue[
    MatchQ[t, comb[const["∀", _],
      abs[bvar[0, _], comb[const["∀", _], abs[bvar[0, _], const["T", _], "y"]], "x"]]],
    "∀x y. T expands to ∀x. ∀y. T"];

  t = parseTerm["!x. T"];
  HOLTest`assertTrue[
    MatchQ[t, comb[const["∀", _], abs[bvar[0, _], const["T", _], "x"]]],
    "ASCII ! → ∀"];

  t = parseTerm["?x. T"];
  HOLTest`assertTrue[
    MatchQ[t, comb[const["∃", _], abs[bvar[0, _], const["T", _], "x"]]],
    "ASCII ? → ∃"];

  t = parseTerm["∀x:bool. x"];
  HOLTest`assertEq[t,
    mkComb[mkConst["∀", tyFun[tyFun[boolTy, boolTy], boolTy]],
      mkAbs[mkVar["x", boolTy], mkVar["x", boolTy]]],
    "∀ with type annotation"];
]];

HOLTest`runTests["parser: type ascription", Module[{t},
  t = parseTerm["(x : bool)"];
  HOLTest`assertEq[t, mkVar["x", boolTy], "(x : bool) constrains x"];
  t = parseTerm["(λx. x : 'a -> 'a)"];
  HOLTest`assertEq[t, mkAbs[mkVar["x", tyVar["a"]], mkVar["x", tyVar["a"]]],
    "lambda with explicit polymorphic type"];
]];

HOLTest`runTests["parser: errors", Module[{},
  HOLTest`assertThrows[parseTerm[""], "parser",
    "empty string"];
  HOLTest`assertThrows[parseTerm["("], "parser",
    "unmatched paren"];
  HOLTest`assertThrows[parseTerm["x ="], "parser",
    "trailing infix without RHS"];
  HOLTest`assertThrows[parseTerm["= x y"], "parser",
    "leading infix"];
  HOLTest`assertThrows[parseTerm["∀."], "parser",
    "binder without variables"];
  HOLTest`assertThrows[parseTerm["∀x"], "parser",
    "binder without dot/body"];
  HOLTest`assertThrows[parseTerm["¬"], "parser",
    "prefix without operand"];
  HOLTest`assertTrue[
    MatchQ[parseTerm["x ⇒ y ∧ z = T"], _comb],
    "complex precedence parse succeeds"];
]];

HOLTest`runTests["parser: type unification failures", Module[{},
  (* (¬ x) where x is forced to be α (free) but ¬ needs bool. So x : bool. OK. *)
  HOLTest`assertEq[parseTerm["¬ x"],
    mkComb[mkConst["¬", tyFun[boolTy, boolTy]], mkVar["x", boolTy]],
    "free var inferred bool from ¬"];
  (* x : bool clashes with x : 'a -> 'a — function vs nullary constructor *)
  HOLTest`assertThrows[
    parseTerm["(x : bool) ∧ (x : 'a -> 'a)"],
    "parser",
    "two ascriptions on same var with incompatible types"];
]];

HOLTest`runTests["parser: round-trip via printer", Module[{terms, t, printed, reparsed},
  terms = {
    parseTerm["x"],
    parseTerm["f x y"],
    parseTerm["f (g x)"],
    parseTerm["x = y"],
    parseTerm["p ∧ q"],
    parseTerm["p ⇒ q ⇒ r"],
    parseTerm["p ∧ q ∨ r"],
    parseTerm["¬ p"],
    parseTerm["¬ ¬ p"],
    parseTerm["¬ (p ∧ q)"],
    parseTerm["λx. x"],
    parseTerm["λx y. x"],
    parseTerm["∀x. T"],
    parseTerm["∀x y. T"],
    parseTerm["∀x. ∃y. T"]
  };
  Do[
    printed = formatTerm[t];
    reparsed = parseTerm[printed];
    HOLTest`assertTrue[aconv[t, reparsed],
      "round-trip: " <> printed],
    {t, terms}
  ];
]];

HOLTest`runTests["parser: tDef capstone", Module[{t},
  (* The structural part of ⊢ T = (λx. x) = (λx. x) — concl of tDef. *)
  t = parseTerm["T = (λx:bool. x) = (λx:bool. x)"];
  HOLTest`assertTrue[aconv[t, concl[tDef]],
    "parses tDef's conclusion"];
]];

HOLTest`runTests["parser: prove integration smoke", Module[{th, alpha, x, eq},
  (* Use the parser to construct a term, then run a tactic. Existing tactics
     don't hit the parser, but we want to confirm parser output flows
     cleanly into kernel rules. *)
  th = REFL[parseTerm["x"]];
  HOLTest`assertTrue[MatchQ[concl[th],
    comb[comb[const["=", _], var["x", _]], var["x", _]]],
    "REFL on a parsed term"];
]];
