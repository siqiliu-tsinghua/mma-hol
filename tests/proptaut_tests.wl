(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Parser`"];
Needs["HOL`Auto`PropTaut`"];

(* Build helpers via the parser so types are inferred uniformly. *)
ptParse[s_String] := HOL`Parser`parseTerm[s];
boolVar[name_String] := mkVar[name, boolTy];

HOLTest`runTests["propTaut: smoke — ⊢ T",
  Module[{th, expected},
    th = HOL`Auto`PropTaut`propTaut[mkConst["T", boolTy]];
    expected = mkConst["T", boolTy];
    HOLTest`assertEq[isThm[th], True, "propTaut[T] is a thm"];
    HOLTest`assertEq[concl[th], expected, "concl is T"];
    HOLTest`assertEq[hyp[th], {}, "no hypotheses"];
  ]];

HOLTest`runTests["propTaut: ⊢ p ⇒ p",
  Module[{tm, th},
    tm = ptParse["p ⇒ p"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[isThm[th], True, "is a thm"];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ p ⇒ p"];
    HOLTest`assertEq[hyp[th], {}, "no hypotheses"];
  ]];

HOLTest`runTests["propTaut: excluded middle ⊢ p ∨ ¬p",
  Module[{tm, th},
    tm = ptParse["p ∨ ¬p"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[isThm[th], True, "is a thm"];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ p ∨ ¬p"];
    HOLTest`assertEq[hyp[th], {}, "no hypotheses"];
  ]];

HOLTest`runTests["propTaut: ⊢ ¬(p ∧ ¬p)",
  Module[{tm, th},
    tm = ptParse["¬(p ∧ ¬p)"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[isThm[th], True, "is a thm"];
    HOLTest`assertEq[aconv[concl[th], tm], True, "non-contradiction"];
  ]];

HOLTest`runTests["propTaut: modus ponens form ⊢ (p ⇒ q) ∧ p ⇒ q",
  Module[{tm, th},
    tm = ptParse["(p ⇒ q) ∧ p ⇒ q"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[isThm[th], True, "is a thm"];
    HOLTest`assertEq[aconv[concl[th], tm], True, "concl ≡ MP form"];
  ]];

HOLTest`runTests["propTaut: De Morgan NNF lemma ⊢ ¬(p ∧ q) = ¬p ∨ ¬q",
  Module[{tm, th},
    tm = ptParse["¬(p ∧ q) = (¬p ∨ ¬q)"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[isThm[th], True, "is a thm"];
    HOLTest`assertEq[aconv[concl[th], tm], True, "De Morgan ∧"];
  ]];

HOLTest`runTests["propTaut: De Morgan ∨ form ⊢ ¬(p ∨ q) = ¬p ∧ ¬q",
  Module[{tm, th},
    tm = ptParse["¬(p ∨ q) = (¬p ∧ ¬q)"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "De Morgan ∨"];
  ]];

HOLTest`runTests["propTaut: ¬¬-elimination ⊢ ¬¬p = p",
  Module[{tm, th},
    tm = ptParse["¬¬p = p"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "double-negation"];
  ]];

HOLTest`runTests["propTaut: imp-as-or ⊢ (p ⇒ q) = (¬p ∨ q)",
  Module[{tm, th},
    tm = ptParse["(p ⇒ q) = (¬p ∨ q)"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "imp/or equiv"];
  ]];

HOLTest`runTests["propTaut: distribution ⊢ p ∨ (q ∧ r) = (p ∨ q) ∧ (p ∨ r)",
  Module[{tm, th},
    tm = ptParse["(p ∨ (q ∧ r)) = ((p ∨ q) ∧ (p ∨ r))"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "∨/∧ distribution"];
  ]];

HOLTest`runTests["propTaut: T-elim ⊢ (T ∧ p) = p",
  Module[{tm, th},
    tm = ptParse["(T ∧ p) = p"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "T ∧ p = p"];
  ]];

HOLTest`runTests["propTaut: F-or ⊢ (F ∨ p) = p",
  Module[{tm, th},
    tm = ptParse["(F ∨ p) = p"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "F ∨ p = p"];
  ]];

HOLTest`runTests["propTaut: closed ⊢ ¬T = F",
  Module[{tm, th},
    tm = ptParse["¬T = F"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "¬T = F"];
    HOLTest`assertEq[hyp[th], {}, "closed, no hyps"];
  ]];

HOLTest`runTests["propTaut: contrapositive ⊢ (p ⇒ q) = (¬q ⇒ ¬p)",
  Module[{tm, th},
    tm = ptParse["(p ⇒ q) = (¬q ⇒ ¬p)"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "contrapositive"];
  ]];

HOLTest`runTests["propTaut: Peirce's law ⊢ ((p ⇒ q) ⇒ p) ⇒ p",
  Module[{tm, th},
    tm = ptParse["((p ⇒ q) ⇒ p) ⇒ p"];
    th = HOL`Auto`PropTaut`propTaut[tm];
    HOLTest`assertEq[aconv[concl[th], tm], True, "Peirce"];
  ]];

HOLTest`runTests["propTaut: rejects non-tautology p = q",
  Module[{tm},
    tm = ptParse["p = q"];
    HOLTest`assertThrows[HOL`Auto`PropTaut`propTaut[tm], "propTaut",
      "p = q is not a tautology"];
  ]];

HOLTest`runTests["propTaut: rejects single var p",
  Module[{tm},
    tm = ptParse["p"];
    HOLTest`assertThrows[HOL`Auto`PropTaut`propTaut[tm], "propTaut",
      "lone p is not a tautology"];
  ]];

HOLTest`runTests["propTaut: rejects non-bool argument",
  Module[{x},
    x = mkVar["x", indTy];
    HOLTest`assertThrows[HOL`Auto`PropTaut`propTaut[x], "propTaut",
      "non-bool input rejected"];
  ]];

(* === nnfThm === *)

HOLTest`runTests["nnfThm: literal unchanged",
  Module[{p, th, out},
    p   = boolVar["p"];
    th  = ASSUME[p];
    out = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], p], True, "concl unchanged"];
    HOLTest`assertEq[hyp[out], {p}, "hyp preserved"];
  ]];

HOLTest`runTests["nnfThm: ¬¬p → p",
  Module[{src, expected, th, out},
    src      = ptParse["¬¬p"];
    expected = boolVar["p"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "concl is p"];
    HOLTest`assertEq[hyp[out], {src}, "hyp preserved"];
  ]];

HOLTest`runTests["nnfThm: De Morgan ∧",
  Module[{src, expected, th, out},
    src      = ptParse["¬(p ∧ q)"];
    expected = ptParse["¬p ∨ ¬q"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "concl is ¬p ∨ ¬q"];
  ]];

HOLTest`runTests["nnfThm: De Morgan ∨",
  Module[{src, expected, th, out},
    src      = ptParse["¬(p ∨ q)"];
    expected = ptParse["¬p ∧ ¬q"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "concl is ¬p ∧ ¬q"];
  ]];

HOLTest`runTests["nnfThm: ⇒-elim",
  Module[{src, expected, th, out},
    src      = ptParse["p ⇒ q"];
    expected = ptParse["¬p ∨ q"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "concl is ¬p ∨ q"];
  ]];

HOLTest`runTests["nnfThm: ¬⇒-elim",
  Module[{src, expected, th, out},
    src      = ptParse["¬(p ⇒ q)"];
    expected = ptParse["p ∧ ¬q"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "concl is p ∧ ¬q"];
  ]];

HOLTest`runTests["nnfThm: triple-neg fixpoint",
  Module[{src, expected, th, out},
    src      = ptParse["¬¬¬p"];
    expected = ptParse["¬p"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "concl is ¬p"];
  ]];

HOLTest`runTests["nnfThm: nested ¬((p ⇒ q) ⇒ r)",
  Module[{src, expected, th, out},
    src      = ptParse["¬((p ⇒ q) ⇒ r)"];
    expected = ptParse["(¬p ∨ q) ∧ ¬r"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`nnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True,
      "concl is (¬p ∨ q) ∧ ¬r"];
  ]];

(* === cnfThm === *)

HOLTest`runTests["cnfThm: literal unchanged",
  Module[{src, th, out},
    src = ptParse["p ∨ q"];
    th  = ASSUME[src];
    out = HOL`Auto`PropTaut`cnfThm[th];
    HOLTest`assertEq[aconv[concl[out], src], True, "p ∨ q already CNF"];
  ]];

HOLTest`runTests["cnfThm: distribute right",
  Module[{src, expected, th, out},
    src      = ptParse["p ∨ (q ∧ r)"];
    expected = ptParse["(p ∨ q) ∧ (p ∨ r)"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`cnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "right distrib"];
  ]];

HOLTest`runTests["cnfThm: distribute left",
  Module[{src, expected, th, out},
    src      = ptParse["(p ∧ q) ∨ r"];
    expected = ptParse["(p ∨ r) ∧ (q ∨ r)"];
    th       = ASSUME[src];
    out      = HOL`Auto`PropTaut`cnfThm[th];
    HOLTest`assertEq[aconv[concl[out], expected], True, "left distrib"];
  ]];

(* === splitConjThm === *)

HOLTest`runTests["splitConjThm: non-∧ singleton",
  Module[{p, th, out},
    p   = boolVar["p"];
    th  = ASSUME[p];
    out = HOL`Auto`PropTaut`splitConjThm[th];
    HOLTest`assertEq[Length[out], 1, "single thm out"];
    HOLTest`assertEq[aconv[concl[out[[1]]], p], True, "thm is p"];
  ]];

HOLTest`runTests["splitConjThm: 2-conj",
  Module[{p, q, th, out},
    p   = boolVar["p"]; q = boolVar["q"];
    th  = HOL`Bool`CONJ[ASSUME[p], ASSUME[q]];
    out = HOL`Auto`PropTaut`splitConjThm[th];
    HOLTest`assertEq[Length[out], 2, "two thms"];
    HOLTest`assertEq[aconv[concl[out[[1]]], p], True, "first is p"];
    HOLTest`assertEq[aconv[concl[out[[2]]], q], True, "second is q"];
  ]];

HOLTest`runTests["splitConjThm: 4-conj",
  Module[{p, q, r, s, conj, out},
    p = boolVar["p"]; q = boolVar["q"];
    r = boolVar["r"]; s = boolVar["s"];
    conj = HOL`Bool`CONJ[
      HOL`Bool`CONJ[ASSUME[p], ASSUME[q]],
      HOL`Bool`CONJ[ASSUME[r], ASSUME[s]]];
    out = HOL`Auto`PropTaut`splitConjThm[conj];
    HOLTest`assertEq[Length[out], 4, "four leaf thms"];
    HOLTest`assertEq[aconv[concl[out[[1]]], p], True, "1st p"];
    HOLTest`assertEq[aconv[concl[out[[4]]], s], True, "4th s"];
  ]];

(* === clausifyPropThm === *)

HOLTest`runTests["clausifyPropThm: ¬(p ⇒ q) → {p, ¬q}",
  Module[{src, th, out, c1, c2},
    src = ptParse["¬(p ⇒ q)"];
    th  = ASSUME[src];
    out = HOL`Auto`PropTaut`clausifyPropThm[th];
    HOLTest`assertEq[Length[out], 2, "two clauses"];
    c1 = boolVar["p"]; c2 = ptParse["¬q"];
    HOLTest`assertEq[aconv[concl[out[[1]]], c1], True, "1st is p"];
    HOLTest`assertEq[aconv[concl[out[[2]]], c2], True, "2nd is ¬q"];
  ]];

HOLTest`runTests["clausifyPropThm: (p ⇒ q) ∧ (q ⇒ r) → 2 clauses",
  Module[{src, th, out, expC1, expC2},
    src = ptParse["(p ⇒ q) ∧ (q ⇒ r)"];
    th  = ASSUME[src];
    out = HOL`Auto`PropTaut`clausifyPropThm[th];
    HOLTest`assertEq[Length[out], 2, "two clauses"];
    expC1 = ptParse["¬p ∨ q"]; expC2 = ptParse["¬q ∨ r"];
    HOLTest`assertEq[aconv[concl[out[[1]]], expC1], True, "clause 1"];
    HOLTest`assertEq[aconv[concl[out[[2]]], expC2], True, "clause 2"];
  ]];

HOLTest`runTests["clausifyPropThm: tautology ¬(p ∧ ¬p) → {¬p ∨ p}",
  Module[{th, out, expected},
    th  = HOL`Auto`PropTaut`propTaut[ptParse["¬(p ∧ ¬p)"]];
    out = HOL`Auto`PropTaut`clausifyPropThm[th];
    HOLTest`assertEq[Length[out], 1, "single clause"];
    expected = ptParse["¬p ∨ p"];
    HOLTest`assertEq[aconv[concl[out[[1]]], expected], True,
      "concl is ¬p ∨ p"];
    HOLTest`assertEq[hyp[out[[1]]], {}, "no hyps"];
  ]];

(* === clausifyContrapositives === *)

HOLTest`runTests["clausifyContrapositives: 1-clause p (unit)",
  Module[{p, th, contras},
    p       = boolVar["p"];
    th      = ASSUME[p];
    contras = HOL`Auto`PropTaut`clausifyContrapositives[th];
    HOLTest`assertEq[Length[contras], 1, "one rule"];
    HOLTest`assertEq[aconv[concl[contras[[1]]], p], True,
      "rule = clause itself"];
    HOLTest`assertEq[hyp[contras[[1]]], {p}, "hyp preserved"];
  ]];

HOLTest`runTests["clausifyContrapositives: 2-clause p ∨ q",
  Module[{src, th, contras, e1, e2},
    src     = ptParse["p ∨ q"];
    th      = ASSUME[src];
    contras = HOL`Auto`PropTaut`clausifyContrapositives[th];
    HOLTest`assertEq[Length[contras], 2, "two rules"];
    e1 = ptParse["¬q ⇒ p"];
    e2 = ptParse["¬p ⇒ q"];
    HOLTest`assertEq[aconv[concl[contras[[1]]], e1], True, "pivot 1: ¬q ⇒ p"];
    HOLTest`assertEq[aconv[concl[contras[[2]]], e2], True, "pivot 2: ¬p ⇒ q"];
    HOLTest`assertEq[hyp[contras[[1]]], {src}, "pivot 1 hyp"];
    HOLTest`assertEq[hyp[contras[[2]]], {src}, "pivot 2 hyp"];
  ]];

HOLTest`runTests["clausifyContrapositives: 3-clause p ∨ q ∨ r",
  Module[{src, th, contras, e1, e2, e3},
    src     = ptParse["p ∨ q ∨ r"];
    th      = ASSUME[src];
    contras = HOL`Auto`PropTaut`clausifyContrapositives[th];
    HOLTest`assertEq[Length[contras], 3, "three rules"];
    e1 = ptParse["¬q ⇒ ¬r ⇒ p"];
    e2 = ptParse["¬p ⇒ ¬r ⇒ q"];
    e3 = ptParse["¬p ⇒ ¬q ⇒ r"];
    HOLTest`assertEq[aconv[concl[contras[[1]]], e1], True, "pivot 1"];
    HOLTest`assertEq[aconv[concl[contras[[2]]], e2], True, "pivot 2"];
    HOLTest`assertEq[aconv[concl[contras[[3]]], e3], True, "pivot 3"];
  ]];

HOLTest`runTests["clausifyContrapositives: ¬p ∨ q (polarity flip)",
  Module[{src, th, contras, e1, e2},
    src     = ptParse["¬p ∨ q"];
    th      = ASSUME[src];
    contras = HOL`Auto`PropTaut`clausifyContrapositives[th];
    HOLTest`assertEq[Length[contras], 2, "two rules"];
    (* pivot 1 (¬p): negate q = ¬q; conclude ¬p *)
    e1 = ptParse["¬q ⇒ ¬p"];
    HOLTest`assertEq[aconv[concl[contras[[1]]], e1], True, "pivot 1 = ¬q ⇒ ¬p"];
    (* pivot 2 (q): negate ¬p = p; conclude q *)
    e2 = ptParse["p ⇒ q"];
    HOLTest`assertEq[aconv[concl[contras[[2]]], e2], True, "pivot 2 = p ⇒ q"];
  ]];

HOLTest`runTests["clausifyContrapositives: ¬p ∨ ¬q ∨ r (mixed polarity)",
  Module[{src, th, contras, e1, e2, e3},
    src     = ptParse["¬p ∨ ¬q ∨ r"];
    th      = ASSUME[src];
    contras = HOL`Auto`PropTaut`clausifyContrapositives[th];
    HOLTest`assertEq[Length[contras], 3, "three rules"];
    (* pivot 1 (¬p): ¬(¬q)=q, ¬r; conclude ¬p ⇒ q ⇒ ¬r ⇒ ¬p *)
    e1 = ptParse["q ⇒ ¬r ⇒ ¬p"];
    HOLTest`assertEq[aconv[concl[contras[[1]]], e1], True, "pivot 1"];
    (* pivot 2 (¬q): ¬(¬p)=p, ¬r; conclude ¬q ⇒ p ⇒ ¬r ⇒ ¬q *)
    e2 = ptParse["p ⇒ ¬r ⇒ ¬q"];
    HOLTest`assertEq[aconv[concl[contras[[2]]], e2], True, "pivot 2"];
    (* pivot 3 (r): ¬(¬p)=p, ¬(¬q)=q; p ⇒ q ⇒ r *)
    e3 = ptParse["p ⇒ q ⇒ r"];
    HOLTest`assertEq[aconv[concl[contras[[3]]], e3], True, "pivot 3"];
  ]];

HOLTest`runTests["clausifyContrapositives: full pipeline (p⇒q)∧(q⇒r) clause 1",
  Module[{src, th, clauses, contras, e1, e2},
    src     = ptParse["(p ⇒ q) ∧ (q ⇒ r)"];
    th      = ASSUME[src];
    clauses = HOL`Auto`PropTaut`clausifyPropThm[th];
    (* clauses[[1]] is ⊢ ¬p ∨ q *)
    contras = HOL`Auto`PropTaut`clausifyContrapositives[clauses[[1]]];
    HOLTest`assertEq[Length[contras], 2, "two rules from ¬p ∨ q"];
    e1 = ptParse["¬q ⇒ ¬p"];
    e2 = ptParse["p ⇒ q"];
    HOLTest`assertEq[aconv[concl[contras[[1]]], e1], True, "pivot 1"];
    HOLTest`assertEq[aconv[concl[contras[[2]]], e2], True, "pivot 2"];
    HOLTest`assertEq[hyp[contras[[1]]], {src}, "hyp = src"];
  ]];
