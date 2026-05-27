(* ::Package:: *)

(* Tests for M7-δ auto/Arith.wl session 1: linTerm AST + parseLin /
   buildLin round-trips. The decision-procedure layer is still a
   stub; these tests exercise only the AST infrastructure. *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Stdlib`Num`"];
Needs["HOL`Auto`Arith`"];

numTy = mkType["num", {}];

parseLin = HOL`Auto`Arith`Private`parseLin;
buildLin = HOL`Auto`Arith`Private`buildLin;
buildLitNum = HOL`Auto`Arith`Private`buildLitNum;
linTerm = HOL`Auto`Arith`Private`linTerm;
linAdd = HOL`Auto`Arith`Private`linAdd;
linScale = HOL`Auto`Arith`Private`linScale;
linZero = HOL`Auto`Arith`Private`linZero;
linConst = HOL`Auto`Arith`Private`linConst;
linVar = HOL`Auto`Arith`Private`linVar;

mkNum[n_Integer] := buildLitNum[n];
mkPlus[a_, b_] :=
  mkComb[mkComb[plusConst[], a], b];
mkTimes[a_, b_] :=
  mkComb[mkComb[timesConst[], a], b];

(* ===== parseLin: HOL ℕ term → linTerm ===== *)

HOLTest`runTests["arith: parseLin on literal 0",
  HOLTest`assertEq[parseLin[zeroConst[]], linTerm[0, <||>],
    "parseLin[0] = linTerm[0, <||>]"]];

HOLTest`runTests["arith: parseLin on literal SUC^3 0 = 3",
  HOLTest`assertEq[parseLin[mkNum[3]], linTerm[3, <||>],
    "parseLin[SUC SUC SUC 0] = linTerm[3, <||>]"]];

HOLTest`runTests["arith: parseLin on a single free variable",
  HOLTest`assertEq[parseLin[mkVar["x", numTy]],
    linTerm[0, <|"x" -> 1|>], "parseLin[x] = 1·x"]];

HOLTest`runTests["arith: parseLin on x + y",
  Module[{xV, yV},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    HOLTest`assertEq[parseLin[mkPlus[xV, yV]],
      linTerm[0, <|"x" -> 1, "y" -> 1|>],
      "x + y"]
  ]];

HOLTest`runTests["arith: parseLin merges x + (2 + x) = 2 + 2x",
  Module[{xV},
    xV = mkVar["x", numTy];
    HOLTest`assertEq[
      parseLin[mkPlus[xV, mkPlus[mkNum[2], xV]]],
      linTerm[2, <|"x" -> 2|>],
      "x + (2 + x)"]
  ]];

HOLTest`runTests["arith: parseLin handles 3 * x via constant scaling",
  Module[{xV},
    xV = mkVar["x", numTy];
    HOLTest`assertEq[parseLin[mkTimes[mkNum[3], xV]],
      linTerm[0, <|"x" -> 3|>], "3 * x = 3·x"]
  ]];

HOLTest`runTests["arith: parseLin handles x * 3 (scalar on the right)",
  Module[{xV},
    xV = mkVar["x", numTy];
    HOLTest`assertEq[parseLin[mkTimes[xV, mkNum[3]]],
      linTerm[0, <|"x" -> 3|>], "x * 3 = 3·x"]
  ]];

HOLTest`runTests["arith: parseLin on the mixed expression 2 + 3*x + y",
  Module[{xV, yV},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    HOLTest`assertEq[
      parseLin[mkPlus[mkNum[2], mkPlus[mkTimes[mkNum[3], xV], yV]]],
      linTerm[2, <|"x" -> 3, "y" -> 1|>], "2 + 3·x + y"]
  ]];

HOLTest`runTests["arith: parseLin rejects product of two variables",
  Module[{xV, yV},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    HOLTest`assertThrows[parseLin[mkTimes[xV, yV]], "arith-parse",
      "non-linear product is rejected"]
  ]];

(* ===== buildLin: linTerm → canonical HOL ℕ term ===== *)

HOLTest`runTests["arith: buildLin renders zero linTerm as bare 0",
  HOLTest`assertEq[buildLin[linZero[]], zeroConst[], "buildLin[0] = 0"]];

HOLTest`runTests["arith: buildLin renders a pure literal constant",
  HOLTest`assertEq[buildLin[linConst[5]], mkNum[5],
    "buildLin[5] = SUC^5 0"]];

HOLTest`runTests["arith: buildLin on a single var (coef 1) drops the * step",
  HOLTest`assertEq[buildLin[linVar["x"]], mkVar["x", numTy],
    "buildLin[1·x] = x (no `1*' wrapper)"]];

HOLTest`runTests["arith: buildLin uses c*x form when coef > 1",
  Module[{xV},
    xV = mkVar["x", numTy];
    HOLTest`assertEq[buildLin[linTerm[0, <|"x" -> 3|>]],
      mkTimes[mkNum[3], xV], "buildLin[3·x] = 3 * x"]
  ]];

HOLTest`runTests["arith: buildLin puts constants first, then sorted vars",
  Module[{xV, yV, expected},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    (* 2 + x + 3·y *)
    expected = mkPlus[mkNum[2], mkPlus[xV, mkTimes[mkNum[3], yV]]];
    HOLTest`assertEq[
      buildLin[linTerm[2, <|"y" -> 3, "x" -> 1|>]],
      expected, "buildLin[2 + 1·x + 3·y] is sorted with constant first"]
  ]];

(* ===== round-trips: parseLin ∘ buildLin = id (on linTerms);    *)
(*       parseLin ∘ buildLin ∘ parseLin = parseLin (on HOL terms) *)

HOLTest`runTests["arith: round-trip linTerm → HOL → linTerm preserves AST",
  Module[{cases},
    cases = {
      linZero[],
      linConst[7],
      linVar["x"],
      linTerm[0, <|"x" -> 1, "y" -> 1|>],
      linTerm[2, <|"x" -> 3|>],
      linTerm[0, <|"a" -> 2, "b" -> 5, "c" -> 1|>],
      linTerm[10, <|"x" -> 4, "y" -> 7|>]
    };
    Scan[Function[lt,
      HOLTest`assertEq[parseLin[buildLin[lt]], lt,
        "round-trip for " <> ToString[lt]]
    ], cases]
  ]];

HOLTest`runTests["arith: linAdd accumulates coefficients and drops zeros",
  HOLTest`assertEq[
    linAdd[linTerm[1, <|"x" -> 2|>], linTerm[3, <|"x" -> -2, "y" -> 1|>]],
    linTerm[4, <|"y" -> 1|>],
    "1+2x ⊕ 3-2x+y = 4 + y"]];

HOLTest`runTests["arith: linScale by 0 collapses to zero",
  HOLTest`assertEq[
    linScale[0, linTerm[5, <|"x" -> 3, "y" -> 1|>]],
    linZero[], "0 * anything = 0"]];

HOLTest`runTests["arith: linScale by 2 doubles everything",
  HOLTest`assertEq[
    linScale[2, linTerm[3, <|"x" -> 1, "y" -> 2|>]],
    linTerm[6, <|"x" -> 2, "y" -> 4|>],
    "2 * (3 + x + 2y) = 6 + 2x + 4y"]];

(* ===== stub behavior ===== *)

HOLTest`runTests["arith: arithProve throws holError tagged arith-stub",
  HOLTest`assertThrows[
    arithProve[mkEq[mkVar["x", numTy], mkVar["x", numTy]]],
    "arith-stub", "stub still firing"]];

(* ===== Session 2: Atom / Formula AST + parse / build / NNF ===== *)

parseAtom = HOL`Auto`Arith`Private`parseAtom;
buildAtom = HOL`Auto`Arith`Private`buildAtom;
parseForm = HOL`Auto`Arith`Private`parseForm;
buildForm = HOL`Auto`Arith`Private`buildForm;
nnfForm = HOL`Auto`Arith`Private`nnfForm;
nnfFormQ = HOL`Auto`Arith`Private`nnfFormQ;

aAtomEq = HOL`Auto`Arith`Private`aAtomEq;
aAtomLeq = HOL`Auto`Arith`Private`aAtomLeq;
aAtomLt = HOL`Auto`Arith`Private`aAtomLt;
aAtomDivides = HOL`Auto`Arith`Private`aAtomDivides;
aFormTrue = HOL`Auto`Arith`Private`aFormTrue;
aFormFalse = HOL`Auto`Arith`Private`aFormFalse;
aFormAtom = HOL`Auto`Arith`Private`aFormAtom;
aFormNot = HOL`Auto`Arith`Private`aFormNot;
aFormAnd = HOL`Auto`Arith`Private`aFormAnd;
aFormOr = HOL`Auto`Arith`Private`aFormOr;
aFormImp = HOL`Auto`Arith`Private`aFormImp;
aFormIff = HOL`Auto`Arith`Private`aFormIff;
aFormForall = HOL`Auto`Arith`Private`aFormForall;
aFormExists = HOL`Auto`Arith`Private`aFormExists;

trueTm[] := mkConst["T", boolTy];
falseTm[] := mkConst["F", boolTy];
andCT[a_, b_] :=
  mkComb[mkComb[mkConst["\[And]", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
orCT[a_, b_] :=
  mkComb[mkComb[mkConst["\[Or]", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
impCT[a_, b_] :=
  mkComb[mkComb[mkConst["\[DoubleRightArrow]", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];
notCT[a_] := mkComb[mkConst["\[Not]", tyFun[boolTy, boolTy]], a];
forallNum[v_, body_] :=
  mkComb[mkConst["\[ForAll]", tyFun[tyFun[numTy, boolTy], boolTy]],
    mkAbs[v, body]];
existsNum[v_, body_] :=
  mkComb[mkConst["\[Exists]", tyFun[tyFun[numTy, boolTy], boolTy]],
    mkAbs[v, body]];
leqTm[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
ltTm[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`ltConst[], a], b];
divTm[c_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], c], b];

(* ----- parseAtom ----- *)

HOLTest`runTests["arith: parseAtom on x = y",
  Module[{xV, yV},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    HOLTest`assertEq[parseAtom[mkEq[xV, yV]],
      aAtomEq[HOL`Auto`Arith`Private`linVar["x"],
              HOL`Auto`Arith`Private`linVar["y"]],
      "x = y"]
  ]];

HOLTest`runTests["arith: parseAtom on x ≤ y + 1",
  Module[{xV, yV},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    HOLTest`assertEq[parseAtom[leqTm[xV, mkPlus[yV, mkNum[1]]]],
      aAtomLeq[HOL`Auto`Arith`Private`linVar["x"],
        HOL`Auto`Arith`Private`linTerm[1, <|"y" -> 1|>]],
      "x ≤ y + 1"]
  ]];

HOLTest`runTests["arith: parseAtom on x < y",
  Module[{xV, yV},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    HOLTest`assertEq[parseAtom[ltTm[xV, yV]],
      aAtomLt[HOL`Auto`Arith`Private`linVar["x"],
              HOL`Auto`Arith`Private`linVar["y"]],
      "x < y"]
  ]];

HOLTest`runTests["arith: parseAtom on divides 3 x",
  Module[{xV},
    xV = mkVar["x", numTy];
    HOLTest`assertEq[parseAtom[divTm[mkNum[3], xV]],
      aAtomDivides[3, HOL`Auto`Arith`Private`linVar["x"]],
      "divides 3 x"]
  ]];

(* ----- parseForm ----- *)

HOLTest`runTests["arith: parseForm on T",
  HOLTest`assertEq[parseForm[trueTm[]], aFormTrue, "T"]];

HOLTest`runTests["arith: parseForm on F",
  HOLTest`assertEq[parseForm[falseTm[]], aFormFalse, "F"]];

HOLTest`runTests["arith: parseForm on ¬ T",
  HOLTest`assertEq[parseForm[notCT[trueTm[]]],
    aFormNot[aFormTrue], "¬ T"]];

HOLTest`runTests["arith: parseForm on T ∧ F",
  HOLTest`assertEq[parseForm[andCT[trueTm[], falseTm[]]],
    aFormAnd[aFormTrue, aFormFalse], "T ∧ F"]];

HOLTest`runTests["arith: parseForm on T ⇒ F",
  HOLTest`assertEq[parseForm[impCT[trueTm[], falseTm[]]],
    aFormImp[aFormTrue, aFormFalse], "T ⇒ F"]];

HOLTest`runTests["arith: parseForm on T = T routes to iff (bool =)",
  HOLTest`assertEq[parseForm[mkEq[trueTm[], trueTm[]]],
    aFormIff[aFormTrue, aFormTrue], "T = T → aFormIff"]];

HOLTest`runTests["arith: parseForm on ∀x. x = x",
  Module[{xV, t, expected},
    xV = mkVar["x", numTy];
    t = forallNum[xV, mkEq[xV, xV]];
    expected = aFormForall["x",
      aFormAtom[aAtomEq[HOL`Auto`Arith`Private`linVar["x"],
        HOL`Auto`Arith`Private`linVar["x"]]]];
    HOLTest`assertEq[parseForm[t], expected, "∀x. x = x"]
  ]];

HOLTest`runTests["arith: parseForm on ∀x. ∃y. x ≤ y",
  Module[{xV, yV, t, expected},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    t = forallNum[xV, existsNum[yV, leqTm[xV, yV]]];
    expected = aFormForall["x", aFormExists["y",
      aFormAtom[aAtomLeq[HOL`Auto`Arith`Private`linVar["x"],
        HOL`Auto`Arith`Private`linVar["y"]]]]];
    HOLTest`assertEq[parseForm[t], expected, "∀x. ∃y. x ≤ y"]
  ]];

HOLTest`runTests["arith: parseForm fresh-renames nested same-named binders",
  Module[{xV, t, parsed},
    xV = mkVar["x", numTy];
    t = forallNum[xV, forallNum[xV, mkEq[xV, xV]]];
    parsed = parseForm[t];
    HOLTest`assertEq[parsed,
      aFormForall["x", aFormForall["x1",
        aFormAtom[aAtomEq[HOL`Auto`Arith`Private`linVar["x1"],
          HOL`Auto`Arith`Private`linVar["x1"]]]]],
      "inner ∀x renamed to x1 because outer x is already bound"]
  ]];

(* ----- buildForm + round-trips ----- *)

HOLTest`runTests["arith: build ∘ parse is aconv-id on ∀x. x = x",
  Module[{xV, t},
    xV = mkVar["x", numTy];
    t = forallNum[xV, mkEq[xV, xV]];
    HOLTest`assertTrue[HOL`Terms`aconv[buildForm[parseForm[t]], t],
      "build ∘ parse aconv-id"]
  ]];

HOLTest`runTests["arith: build ∘ parse preserves aconv on ∀x. ∀x. x = x",
  Module[{xV, t},
    xV = mkVar["x", numTy];
    t = forallNum[xV, forallNum[xV, mkEq[xV, xV]]];
    HOLTest`assertTrue[HOL`Terms`aconv[buildForm[parseForm[t]], t],
      "build ∘ parse aconv-id even with nested same-named binder"]
  ]];

HOLTest`runTests["arith: build ∘ parse round-trips a mixed formula",
  Module[{xV, yV, t},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    (* ∀x. ∃y. (x ≤ y) ∧ ¬(x = y) *)
    t = forallNum[xV, existsNum[yV,
      andCT[leqTm[xV, yV], notCT[mkEq[xV, yV]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[buildForm[parseForm[t]], t],
      "round-trip preserves α-equivalence"]
  ]];

(* ----- nnfForm ----- *)

HOLTest`runTests["arith: nnfForm strips double negation",
  HOLTest`assertEq[
    nnfForm[aFormNot[aFormNot[aFormTrue]]], aFormTrue,
    "¬¬T → T"]];

HOLTest`runTests["arith: nnfForm pushes ¬ through ∧",
  HOLTest`assertEq[
    nnfForm[aFormNot[aFormAnd[aFormTrue, aFormFalse]]],
    aFormOr[aFormFalse, aFormTrue],
    "¬(T ∧ F) → ¬T ∨ ¬F → F ∨ T"]];

HOLTest`runTests["arith: nnfForm expands ⇒",
  HOLTest`assertEq[
    nnfForm[aFormImp[aFormTrue, aFormFalse]],
    aFormOr[aFormFalse, aFormFalse],
    "T ⇒ F → ¬T ∨ F → F ∨ F"]];

HOLTest`runTests["arith: nnfForm pushes ¬ through ∀",
  Module[{atom},
    atom = aFormAtom[aAtomEq[HOL`Auto`Arith`Private`linVar["x"],
      HOL`Auto`Arith`Private`linVar["x"]]];
    HOLTest`assertEq[
      nnfForm[aFormNot[aFormForall["x", atom]]],
      aFormExists["x", aFormNot[atom]],
      "¬(∀x. P) → ∃x. ¬P"]
  ]];

HOLTest`runTests["arith: nnfForm is idempotent on already-NNF input",
  Module[{atom1, atom2, input},
    atom1 = aFormAtom[aAtomEq[HOL`Auto`Arith`Private`linVar["x"],
      HOL`Auto`Arith`Private`linVar["x"]]];
    atom2 = aFormAtom[aAtomLeq[HOL`Auto`Arith`Private`linVar["x"],
      HOL`Auto`Arith`Private`linVar["y"]]];
    input = aFormForall["x", aFormExists["y",
      aFormAnd[atom2, aFormNot[atom1]]]];
    HOLTest`assertEq[nnfForm[input], input,
      "nnf is identity on NNF input"]
  ]];

HOLTest`runTests["arith: nnfForm output is always in NNF (nnfFormQ predicate)",
  Module[{cases},
    cases = {
      aFormNot[aFormAnd[aFormTrue, aFormFalse]],
      aFormImp[aFormTrue, aFormFalse],
      aFormIff[aFormTrue, aFormFalse],
      aFormNot[aFormForall["x",
        aFormImp[aFormAtom[aAtomLeq[
          HOL`Auto`Arith`Private`linVar["x"],
          HOL`Auto`Arith`Private`linVar["y"]]],
          aFormFalse]]]
    };
    Scan[Function[f,
      HOLTest`assertTrue[nnfFormQ[nnfForm[f]],
        "nnfFormQ holds on nnfForm[" <> ToString[f] <> "]"]
    ], cases]
  ]];

(* ===== Session 3: nnfConv — propositional NNF certificate ===== *)

nnfConv = HOL`Auto`Arith`nnfConv;

(* Verify the theorem is well-formed and its LHS matches the input  *)
(* term. The RHS shape is checked separately per case.               *)
isEqThmFromTo[th_, lhsTm_, rhsTm_] :=
  hyp[th] === {} &&
  concl[th] === mkEq[lhsTm, rhsTm];

HOLTest`runTests["arith: nnfConv on T returns ⊢ T = T (REFL)",
  Module[{th},
    th = nnfConv[trueTm[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], mkEq[trueTm[], trueTm[]],
      "⊢ T = T"]
  ]];

eqLhsOf[th_] := concl[th][[1, 2]];
eqRhsOf[th_] := concl[th][[2]];

HOLTest`runTests["arith: nnfConv on ¬¬T returns ⊢ ¬¬T = T",
  Module[{th, p, q},
    th = nnfConv[notCT[notCT[trueTm[]]]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqLhsOf[th], notCT[notCT[trueTm[]]],
      "LHS is ¬¬T"];
    HOLTest`assertEq[eqRhsOf[th], trueTm[], "RHS is T"]
  ]];

HOLTest`runTests["arith: nnfConv on ¬(p ∧ q) returns ¬p ∨ ¬q",
  Module[{th, p, q},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    th = nnfConv[notCT[andCT[p, q]]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqLhsOf[th], notCT[andCT[p, q]], "LHS"];
    HOLTest`assertEq[eqRhsOf[th], orCT[notCT[p], notCT[q]],
      "RHS = ¬p ∨ ¬q"]
  ]];

HOLTest`runTests["arith: nnfConv on p ⇒ q returns ¬p ∨ q",
  Module[{th, p, q},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    th = nnfConv[impCT[p, q]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqRhsOf[th], orCT[notCT[p], q],
      "RHS = ¬p ∨ q"]
  ]];

HOLTest`runTests["arith: nnfConv on ¬(¬p ∧ q) — multi-step fixpoint",
  Module[{th, p, q},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    th = nnfConv[notCT[andCT[notCT[p], q]]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    (* Should reduce ¬(¬p ∧ q) → ¬¬p ∨ ¬q → p ∨ ¬q *)
    HOLTest`assertEq[eqRhsOf[th], orCT[p, notCT[q]],
      "RHS = p ∨ ¬q after multi-step fixpoint"]
  ]];

HOLTest`runTests["arith: nnfConv on (p ⇔ q) returns (p∧q) ∨ (¬p∧¬q)",
  Module[{th, p, q},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    th = nnfConv[mkEq[p, q]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqRhsOf[th],
      orCT[andCT[p, q], andCT[notCT[p], notCT[q]]],
      "RHS = (p ∧ q) ∨ (¬p ∧ ¬q)"]
  ]];

HOLTest`runTests["arith: nnfConv on ¬(p ⇔ q) — bottom-up: inner ⇔ rewrites first, then ¬ De Morgans",
  Module[{th, p, q, expectedRhs},
    p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
    th = nnfConv[notCT[mkEq[p, q]]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    (* DEPTHCONV rewrites the inner `p = q` to `(p ∧ q) ∨ (¬p ∧ ¬q)` *)
    (* first, then ¬(…) deMorgans to (¬(p ∧ q)) ∧ (¬(¬p ∧ ¬q)), which *)
    (* further reduces to (¬p ∨ ¬q) ∧ (p ∨ q). Different from AST-       *)
    (* level nnfForm's DNF iff form but still in NNF.                    *)
    expectedRhs = andCT[
      orCT[notCT[p], notCT[q]],
      orCT[p, q]];
    HOLTest`assertEq[eqRhsOf[th], expectedRhs,
      "RHS = (¬p ∨ ¬q) ∧ (p ∨ q) — CNF-style ¬iff"]
  ]];

HOLTest`runTests["arith: nnfConv descends under ∀ (pass-through body)",
  Module[{xV, p, body, th, expectedBody},
    xV = mkVar["x", numTy];
    p = mkVar["p", boolTy];
    (* ∀x:num. ¬¬p — bound `x` unused, inner body has propositional ¬¬p. *)
    body = forallNum[xV, notCT[notCT[p]]];
    th = nnfConv[body];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    expectedBody = forallNum[xV, p];
    HOLTest`assertTrue[
      HOL`Terms`aconv[eqRhsOf[th], expectedBody],
      "RHS aconv ∀x. p (inner ¬¬ stripped under ∀)"]
  ]];

(* ===== Session 4: quantifier deMorgan ===== *)

HOLTest`runTests["arith: notExistsNumThm — ⊢ ∀P. ¬(∃x. P x) = ∀x. ¬P x",
  Module[{th, c},
    th = HOL`Auto`Arith`notExistsNumThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["=", _],
          comb[const["¬", _], comb[const["∃", _], _]]],
          comb[const["∀", _], _]], _]]],
      "shape: ∀P. ¬(∃…) = ∀(¬…)"]
  ]];

HOLTest`runTests["arith: notForallNumThm — ⊢ ∀P. ¬(∀x. P x) = ∃x. ¬P x",
  Module[{th, c},
    th = HOL`Auto`Arith`notForallNumThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[bvar[0, _],
        comb[comb[const["=", _],
          comb[const["¬", _], comb[const["∀", _], _]]],
          comb[const["∃", _], _]], _]]],
      "shape: ∀P. ¬(∀…) = ∃(¬…)"]
  ]];

HOLTest`runTests["arith: nnfConv on ¬(∀x:num. x = x) — pushes ¬ inside ∀",
  Module[{xV, t, th, rhs, expected},
    xV = mkVar["x", numTy];
    t = notCT[forallNum[xV, mkEq[xV, xV]]];
    th = nnfConv[t];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqLhsOf[th], t, "LHS preserved"];
    (* RHS: ∃y:num. ¬(y = y) (binder name from the theorem's proof). *)
    expected = existsNum[xV, notCT[mkEq[xV, xV]]];
    HOLTest`assertTrue[HOL`Terms`aconv[eqRhsOf[th], expected],
      "RHS aconv ∃x. ¬(x = x)"]
  ]];

HOLTest`runTests["arith: nnfConv on ¬(∃x:num. x ≤ 0) — pushes ¬ inside ∃",
  Module[{xV, t, th, expected, leqZ},
    xV = mkVar["x", numTy];
    leqZ = mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV],
      HOL`Stdlib`Num`zeroConst[]];
    t = notCT[existsNum[xV, leqZ]];
    th = nnfConv[t];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqLhsOf[th], t, "LHS preserved"];
    expected = forallNum[xV, notCT[leqZ]];
    HOLTest`assertTrue[HOL`Terms`aconv[eqRhsOf[th], expected],
      "RHS aconv ∀x. ¬(x ≤ 0)"]
  ]];

HOLTest`runTests["arith: nnfConv on ¬(∀x. ∃y. x ≤ y) — nested quantifier deMorgan",
  Module[{xV, yV, leqXY, inner, t, th, expected},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    leqXY = mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV], yV];
    inner = existsNum[yV, leqXY];
    t = notCT[forallNum[xV, inner]];
    th = nnfConv[t];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqLhsOf[th], t, "LHS preserved"];
    (* Expected after NNF: ∃x. ∀y. ¬(x ≤ y) *)
    expected = existsNum[xV, forallNum[yV, notCT[leqXY]]];
    HOLTest`assertTrue[HOL`Terms`aconv[eqRhsOf[th], expected],
      "RHS aconv ∃x. ∀y. ¬(x ≤ y)"]
  ]];

HOLTest`runTests["arith: nnfConv on ¬(p ⇒ (∀x:num. x ≤ y)) — mixed prop + quantifier",
  Module[{xV, yV, p, leqXY, inner, t, th, expected},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    p = mkVar["pq", boolTy];
    leqXY = mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV], yV];
    inner = forallNum[xV, leqXY];
    t = notCT[impCT[p, inner]];
    th = nnfConv[t];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[eqLhsOf[th], t, "LHS preserved"];
    (* Expected: ¬(p ⇒ ∀x. x ≤ y) → p ∧ ¬(∀x. x ≤ y) → p ∧ ∃x. ¬(x ≤ y) *)
    expected = andCT[p, existsNum[xV, notCT[leqXY]]];
    HOLTest`assertTrue[HOL`Terms`aconv[eqRhsOf[th], expected],
      "RHS aconv p ∧ ∃x. ¬(x ≤ y)"]
  ]];

(* ===== Session 5: Cooper QE building blocks (AST-level) ===== *)

normalizeAtom = HOL`Auto`Arith`Private`normalizeAtom;
normalizeAtomsForm = HOL`Auto`Arith`Private`normalizeAtomsForm;
linCoefOf = HOL`Auto`Arith`Private`linCoefOf;
linSub = HOL`Auto`Arith`Private`linSub;
atomCoefOnX = HOL`Auto`Arith`Private`atomCoefOnX;
formAtomsInvolvingX = HOL`Auto`Arith`Private`formAtomsInvolvingX;
deltaOnX = HOL`Auto`Arith`Private`deltaOnX;
phiMinusInfOnX = HOL`Auto`Arith`Private`phiMinusInfOnX;

HOLTest`runTests["arith: normalizeAtom rewrites x ≤ 5 as (x - 5) ≤ 0",
  HOLTest`assertEq[
    normalizeAtom[aAtomLeq[linVar["x"], HOL`Auto`Arith`Private`linConst[5]]],
    aAtomLeq[linTerm[-5, <|"x" -> 1|>], HOL`Auto`Arith`Private`linZero[]],
    "x ≤ 5  ↦  (x - 5) ≤ 0"]];

HOLTest`runTests["arith: normalizeAtom preserves aAtomDivides",
  Module[{atom},
    atom = aAtomDivides[3, linVar["x"]];
    HOLTest`assertEq[normalizeAtom[atom], atom,
      "divides atoms pass through normalization"]
  ]];

HOLTest`runTests["arith: linCoefOf — present and absent variables",
  Module[{lt},
    lt = linTerm[7, <|"x" -> 3, "y" -> -2|>];
    HOLTest`assertEq[linCoefOf[lt, "x"], 3, "x → 3"];
    HOLTest`assertEq[linCoefOf[lt, "y"], -2, "y → -2"];
    HOLTest`assertEq[linCoefOf[lt, "z"], 0, "absent z → 0"]
  ]];

HOLTest`runTests["arith: atomCoefOnX on each atom flavor",
  Module[{lt},
    lt = linTerm[1, <|"x" -> 4|>];
    HOLTest`assertEq[atomCoefOnX[aAtomEq[lt, HOL`Auto`Arith`Private`linZero[]], "x"],
      4, "Eq: 4"];
    HOLTest`assertEq[atomCoefOnX[aAtomLeq[lt, HOL`Auto`Arith`Private`linZero[]], "x"],
      4, "Leq: 4"];
    HOLTest`assertEq[atomCoefOnX[aAtomLt[lt, HOL`Auto`Arith`Private`linZero[]], "x"],
      4, "Lt: 4"];
    HOLTest`assertEq[atomCoefOnX[aAtomDivides[5, lt], "x"],
      4, "Divides: 4"]
  ]];

HOLTest`runTests["arith: formAtomsInvolvingX flattens & flags negation",
  Module[{ltX, ltY, atomXleq, atomXeq, atomY, form, atoms},
    ltX = linVar["x"];
    ltY = linVar["y"];
    atomXleq = aAtomLeq[ltX, HOL`Auto`Arith`Private`linConst[5]];
    atomXeq = aAtomEq[ltX, HOL`Auto`Arith`Private`linConst[3]];
    atomY = aAtomLeq[ltY, HOL`Auto`Arith`Private`linConst[10]];
    form = aFormAnd[
      aFormAtom[atomXleq],
      aFormAnd[aFormNot[aFormAtom[atomXeq]], aFormAtom[atomY]]];
    atoms = formAtomsInvolvingX[form, "x"];
    HOLTest`assertEq[Length[atoms], 2,
      "two atoms involve x (the y-atom is filtered out)"];
    HOLTest`assertEq[atoms[[1]], {False, atomXleq}, "first: positive x ≤ 5"];
    HOLTest`assertEq[atoms[[2]], {True, atomXeq}, "second: negated x = 3"]
  ]];

HOLTest`runTests["arith: deltaOnX — empty → 1, single → modulus, multiple → LCM",
  Module[{ltX},
    ltX = linVar["x"];
    HOLTest`assertEq[deltaOnX[aFormAtom[aAtomLeq[ltX,
      HOL`Auto`Arith`Private`linConst[5]]], "x"], 1,
      "no divisibility → 1"];
    HOLTest`assertEq[deltaOnX[aFormAtom[aAtomDivides[3, ltX]], "x"], 3,
      "single 3 | x → 3"];
    HOLTest`assertEq[deltaOnX[aFormAnd[
      aFormAtom[aAtomDivides[4, ltX]],
      aFormAtom[aAtomDivides[6, ltX]]], "x"], 12,
      "4 | x ∧ 6 | x → LCM 12"]
  ]];

HOLTest`runTests["arith: deltaOnX ignores divisibility on other variables",
  Module[{ltX, ltY, form},
    ltX = linVar["x"]; ltY = linVar["y"];
    form = aFormAnd[
      aFormAtom[aAtomDivides[5, ltY]],
      aFormAtom[aAtomDivides[7, ltX]]];
    HOLTest`assertEq[deltaOnX[form, "x"], 7,
      "ignore 5 | y when computing δ for x"]
  ]];

HOLTest`runTests["arith: phiMinusInfOnX — x ≤ 5 (coef +1) → T",
  Module[{ltX, normalized},
    ltX = linVar["x"];
    normalized = normalizeAtom[aAtomLeq[ltX, HOL`Auto`Arith`Private`linConst[5]]];
    HOLTest`assertEq[phiMinusInfOnX[aFormAtom[normalized], "x"],
      aFormTrue, "x → -∞ makes x ≤ 5 true"]
  ]];

HOLTest`runTests["arith: phiMinusInfOnX — ¬(x ≤ 5) (i.e. x > 5) → F",
  Module[{ltX, normalized},
    ltX = linVar["x"];
    normalized = normalizeAtom[aAtomLeq[ltX, HOL`Auto`Arith`Private`linConst[5]]];
    HOLTest`assertEq[
      phiMinusInfOnX[aFormNot[aFormAtom[normalized]], "x"],
      aFormFalse, "x → -∞ falsifies x > 5"]
  ]];

HOLTest`runTests["arith: phiMinusInfOnX — x = 3 → F (equality misses at -∞)",
  Module[{ltX, normalized},
    ltX = linVar["x"];
    normalized = normalizeAtom[aAtomEq[ltX, HOL`Auto`Arith`Private`linConst[3]]];
    HOLTest`assertEq[phiMinusInfOnX[aFormAtom[normalized], "x"],
      aFormFalse, "x → -∞ falsifies x = 3"]
  ]];

HOLTest`runTests["arith: phiMinusInfOnX — divisibility atom is preserved",
  Module[{ltX, divAtom},
    ltX = linVar["x"];
    divAtom = aAtomDivides[3, ltX];
    HOLTest`assertEq[phiMinusInfOnX[aFormAtom[divAtom], "x"],
      aFormAtom[divAtom], "3 | x is periodic, kept for plug-in"]
  ]];

HOLTest`runTests["arith: phiMinusInfOnX — atoms not involving x pass through",
  Module[{ltY, atomY},
    ltY = linVar["y"];
    atomY = aAtomLeq[ltY, HOL`Auto`Arith`Private`linConst[10]];
    HOLTest`assertEq[phiMinusInfOnX[aFormAtom[atomY], "x"],
      aFormAtom[atomY], "y ≤ 10 doesn't depend on x"]
  ]];

HOLTest`runTests["arith: phiMinusInfOnX — full body x ≤ 5 ∧ 3 | x",
  Module[{ltX, body, normalized, result},
    ltX = linVar["x"];
    body = aFormAnd[
      aFormAtom[aAtomLeq[ltX, HOL`Auto`Arith`Private`linConst[5]]],
      aFormAtom[aAtomDivides[3, ltX]]];
    normalized = normalizeAtomsForm[body];
    result = phiMinusInfOnX[normalized, "x"];
    (* φ_{-∞} of (x ≤ 5 ∧ 3 | x) = T ∧ (3 | x). *)
    HOLTest`assertEq[result,
      aFormAnd[aFormTrue, aFormAtom[aAtomDivides[3, ltX]]],
      "x≤5 → T, 3|x kept; ∧ structure preserved"]
  ]];

(* ===== Session 6: substitution, B-set, cooperExistsStep ===== *)

substVarInLin = HOL`Auto`Arith`Private`substVarInLin;
substVarInAtom = HOL`Auto`Arith`Private`substVarInAtom;
substVarInForm = HOL`Auto`Arith`Private`substVarInForm;
bSetOnX = HOL`Auto`Arith`Private`bSetOnX;
cooperExistsStep = HOL`Auto`Arith`Private`cooperExistsStep;

HOLTest`runTests["arith: substVarInLin replaces x by a constant in (x + 3)",
  HOLTest`assertEq[
    substVarInLin[linTerm[3, <|"x" -> 1|>], "x",
      HOL`Auto`Arith`Private`linConst[7]],
    linTerm[10, <||>],
    "(1·x + 3)[x ↦ 7] = 10"]];

HOLTest`runTests["arith: substVarInLin replaces x by another linTerm",
  HOLTest`assertEq[
    substVarInLin[linTerm[0, <|"x" -> 2, "y" -> 1|>], "x",
      linTerm[1, <|"z" -> 1|>]],
    linTerm[2, <|"y" -> 1, "z" -> 2|>],
    "(2·x + y)[x ↦ (z + 1)] = 2(z+1) + y = 2 + y + 2z"]];

HOLTest`runTests["arith: substVarInLin on a linTerm without x is identity",
  Module[{lt},
    lt = linTerm[5, <|"y" -> 2|>];
    HOLTest`assertEq[substVarInLin[lt, "x",
      HOL`Auto`Arith`Private`linConst[100]],
      lt, "y + 5 doesn't mention x"]
  ]];

HOLTest`runTests["arith: substVarInForm respects binder shadowing on ∃",
  Module[{xV, body, t, result},
    xV = linVar["x"];
    body = aFormExists["x",
      aFormAtom[aAtomEq[linVar["x"],
        HOL`Auto`Arith`Private`linConst[5]]]];
    t = HOL`Auto`Arith`Private`linConst[42];
    result = substVarInForm[body, "x", t];
    HOLTest`assertEq[result, body,
      "the inner ∃x shadows; substitution leaves the body untouched"]
  ]];

HOLTest`runTests["arith: bSetOnX — x = 5 contributes b = 4",
  Module[{eqAtom, form},
    eqAtom = HOL`Auto`Arith`Private`normalizeAtom[
      aAtomEq[linVar["x"], HOL`Auto`Arith`Private`linConst[5]]];
    form = aFormAtom[eqAtom];
    HOLTest`assertEq[bSetOnX[form, "x"],
      {linTerm[4, <||>]},
      "x = 5 → witness 4 (so b + 1 = 5)"]
  ]];

HOLTest`runTests["arith: bSetOnX — x ≤ 5 contributes no witness (upper bound)",
  Module[{leqAtom, form},
    leqAtom = HOL`Auto`Arith`Private`normalizeAtom[
      aAtomLeq[linVar["x"], HOL`Auto`Arith`Private`linConst[5]]];
    form = aFormAtom[leqAtom];
    HOLTest`assertEq[bSetOnX[form, "x"], {},
      "x ≤ 5 is an upper bound; not in B"]
  ]];

HOLTest`runTests["arith: bSetOnX — 3 ≤ x contributes b = 2 (lower bound)",
  Module[{leqAtom, form},
    leqAtom = HOL`Auto`Arith`Private`normalizeAtom[
      aAtomLeq[HOL`Auto`Arith`Private`linConst[3], linVar["x"]]];
    form = aFormAtom[leqAtom];
    HOLTest`assertEq[bSetOnX[form, "x"],
      {linTerm[2, <||>]},
      "3 ≤ x → witness 2 (so b + 1 = 3)"]
  ]];

HOLTest`runTests["arith: bSetOnX — 3 < x (strict) contributes b = 3",
  Module[{ltAtom, form},
    ltAtom = HOL`Auto`Arith`Private`normalizeAtom[
      aAtomLt[HOL`Auto`Arith`Private`linConst[3], linVar["x"]]];
    form = aFormAtom[ltAtom];
    HOLTest`assertEq[bSetOnX[form, "x"],
      {linTerm[3, <||>]},
      "3 < x → witness 3 (so b + 1 = 4)"]
  ]];

HOLTest`runTests["arith: bSetOnX — divisibility atoms don't contribute",
  Module[{divAtom, form},
    divAtom = aAtomDivides[7, linVar["x"]];
    form = aFormAtom[divAtom];
    HOLTest`assertEq[bSetOnX[form, "x"], {},
      "3 | x is periodic; not in B"]
  ]];

HOLTest`runTests["arith: bSetOnX — multiple atoms collect all witnesses",
  Module[{ltX, atomLow, atomEq, form},
    ltX = linVar["x"];
    (* 3 ≤ x  ∧  x = 5  ∧  x ≤ 7  *)
    atomLow = HOL`Auto`Arith`Private`normalizeAtom[
      aAtomLeq[HOL`Auto`Arith`Private`linConst[3], ltX]];
    atomEq = HOL`Auto`Arith`Private`normalizeAtom[
      aAtomEq[ltX, HOL`Auto`Arith`Private`linConst[5]]];
    form = aFormAnd[aFormAtom[atomLow],
      aFormAnd[aFormAtom[atomEq],
        aFormAtom[HOL`Auto`Arith`Private`normalizeAtom[
          aAtomLeq[ltX, HOL`Auto`Arith`Private`linConst[7]]]]]];
    HOLTest`assertEq[bSetOnX[form, "x"],
      {linTerm[2, <||>], linTerm[4, <||>]},
      "{2 from 3≤x, 4 from x=5}; x≤7 is upper bound, skipped"]
  ]];

HOLTest`runTests["arith: cooperExistsStep on ∃x. x = 5 produces 0=0 disjunct",
  Module[{eqAtom, form, result, expected},
    eqAtom = aAtomEq[linVar["x"], HOL`Auto`Arith`Private`linConst[5]];
    form = aFormAtom[eqAtom];
    result = cooperExistsStep["x", form];
    (* φ_{-∞} = F (eq atom limit). δ = 1. B = {4}. *)
    (* body[x ↦ 4 + 1 = 5] = (5 = 5) normalized = (0 = 0). *)
    expected = aFormOr[aFormFalse,
      aFormAtom[aAtomEq[linTerm[0, <||>], linTerm[0, <||>]]]];
    HOLTest`assertEq[result, expected,
      "∃x. x=5 → F ∨ (0=0)"]
  ]];

HOLTest`runTests["arith: cooperExistsStep on ∃x. 3 ≤ x ∧ x ≤ 7",
  Module[{ltX, form, result},
    ltX = linVar["x"];
    form = aFormAnd[
      aFormAtom[aAtomLeq[HOL`Auto`Arith`Private`linConst[3], ltX]],
      aFormAtom[aAtomLeq[ltX, HOL`Auto`Arith`Private`linConst[7]]]];
    result = cooperExistsStep["x", form];
    (* δ = 1. B = {2}. φ_{-∞} of (3≤x ∧ x≤7) = F ∧ T = F (effectively). *)
    (* body[x ↦ 2 + 1 = 3] normalized = (3 - 3 ≤ 0) ∧ (3 - 7 ≤ 0)        *)
    (*                                = (0 ≤ 0) ∧ (-4 ≤ 0).               *)
    HOLTest`assertEq[result,
      aFormOr[
        aFormAnd[aFormFalse, aFormTrue],     (* φ_{-∞}[x ↦ 1] *)
        aFormAnd[
          aFormAtom[aAtomLeq[linTerm[0, <||>], linTerm[0, <||>]]],
          aFormAtom[aAtomLeq[linTerm[-4, <||>], linTerm[0, <||>]]]]],
      "QE result is the F∨T disjunct + the witness-substituted body"]
  ]];

HOLTest`runTests["arith: cooperExistsStep on empty B-set (e.g. ∃x. x ≤ 5)",
  Module[{leqAtom, form, result},
    leqAtom = aAtomLeq[linVar["x"], HOL`Auto`Arith`Private`linConst[5]];
    form = aFormAtom[leqAtom];
    result = cooperExistsStep["x", form];
    (* δ = 1, B = {}, φ_{-∞} = T. So minfDisjunct = T, bDisjunct = F. *)
    HOLTest`assertEq[result, aFormOr[aFormTrue, aFormFalse],
      "∃x. x ≤ 5 ⇒ φ_{-∞} carries the day (T at -∞)"]
  ]];
