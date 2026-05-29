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

HOLTest`runTests["arith: arithProve closes the num equality x = x",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = mkEq[xV, xV];
    th = arithProve[goal];
    HOLTest`assertEq[concl[th], goal, "⊢ x = x"]
  ]];

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

(* ===== Session 12: Cooper-instance theorems ===== *)

HOLTest`runTests["arith: existsEqThm — ⊢ ∀a. (∃x. x = a) = T",
  Module[{th, c},
    th = HOL`Auto`Arith`existsEqThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[const["∃", _], _]],
          const["T", _]]]],
      "shape: ∀a. (∃x. …) = T"]
  ]];

HOLTest`runTests["arith: existsLeqUbThm — ⊢ ∀a. (∃x. x ≤ a) = T",
  Module[{th, c},
    th = HOL`Auto`Arith`existsLeqUbThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[const["∃", _], _]],
          const["T", _]]]],
      "shape: ∀a. (∃x. …) = T"]
  ]];

HOLTest`runTests["arith: existsLowerBoundThm — ⊢ ∀a. (∃x. a ≤ x) = T",
  Module[{th, c},
    th = HOL`Auto`Arith`existsLowerBoundThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 1,
        comb[comb[const["=", _], comb[const["∃", _], _]],
          const["T", _]]]],
      "shape: ∀a. (∃x. …) = T"]
  ]];

HOLTest`runTests["arith: existsBoundedThm — ⊢ ∀a b. (∃x. a ≤ x ∧ x ≤ b) = (a ≤ b)",
  Module[{th, c},
    th = HOL`Auto`Arith`existsBoundedThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _],
          comb[const["∃", _], _]], _]]],
      "shape: ∀a. ∀b. (∃x. …) = (…)"]
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

(* ===== Session 6: substitution, B-set ===== *)

substVarInLin = HOL`Auto`Arith`Private`substVarInLin;
substVarInAtom = HOL`Auto`Arith`Private`substVarInAtom;
substVarInForm = HOL`Auto`Arith`Private`substVarInForm;
bSetOnX = HOL`Auto`Arith`Private`bSetOnX;

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

(* ===== Session 7: simpForm — propositional simplification ===== *)

simpForm = HOL`Auto`Arith`Private`simpForm;

HOLTest`runTests["arith: simpForm evaluates ground equality (0 = 0 → T, 5 = 3 → F)",
  Module[{lin0, lin5, lin3},
    lin0 = HOL`Auto`Arith`Private`linConst[0];
    lin5 = HOL`Auto`Arith`Private`linConst[5];
    lin3 = HOL`Auto`Arith`Private`linConst[3];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomEq[lin0, lin0]]],
      aFormTrue, "0 = 0 → T"];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomEq[lin5, lin3]]],
      aFormFalse, "5 = 3 → F"]
  ]];

HOLTest`runTests["arith: simpForm evaluates ground ≤ and <",
  Module[{lin0, lin5, linNeg4},
    lin0 = HOL`Auto`Arith`Private`linConst[0];
    lin5 = HOL`Auto`Arith`Private`linConst[5];
    linNeg4 = linTerm[-4, <||>];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomLeq[linNeg4, lin0]]],
      aFormTrue, "-4 ≤ 0 → T"];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomLeq[lin5, lin0]]],
      aFormFalse, "5 ≤ 0 → F"];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomLt[lin0, lin5]]],
      aFormTrue, "0 < 5 → T"];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomLt[lin5, lin5]]],
      aFormFalse, "5 < 5 → F"]
  ]];

HOLTest`runTests["arith: simpForm evaluates ground divisibility (3 | 6 → T, 3 | 7 → F)",
  Module[{lin6, lin7},
    lin6 = HOL`Auto`Arith`Private`linConst[6];
    lin7 = HOL`Auto`Arith`Private`linConst[7];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomDivides[3, lin6]]],
      aFormTrue, "3 | 6 → T"];
    HOLTest`assertEq[simpForm[aFormAtom[aAtomDivides[3, lin7]]],
      aFormFalse, "3 | 7 → F"]
  ]];

HOLTest`runTests["arith: simpForm leaves non-ground atoms alone",
  Module[{xV, atomNonGround, wrapped},
    xV = linVar["x"];
    atomNonGround = aAtomEq[xV, HOL`Auto`Arith`Private`linConst[5]];
    wrapped = aFormAtom[atomNonGround];
    HOLTest`assertEq[simpForm[wrapped], wrapped,
      "x = 5 stays as-is (x is free)"]
  ]];

HOLTest`runTests["arith: simpForm folds T/F through ∧ ∨ ¬",
  Module[{xV, atomX},
    xV = linVar["x"];
    atomX = aFormAtom[aAtomEq[xV, HOL`Auto`Arith`Private`linConst[1]]];
    HOLTest`assertEq[simpForm[aFormAnd[aFormTrue, atomX]],
      atomX, "T ∧ x → x"];
    HOLTest`assertEq[simpForm[aFormAnd[aFormFalse, atomX]],
      aFormFalse, "F ∧ x → F"];
    HOLTest`assertEq[simpForm[aFormOr[aFormFalse, atomX]],
      atomX, "F ∨ x → x"];
    HOLTest`assertEq[simpForm[aFormOr[aFormTrue, atomX]],
      aFormTrue, "T ∨ x → T"];
    HOLTest`assertEq[simpForm[aFormNot[aFormTrue]],
      aFormFalse, "¬T → F"];
    HOLTest`assertEq[simpForm[aFormNot[aFormNot[atomX]]],
      atomX, "¬¬x → x"]
  ]];

(* ===== Session 8: ground arithmetic provers ===== *)

proveGroundAddEq = HOL`Auto`Arith`Private`proveGroundAddEq;
proveGroundMultEq = HOL`Auto`Arith`Private`proveGroundMultEq;
proveGroundLeq = HOL`Auto`Arith`Private`proveGroundLeq;
proveGroundLt = HOL`Auto`Arith`Private`proveGroundLt;
proveGroundDivides = HOL`Auto`Arith`Private`proveGroundDivides;
buildLitNum = HOL`Auto`Arith`Private`buildLitNum;

plusN[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`plusConst[], a], b];
timesN[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`timesConst[], a], b];
leqN[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
ltN[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`ltConst[], a], b];
divN[a_, b_] :=
  mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], a], b];

HOLTest`runTests["arith: proveGroundAddEq[2,3] ⊢ 2 + 3 = 5",
  Module[{th},
    th = proveGroundAddEq[2, 3];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th],
      mkEq[plusN[buildLitNum[2], buildLitNum[3]], buildLitNum[5]],
      "⊢ 2 + 3 = 5"]
  ]];

HOLTest`runTests["arith: proveGroundAddEq edge cases (0 + n, n + 0)",
  Module[{},
    HOLTest`assertEq[concl[proveGroundAddEq[0, 5]],
      mkEq[plusN[buildLitNum[0], buildLitNum[5]], buildLitNum[5]],
      "⊢ 0 + 5 = 5"];
    HOLTest`assertEq[concl[proveGroundAddEq[7, 0]],
      mkEq[plusN[buildLitNum[7], buildLitNum[0]], buildLitNum[7]],
      "⊢ 7 + 0 = 7"]
  ]];

HOLTest`runTests["arith: proveGroundMultEq[3,4] ⊢ 3 * 4 = 12",
  Module[{th},
    th = proveGroundMultEq[3, 4];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th],
      mkEq[timesN[buildLitNum[3], buildLitNum[4]], buildLitNum[12]],
      "⊢ 3 * 4 = 12"]
  ]];

HOLTest`runTests["arith: proveGroundMultEq edge cases (m * 0)",
  HOLTest`assertEq[concl[proveGroundMultEq[5, 0]],
    mkEq[timesN[buildLitNum[5], buildLitNum[0]], buildLitNum[0]],
    "⊢ 5 * 0 = 0"]];

HOLTest`runTests["arith: proveGroundLeq[2,5] ⊢ 2 ≤ 5",
  Module[{th},
    th = proveGroundLeq[2, 5];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], leqN[buildLitNum[2], buildLitNum[5]],
      "⊢ 2 ≤ 5"]
  ]];

HOLTest`runTests["arith: proveGroundLeq[3,3] ⊢ 3 ≤ 3 (reflexive)",
  HOLTest`assertEq[concl[proveGroundLeq[3, 3]],
    leqN[buildLitNum[3], buildLitNum[3]],
    "⊢ 3 ≤ 3"]];

HOLTest`runTests["arith: proveGroundLt[2,5] ⊢ 2 < 5",
  Module[{th},
    th = proveGroundLt[2, 5];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], ltN[buildLitNum[2], buildLitNum[5]],
      "⊢ 2 < 5"]
  ]];

HOLTest`runTests["arith: proveGroundDivides[3,12] ⊢ divides 3 12",
  Module[{th},
    th = proveGroundDivides[3, 12];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], divN[buildLitNum[3], buildLitNum[12]],
      "⊢ divides 3 12"]
  ]];

HOLTest`runTests["arith: proveGroundDivides[7, 49] ⊢ divides 7 49",
  HOLTest`assertEq[concl[proveGroundDivides[7, 49]],
    divN[buildLitNum[7], buildLitNum[49]],
    "⊢ divides 7 49"]];

HOLTest`runTests["arith: proveGroundDivides rejects non-divisible",
  HOLTest`assertThrows[
    proveGroundDivides[3, 10], "arith-ground",
    "3 does not divide 10"]];

(* ===== Session 9: arithProveExists — ∃-SAT → HOL theorem ===== *)

findSatWitness = HOL`Auto`Arith`Private`findSatWitness;
proveGroundAtomTm = HOL`Auto`Arith`Private`proveGroundAtomTm;
proveGroundFormulaTm = HOL`Auto`Arith`Private`proveGroundFormulaTm;
arithProveExists = HOL`Auto`Arith`Private`arithProveExists;

existsNumTm[v_, body_] :=
  mkComb[mkConst["\[Exists]", tyFun[tyFun[numTy, boolTy], boolTy]],
    mkAbs[v, body]];

HOLTest`runTests["arith: findSatWitness on ∃x. x = 5",
  Module[{xV, body},
    xV = linVar["x"];
    body = aFormAtom[aAtomEq[xV, HOL`Auto`Arith`Private`linConst[5]]];
    HOLTest`assertEq[findSatWitness["x", body], 5,
      "witness is 5"]
  ]];

HOLTest`runTests["arith: findSatWitness on ∃x. 3 ≤ x ∧ x ≤ 7",
  Module[{xV, body, w},
    xV = linVar["x"];
    body = aFormAnd[
      aFormAtom[aAtomLeq[HOL`Auto`Arith`Private`linConst[3], xV]],
      aFormAtom[aAtomLeq[xV, HOL`Auto`Arith`Private`linConst[7]]]];
    w = findSatWitness["x", body];
    HOLTest`assertTrue[IntegerQ[w] && 3 <= w <= 7,
      "witness is in [3, 7], got " <> ToString[w]]
  ]];

HOLTest`runTests["arith: findSatWitness returns Missing on UNSAT",
  Module[{xV, body},
    xV = linVar["x"];
    body = aFormAnd[
      aFormAtom[aAtomLeq[HOL`Auto`Arith`Private`linConst[10], xV]],
      aFormAtom[aAtomLeq[xV, HOL`Auto`Arith`Private`linConst[3]]]];
    HOLTest`assertTrue[MissingQ[findSatWitness["x", body]],
      "no x satisfies 10 ≤ x ∧ x ≤ 3"]
  ]];

HOLTest`runTests["arith: proveGroundAtomTm — 0 = 0 via REFL",
  Module[{th},
    th = proveGroundAtomTm[mkEq[buildLitNum[0], buildLitNum[0]]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], mkEq[buildLitNum[0], buildLitNum[0]],
      "⊢ 0 = 0"]
  ]];

HOLTest`runTests["arith: proveGroundFormulaTm on (3 ≤ 5) ∧ (5 ≤ 7)",
  Module[{tm, th, leq35, leq57},
    leq35 = mkComb[mkComb[HOL`Stdlib`Num`leqConst[], buildLitNum[3]],
      buildLitNum[5]];
    leq57 = mkComb[mkComb[HOL`Stdlib`Num`leqConst[], buildLitNum[5]],
      buildLitNum[7]];
    tm = mkComb[mkComb[mkConst["\[And]",
      tyFun[boolTy, tyFun[boolTy, boolTy]]], leq35], leq57];
    th = proveGroundFormulaTm[tm];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], tm, "⊢ (3 ≤ 5) ∧ (5 ≤ 7)"]
  ]];

HOLTest`runTests["arith: arithProveExists on ∃x. x = 5",
  Module[{goal, th},
    goal = existsNumTm[mkVar["x", numTy],
      mkEq[mkVar["x", numTy], buildLitNum[5]]];
    th = arithProveExists[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∃x. x = 5"]
  ]];

HOLTest`runTests["arith: arithProveExists on ∃x. 3 ≤ x ∧ x ≤ 7",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV, mkComb[mkComb[
      mkConst["\[And]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkComb[mkComb[HOL`Stdlib`Num`leqConst[], buildLitNum[3]], xV]],
      mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV], buildLitNum[7]]]];
    th = arithProveExists[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "⊢ ∃x. 3 ≤ x ∧ x ≤ 7"]
  ]];

HOLTest`runTests["arith: arithProveExists on ∃x. x = 6 ∧ divides 3 x",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV, mkComb[mkComb[
      mkConst["\[And]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[xV, buildLitNum[6]]],
      mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], buildLitNum[3]], xV]]];
    th = arithProveExists[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "⊢ ∃x. x = 6 ∧ divides 3 x"]
  ]];

HOLTest`runTests["arith: arithProveExists on ∃x. divides 4 x",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV,
      mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], buildLitNum[4]], xV]];
    th = arithProveExists[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∃x. divides 4 x"]
  ]];

HOLTest`runTests["arith: arithProveExists fails on UNSAT goal",
  Module[{xV, goal},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV, mkComb[mkComb[
      mkConst["\[And]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkComb[mkComb[HOL`Stdlib`Num`leqConst[], buildLitNum[10]], xV]],
      mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV], buildLitNum[3]]]];
    HOLTest`assertThrows[arithProveExists[goal], "arith-prove-exists",
      "no witness for 10 ≤ x ∧ x ≤ 3"]
  ]];

(* ===== Session 10: proveGroundReduceTm + compound atom in arithProveExists ===== *)

proveGroundReduceTm = HOL`Auto`Arith`Private`proveGroundReduceTm;

HOLTest`runTests["arith: proveGroundReduceTm — leaf 0 and SUC^k 0",
  Module[{},
    HOLTest`assertEq[concl[proveGroundReduceTm[buildLitNum[0]]],
      mkEq[buildLitNum[0], buildLitNum[0]],
      "⊢ 0 = 0 via REFL"];
    HOLTest`assertEq[concl[proveGroundReduceTm[buildLitNum[5]]],
      mkEq[buildLitNum[5], buildLitNum[5]], "⊢ 5 = 5 via REFL"]
  ]];

HOLTest`runTests["arith: proveGroundReduceTm — 0 + 3 = 3",
  HOLTest`assertEq[
    concl[proveGroundReduceTm[plusN[buildLitNum[0], buildLitNum[3]]]],
    mkEq[plusN[buildLitNum[0], buildLitNum[3]], buildLitNum[3]],
    "⊢ 0 + 3 = 3"]];

HOLTest`runTests["arith: proveGroundReduceTm — 2 * 3 + 1 = 7",
  Module[{tm, th},
    tm = plusN[timesN[buildLitNum[2], buildLitNum[3]], buildLitNum[1]];
    th = proveGroundReduceTm[tm];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], mkEq[tm, buildLitNum[7]],
      "⊢ 2*3 + 1 = 7"]
  ]];

HOLTest`runTests["arith: proveGroundReduceTm — nested (1+2) + (3+4) = 10",
  Module[{tm, th},
    tm = plusN[plusN[buildLitNum[1], buildLitNum[2]],
      plusN[buildLitNum[3], buildLitNum[4]]];
    th = proveGroundReduceTm[tm];
    HOLTest`assertEq[concl[th], mkEq[tm, buildLitNum[10]],
      "⊢ (1+2) + (3+4) = 10"]
  ]];

HOLTest`runTests["arith: arithProveExists on ∃x. x + 3 ≤ 5 (compound LHS atom)",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV, mkComb[mkComb[HOL`Stdlib`Num`leqConst[],
      plusN[xV, buildLitNum[3]]], buildLitNum[5]]];
    th = arithProveExists[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "⊢ ∃x. x + 3 ≤ 5"]
  ]];

HOLTest`runTests["arith: arithProveExists on ∃x. (x + 1) = 4 (compound LHS in =)",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV,
      mkEq[plusN[xV, buildLitNum[1]], buildLitNum[4]]];
    th = arithProveExists[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∃x. (x + 1) = 4"]
  ]];

HOLTest`runTests["arith: arithProveExists on ∃x. x + 2 ≤ x + 5 (both compound)",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV, mkComb[mkComb[HOL`Stdlib`Num`leqConst[],
      plusN[xV, buildLitNum[2]]], plusN[xV, buildLitNum[5]]]];
    th = arithProveExists[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∃x. x + 2 ≤ x + 5"]
  ]];

(* ===== Session 11: arithProve public wrap + nested ∃ + ARITH tactic ===== *)

arithProve = HOL`Auto`Arith`arithProve;
ARITH = HOL`Auto`Arith`ARITH;

HOLTest`runTests["arith: arithProve on single ∃ (same as arithProveExists)",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV, mkEq[xV, buildLitNum[5]]];
    th = arithProve[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∃x. x = 5"]
  ]];

HOLTest`runTests["arith: arithProve on nested ∃x. ∃y. x ≤ y",
  Module[{xV, yV, goal, th},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    goal = existsNumTm[xV, existsNumTm[yV,
      mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV], yV]]];
    th = arithProve[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "⊢ ∃x. ∃y. x ≤ y (recursion picks (0, 0))"]
  ]];

HOLTest`runTests["arith: arithProve on nested ∃ with constraint",
  Module[{xV, yV, goal, th},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    goal = existsNumTm[xV, existsNumTm[yV, mkComb[mkComb[
      mkConst["\[And]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
      mkEq[xV, buildLitNum[3]]],
      mkEq[yV, buildLitNum[7]]]]];
    th = arithProve[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "⊢ ∃x. ∃y. x = 3 ∧ y = 7"]
  ]];

HOLTest`runTests["arith: arithProve closes ∀x. x ≤ x via Farkas",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = mkComb[mkConst["\[ForAll]",
      tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[xV, mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV], xV]]];
    th = arithProve[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀x. x ≤ x"]
  ]];

HOLTest`runTests["arith: ARITH closes ∀x. x + x ≤ x + x (merge)",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = forallNum[xV, leqN[plusN[xV, xV], plusN[xV, xV]]];
    th = arithProve[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀x. x + x ≤ x + x"]
  ]];

HOLTest`runTests["arith: ARITH closes ∀x. 2·x ≤ 2·x (literal coef)",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = forallNum[xV, leqN[timesN[mkNum[2], xV], timesN[mkNum[2], xV]]];
    th = arithProve[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀x. 2·x ≤ 2·x"]
  ]];

HOLTest`runTests["arith: ARITH throws arith-norm on deferred k·(a+b)",
  Module[{xV, goal},
    xV = mkVar["x", numTy];
    goal = forallNum[xV,
      leqN[timesN[mkNum[2], plusN[xV, xV]],
           timesN[mkNum[2], plusN[xV, xV]]]];
    HOLTest`assertThrows[arithProve[goal], "arith-norm",
      "literal·(a+b) distribution still deferred"]
  ]];

HOLTest`runTests["arith: ARITH tactic closes ∃-SAT goal via prove[]",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = existsNumTm[xV, mkEq[xV, buildLitNum[5]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "ARITH tactic via prove[] yields ⊢ ∃x. x = 5"]
  ]];

HOLTest`runTests["arith: ARITH tactic on nested ∃ via prove[]",
  Module[{xV, yV, goal, th},
    xV = mkVar["x", numTy]; yV = mkVar["y", numTy];
    goal = existsNumTm[xV, existsNumTm[yV,
      mkEq[plusN[xV, buildLitNum[1]], yV]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "ARITH tactic closes ⊢ ∃x. ∃y. x + 1 = y"]
  ]];

(* ===== linNormConv: proof-producing linear normalizer ===== *)
(* Invariant for every supported t: linNormConv[t] returns the   *)
(* hyp-free theorem ⊢ t = buildLin[parseLin[t]]. Asserting the    *)
(* full equation forces the RHS to be canonical (a normalizer     *)
(* that returned REFL[t] would fail on non-canonical inputs like  *)
(* y + x) and the theorem to be kernel-valid.                     *)

linNormConv = HOL`Auto`Arith`linNormConv;
sucN[x_] := mkComb[sucConst[], x];

normInvariant[label_, t_] :=
  HOLTest`runTests["arith: linNormConv " <> label,
    Module[{th},
      th = linNormConv[t];
      HOLTest`assertEq[hyp[th], {}, "no hyps"];
      HOLTest`assertEq[concl[th], mkEq[t, buildLin[parseLin[t]]],
        "⊢ t = buildLin[parseLin[t]]"]
    ]];

With[{mV = mkVar["m", numTy], nV = mkVar["n", numTy],
      pV = mkVar["p", numTy]},
  normInvariant["on x (already canonical var)", mkVar["x", numTy]];
  normInvariant["on literal 3", mkNum[3]];
  normInvariant["keeps m + n sorted", mkPlus[mV, nV]];
  normInvariant["sorts n + m → m + n", mkPlus[nV, mV]];
  normInvariant["reassociates (m + n) + p", mkPlus[mkPlus[mV, nV], pV]];
  normInvariant["sorts + reassociates n + (m + p)",
    mkPlus[nV, mkPlus[mV, pV]]];
  normInvariant["SUC (n + p) → 1 + (n + p)", sucN[mkPlus[nV, pV]]];
  normInvariant["m + SUC (n + p) [capstone LHS]",
    mkPlus[mV, sucN[mkPlus[nV, pV]]]];
  normInvariant["n + (m + p) [capstone RHS]",
    mkPlus[nV, mkPlus[mV, pV]]];
  normInvariant["constant fold 2 + (m + 3)",
    mkPlus[mkNum[2], mkPlus[mV, mkNum[3]]]];
  normInvariant["merge m + m → 2·m", mkPlus[mV, mV]];
  normInvariant["merge m + (m + n) → 2·m + n",
    mkPlus[mV, mkPlus[mV, nV]]];
  normInvariant["merge m + (2 + m) → 2 + 2·m",
    mkPlus[mV, mkPlus[mkNum[2], mV]]];
  normInvariant["merge n + m + m → m·2 + n (sort + merge)",
    mkPlus[nV, mkPlus[mV, mV]]];
  normInvariant["double merge (m+n) + (m+n) → 2·m + 2·n",
    mkPlus[mkPlus[mV, nV], mkPlus[mV, nV]]];
  normInvariant["merge to coef 3: m + (m + m)",
    mkPlus[mV, mkPlus[mV, mV]]];
  normInvariant["monomial 2·m is canonical", mkTimes[mkNum[2], mV]];
  normInvariant["monomial 1·m → m", mkTimes[mkNum[1], mV]];
  normInvariant["monomial 0·m → 0", mkTimes[mkNum[0], mV]];
  normInvariant["merge 2·m + 3·m → 5·m",
    mkPlus[mkTimes[mkNum[2], mV], mkTimes[mkNum[3], mV]]];
];

(* ===== ARITH on ∀ goals via Farkas refutation ===== *)

HOLTest`runTests["arith: ARITH capstone ∀m n p. m≤n ⇒ m+p ≤ n+p",
  Module[{mV, nV, pV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy]; pV = mkVar["p", numTy];
    goal = forallNum[mV, forallNum[nV, forallNum[pV,
      impCT[leqN[mV, nV], leqN[plusN[mV, pV], plusN[nV, pV]]]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal,
      "⊢ ∀m n p. m ≤ n ⇒ m + p ≤ n + p"]
  ]];

HOLTest`runTests["arith: ARITH ∀n. n ≤ SUC n (no hyp, single fact)",
  Module[{nV, goal, th},
    nV = mkVar["n", numTy];
    goal = forallNum[nV, leqN[nV, sucN[nV]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀n. n ≤ SUC n"]
  ]];

HOLTest`runTests["arith: ARITH ∀m n. m < n ⇒ m ≤ n (< hypothesis)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV, impCT[ltN[mV, nV], leqN[mV, nV]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m < n ⇒ m ≤ n"]
  ]];

HOLTest`runTests["arith: ARITH ∀m n. m ≤ n ⇒ m < SUC n (< conclusion)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV,
      impCT[leqN[mV, nV], ltN[mV, sucN[nV]]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m ≤ n ⇒ m < SUC n"]
  ]];

HOLTest`runTests["arith: ARITH ∀x. 1 ≤ x ⇒ 2 ≤ x + x (non-unit λ)",
  Module[{xV, goal, th},
    (* FM certificate uses the hypothesis twice: λ = (2, 1). The old
       unit-subset oracle could never find this. *)
    xV = mkVar["x", numTy];
    goal = forallNum[xV,
      impCT[leqN[mkNum[1], xV], leqN[mkNum[2], plusN[xV, xV]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀x. 1 ≤ x ⇒ 2 ≤ x + x"]
  ]];

HOLTest`runTests["arith: ARITH ∀x. x ≤ x + x (needs 0 ≤ x)",
  Module[{xV, goal, th},
    xV = mkVar["x", numTy];
    goal = forallNum[xV, leqN[xV, plusN[xV, xV]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀x. x ≤ x + x"]
  ]];

HOLTest`runTests["arith: ARITH ∀m n. m ≤ m + n (needs 0 ≤ n)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV, leqN[mV, plusN[mV, nV]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m ≤ m + n"]
  ]];

HOLTest`runTests["arith: ARITH rejects the false goal ∀x. x ≤ 0",
  Module[{xV, goal},
    xV = mkVar["x", numTy];
    goal = forallNum[xV, leqN[xV, mkNum[0]]];
    HOLTest`assertThrows[arithProve[goal], "arith-farkas",
      "x ≤ 0 is false; nonnegativity cannot rescue it"]
  ]];

(* ===== atom abstraction: nonlinear m·n generalized to a variable ===== *)
(* m·n is opaque to linear arithmetic, so ARITH abstracts it to a fresh *)
(* atom and reasons about that atom; GEN then binds m,n inside it.       *)

HOLTest`runTests["arith: ARITH ∀m n. m·n ≤ m·n + 1 (nonlinear atom)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV,
      leqN[timesN[mV, nV], plusN[timesN[mV, nV], mkNum[1]]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m·n ≤ m·n + 1"]
  ]];

HOLTest`runTests["arith: ARITH ∀m n. m·n ≤ m·n (reflexive atom)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV,
      leqN[timesN[mV, nV], timesN[mV, nV]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m·n ≤ m·n"]
  ]];

HOLTest`runTests["arith: ARITH ∀m n. m·n ≤ m·n + m·n (atom merge + 0≤atom)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV,
      leqN[timesN[mV, nV], plusN[timesN[mV, nV], timesN[mV, nV]]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m·n ≤ m·n + m·n"]
  ]];

(* ===== equality (=) atoms: conclusions via antisymmetry, =-hyps split ===== *)

eqN[a_, b_] := mkEq[a, b];

HOLTest`runTests["arith: ARITH ∀m n. m + n = n + m (= conclusion)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV, eqN[plusN[mV, nV], plusN[nV, mV]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m + n = n + m"]
  ]];

HOLTest`runTests["arith: ARITH ∀m n p. m = n ⇒ m + p = n + p (= hyp + concl)",
  Module[{mV, nV, pV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy]; pV = mkVar["p", numTy];
    goal = forallNum[mV, forallNum[nV, forallNum[pV,
      impCT[eqN[mV, nV], eqN[plusN[mV, pV], plusN[nV, pV]]]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n p. m = n ⇒ m + p = n + p"]
  ]];

HOLTest`runTests["arith: ARITH ∀m n. m = n ⇒ m ≤ n (= hypothesis)",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV, impCT[eqN[mV, nV], leqN[mV, nV]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m = n ⇒ m ≤ n"]
  ]];

HOLTest`runTests["arith: arithProve closes a bare open goal m + n = n + m",
  Module[{mV, nV, goal, th},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = eqN[plusN[mV, nV], plusN[nV, mV]];
    th = arithProve[goal];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ m + n = n + m (free m, n)"]
  ]];

HOLTest`runTests["arith: arithProve rejects an unsupported goal shape",
  HOLTest`assertThrows[
    arithProve[divN[buildLitNum[3], mkVar["x", numTy]]],
    "arith-not-supported", "divides 3 x is not a ≤/</= goal"]];

HOLTest`runTests["arith: ARITH ∀m n. m·n + n·m = n·m + m·n (two distinct atoms)",
  Module[{mV, nV, goal, th},
    (* Regression: ≥2 distinct atoms in a normalized side exercises
       firstMonoOf, which must materialize the atom term, not var[key]. *)
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    goal = forallNum[mV, forallNum[nV,
      eqN[plusN[timesN[mV, nV], timesN[nV, mV]],
          plusN[timesN[nV, mV], timesN[mV, nV]]]]];
    th = HOL`Tactics`prove[goal, ARITH[]];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertEq[concl[th], goal, "⊢ ∀m n. m·n + n·m = n·m + m·n"]
  ]];

(* ===== Phase B: Fourier–Motzkin oracle (farkasFM, untrusted) ===== *)
(* diffs are linTerm[const, vars] standing for `≤ 0` constraints.    *)
(* farkasFM returns an Association origIdx→integer λ (Farkas cert)    *)
(* or $Failed. Compare KeySort'd since cert key order is incidental. *)

farkasFM = HOL`Auto`Arith`Private`farkasFM;

HOLTest`runTests["arith: farkasFM capstone diffs → {1→1, 2→1}",
  HOLTest`assertEq[
    KeySort[farkasFM[{linTerm[0, <|"m" -> 1, "n" -> -1|>],
                      linTerm[1, <|"m" -> -1, "n" -> 1|>]}]],
    KeySort[<|1 -> 1, 2 -> 1|>],
    "m-n ≤0, n-m+1 ≤0 refuted by λ=(1,1)"]];

HOLTest`runTests["arith: farkasFM single positive constant → {1→1}",
  HOLTest`assertEq[
    KeySort[farkasFM[{linTerm[2, <||>]}]],
    KeySort[<|1 -> 1|>],
    "2 ≤ 0 is already contradictory"]];

HOLTest`runTests["arith: farkasFM finds non-unit multiplier λ=(1,2)",
  HOLTest`assertEq[
    KeySort[farkasFM[{linTerm[-1, <|"x" -> 2|>],
                      linTerm[1, <|"x" -> -1|>]}]],
    KeySort[<|1 -> 1, 2 -> 2|>],
    "2x-1 ≤0, 1-x ≤0 needs λ=(1,2) — unbeatable by unit subsets"]];

HOLTest`runTests["arith: farkasFM returns $Failed on a feasible system",
  HOLTest`assertEq[
    farkasFM[{linTerm[0, <|"x" -> 1|>]}],
    $Failed,
    "x ≤ 0 alone is feasible (x = 0)"]];

HOLTest`runTests["arith: farkasFM eliminates a middle variable (3 facts)",
  Module[{cert},
    (* x ≤ y, y ≤ z, z+1 ≤ x  ⇒  x ≤ y ≤ z < z+1 ≤ x, infeasible.
       diffs: x-y ≤0, y-z ≤0, z+1-x ≤0; λ=(1,1,1). *)
    cert = farkasFM[{linTerm[0, <|"x" -> 1, "y" -> -1|>],
                     linTerm[0, <|"y" -> 1, "z" -> -1|>],
                     linTerm[1, <|"z" -> 1, "x" -> -1|>]}];
    HOLTest`assertEq[KeySort[cert], KeySort[<|1 -> 1, 2 -> 1, 3 -> 1|>],
      "chain refutation λ=(1,1,1)"]
  ]];
