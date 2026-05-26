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
