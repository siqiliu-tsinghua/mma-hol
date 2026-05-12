(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Tactics`"];
Needs["HOL`Stdlib`Set`"];
Needs["HOL`Auto`Set`"];

(* ===== capstone: S ∪ T = T ∪ S ===== *)

HOLTest`runTests["auto/Set: setProve closes UNION commutativity (capstone)",
  Module[{alpha, setT, S, T, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT]; T = mkVar["T", setT];
    goal = mkEq[unionTerm[S, T], unionTerm[T, S]];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal,
      "⊢ S ∪ T = T ∪ S (the M7-γ capstone, one-line proof)"];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
]];

HOLTest`runTests["auto/Set: setProve closes INTER commutativity",
  Module[{alpha, setT, S, T, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT]; T = mkVar["T", setT];
    goal = mkEq[interTerm[S, T], interTerm[T, S]];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal, "⊢ S ∩ T = T ∩ S"];
]];

HOLTest`runTests["auto/Set: setProve closes UNION associativity",
  Module[{alpha, setT, S, T, U, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT]; T = mkVar["T", setT]; U = mkVar["U", setT];
    goal = mkEq[
      unionTerm[unionTerm[S, T], U],
      unionTerm[S, unionTerm[T, U]]];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal, "⊢ (S ∪ T) ∪ U = S ∪ (T ∪ U)"];
]];

HOLTest`runTests["auto/Set: setProve closes INTER over UNION distributivity",
  Module[{alpha, setT, S, T, U, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT]; T = mkVar["T", setT]; U = mkVar["U", setT];
    goal = mkEq[
      interTerm[S, unionTerm[T, U]],
      unionTerm[interTerm[S, T], interTerm[S, U]]];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal,
      "⊢ S ∩ (T ∪ U) = (S ∩ T) ∪ (S ∩ U)"];
]];

HOLTest`runTests["auto/Set: setProve closes UNION identity (EMPTY)",
  Module[{alpha, setT, S, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT];
    goal = mkEq[
      unionTerm[S, mkConst["EMPTY", constType["EMPTY"]]],
      S];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal, "⊢ S ∪ EMPTY = S"];
]];

HOLTest`runTests["auto/Set: setProve closes INTER identity (UNIV)",
  Module[{alpha, setT, S, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT];
    goal = mkEq[
      interTerm[S, mkConst["UNIV", constType["UNIV"]]],
      S];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal, "⊢ S ∩ UNIV = S"];
]];

HOLTest`runTests["auto/Set: setProve closes INTER annihilator (EMPTY)",
  Module[{alpha, setT, S, emptyTm, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT];
    emptyTm = mkConst["EMPTY", constType["EMPTY"]];
    goal = mkEq[interTerm[S, emptyTm], emptyTm];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal, "⊢ S ∩ EMPTY = EMPTY"];
]];

HOLTest`runTests["auto/Set: setProve closes DIFF and double-complement-style",
  Module[{alpha, setT, S, T, U, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT]; T = mkVar["T", setT];
    goal = mkEq[
      diffTerm[S, T],
      interTerm[S, diffTerm[mkConst["UNIV", constType["UNIV"]], T]]];
    th = setProve[goal];
    HOLTest`assertEq[concl[th], goal, "⊢ S ∖ T = S ∩ (UNIV ∖ T)"];
]];

(* ===== SET tactic ===== *)

HOLTest`runTests["auto/Set: SET tactic closes the capstone",
  Module[{alpha, setT, S, T, goal, th},
    alpha = mkVarType["A"]; setT = tyFun[alpha, boolTy];
    S = mkVar["S", setT]; T = mkVar["T", setT];
    goal = mkEq[unionTerm[S, T], unionTerm[T, S]];
    th = HOL`Tactics`prove[goal, HOL`Auto`Set`SET[]];
    HOLTest`assertEq[concl[th], goal, "prove[…, SET[]] closes S ∪ T = T ∪ S"];
]];

(* ===== error handling ===== *)

HOLTest`runTests["auto/Set: setProve rejects non-equation",
  Module[{S},
    S = mkVar["S", tyFun[mkVarType["A"], boolTy]];
    HOLTest`assertThrows[setProve[S], "set",
      "setProve rejects a non-equation input"];
]];
