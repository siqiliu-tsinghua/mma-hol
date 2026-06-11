(* ::Package:: *)

(* Tests for M7-7 stdlib/Real/MinMax.wl - binary maximum and minimum on real. *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Pair`"];
Needs["HOL`Stdlib`Num`"];
Needs["HOL`Stdlib`Int`"];
Needs["HOL`Stdlib`Rat`"];
Needs["HOL`Stdlib`Real`"];

HOLTest`runTests["stdlib/Real: realMaxDefThm - maximum definition",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMaxDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMaxDefThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMinDefThm - minimum definition",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMinDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMinDefThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMaxLeCaseThm - maximum nondecreasing case",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMaxLeCaseThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMaxLeCaseThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMaxGtCaseThm - maximum non-le case",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMaxGtCaseThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMaxGtCaseThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMinLeCaseThm - minimum nondecreasing case",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMinLeCaseThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMinLeCaseThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMinGtCaseThm - minimum non-le case",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMinGtCaseThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMinGtCaseThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLeMaxLeftThm - left argument is below max",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeMaxLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeMaxLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLeMaxRightThm - right argument is below max",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeMaxRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeMaxRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMinLeLeftThm - min is below left argument",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMinLeLeftThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMinLeLeftThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMinLeRightThm - min is below right argument",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMinLeRightThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMinLeRightThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMaxLubThm - max is least upper bound",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMaxLubThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMaxLubThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMinGlbThm - min is greatest lower bound",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMinGlbThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMinGlbThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMaxCommThm - max is commutative",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMaxCommThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMaxCommThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realMinCommThm - min is commutative",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realMinCommThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realMinCommThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAbsMaxThm - abs as max of x and -x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsMaxThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsMaxThm], "is a theorem"]];
