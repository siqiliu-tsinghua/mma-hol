(* ::Package:: *)

(* Tests for M7-7 stdlib/Real/Abs.wl - absolute value on real. *)

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

HOLTest`runTests["stdlib/Real: realAbsDefThm - absolute value definition",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsDefThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsDefThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAbsPosThm - non-negative case",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsPosThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsPosThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAbsNegCaseThm - negative case",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsNegCaseThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsNegCaseThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAbsZeroThm - abs 0 = 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsZeroThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsZeroThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAbsNonnegThm - abs is non-negative",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsNonnegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsNonnegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realLeAbsSelfThm - x <= abs x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realLeAbsSelfThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realLeAbsSelfThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realNegLeAbsThm - -x <= abs x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realNegLeAbsThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realNegLeAbsThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAbsNegThm - abs (-x) = abs x",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsNegThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsNegThm], "is a theorem"]];

HOLTest`runTests["stdlib/Real: realAbsTriangleThm - triangle inequality",
  HOLTest`assertEq[hyp[HOL`Stdlib`Real`realAbsTriangleThm], {}, "no hyps"];
  HOLTest`assertTrue[isThm[HOL`Stdlib`Real`realAbsTriangleThm], "is a theorem"]];
