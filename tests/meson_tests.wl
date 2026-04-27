(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Drule`"];
Needs["HOL`Tactics`"];
Needs["HOL`Auto`Meson`"];

(* M7-α-1: skeleton tests.  At this stage MESON signs to noTac and
   mesonProve throws — we verify the wiring, not the search. Tests for
   actual proving land with M7-α-3 (search engine) and M7-α-4 (replay). *)

HOLTest`runTests["meson: skeleton — public symbols exist",
  Module[{},
    HOLTest`assertTrue[ValueQ[mesonMaxDepth] || NumericQ[mesonMaxDepth],
      "mesonMaxDepth bound"];
    HOLTest`assertEq[mesonMaxDepth, 50, "default depth cap is 50"];
  ]];

HOLTest`runTests["meson: skeleton — MESON[{}] signs to tactic failure",
  Module[{p, g},
    p = mkVar["p", boolTy];
    g = goal[{}, p];
    HOLTest`assertThrows[MESON[{}][g], "tactic",
      "MESON skeleton fails as a tactic (signs to noTac)"];
  ]];

HOLTest`runTests["meson: skeleton — mesonProve throws meson-tag",
  Module[{p},
    p = mkVar["p", boolTy];
    HOLTest`assertThrows[mesonProve[p, {}], "meson",
      "mesonProve skeleton throws meson tag"];
  ]];
