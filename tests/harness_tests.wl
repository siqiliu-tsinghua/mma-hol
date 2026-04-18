(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];

HOLTest`runTests["harness basics", Module[{},
  HOLTest`assertEq[1 + 1, 2, "assertEq on equal values"];
  HOLTest`assertTrue[True, "assertTrue on True"];
  HOLTest`assertTrue[1 < 2, "assertTrue on arithmetic"];
]];

HOLTest`runTests["harness assertThrows", Module[{},
  HOLTest`assertThrows[
    HOL`Error`holError["demo", "expected throw"],
    "demo",
    "assertThrows catches literal tag"
  ];
  HOLTest`assertThrows[
    HOL`Error`holError["whatever", "x"],
    _String,
    "assertThrows accepts pattern"
  ];
]];

HOLTest`runTests["harness counters", Module[{},
  HOLTest`assertTrue[IntegerQ[HOLTest`Private`$pass], "pass counter is Integer"];
  HOLTest`assertTrue[IntegerQ[HOLTest`Private`$fail], "fail counter is Integer"];
  HOLTest`assertTrue[HOLTest`Private`$pass >= 0, "pass counter nonneg"];
  HOLTest`assertTrue[HOLTest`Private`$fail >= 0, "fail counter nonneg"];
]];
