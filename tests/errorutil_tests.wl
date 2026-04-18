(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];

HOLTest`runTests["ErrorUtil: holError throws holErrorTag", Module[{},
  HOLTest`assertThrows[
    HOL`Error`holError["type", "arity mismatch"],
    "type",
    "tag is carried through"
  ];
]];

HOLTest`runTests["ErrorUtil: Failure payload shape", Module[{f},
  f = Catch[
    HOL`Error`holError["kernel", "boom", <|"hint" -> "look here"|>];
    Null,
    HOL`Error`holErrorTag,
    #1 &
  ];
  HOLTest`assertTrue[FailureQ[f], "result is a Failure"];
  HOLTest`assertEq[f[[2, "tag"]], "kernel", "tag field"];
  HOLTest`assertEq[f[[2, "msg"]], "boom", "msg field"];
  HOLTest`assertEq[f[[2, "hint"]], "look here", "extra field merged"];
  HOLTest`assertTrue[ListQ[f[[2, "stack"]]], "stack captured as a list"];
]];

HOLTest`runTests["ErrorUtil: withHOLErrors passes values through", Module[{},
  HOLTest`assertEq[HOL`Error`withHOLErrors[42], 42, "plain value returned"];
  HOLTest`assertTrue[
    FailureQ[HOL`Error`withHOLErrors[HOL`Error`holError["t", "m"]]],
    "throw becomes a Failure"
  ];
]];

HOLTest`runTests["ErrorUtil: holFailureQ", Module[{f},
  f = HOL`Error`withHOLErrors[HOL`Error`holError["t", "m"]];
  HOLTest`assertTrue[HOL`Error`holFailureQ[f], "holFailureQ on real failure"];
  HOLTest`assertEq[HOL`Error`holFailureQ[42], False, "holFailureQ rejects non-failure"];
]];
