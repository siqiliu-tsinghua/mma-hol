(* ::Package:: *)

BeginPackage["HOLTest`", {"HOL`Error`"}];

group::usage         = "group[name] prints a section header in test output.";
assertEq::usage      = "assertEq[actual, expected, name] passes iff actual === expected.";
assertTrue::usage    = "assertTrue[cond, name] passes iff cond === True.";
assertThrows::usage  =
  "assertThrows[expr, tagPattern, name] passes iff evaluating expr throws a HOLError whose tag matches tagPattern.";
runTests::usage      = "runTests[name, body] wraps body, catches escaped throws, and reports a group-level failure on escape.";
registerFailure::usage = "registerFailure[name, detail] records a manual failure.";
testSummary::usage   = "testSummary[] prints pass/fail counts and returns {passed, failed}.";
testExit::usage      = "testExit[] prints summary and Exit[0] on all-pass, Exit[1] otherwise.";
resetCounters::usage = "resetCounters[] clears pass/fail counters. Used only from CI entry.";

Begin["`Private`"];

$pass = 0;
$fail = 0;

resetCounters[] := ($pass = 0; $fail = 0;);

pass[name_] := ($pass++; Print["  ok  ", name];);
fail[name_, detail_] := ($fail++; Print["  FAIL ", name]; Print["       ", detail];);

group[name_String] := Print["::: ", name];

assertEq[actual_, expected_, name_String] :=
  If[actual === expected,
    pass[name],
    fail[name,
      Row[{"expected ", ToString[expected, InputForm], " got ", ToString[actual, InputForm]}]
    ]
  ];

assertTrue[cond_, name_String] :=
  If[cond === True,
    pass[name],
    fail[name, Row[{"expected True got ", ToString[cond, InputForm]}]]
  ];

SetAttributes[assertThrows, HoldFirst];
assertThrows[expr_, tagPattern_, name_String] :=
  Module[{thrown = False, tag = None, val},
    val = Catch[expr; Null,
      HOL`Error`holErrorTag,
      (thrown = True;
       tag = Which[
         MatchQ[#1, _Failure] && AssociationQ[#1[[2]]] && KeyExistsQ[#1[[2]], "tag"], #1[[2, "tag"]],
         True, None
       ];
       Null) &
    ];
    Which[
      ! thrown,
        fail[name, Row[{"expected throw matching ", ToString[tagPattern, InputForm], ", no throw"}]],
      ! MatchQ[tag, tagPattern],
        fail[name, Row[{"expected tag matching ", ToString[tagPattern, InputForm], ", got ", ToString[tag, InputForm]}]],
      True,
        pass[name]
    ]
  ];

registerFailure[name_String, detail_] := fail[name, detail];

SetAttributes[runTests, HoldRest];
runTests[name_String, body_] :=
  Module[{r},
    group[name];
    r = Catch[body, _, (fail[name <> " (escaped throw)", Row[{"tag=", ToString[#2, InputForm], " value=", ToString[#1, InputForm]}]]; $Failed) &];
    r
  ];

testSummary[] :=
  (Print["---"];
   Print[" passed: ", $pass];
   Print[" failed: ", $fail];
   {$pass, $fail});

testExit[] :=
  Module[{r = testSummary[]},
    If[r[[2]] === 0, Exit[0], Exit[1]]
  ];

End[];
EndPackage[];
