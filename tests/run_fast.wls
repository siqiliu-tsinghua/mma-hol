#!/usr/bin/env wolframscript

(* Fast test runner: restore the Stable-mode bootstrap snapshot from  *)
(* disk, then run a chosen subset of test files.                       *)
(*                                                                    *)
(* Usage:                                                             *)
(*   wolframscript -file tests/run_fast.wls                           *)
(*     (runs *all* *_tests.wl files)                                  *)
(*   wolframscript -file tests/run_fast.wls num                       *)
(*     (runs only tests/*num*_tests.wl)                                *)
(*   wolframscript -file tests/run_fast.wls num simp                  *)
(*     (runs tests matching any of {num, simp})                        *)
(*                                                                    *)
(* If bootstrap.mx is missing OR older than any source file, exits     *)
(* with a hint to rerun build_snapshot.wls.                            *)

$HOLEncapsulationMode = "Stable";

Module[{repoRoot, snapshotFile, args, patterns, allTestFiles,
        chosenTestFiles, sourceFiles, snapMtime, staleSrcs, startTime},

  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  snapshotFile = FileNameJoin[{repoRoot, "bootstrap.mx"}];
  $Path = Prepend[$Path, repoRoot];

  If[!FileExistsQ[snapshotFile],
    Print["[run_fast] No snapshot found at ", snapshotFile];
    Print["           Run: wolframscript -file tests/build_snapshot.wls"];
    Exit[2]];

  (* Staleness check: any source file (libraries + Kernel + bootstrap) *)
  (* newer than the snapshot triggers a stop with a hint.               *)
  sourceFiles = Flatten[{
    FileNames["*.wl", repoRoot],
    FileNames["*.wl", FileNameJoin[{repoRoot, "auto"}]],
    FileNames["*.wl", FileNameJoin[{repoRoot, "stdlib"}], Infinity]
  }];
  snapMtime = FileDate[snapshotFile, "Modification"];
  staleSrcs = Select[sourceFiles,
    AbsoluteTime[FileDate[#, "Modification"]] > AbsoluteTime[snapMtime] &];
  If[Length[staleSrcs] > 0,
    Print["[run_fast] Snapshot is older than these source files:"];
    Scan[Print["  ", FileNameTake[#, -2]] &, Take[staleSrcs, UpTo[10]]];
    Print["[run_fast] Rerun: wolframscript -file tests/build_snapshot.wls"];
    Exit[3]];

  args = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 1,
    Drop[$ScriptCommandLine, 1], {}];
  patterns = args;

  startTime = AbsoluteTime[];
  Print["[run_fast] Restoring snapshot from ", snapshotFile, " ..."];
  Get[snapshotFile];

  (* DumpSave doesn't preserve $ContextPath / $Packages. Add every       *)
  (* public HOL`* context (excluding Private subcontexts) so tests can   *)
  (* refer to mkType / mkComb / concl / etc. by short names.             *)
  Module[{holPublicContexts},
    holPublicContexts = Select[Contexts[],
      StringMatchQ[#, "HOL`*"] && !StringContainsQ[#, "Private`"] &];
    $ContextPath = Join[holPublicContexts, $ContextPath];
    $Packages = Union[$Packages, holPublicContexts];
  ];

  Print["[run_fast] Loading harness..."];
  Get[FileNameJoin[{repoRoot, "ErrorUtil.wl"}]];
  Get[FileNameJoin[{repoRoot, "tests", "harness.wl"}]];

  HOLTest`resetCounters[];

  (* kernel_tests.wl exercises pre-bootstrap kernel state — axiom        *)
  (* intake open, constants/types unregistered. The snapshot has these   *)
  (* already locked / populated, so those tests can't be replayed from a *)
  (* restored kernel. Skip them.                                         *)
  allTestFiles = Select[
    FileNames["*_tests.wl", FileNameJoin[{repoRoot, "tests"}]],
    !StringMatchQ[FileNameTake[#], "kernel_tests.wl"] &];
  chosenTestFiles = If[patterns === {},
    allTestFiles,
    Select[allTestFiles, Function[fname,
      AnyTrue[patterns, StringContainsQ[FileNameTake[fname], #] &]]]];

  If[chosenTestFiles === {},
    Print["[run_fast] No test files matched patterns: ", patterns];
    Exit[4]];

  Print["[run_fast] Restore + harness done in ",
    Round[AbsoluteTime[] - startTime, 0.1], " s"];
  Print["[run_fast] Running ", Length[chosenTestFiles], " test file(s)..."];

  Scan[Function[f,
    Module[{t0 = AbsoluteTime[]},
      Get[f];
      Print["  [", Round[AbsoluteTime[] - t0, 0.01], "s] ", FileNameTake[f]]
    ]], chosenTestFiles];

  HOLTest`testExit[]
]
