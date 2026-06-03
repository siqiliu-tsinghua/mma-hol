#!/usr/bin/env wolframscript

(* Fast FRONTIER dev loop: restore bootstrap.mx, load the file(s) you are     *)
(* actively developing ON TOP (they are NOT yet folded into the snapshot),    *)
(* then run matching tests. The point: editing a frontier library file no     *)
(* longer forces a ~7-min full cold rebuild — restore the frozen base         *)
(* (seconds) and re-load only the file you changed.                            *)
(*                                                                            *)
(* Usage:                                                                     *)
(*   wolframscript -file tests/dev.wls <frontier.wl> [more.wl ...] [pat ...]  *)
(*     Args that name an existing file (relative to the repo root) are loaded  *)
(*     as frontier files, in the given order; the remaining args are          *)
(*     test-file patterns (like run_fast). With no patterns, all *_tests.wl   *)
(*     run.                                                                    *)
(*   e.g.  tests/dev.wls stdlib/Real/Field.wl real                            *)
(*         (restore base, load Field.wl on top, run tests/real_tests.wl)       *)
(*                                                                            *)
(* STALENESS: bootstrap.mx must be newer than every source .wl EXCEPT the     *)
(* named frontier files (which are always re-loaded fresh). If an UPSTREAM    *)
(* file changed, the base is stale → rebuild with build_snapshot.wls.          *)
(*                                                                            *)
(* This is Stable-mode like run_fast: it catches logic errors, NOT Strict     *)
(* gensym/load-order issues. The authoritative per-stage gate stays the cold  *)
(* Strict run_all.                                                             *)

$HOLEncapsulationMode = "Stable";

Module[{repoRoot, snapshotFile, args, frontierFiles, patterns, sourceFiles,
        snapMtime, staleSrcs, holPublic, allTestFiles, chosenTestFiles,
        startTime},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  snapshotFile = FileNameJoin[{repoRoot, "bootstrap.mx"}];
  $Path = Prepend[$Path, repoRoot];

  If[!FileExistsQ[snapshotFile],
    Print["[dev] no snapshot at ", snapshotFile,
      " — run build_snapshot.wls first."];
    Exit[2]];

  args = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 1,
    Drop[$ScriptCommandLine, 1], {}];
  (* auto-split: an arg resolving to an existing file is a frontier file;     *)
  (* everything else is a test-file pattern.                                  *)
  frontierFiles = Select[args, FileExistsQ[FileNameJoin[{repoRoot, #}]] &];
  patterns = Complement[args, frontierFiles];

  If[frontierFiles === {},
    Print["[dev] no frontier file given (an arg must name an existing .wl"];
    Print["      relative to the repo root). usage: dev.wls <file.wl> [pat...]"];
    Exit[2]];

  (* staleness: every source EXCEPT the frontier files must predate the snap. *)
  sourceFiles = Complement[
    Flatten[{
      FileNames["*.wl", repoRoot],
      FileNames["*.wl", FileNameJoin[{repoRoot, "auto"}]],
      FileNames["*.wl", FileNameJoin[{repoRoot, "stdlib"}], Infinity]
    }],
    FileNameJoin[{repoRoot, #}] & /@ frontierFiles];
  snapMtime = FileDate[snapshotFile, "Modification"];
  staleSrcs = Select[sourceFiles,
    AbsoluteTime[FileDate[#, "Modification"]] > AbsoluteTime[snapMtime] &];
  If[Length[staleSrcs] > 0,
    Print["[dev] snapshot is older than these NON-frontier sources:"];
    Scan[Print["  ", FileNameTake[#, -2]] &, Take[staleSrcs, UpTo[10]]];
    Print["[dev] an upstream file changed — rebuild: build_snapshot.wls"];
    Exit[3]];

  startTime = AbsoluteTime[];
  Print["[dev] restoring snapshot ", snapshotFile, " ..."];
  Get[snapshotFile];

  holPublic = Select[Contexts[],
    StringMatchQ[#, "HOL`*"] && !StringContainsQ[#, "Private`"] &];
  $ContextPath = Join[holPublic, $ContextPath];

  Print["[dev] loading ", Length[frontierFiles], " frontier file(s) on top..."];
  Scan[Function[f,
    Module[{t0 = AbsoluteTime[]},
      Get[FileNameJoin[{repoRoot, f}]];
      Print["  [", Round[AbsoluteTime[] - t0, 0.1], "s] ", f]
    ]], frontierFiles];

  (* frontier files may introduce new public contexts — re-add so tests can  *)
  (* use short names. *)
  holPublic = Select[Contexts[],
    StringMatchQ[#, "HOL`*"] && !StringContainsQ[#, "Private`"] &];
  $ContextPath = Join[holPublic, $ContextPath];

  Get[FileNameJoin[{repoRoot, "ErrorUtil.wl"}]];
  Get[FileNameJoin[{repoRoot, "tests", "harness.wl"}]];
  HOLTest`resetCounters[];

  allTestFiles = Select[
    FileNames["*_tests.wl", FileNameJoin[{repoRoot, "tests"}]],
    !StringMatchQ[FileNameTake[#], "kernel_tests.wl"] &];
  chosenTestFiles = If[patterns === {},
    allTestFiles,
    Select[allTestFiles, Function[fname,
      AnyTrue[patterns, StringContainsQ[FileNameTake[fname], #] &]]]];
  If[chosenTestFiles === {},
    Print["[dev] no test files matched patterns: ", patterns];
    Exit[4]];

  Print["[dev] restore + frontier + harness done in ",
    Round[AbsoluteTime[] - startTime, 0.1], " s"];
  Print["[dev] running ", Length[chosenTestFiles], " test file(s)..."];
  Scan[Function[f,
    Module[{t0 = AbsoluteTime[]},
      Get[f];
      Print["  [", Round[AbsoluteTime[] - t0, 0.01], "s] ", FileNameTake[f]]
    ]], chosenTestFiles];

  HOLTest`testExit[]
]
