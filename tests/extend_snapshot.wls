#!/usr/bin/env wolframscript

(* Incrementally advance bootstrap.mx by loading one or more newly-graduated *)
(* library files ON TOP of the existing snapshot, then re-dumping — seconds, *)
(* not a ~7-min full cold rebuild. Use when a file you just finished is added *)
(* to build_snapshot.wls's load list: instead of cold-rebuilding the whole    *)
(* world, fold the new file into the snapshot in place.                       *)
(*                                                                            *)
(* Usage:                                                                     *)
(*   wolframscript -file tests/extend_snapshot.wls <file.wl> [more.wl ...]    *)
(*     paths relative to the repo root, in dependency order.                   *)
(*   e.g.  tests/extend_snapshot.wls stdlib/Real/Field.wl                     *)
(*                                                                            *)
(* The file(s) MUST already be added to build_snapshot.wls's list (so cold    *)
(* rebuilds stay consistent) and must depend only on what is already in the   *)
(* snapshot (re-loading a file already in the snapshot will throw, e.g. on a   *)
(* newBasicTypeDefinition for an already-declared type).                       *)
(*                                                                            *)
(* SAFETY: this produces a Stable-mode snapshot equivalent to cold-loading     *)
(* the same files in order, but does NOT re-verify upstream and shares the     *)
(* Stable-vs-Strict gap (memory testing_cadence_stable_strict). Run a full     *)
(* build_snapshot.wls + cold Strict run_all at each stage boundary as the      *)
(* authoritative gate.                                                         *)

$HOLEncapsulationMode = "Stable";

Module[{repoRoot, snapshotFile, args, files, holContexts, holPublic,
        startTime, sizeBefore, sizeAfter},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  snapshotFile = FileNameJoin[{repoRoot, "bootstrap.mx"}];
  $Path = Prepend[$Path, repoRoot];

  args = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 1,
    Drop[$ScriptCommandLine, 1], {}];
  If[args === {},
    Print["[extend] usage: extend_snapshot.wls <file.wl> [more.wl ...]"];
    Print["         paths relative to repo root, in dependency order."];
    Exit[2]];

  If[!FileExistsQ[snapshotFile],
    Print["[extend] no snapshot at ", snapshotFile,
      " — run build_snapshot.wls first."];
    Exit[2]];

  files = args;
  Scan[Function[f,
    If[!FileExistsQ[FileNameJoin[{repoRoot, f}]],
      Print["[extend] no such file: ", f]; Exit[2]]], files];

  sizeBefore = Round[FileByteCount[snapshotFile] / 1024];
  startTime = AbsoluteTime[];
  Print["[extend] restoring ", snapshotFile, " (", sizeBefore, " KB)..."];
  Get[snapshotFile];

  (* DumpSave does not preserve $ContextPath; re-add public HOL contexts so a *)
  (* file using short names at load resolves them (BeginPackage import lists  *)
  (* also cover their own deps — this is belt-and-suspenders).                *)
  holPublic = Select[Contexts[],
    StringMatchQ[#, "HOL`*"] && !StringContainsQ[#, "Private`"] &];
  $ContextPath = Join[holPublic, $ContextPath];

  Scan[Function[f,
    Module[{t0 = AbsoluteTime[]},
      Print["[extend] loading ", f, " ..."];
      Get[FileNameJoin[{repoRoot, f}]];
      Print["  [", Round[AbsoluteTime[] - t0, 0.1], "s] ", f]
    ]], files];

  holContexts = Select[Contexts[], StringMatchQ[#, "HOL`*"] &];
  Print["[extend] re-dumping ", Length[holContexts], " HOL contexts..."];
  DumpSave[snapshotFile, Evaluate[holContexts]];

  sizeAfter = Round[FileByteCount[snapshotFile] / 1024];
  Print["[extend] done: ", snapshotFile, " (", sizeBefore, " → ", sizeAfter,
    " KB, ", Round[AbsoluteTime[] - startTime, 0.1], " s)"];
]
