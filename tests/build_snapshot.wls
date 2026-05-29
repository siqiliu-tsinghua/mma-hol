#!/usr/bin/env wolframscript

(* Cold-boot the full library stack in Stable encapsulation mode,    *)
(* then DumpSave the entire HOL` context tree to bootstrap.mx for    *)
(* fast restore. Re-run this script whenever any library file or the *)
(* kernel ABI changes; tests/run_fast.wls checks mtimes and prints a *)
(* hint when the snapshot is stale.                                  *)

$HOLEncapsulationMode = "Stable";

Module[{repoRoot, snapshotFile, allHolSyms, holContexts,
        startTime, libs, sizeKB},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  snapshotFile = FileNameJoin[{repoRoot, "bootstrap.mx"}];
  $Path = Prepend[$Path, repoRoot];

  startTime = AbsoluteTime[];

  libs = {
    {"ErrorUtil.wl"},
    {"Types.wl"},
    {"Terms.wl"},
    {"Kernel.wl"},
    {"Bootstrap.wl"},
    {"Equal.wl"},
    {"Bool.wl"},
    {"Drule.wl"},
    {"Tactics.wl"},
    {"Printer.wl"},
    {"Parser.wl"},
    {"auto", "PropTaut.wl"},
    {"auto", "Meson.wl"},
    {"auto", "Simp.wl"},
    {"stdlib", "Pair.wl"},
    {"stdlib", "Sum.wl"},
    {"stdlib", "Option.wl"},
    {"stdlib", "Set.wl"},
    {"auto", "Set.wl"},
    {"stdlib", "Num.wl"},
    {"auto", "Arith.wl"},
    {"stdlib", "List.wl"},
    {"stdlib", "Finite.wl"},
    {"stdlib", "FTA.wl"}
  };

  Print["[snapshot] mode: Stable; loading ", Length[libs], " libraries..."];
  Scan[
    Function[rel,
      Get[FileNameJoin[Prepend[rel, repoRoot]]]
    ],
    libs
  ];

  Print["[snapshot] libraries loaded in ",
    Round[AbsoluteTime[] - startTime, 0.1], " s"];

  (* Enumerate every HOL` context. Pass them as context-pattern        *)
  (* strings to DumpSave (lists of bare symbol names do NOT preserve   *)
  (* DownValues — context patterns do).                                 *)
  holContexts = Select[Contexts[], StringMatchQ[#, "HOL`*"] &];

  Print["[snapshot] dumping ", Length[holContexts], " HOL contexts..."];

  (* `DumpSave` has HoldRest — wrap with Evaluate or it sees the     *)
  (* literal symbol `holContexts` and saves nothing useful.           *)
  DumpSave[snapshotFile, Evaluate[holContexts]];

  sizeKB = Round[FileByteCount[snapshotFile] / 1024];
  Print["[snapshot] done: ", snapshotFile, " (", sizeKB, " KB, total ",
    Round[AbsoluteTime[] - startTime, 0.1], " s)"];
]
