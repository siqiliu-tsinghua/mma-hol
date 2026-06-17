#!/usr/bin/env wolframscript

(* Cold-boot the library stack in Stable encapsulation mode, then DumpSave  *)
(* the entire HOL` context tree to bootstrap.mx for fast restore. This is    *)
(* the FULL (re)build / re-baseline tool; the inner dev loop should use      *)
(* tests/dev.wls (restore + load only the frontier file) and tests/         *)
(* extend_snapshot.wls (fold a graduated file into the snapshot in seconds), *)
(* so a full cold rebuild is only needed when an UPSTREAM file changes or to *)
(* produce a clean authoritative base.                                       *)
(*                                                                          *)
(* Usage:                                                                   *)
(*   wolframscript -file tests/build_snapshot.wls                           *)
(*     full cold rebuild of bootstrap.mx (all libraries).                    *)
(*   wolframscript -file tests/build_snapshot.wls <uptoPattern>             *)
(*     PARTIAL rebuild: load only through the first library whose filename   *)
(*     contains <uptoPattern> (e.g. `Rat` → through stdlib/Rat.wl). Still    *)
(*     writes bootstrap.mx — use to re-baseline at a layer (the in-flight    *)
(*     file is then loaded on top via tests/dev.wls). Loudly flagged.        *)

$HOLEncapsulationMode = "Stable";

Module[{repoRoot, snapshotFile, holContexts, startTime, libs, loadList,
        args, uptoPattern, pos, sizeKB},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  snapshotFile = FileNameJoin[{repoRoot, "bootstrap.mx"}];
  $Path = Prepend[$Path, repoRoot];

  args = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 1,
    Drop[$ScriptCommandLine, 1], {}];
  uptoPattern = If[args === {}, None, First[args]];

  (* Ordered library load list (dependency order). The single source of     *)
  (* truth for COLD builds; tests/dev.wls and tests/extend_snapshot.wls      *)
  (* operate on the resulting snapshot incrementally and need no list.       *)
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
    {"stdlib", "FTA.wl"},
    {"stdlib", "Int.wl"},
    {"stdlib", "Rat.wl"},
    {"stdlib", "Real", "Cut.wl"},
    {"stdlib", "Real", "RatAux.wl"},
    {"stdlib", "Real", "Field.wl"},
    {"stdlib", "Real", "Mul.wl"},
    {"stdlib", "Real", "Inv.wl"},
    {"stdlib", "Real", "Complete.wl"},
    {"stdlib", "Real", "Abs.wl"},
    {"stdlib", "Real", "MinMax.wl"},
    {"auto", "RealArith.wl"},
    {"stdlib", "Real", "Seq.wl"},
    {"stdlib", "Real", "SeqAux.wl"},
    {"stdlib", "Real", "Compact.wl"},
    {"stdlib", "Real", "Connected.wl"},
    {"stdlib", "Real", "Topology.wl"},
    {"stdlib", "Real", "CompactSet.wl"}
  };

  loadList = If[uptoPattern === None, libs,
    (pos = SelectFirst[Range[Length[libs]],
       StringContainsQ[Last[libs[[#]]], uptoPattern] &, $Failed];
     If[pos === $Failed,
       Print["[snapshot] no library filename contains '", uptoPattern, "'"];
       Exit[2]];
     Take[libs, pos])];

  startTime = AbsoluteTime[];
  Print["[snapshot] mode: Stable; loading ", Length[loadList], " of ",
    Length[libs], " libraries",
    If[uptoPattern === None, " (full)...",
      " (through " <> uptoPattern <> ")..."]];

  Scan[
    Function[rel,
      Module[{t0 = AbsoluteTime[]},
        Get[FileNameJoin[Prepend[rel, repoRoot]]];
        Print["  [", Round[AbsoluteTime[] - t0, 0.1], "s] ", FileNameJoin[rel]]
      ]],
    loadList];

  Print["[snapshot] libraries loaded in ",
    Round[AbsoluteTime[] - startTime, 0.1], " s"];

  If[uptoPattern =!= None,
    Print["[snapshot] *** PARTIAL snapshot (through ", uptoPattern,
      ") — NOT the full world. Rebuild with no args before a full run_fast/CI. ***"]];

  (* Enumerate every HOL` context. Pass them as context-pattern strings to   *)
  (* DumpSave (lists of bare symbol names do NOT preserve DownValues).        *)
  holContexts = Select[Contexts[], StringMatchQ[#, "HOL`*"] &];
  Print["[snapshot] dumping ", Length[holContexts], " HOL contexts..."];

  (* DumpSave has HoldRest — Evaluate or it saves the literal symbol.         *)
  DumpSave[snapshotFile, Evaluate[holContexts]];

  sizeKB = Round[FileByteCount[snapshotFile] / 1024];
  Print["[snapshot] done: ", snapshotFile, " (", sizeKB, " KB, total ",
    Round[AbsoluteTime[] - startTime, 0.1], " s)"];
]
