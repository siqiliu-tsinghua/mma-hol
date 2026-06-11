#!/usr/bin/env wolframscript

Module[{repoRoot, preBootstrapTests, postBootstrapTests, runGroup},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  $Path = Prepend[$Path, repoRoot];
  $Path = Prepend[$Path, FileNameJoin[{repoRoot, "tests"}]];

  Scan[
    Function[rel, Get[FileNameJoin[Prepend[rel, repoRoot]]]],
    {
      {"ErrorUtil.wl"},
      {"Types.wl"},
      {"Terms.wl"},
      {"Kernel.wl"},
      (* harness quantNestPat resolves HOL`Terms` heads at read-time; Terms must load first *)
      {"tests", "harness.wl"}
    }
  ];

  HOLTest`resetCounters[];

  runGroup[label_, files_] := (
    Print["=== ", label, " ==="];
    Scan[
      Function[f,
        Print[">>> ", FileNameTake[f]];
        Get[f]
      ],
      files
    ]
  );

  preBootstrapTests  = {FileNameJoin[{repoRoot, "tests", "kernel_tests.wl"}]};
  postBootstrapTests = Complement[
    FileNames["*_tests.wl", FileNameJoin[{repoRoot, "tests"}]],
    preBootstrapTests];

  runGroup["pre-bootstrap", preBootstrapTests];

  Get[FileNameJoin[{repoRoot, "Bootstrap.wl"}]];
  Get[FileNameJoin[{repoRoot, "Equal.wl"}]];
  Get[FileNameJoin[{repoRoot, "Bool.wl"}]];
  Get[FileNameJoin[{repoRoot, "Drule.wl"}]];
  Get[FileNameJoin[{repoRoot, "Tactics.wl"}]];
  Get[FileNameJoin[{repoRoot, "Printer.wl"}]];
  Get[FileNameJoin[{repoRoot, "Parser.wl"}]];
  Get[FileNameJoin[{repoRoot, "auto", "PropTaut.wl"}]];
  Get[FileNameJoin[{repoRoot, "auto", "Meson.wl"}]];
  Get[FileNameJoin[{repoRoot, "auto", "Simp.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Pair.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Sum.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Option.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Set.wl"}]];
  Get[FileNameJoin[{repoRoot, "auto", "Set.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Num.wl"}]];
  Get[FileNameJoin[{repoRoot, "auto", "Arith.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "List.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Finite.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "FTA.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Int.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Rat.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Real", "Cut.wl"}]];
  (* Cut → RatAux → Field → Mul → Inv → Complete: the ℝ ordered-field core
     (GRADUATED 2026-06-10: group + ring + field + linear order + ×/≤ compat
     + ℚ↪ℝ homomorphism) + Dedekind completeness / Archimedean / ℚ-density.
     New Real files (Roots.wl, Seq.wl) are the next frontier. *)
  Get[FileNameJoin[{repoRoot, "stdlib", "Real", "RatAux.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Real", "Field.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Real", "Mul.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Real", "Inv.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Real", "Complete.wl"}]];
  Get[FileNameJoin[{repoRoot, "stdlib", "Real", "Abs.wl"}]];

  runGroup["post-bootstrap", postBootstrapTests];

  HOLTest`testExit[]
]
