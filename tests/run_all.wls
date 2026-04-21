#!/usr/bin/env wolframscript

Module[{repoRoot, preBootstrapTests, postBootstrapTests, runGroup},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  $Path = Prepend[$Path, repoRoot];
  $Path = Prepend[$Path, FileNameJoin[{repoRoot, "tests"}]];

  Scan[
    Function[rel, Get[FileNameJoin[Prepend[rel, repoRoot]]]],
    {
      {"ErrorUtil.wl"},
      {"tests", "harness.wl"},
      {"Types.wl"},
      {"Terms.wl"},
      {"Kernel.wl"}
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

  runGroup["post-bootstrap", postBootstrapTests];

  HOLTest`testExit[]
]
