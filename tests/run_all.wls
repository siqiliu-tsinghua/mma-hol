#!/usr/bin/env wolframscript

Module[{repoRoot, testFiles},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];
  $Path = Prepend[$Path, repoRoot];
  $Path = Prepend[$Path, FileNameJoin[{repoRoot, "tests"}]];

  Scan[
    Function[rel, Get[FileNameJoin[Prepend[rel, repoRoot]]]],
    {
      {"ErrorUtil.wl"},
      {"tests", "harness.wl"},
      {"Types.wl"}
    }
  ];

  HOLTest`resetCounters[];

  testFiles = FileNames["*_tests.wl", FileNameJoin[{repoRoot, "tests"}]];
  Print["discovered ", Length[testFiles], " test file(s)"];
  Scan[
    Function[f,
      Print[">>> ", FileNameTake[f]];
      Get[f]
    ],
    testFiles
  ];

  HOLTest`testExit[]
]
