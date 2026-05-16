#!/usr/bin/env wolframscript

(* Lint: enforce the trust-boundary convention                       *)
(*                                                                   *)
(* Any reference to `HOL`Kernel`Private`*` outside Kernel.wl is a    *)
(* bug. Scans all .wl and .wls files in the repo for literal         *)
(* `HOL`Kernel`Private` substrings, prints offending file:line for   *)
(* each, exits nonzero if any found.                                  *)
(*                                                                   *)
(* See CLAUDE.md trust-boundary rule 0 for rationale.                *)

Module[{repoRoot, files, allowedFiles, violations, kernelFile},
  repoRoot = ParentDirectory[DirectoryName[$InputFileName]];

  files = Join[
    FileNames["*.wl", repoRoot],
    FileNames["*.wl", FileNameJoin[{repoRoot, "auto"}]],
    FileNames["*.wl", FileNameJoin[{repoRoot, "stdlib"}]],
    FileNames["*.wl", FileNameJoin[{repoRoot, "tests"}]],
    FileNames["*.wls", FileNameJoin[{repoRoot, "tests"}]]
  ];

  (* Files allowed to mention HOL`Kernel`Private`. *)
  kernelFile = FileNameJoin[{repoRoot, "Kernel.wl"}];
  allowedFiles = {
    kernelFile,
    (* This lint script itself contains the pattern as a string.     *)
    $InputFileName,
    (* Snapshot builder + run_fast both reference Private contexts   *)
    (* to set up $ContextPath after restore.                         *)
    FileNameJoin[{repoRoot, "tests", "build_snapshot.wls"}],
    FileNameJoin[{repoRoot, "tests", "run_fast.wls"}]
  };

  files = Complement[files, allowedFiles];

  violations = Reap[
    Scan[
      Function[f,
        Module[{lines = StringSplit[Import[f, "Text"], "\n"], i},
          Do[
            If[StringContainsQ[lines[[i]], "HOL`Kernel`Private`"],
              Sow[{f, i, StringTake[lines[[i]], UpTo[80]]}]
            ],
            {i, Length[lines]}
          ]
        ]
      ],
      files
    ]
  ][[2]];

  If[violations === {},
    Print["[lint] OK: no `HOL`Kernel`Private`*` references outside Kernel.wl"];
    Exit[0]
  ];

  violations = First[violations];
  Print["[lint] FAIL: ", Length[violations],
    " trust-boundary violation(s) — references to HOL`Kernel`Private` outside Kernel.wl:"];
  Scan[
    Function[v,
      Print["  ", FileNameTake[v[[1]], -2], ":", v[[2]], "    ", v[[3]]]
    ],
    violations];
  Exit[1]
]
