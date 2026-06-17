#!/usr/bin/env wolframscript
(* Regenerates demos/examples.nb from the verified example code below.       *)
(* Run: wolframscript -file demos/build_examples_nb.wls                       *)
(* The .nb itself is committed; rerun this only after editing the examples.  *)

repoRoot = ParentDirectory[DirectoryName[$InputFileName]];

loadCode = StringJoin[
  "(* Load the library: Stable mode + restore the prebuilt snapshot. *)\n",
  "root = ParentDirectory[NotebookDirectory[]];\n",
  "Global`$HOLEncapsulationMode = \"Stable\";\n",
  "Get[FileNameJoin[{root, \"bootstrap.mx\"}]];\n",
  "$ContextPath = Join[\n",
  "  Select[Contexts[], StringMatchQ[#, \"HOL`*\"] && ! StringContainsQ[#, \"Private`\"] &],\n",
  "  $ContextPath];"];

cells = {
  Cell["mma-hol \[Dash] Runnable Examples", "Title"],
  Cell[TextData[{
     "An LCF-style HOL theorem prover in the Wolfram Language. Evaluate the ",
     "cells top to bottom with Shift+Enter. The first cell loads the prebuilt ",
     "snapshot (",
     Cell[BoxData["bootstrap.mx"]],
     "); if it is missing, run ",
     Cell[BoxData["wolframscript -file tests/build_snapshot.wls"]],
     " in the repo root first."}], "Text"],

  Cell["Setup", "Section"],
  Cell["Load the kernel + the full standard library:", "Text"],
  Cell[loadCode, "Input"],

  Cell["1. The trusted kernel", "Section"],
  Cell["Every value of theorem type is built by the 10 primitive rules. \
formatThm renders a theorem as \[RightTee] p.", "Text"],
  Cell["formatThm[TRUTH]", "Input"],

  Cell["2. Propositional automation", "Section"],
  Cell["propTaut decides propositional tautologies and returns a kernel-checked theorem. \
parseTerm reads HOL syntax (==> implication, \\/ or, ~ not).", "Text"],
  Cell["formatThm[propTaut[parseTerm[\"p ==> p\"]]]", "Input"],
  Cell["formatThm[propTaut[parseTerm[\"p \\\\/ ~p\"]]]", "Input"],

  Cell["3. Proving with tactics", "Section"],
  Cell["prove[goal, tactic] runs a tactic against a goal and returns the discharged theorem.", "Text"],
  Cell["formatThm[prove[parseTerm[\"T\"], acceptTac[TRUTH]]]", "Input"],

  Cell["4. The standard library: marquee theorems", "Section"],
  Cell["The real numbers are built from Dedekind cuts; these are the proven capstones \
of stdlib/Real/ (all 0-sorry, rechecked by the kernel).", "Text"],
  Cell["(* Dedekind completeness: every nonempty bounded-above set has a least upper bound *)\n\
formatThm[HOL`Stdlib`Real`dedekindCompleteThm]", "Input"],
  Cell["(* Bolzano-Weierstrass *)\n\
formatThm[HOL`Stdlib`Real`bwSequentialThm]", "Input"],
  Cell["(* Heine-Borel for a closed interval *)\n\
formatThm[HOL`Stdlib`Real`compactnessPrincipleThm]", "Input"],
  Cell["(* compact <=> sequentially compact (general real sets) *)\n\
formatThm[HOL`Stdlib`Real`compactIffSequentialCompactThm]", "Input"],
  Cell["(* connected <=> interval *)\n\
formatThm[HOL`Stdlib`Real`connectedIffIntervalSetThm]", "Input"],

  Cell["Next steps", "Section"],
  Cell[TextData[{
     "See ", Cell[BoxData["README.md"]], " for the project overview and ",
     Cell[BoxData["docs/USER_GUIDE.md"]],
     " for the API and how to develop your own proofs."}], "Text"]
};

nb = Notebook[cells, WindowSize -> {800, 700}];
out = FileNameJoin[{repoRoot, "demos", "examples.nb"}];
Export[out, nb];
Print["wrote: ", out, "  bytes: ", FileByteCount[out]];
