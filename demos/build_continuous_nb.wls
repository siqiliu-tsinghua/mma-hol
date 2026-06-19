#!/usr/bin/env wolframscript
(* Regenerates demos/continuous.nb. Run: wolframscript -file demos/build_continuous_nb.wls *)

repoRoot = ParentDirectory[DirectoryName[$InputFileName]];

loadCode = StringJoin[
  "(* Load the kernel + stdlib snapshot, then the (demo) continuity theory. *)\n",
  "root = ParentDirectory[NotebookDirectory[]];\n",
  "Global`$HOLEncapsulationMode = \"Stable\";\n",
  "Get[FileNameJoin[{root, \"bootstrap.mx\"}]];\n",
  "$ContextPath = Join[\n",
  "  Select[Contexts[], StringMatchQ[#, \"HOL`*\"] && ! StringContainsQ[#, \"Private`\"] &],\n",
  "  $ContextPath];\n",
  "Get[FileNameJoin[{root, \"demos\", \"Continuous.wl\"}]];\n",
  "$ContextPath = Prepend[$ContextPath, \"HOL`Demos`Continuous`\"];"];

cells = {
  Cell["Continuous functions on a closed interval", "Title"],
  Cell[TextData[{
     "Continuous functions are NOT part of this library's real-number theory \[Dash] ",
     "in the Lean blueprint they are the next chapter. But the point-set topology we ",
     "already have (open / closed / compact / connected) makes the classical theorems ",
     "on a closed interval fall out cheaply. Everything below is kernel-checked, 0-sorry, ",
     "and lives in the demo file ", Cell[BoxData["demos/Continuous.wl"]], ". Evaluate the ",
     "cells top to bottom (Shift+Enter)."}], "Text"],

  Cell["Setup", "Section"],
  Cell["Load the kernel + stdlib snapshot and the continuity development:", "Text"],
  Cell[loadCode, "Input"],

  Cell["1. Continuity, topologically", "Section"],
  Cell[TextData[{
     "We use the topological definition: f is continuous when the preimage of every ",
     "open set is open. No epsilons, no limits \[Dash] just ",
     Cell[BoxData["isOpen"]], " and ", Cell[BoxData["PREIMAGE"]], "."}], "Text"],
  Cell["formatThm[continuousDefThm]", "Input"],

  Cell["2. The two image theorems", "Section"],
  Cell["The continuous image of a compact set is compact (pull an open cover of the \
image back through f, take a finite subcover, push it forward):", "Text"],
  Cell["formatThm[continuousImageCompactThm]", "Input"],
  Cell["The continuous image of a connected set is connected (a separation of the image \
pulls back to a separation of the domain):", "Text"],
  Cell["formatThm[continuousImageConnectedThm]", "Input"],

  Cell["3. A closed interval is compact", "Section"],
  Cell["[a,b] is closed (Topology) and bounded (lo=a, hi=b), hence compact:", "Text"],
  Cell["formatThm[closedIntervalCompactThm]", "Input"],

  Cell["4. Boundedness on [a,b]", "Section"],
  Cell["[a,b] is compact, so its continuous image is compact, hence closed and bounded \
\[Dash] in particular bounded. A continuous function on a closed interval is bounded:", "Text"],
  Cell["formatThm[continuousImageBoundedThm]", "Input"],

  Cell["5. The intermediate value theorem", "Section"],
  Cell[TextData[{
     "[a,b] is also connected, so its continuous image is connected, hence an interval. ",
     "Since the image contains f(a) and f(b), it contains every value between them ",
     "\[Dash] the function-form IVT, proved from pure topology with no continuous-",
     "function analysis:"}], "Text"],
  Cell["formatThm[continuousIVTThm]", "Input"],

  Cell["6. The extreme value theorem", "Section"],
  Cell[TextData[{
     "The image of [a,b] is also compact, hence closed and bounded, so its supremum ",
     "is attained: there is a point where f reaches its maximum. The proof builds a ",
     "sequence approaching the supremum (each term within ",
     Cell[BoxData["1/(n+1)"]], " of it), uses that a closed set contains its sequential ",
     "limits, and reads the maximiser off the resulting image membership:"}], "Text"],
  Cell["formatThm[continuousEVTThm]", "Input"],

  Cell["A live check", "Section"],
  Cell["Each statement above is a real theorem object; the kernel built it. For example, \
the EVT has no hypotheses beyond the ones shown, and is genuinely a theorem:", "Text"],
  Cell["{isThm[continuousEVTThm], hyp[continuousEVTThm]}", "Input"],

  Cell["Next steps", "Section"],
  Cell[TextData[{
     "See ", Cell[BoxData["demos/Continuous.wl"]], " for the proofs and ",
     Cell[BoxData["docs/USER_GUIDE.md"]], " for the API."}], "Text"]
};

nb = Notebook[cells, WindowSize -> {820, 720}];
out = FileNameJoin[{repoRoot, "demos", "continuous.nb"}];
Export[out, nb];
Print["wrote: ", out, "  bytes: ", FileByteCount[out]];
