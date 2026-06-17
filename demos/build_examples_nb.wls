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

  Cell["5. A proof from scratch, checked live", "Section"],
  Cell["The cells above only displayed finished theorems. Here we BUILD one: prove \
sets a goal, a tactic discharges it, and the kernel rechecks every step. We prove \
p /\\ q ==> q /\\ p (note the swap).", "Text"],
  Cell["goalA = parseTerm[\"p /\\\\ q ==> q /\\\\ p\"];\n\
thmA = prove[goalA,\n\
  THEN[dischTac,\n\
    THENL[conjTac, {\n\
      acceptTac[CONJUNCT2[ASSUME[goalA[[1, 2]]]]],\n\
      acceptTac[CONJUNCT1[ASSUME[goalA[[1, 2]]]]]}]]];\n\
formatThm[thmA]", "Input"],

  Cell["6. Real analysis, proved automatically", "Section"],
  Cell["realArithProve decides linear real arithmetic and emits a Farkas certificate the \
kernel replays. A few builders state the goal as a HOL term (we lift the forall/imp \
constants out of parseTerm to avoid typing Unicode), then the prover proves the midpoint \
inequality  a < b ==> a < (a+b)/2  by itself.", "Text"],
  Cell["realTy = mkType[\"real\", {}];\n\
forallName = parseTerm[\"!z. z\"][[1, 1]];\n\
impName = parseTerm[\"a ==> b\"][[1, 1, 1]];\n\
all[v_, body_] := mkComb[mkConst[forallName, tyFun[tyFun[typeOf[v], boolTy], boolTy]], mkAbs[v, body]];\n\
imp[p_, q_] := mkComb[mkComb[mkConst[impName, tyFun[boolTy, tyFun[boolTy, boolTy]]], p], q];\n\
nat[n_] := Nest[mkComb[HOL`Stdlib`Num`sucConst[], #] &, HOL`Stdlib`Num`zeroConst[], n];\n\
rnum[n_] := mkComb[HOL`Stdlib`Real`realOfRatConst[], mkComb[HOL`Stdlib`Rat`ratOfIntConst[], mkComb[HOL`Stdlib`Int`intOfNumConst[], nat[n]]]];\n\
rLt[u_, v_] := mkComb[mkComb[HOL`Stdlib`Real`realLtConst[], u], v];\n\
rAdd[u_, v_] := mkComb[mkComb[HOL`Stdlib`Real`realAddConst[], u], v];\n\
rMul[u_, v_] := mkComb[mkComb[HOL`Stdlib`Real`realMulConst[], u], v];\n\
rInv[u_] := mkComb[HOL`Stdlib`Real`realInvConst[], u];\n\
a = mkVar[\"a\", realTy]; b = mkVar[\"b\", realTy];\n\
midpoint = all[a, all[b, imp[rLt[a, b], rLt[a, rMul[rAdd[a, b], rInv[rnum[2]]]]]]];\n\
formatThm[HOL`Auto`RealArith`realArithProve[midpoint]]", "Input"],

  Cell["7. \[Dash] and the kernel will not be fooled", "Section"],
  Cell["The same prover refuses a false statement. Asked to prove  forall x y. x < y  it \
throws rather than return a theorem: that is the LCF trust boundary in action.", "Text"],
  Cell["x = mkVar[\"x\", realTy]; y = mkVar[\"y\", realTy];\n\
Catch[HOL`Auto`RealArith`realArithProve[all[x, all[y, rLt[x, y]]]], _,\n\
  Function[{v, t}, \"refused: the prover threw rather than return a theorem\"]]", "Input"],

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
