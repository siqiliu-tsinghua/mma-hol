(* ::Package:: *)

(* M7-α MESON — Model Elimination tactic for first-order HOL.

   Skeleton (M7-α-1):  public entry points sign to noTac. Subsequent
   commits fill in preprocessing (M7-α-2), search (M7-α-3), proof
   reconstruction (M7-α-4), and Brand modification for equality (M7-α-5).

   Trust boundary: search runs in untrusted code. Proof reconstruction
   in M7-α-4 will replay the search trace through the kernel's 10
   primitive rules, so a bug in search at worst means "can't prove",
   never "produces a false theorem". *)

BeginPackage["HOL`Auto`Meson`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Tactics`"
}];

MESON::usage =
  "MESON[thms_List][g_goal] — Model Elimination tactic. Negates the goal, " <>
  "preprocesses (NNF / Skolemize / CNF), runs iterative-deepening connection " <>
  "tableaux against the negated goal + thms as oriented clauses, then replays " <>
  "the refutation as a HOL proof. Skeleton in M7-α-1 signs to noTac.";

mesonProve::usage =
  "mesonProve[tm_, thms_List] — proof builder counterpart of MESON. " <>
  "Skeleton in M7-α-1 throws 'meson' tag.";

mesonMaxDepth::usage =
  "mesonMaxDepth — Integer, the iterative-deepening cap. Default 50; " <>
  "raise if you hit 'depth exceeded' on theorems known to be provable.";

Begin["`Private`"];

mesonMaxDepth = 50;

(* M7-α-1 stubs.  The MESON tactic and mesonProve both fail-through to
   their kernel counterparts so call sites can already wire MESON into
   THEN/ORELSE chains; they will start succeeding once M7-α-3 lands. *)

HOL`Auto`Meson`MESON[thms_List][g_goal] :=
  HOL`Tactics`noTac[g];

HOL`Auto`Meson`mesonProve[tm_, thms_List] :=
  HOL`Error`holError["meson", "mesonProve: skeleton — search not implemented yet",
    <|"goal" -> tm|>];

End[];
EndPackage[];
