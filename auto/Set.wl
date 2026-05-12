(* ::Package:: *)

(* M7-γ auto/Set.wl — SET decision procedure for set-algebraic equations.

   Strategy: given a goal `f = g` where f, g : α → bool are built from
   UNION / INTER / DIFF / EMPTY / UNIV applied to free set variables,
   close it in three steps:

     (1) function extensionality reduces `f = g` to `∀x. f x = g x`;
     (2) simpConv unfolds the set ops via their def thms, beta-reducing
         to a body where the connectives are propositional and the
         atoms are `S x` / `T x` applications of the free set vars;
     (3) propTaut closes the propositional core. Atoms like `S x` are
         abstracted to fresh bool vars at propTaut's entry, so any
         Boolean tautology over them is provable.

   The function-ext step uses etaAx + ABS: from Γ ⊢ f x = g x, ABS[x]
   gives ⊢ (λx. f x) = (λx. g x), then η on both sides chains back to
   ⊢ f = g. ISPEC handles the polymorphic instantiation of etaAx.

   Trust boundary: all reasoning goes through the kernel rules; this
   file just orchestrates simpConv + propTaut + etaAx/ABS/TRANS into a
   one-call solver. *)

BeginPackage["HOL`Auto`Set`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Tactics`", "HOL`Auto`PropTaut`", "HOL`Auto`Simp`",
  "HOL`Stdlib`Set`"
}];

setProve::usage =
  "setProve[t] — proves a set-algebraic equation `S = T` (S, T sets of "<>
  "the same α-set type, built from UNION/INTER/DIFF/EMPTY/UNIV applied "<>
  "to free set variables). Returns Γ ⊢ S = T. Closes by function "    <>
  "extensionality + simpConv (set defs) + propTaut.";

SET::usage =
  "SET[][g_goal] — tactic. Calls setProve on the goal's conclusion. "  <>
  "Closes the goal if the conclusion is a set-algebra equation.";

Begin["`Private`"];

setRules[] := {
  HOL`Stdlib`Set`unionDefThm,
  HOL`Stdlib`Set`interDefThm,
  HOL`Stdlib`Set`diffDefThm,
  HOL`Stdlib`Set`emptyDefThm,
  HOL`Stdlib`Set`univDefThm
};

pickFresh[preferred_String, forbidden_List] :=
  Module[{i, cand},
    cand = preferred; i = 0;
    While[MemberQ[forbidden, cand],
      i++; cand = preferred <> "_" <> ToString[i]];
    cand
  ];

(* funcExt: given xV, fTm, gTm, and Γ ⊢ f x = g x, lift to Γ ⊢ f = g.   *)
(* ABS[x] yields ⊢ (λx. f x) = (λx. g x); ISPEC of etaAx folds those    *)
(* outer λ's away.                                                      *)
funcExt[xV_, fTm_, gTm_, bodyTh_] :=
  Module[{absEq, etaF, etaG, symF},
    absEq = HOL`Kernel`ABS[xV, bodyTh];
    etaF = HOL`Bool`ISPEC[fTm, HOL`Bootstrap`etaAx];
    etaG = HOL`Bool`ISPEC[gTm, HOL`Bootstrap`etaAx];
    symF = HOL`Equal`SYM[etaF];
    TRANS[TRANS[symF, absEq], etaG]
  ];

setProve[goalTm_] :=
  Module[{lhs, rhs, fTy, domTy, ranTy,
          freeNames, xName, xV,
          appliedEq, simpEq, simpRhs, propTh, bodyTh},
    If[!MatchQ[goalTm, comb[comb[const["=", _], _], _]],
      HOL`Error`holError["set", "setProve: goal must be an equation",
        <|"got" -> goalTm|>]];
    lhs = goalTm[[1, 2]]; rhs = goalTm[[2]];
    fTy = typeOf[lhs];
    If[fTy =!= typeOf[rhs],
      HOL`Error`holError["set", "setProve: LHS/RHS types differ",
        <|"lhsTy" -> fTy, "rhsTy" -> typeOf[rhs]|>]];
    If[!MatchQ[fTy, tyApp["fun", {_, _}]],
      HOL`Error`holError["set",
        "setProve: equation sides must be set-typed (α → bool)",
        <|"got" -> fTy|>]];
    {domTy, ranTy} = {fTy[[2, 1]], fTy[[2, 2]]};
    If[ranTy =!= boolTy,
      HOL`Error`holError["set",
        "setProve: range type must be bool (sets are α → bool)",
        <|"got" -> ranTy|>]];

    freeNames = First /@ freesIn[goalTm];
    xName = pickFresh["x", freeNames];
    xV = mkVar[xName, domTy];

    appliedEq = mkEq[mkComb[lhs, xV], mkComb[rhs, xV]];

    (* (2) simpConv unfolds the set ops; basic schemas + def thms.       *)
    simpEq = HOL`Auto`Simp`simpConv[setRules[]][appliedEq];
    simpRhs = concl[simpEq][[2]];

    (* (3) propTaut closes the propositional core. *)
    propTh = HOL`Auto`PropTaut`propTaut[simpRhs];
    bodyTh = EQMP[HOL`Equal`SYM[simpEq], propTh];

    (* (1) Function extensionality. *)
    funcExt[xV, lhs, rhs, bodyTh]
  ];

HOL`Auto`Set`SET[][g : HOL`Tactics`goal[asms_, conclTm_]] :=
  Module[{th},
    th = setProve[conclTm];
    HOL`Tactics`tacResult[{}, Function[{thList}, th]]
  ];

End[];
EndPackage[];
