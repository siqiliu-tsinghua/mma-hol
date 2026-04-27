(* ::Package:: *)

(* M7-α MESON — Model Elimination tactic for first-order HOL.

   Trust boundary: search and preprocessing run in untrusted code.
   Proof reconstruction (M7-α-4) replays the refutation through the
   kernel's 10 primitive rules; a bug in preprocessing or search at
   worst means "can't prove", never "produces a false theorem". *)

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

mLit::usage =
  "mLit[sign, atom] — internal MESON literal node. sign : True (positive) | " <>
  "False (negated); atom is a HOL term of type bool with no propositional connectives or quantifiers.";

mClause::usage =
  "mClause[lits_List] — internal MESON clause node. Disjunction of mLit values.";

mesonNNF::usage =
  "mesonNNF[t] — Negation Normal Form. Pushes ¬ through ∧/∨/⇒/⇔/∀/∃ down to literals; expands ⇒ and ⇔ into ∧/∨; strips double negation. No-op on already-NNF formulas.";

mesonSkolemize::usage =
  "mesonSkolemize[t] — assumes input is in NNF. Walks left-to-right, replacing ∀x. P with P[x_/x] (x_ a fresh free variable, treated as a logical universal during search), and ∃x. P with P[sk(u…)/x] where sk is a fresh Skolem constant or function (registered via newConstant) applied to the universal variables in scope. Returns a quantifier-free term.";

mesonCNF::usage =
  "mesonCNF[t] — assumes input is in NNF and quantifier-free. Distributes ∨ over ∧; returns a list of mClause values (clause set, conjunction of disjunctions of literals).";

mesonClausify::usage =
  "mesonClausify[t] — full preprocessing: mesonNNF → mesonSkolemize → mesonCNF → mesonFactor. Returns a list of mClause values ready for the search engine.";

mesonFactor::usage =
  "mesonFactor[clauses_List] — within each clause: dedup literals, drop tautologies (clauses with both p and ¬p). Across clauses: dedup duplicates.";

mesonOpenSubst::usage =
  "mesonOpenSubst[body, depth, repl] — de-Bruijn opening: replaces bvar[depth, _] with repl in body, decrementing higher-level bvars by 1. Used internally; exposed for testing.";

mesonResetState::usage =
  "mesonResetState[] — reset the fresh-variable counter. (The Skolem counter is monotonic across the session because Skolem constants are registered permanently with the kernel; resetting would cause newConstant collisions.) Called at the start of each top-level MESON invocation; exposed for deterministic testing of fresh-var output.";

Begin["`Private`"];

mesonMaxDepth = 50;

$skolCounter = 0;
$freshVarCounter = 0;

HOL`Auto`Meson`mesonResetState[] := ($freshVarCounter = 0;);

freshSkolemName[] := ($skolCounter += 1; "?sk" <> ToString[$skolCounter]);

freshLogicalName[origin_String, forbidden_List] :=
  Module[{cand, i = 0},
    cand = origin;
    While[MemberQ[forbidden, cand],
      $freshVarCounter += 1;
      cand = origin <> "_" <> ToString[$freshVarCounter]
    ];
    cand
  ];

(* ============================================================ *)
(* Recognizers and destructors for HOL connectives.             *)

isAndQ[comb[comb[const["∧", _], _], _]] := True;
isAndQ[_] := False;

isOrQ[comb[comb[const["∨", _], _], _]] := True;
isOrQ[_] := False;

isImpQ[comb[comb[const["⇒", _], _], _]] := True;
isImpQ[_] := False;

isNotQ[comb[const["¬", _], _]] := True;
isNotQ[_] := False;

isForallQ[comb[const["∀", _], abs[bvar[0, _], _, _String]]] := True;
isForallQ[_] := False;

isExistsQ[comb[const["∃", _], abs[bvar[0, _], _, _String]]] := True;
isExistsQ[_] := False;

$boolEqTy = tyApp["fun", {tyApp["bool", {}], tyApp["fun", {tyApp["bool", {}], tyApp["bool", {}]}]}];

isIffQ[comb[comb[const["=", $boolEqTy], _], _]] := True;
isIffQ[_] := False;

destAnd[comb[comb[const["∧", _], p_], q_]] := {p, q};
destOr[comb[comb[const["∨", _], p_], q_]]  := {p, q};
destImp[comb[comb[const["⇒", _], p_], q_]] := {p, q};
destNot[comb[const["¬", _], p_]] := p;
destIff[comb[comb[const["=", _], p_], q_]] := {p, q};

(* Returns {bv, body, origin} of an abs-headed quantifier. *)
destForall[comb[const["∀", _], absNode_]] := absNode;
destExists[comb[const["∃", _], absNode_]] := absNode;

(* ============================================================ *)
(* Connective constructors that don't go through the kernel.    *)
(* These are below-kernel structural builders — safe because    *)
(* the constants and types come from already-registered terms.  *)

$boolBoolBoolTy = tyApp["fun", {tyApp["bool", {}], tyApp["fun", {tyApp["bool", {}], tyApp["bool", {}]}]}];
$boolBoolTy     = tyApp["fun", {tyApp["bool", {}], tyApp["bool", {}]}];

$andConst    = const["∧", $boolBoolBoolTy];
$orConst     = const["∨", $boolBoolBoolTy];
$impConst    = const["⇒", $boolBoolBoolTy];
$notConst    = const["¬", $boolBoolTy];

mkAndStruct[p_, q_] := comb[comb[$andConst, p], q];
mkOrStruct[p_, q_]  := comb[comb[$orConst, p], q];
mkImpStruct[p_, q_] := comb[comb[$impConst, p], q];
mkNotStruct[p_]     := comb[$notConst, p];

(* For ∀/∃ we need the type, since ∀ : (α → bool) → bool is polymorphic. *)
mkForallStruct[absNode_, varTy_] :=
  comb[const["∀", tyApp["fun", {tyApp["fun", {varTy, tyApp["bool", {}]}], tyApp["bool", {}]}]], absNode];
mkExistsStruct[absNode_, varTy_] :=
  comb[const["∃", tyApp["fun", {tyApp["fun", {varTy, tyApp["bool", {}]}], tyApp["bool", {}]}]], absNode];

(* ============================================================ *)
(* de-Bruijn opening: replace bvar[depth, _] with repl, shifting *)
(* deeper bvars down by 1.                                       *)

HOL`Auto`Meson`mesonOpenSubst[body_, depth_Integer, repl_] :=
  openSubstImpl[body, depth, repl];

openSubstImpl[v : var[_, _], _, _]  := v;
openSubstImpl[c : const[_, _], _, _] := c;
openSubstImpl[bvar[i_Integer, ty_], depth_Integer, repl_] :=
  Which[
    i < depth,  bvar[i, ty],
    i === depth, repl,
    True,        bvar[i - 1, ty]
  ];
openSubstImpl[comb[f_, x_], depth_Integer, repl_] :=
  comb[openSubstImpl[f, depth, repl], openSubstImpl[x, depth, repl]];
openSubstImpl[abs[bv_, body_, name_String], depth_Integer, repl_] :=
  abs[bv, openSubstImpl[body, depth + 1, repl], name];

(* ============================================================ *)
(* NNF: push ¬ to literals, expand ⇒ and ⇔.                     *)

HOL`Auto`Meson`mesonNNF[t_] := nnfImpl[t, True];

nnfImpl[t_, polarity_] :=
  Which[
    isNotQ[t], nnfImpl[destNot[t], !polarity],
    isAndQ[t],
      Module[{p, q, np, nq},
        {p, q} = destAnd[t]; np = nnfImpl[p, polarity]; nq = nnfImpl[q, polarity];
        If[polarity, mkAndStruct[np, nq], mkOrStruct[np, nq]]
      ],
    isOrQ[t],
      Module[{p, q, np, nq},
        {p, q} = destOr[t]; np = nnfImpl[p, polarity]; nq = nnfImpl[q, polarity];
        If[polarity, mkOrStruct[np, nq], mkAndStruct[np, nq]]
      ],
    isImpQ[t],
      Module[{p, q},
        {p, q} = destImp[t];
        nnfImpl[mkOrStruct[mkNotStruct[p], q], polarity]
      ],
    isIffQ[t],
      Module[{p, q},
        {p, q} = destIff[t];
        nnfImpl[mkAndStruct[mkImpStruct[p, q], mkImpStruct[q, p]], polarity]
      ],
    isForallQ[t],
      Module[{absNode, bv, body, origin, newBody, ty},
        absNode = destForall[t];
        bv = absNode[[1]]; body = absNode[[2]]; origin = absNode[[3]];
        ty = bv[[2]];
        newBody = nnfImpl[body, polarity];
        If[polarity,
          mkForallStruct[abs[bv, newBody, origin], ty],
          mkExistsStruct[abs[bv, newBody, origin], ty]
        ]
      ],
    isExistsQ[t],
      Module[{absNode, bv, body, origin, newBody, ty},
        absNode = destExists[t];
        bv = absNode[[1]]; body = absNode[[2]]; origin = absNode[[3]];
        ty = bv[[2]];
        newBody = nnfImpl[body, polarity];
        If[polarity,
          mkExistsStruct[abs[bv, newBody, origin], ty],
          mkForallStruct[abs[bv, newBody, origin], ty]
        ]
      ],
    True,  (* atomic literal *)
      If[polarity, t, mkNotStruct[t]]
  ];

(* ============================================================ *)
(* Skolemization.  Walks NNF term left to right, accumulating    *)
(* the universal-variable scope as a list of free vars. Each ∀   *)
(* opens to a fresh free variable; each ∃ opens to a Skolem term *)
(* (fresh constant applied to the current universal scope).      *)

HOL`Auto`Meson`mesonSkolemize[t_] := skolemizeImpl[t, {}, freeNamesOf[t]];

freeNamesOf[t_] := DeleteDuplicates[Cases[t, var[n_String, _] :> n, {0, Infinity}]];

(* skolemizeImpl[t, univScope, forbiddenNames] *)
skolemizeImpl[t_, univ_List, forbidden_List] :=
  Which[
    isForallQ[t],
      Module[{absNode, bv, body, origin, ty, freshN, v, opened},
        absNode = destForall[t];
        bv = absNode[[1]]; body = absNode[[2]]; origin = absNode[[3]];
        ty = bv[[2]];
        freshN = freshLogicalName[origin, forbidden];
        v = var[freshN, ty];
        opened = openSubstImpl[body, 0, v];
        skolemizeImpl[opened, Append[univ, v], Append[forbidden, freshN]]
      ],
    isExistsQ[t],
      Module[{absNode, bv, body, origin, ty, skName, skTy, skTerm, opened},
        absNode = destExists[t];
        bv = absNode[[1]]; body = absNode[[2]]; origin = absNode[[3]];
        ty = bv[[2]];
        skName = freshSkolemName[];
        skTy = Fold[tyApp["fun", {#2[[2]], #1}] &, ty, Reverse[univ]];
        HOL`Kernel`newConstant[skName, skTy];
        skTerm = Fold[comb[#1, #2] &, const[skName, skTy], univ];
        opened = openSubstImpl[body, 0, skTerm];
        skolemizeImpl[opened, univ, forbidden]
      ],
    isAndQ[t],
      Module[{p, q},
        {p, q} = destAnd[t];
        mkAndStruct[skolemizeImpl[p, univ, forbidden],
                    skolemizeImpl[q, univ, forbidden]]
      ],
    isOrQ[t],
      Module[{p, q},
        {p, q} = destOr[t];
        mkOrStruct[skolemizeImpl[p, univ, forbidden],
                   skolemizeImpl[q, univ, forbidden]]
      ],
    isNotQ[t], mkNotStruct[skolemizeImpl[destNot[t], univ, forbidden]],
    True, t
  ];

(* ============================================================ *)
(* CNF conversion.  Input must be quantifier-free, NNF.          *)
(* Output: list of mClause values.                               *)

HOL`Auto`Meson`mesonCNF[t_] := cnfImpl[t];

cnfImpl[t_] :=
  Which[
    isAndQ[t],
      Module[{p, q}, {p, q} = destAnd[t]; Join[cnfImpl[p], cnfImpl[q]]],
    isOrQ[t],
      Module[{p, q, lefts, rights},
        {p, q} = destOr[t];
        lefts = cnfImpl[p]; rights = cnfImpl[q];
        Flatten[Outer[mergeClauses, lefts, rights, 1]]
      ],
    isNotQ[t], {mClause[{mLit[False, destNot[t]]}]},
    True,      {mClause[{mLit[True,  t]}]}
  ];

mergeClauses[mClause[ls1_], mClause[ls2_]] := mClause[Join[ls1, ls2]];

(* ============================================================ *)
(* Factoring: dedup literals within a clause, drop tautologies   *)
(* (clauses containing both p and ¬p), dedup clauses across set. *)

HOL`Auto`Meson`mesonFactor[clauses_List] :=
  DeleteDuplicates[Select[Map[factorClause, clauses], ! tautologyQ[#] &]];

factorClause[mClause[lits_]] := mClause[DeleteDuplicates[lits]];

tautologyQ[mClause[lits_]] :=
  AnyTrue[lits, Function[lit,
    MemberQ[lits, mLit[!lit[[1]], lit[[2]]]]]];

(* ============================================================ *)
(* Full pipeline.                                                *)

HOL`Auto`Meson`mesonClausify[t_] :=
  Module[{nnf, skol, clauses},
    nnf = nnfImpl[t, True];
    skol = skolemizeImpl[nnf, {}, freeNamesOf[nnf]];
    clauses = cnfImpl[skol];
    HOL`Auto`Meson`mesonFactor[clauses]
  ];

(* ============================================================ *)
(* M7-α-1 stubs for MESON / mesonProve.  M7-α-3 will replace.   *)

HOL`Auto`Meson`MESON[thms_List][g_goal] :=
  HOL`Tactics`noTac[g];

HOL`Auto`Meson`mesonProve[tm_, thms_List] :=
  HOL`Error`holError["meson", "mesonProve: search not implemented yet",
    <|"goal" -> tm|>];

End[];
EndPackage[];
