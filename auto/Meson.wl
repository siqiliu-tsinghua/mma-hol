(* ::Package:: *)

(* M7-α MESON — Model Elimination tactic for first-order HOL.

   Trust boundary: search and preprocessing run in untrusted code.
   Proof reconstruction (M7-α-4) replays the refutation through the
   kernel's 10 primitive rules; a bug in preprocessing or search at
   worst means "can't prove", never "produces a false theorem". *)

BeginPackage["HOL`Auto`Meson`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Tactics`", "HOL`Auto`PropTaut`"
}];

MESON::usage =
  "MESON[thms_List][g_goal] — Model Elimination tactic. Negates the goal, " <>
  "preprocesses (NNF / Skolemize / CNF), runs iterative-deepening connection " <>
  "tableaux against the negated goal + thms as oriented clauses, then replays " <>
  "the refutation as a HOL proof. Skeleton in M7-α-1 signs to noTac.";

mesonProve::usage =
  "mesonProve[tm_, thms_List] — proof builder counterpart of MESON. " <>
  "Skeleton in M7-α-1 throws 'meson' tag.";

mesonProveProp::usage =
  "mesonProveProp[goal, premiseThms] — propositional MESON proof builder " <>
  "(M7-α-4-c). Negates goal, clausifies premises + ¬goal via PropTaut, runs " <>
  "mesonRefute, replays the trace through HOL Light-style contrapositive MP " <>
  "chains, returns ⊢ goal under premise hypotheses. Start clauses with k>1 " <>
  "literals are handled by per-lit ASSUME + right-folded DISJCASES on the " <>
  "original clause theorem. Atoms must be bool-typed free vars or boolean " <>
  "constants (no quantifiers, no first-order Skolemization — α-4-d).";

clausifyFOLThm::usage =
  "clausifyFOLThm[Γ ⊢ φ] — full thm-layer clausifier (α-4-d-β). Applies " <>
  "nnfThm, then walks the result splitting top-level ∧ via CONJUNCT1/2, " <>
  "specializing top-level ∀ to a fresh free variable via SPEC, and " <>
  "Skolemizing top-level ∃ via selectAx + newDefinition (NYI; α-4-d-β-2). " <>
  "Falls through to cnfThm + splitConjThm on quantifier-free leaves. " <>
  "Returns a list of clause theorems whose conjunction is propositionally " <>
  "equivalent (modulo Skolem definitions) to φ.";

specWithFreshName::usage =
  "specWithFreshName[Γ ⊢ ∀x. P x] — SPEC the universal with a fresh free " <>
  "variable name (avoiding collisions with hypotheses, conclusion, and " <>
  "registered constants). Returns Γ ⊢ P[x_fresh].";

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

mesonUnify::usage =
  "mesonUnify[t1, t2, σ] — Robinson-style MGU on first-order HOL terms. Substitution σ is an Association from var-name strings to terms. Returns extended substitution on success or the sentinel mesonUnifyFailed on failure. Free vars (var[name, ty]) are logical (instantiable); constants and bound vars are rigid. Includes occurs check.";

mesonUnifyFailed::usage =
  "mesonUnifyFailed — sentinel returned by mesonUnify on failure.";

mesonRefute::usage =
  "mesonRefute[clauses_List, maxDepth_Integer] — top-level search. Iterative deepening from depth 0 to maxDepth on a Model Elimination tableaux. Returns the trace (a mProof tree) on success or mesonRefuteFailed if no refutation found within bound. The clause set is assumed unsatisfiable for a successful call (i.e., the input is the clausified negated goal ∧ premises).";

mesonRefuteFailed::usage =
  "mesonRefuteFailed — sentinel returned by mesonRefute when no refutation is found.";

mProof::usage =
  "mProof[kind, …] — internal proof-trace node. Four kinds: " <>
  "mProof[\"start\", clause, tag, subTrees] — search picked clause as root with rename-tag tag; subTrees is the list of sub-proofs closing each lit of clause (one per lit, sharing the empty initial ancestor list). " <>
  "mProof[\"empty\", clause] — clause was empty (vacuous refutation). " <>
  "mProof[\"extension\", lit, clause, tag, pivotLit, σ, subTrees] — closed lit by extending against the (tagged copy of) clause's pivotLit; tag is the per-step rename tag (replay re-tags the contrapositive rule with this tag before applying σ); subTrees is the list of sub-proofs closing each non-pivot lit of clause (each sees ancestors = lit :: caller-ancestors). An empty subTrees list represents a unit-pivot extension that closes immediately. " <>
  "mProof[\"reduction\", lit, ancestor, σ] — closed lit by unifying with path ancestor; leaf node (no further subgoals, no fresh tag).";

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
(* MGU — Robinson-style first-order unification.                 *)

mesonUnifyFailedTag = "$mesonUnifyFailed$";
HOL`Auto`Meson`mesonUnifyFailed = mesonUnifyFailedTag;

(* Apply substitution to a term.  σ is an Association name → term. *)
applySubstTerm[σ_Association, t_] :=
  If[Length[σ] === 0, t,
    t /. var[n_String, ty_] :> Lookup[σ, n, var[n, ty]]
  ];

(* Walk substitution chains: apply σ repeatedly to a single var until stable. *)
walkVar[name_String, ty_, σ_Association] :=
  Module[{cur = var[name, ty], next, n2},
    While[MatchQ[cur, var[n2_String, _]] && KeyExistsQ[σ, cur[[1]]],
      cur = σ[cur[[1]]]
    ];
    cur
  ];

typeOfFOTerm[var[_, ty_]]      := ty;
typeOfFOTerm[const[_, ty_]]    := ty;
typeOfFOTerm[bvar[_, ty_]]     := ty;
typeOfFOTerm[comb[f_, _]]      := typeOfFOTerm[f] /. tyApp["fun", {_, b_}] :> b;

HOL`Auto`Meson`mesonUnify[t1_, t2_, σ_Association] :=
  unifyImpl[t1, t2, σ];

unifyImpl[t1_, t2_, σ_] :=
  Module[{a, b},
    a = If[MatchQ[t1, var[_, _]], walkVar[t1[[1]], t1[[2]], σ], t1];
    b = If[MatchQ[t2, var[_, _]], walkVar[t2[[1]], t2[[2]], σ], t2];
    Which[
      a === b, σ,
      MatchQ[a, var[_, _]], unifyVarBind[a, b, σ],
      MatchQ[b, var[_, _]], unifyVarBind[b, a, σ],
      MatchQ[a, comb[_, _]] && MatchQ[b, comb[_, _]],
        Module[{σ1},
          σ1 = unifyImpl[a[[1]], b[[1]], σ];
          If[σ1 === mesonUnifyFailedTag, mesonUnifyFailedTag,
            unifyImpl[a[[2]], b[[2]], σ1]]
        ],
      MatchQ[a, const[_, _]] && MatchQ[b, const[_, _]],
        If[a === b, σ, mesonUnifyFailedTag],
      MatchQ[a, bvar[_, _]] && MatchQ[b, bvar[_, _]],
        If[a === b, σ, mesonUnifyFailedTag],
      True, mesonUnifyFailedTag
    ]
  ];

(* Bool-typed vars represent atomic propositions (rigid).  Other types  *)
(* are first-order logical vars (instantiable).  A bool-typed var only  *)
(* unifies with a syntactically identical term.                         *)
unifyVarBind[var[n_String, ty_], t_, σ_] :=
  Module[{tWalked},
    tWalked = applySubstTerm[σ, t];
    If[tWalked === var[n, ty], σ,
      If[ty === tyApp["bool", {}], mesonUnifyFailedTag,
        If[typeOfFOTerm[tWalked] =!= ty, mesonUnifyFailedTag,
          If[occursIn[n, tWalked, σ], mesonUnifyFailedTag,
            Append[σ, n -> tWalked]
          ]
        ]
      ]
    ]
  ];

occursIn[name_String, t_, σ_] :=
  MemberQ[
    Cases[applySubstTerm[σ, t], var[m_String, _] :> m, {0, Infinity}],
    name];

(* ============================================================ *)
(* Renaming apart: append a unique tag to all var names.        *)
(* Skolem constants (const[...]) are rigid and stay shared.     *)

$mesonRenameCounter = 0;

(* Bool-typed free vars are propositional atoms (rigid). Other types   *)
(* are first-order logical vars (instantiable, must be apart per use). *)
(* Returns the pair {renamedClause, tag}. Tag is recorded in the trace *)
(* so replay can re-rename the corresponding contrapositive rule and   *)
(* clauseThm consistently before applying σ_final via INST.            *)
renameClauseApart[mClause[lits_]] :=
  Module[{tag, lits2},
    $mesonRenameCounter += 1;
    tag = "@" <> ToString[$mesonRenameCounter];
    lits2 = lits /. v : var[name_String, ty_] :>
      If[ty === tyApp["bool", {}], v, var[name <> tag, ty]];
    {mClause[lits2], tag}
  ];

(* ============================================================ *)
(* Search.  Model elimination with iterative deepening.          *)
(*                                                                *)
(* Two-layer expander, mirroring HOL Light meson.ml.              *)
(*   expandOne[lit, ancestors, depth, σ, clauses]                *)
(*     — close one goal literal. Pushes lit onto ancestors only  *)
(*       when descending into its own new subgoals, never into   *)
(*       siblings at the caller's level.                          *)
(*   expandSiblings[lits, ancestors, depth, σ, clauses]          *)
(*     — close a list of goals that share the SAME ancestors      *)
(*       (start-clause lits, or non-pivot lits from one extension *)
(*       step). σ and depth thread sequentially across siblings.  *)
(*                                                                *)
(* The previous single-function implementation linearized lits   *)
(* into one chain and prepended the just-extended lit onto the   *)
(* ancestors of the entire `Join[newSubgoals, rest]`. That made  *)
(* a sibling at the caller's level inherit a parent it doesn't   *)
(* actually descend from — sound only when the rest list happens *)
(* to be Horn (≤ one new subgoal per extension).                  *)

mesonAttemptTag = "$mesonAttempt$";
HOL`Auto`Meson`mesonRefuteFailed = "$mesonRefuteFailed$";

oppositeSign[mLit[s1_, _], mLit[s2_, _]] := s1 =!= s2;

HOL`Auto`Meson`mesonRefute[clauses_List, maxDepth_Integer] :=
  Module[{result = HOL`Auto`Meson`mesonRefuteFailed, depth = 0, found = False},
    While[!found && depth <= maxDepth,
      result = mesonSearchAtDepth[clauses, depth];
      If[result =!= HOL`Auto`Meson`mesonRefuteFailed, found = True];
      depth += 1
    ];
    result
  ];

mesonSearchAtDepth[clauses_List, depth_Integer] :=
  Catch[
    Module[{renPair, cRen, tag, startLits, result},
      Do[
        renPair = renameClauseApart[c0];
        cRen = renPair[[1]]; tag = renPair[[2]];
        startLits = cRen[[1]];
        If[startLits === {},
          Throw[mProof["empty", c0], mesonAttemptTag]
        ];
        result = expandSiblings[startLits, {}, depth, <||>, clauses];
        If[result[[1]],
          Throw[mProof["start", c0, tag, result[[4]]], mesonAttemptTag]
        ],
        {c0, clauses}
      ];
      HOL`Auto`Meson`mesonRefuteFailed
    ],
    mesonAttemptTag
  ];

(* {True, σ', depthLeft, subTrees} on success | {False}. Empty list   *)
(* succeeds at any depth with no subTrees; non-empty at depth=0 fails *)
(* (matches the previous behavior — extensions cost depth, reductions *)
(* don't, but a goal cannot even be considered when depth is exhausted *)
(* if there's no ancestor to close it against and we haven't tried).  *)
expandSiblings[{}, _, depth_, σ_, _] := {True, σ, depth, {}};

expandSiblings[lits_List, ancestors_, depth_Integer, σ_, allClauses_] :=
  Module[{first, rest, firstR, restR},
    first = First[lits];
    rest  = Rest[lits];
    firstR = expandOne[first, ancestors, depth, σ, allClauses];
    If[!firstR[[1]], Return[{False}]];
    restR  = expandSiblings[rest, ancestors, firstR[[3]], firstR[[2]], allClauses];
    If[!restR[[1]], Return[{False}]];
    {True, restR[[2]], restR[[3]], Prepend[restR[[4]], firstR[[4]]]}
  ];

(* {True, σ', depthLeft, tree} on success | {False}. *)
expandOne[lit_, ancestors_, depth_Integer, σ_, allClauses_] :=
  If[depth === 0, {False},
    Catch[
      Module[{},
        Do[
          If[oppositeSign[lit, anc],
            Module[{σ1},
              σ1 = unifyImpl[lit[[2]], anc[[2]], σ];
              If[σ1 =!= mesonUnifyFailedTag,
                Throw[
                  {True, σ1, depth,
                    mProof["reduction", lit, anc, σ1]},
                  mesonAttemptTag]
              ]
            ]
          ],
          {anc, ancestors}
        ];
        Do[
          Module[{renPair, cRen, cTag, cLits},
            renPair = renameClauseApart[c];
            cRen  = renPair[[1]]; cTag = renPair[[2]];
            cLits = cRen[[1]];
            Do[
              If[oppositeSign[lit, litC],
                Module[{σ1, newSubgoals, sub},
                  σ1 = unifyImpl[lit[[2]], litC[[2]], σ];
                  If[σ1 =!= mesonUnifyFailedTag,
                    newSubgoals = DeleteCases[cLits, litC, 1, 1];
                    sub = expandSiblings[
                      newSubgoals,
                      Prepend[ancestors, lit],
                      depth - 1,
                      σ1,
                      allClauses
                    ];
                    If[sub[[1]],
                      Throw[
                        {True, sub[[2]], sub[[3]],
                          mProof["extension", lit, c, cTag, litC, σ1, sub[[4]]]},
                        mesonAttemptTag]
                    ]
                  ]
                ]
              ],
              {litC, cLits}
            ]
          ],
          {c, allClauses}
        ];
        {False}
      ],
      mesonAttemptTag
    ]
  ];

(* ============================================================ *)
(* M7-α-4-c — Propositional proof reconstruction.                *)
(*                                                                *)
(* Walks the linearized mProof trace and replays each closure as  *)
(* a HOL theorem combination. Each "open lit" L corresponds to a  *)
(* hypothesis ⊢ L_term in the current branch; closing it produces *)
(* ⊢ F under that hypothesis. Extension uses the pre-built        *)
(* contrapositive rule (from clausifyContrapositives), MPing in   *)
(* the ⊢ ¬Lⱼ for each non-pivot subgoal (recursively closed).     *)

(* === Helpers for matching trace lits to clause records. ====== *)

stripTagAtom[t_] :=
  t /. var[name_String, ty_] :>
    Module[{idx = StringPosition[name, "@"]},
      If[idx === {}, var[name, ty],
        var[StringTake[name, idx[[1, 1]] - 1], ty]]];

stripTagLit[mLit[s_, atom_]] := mLit[s, stripTagAtom[atom]];

collectDisjunctTerms[t_] :=
  If[isOrQ[t],
    Module[{p, q}, {p, q} = destOr[t];
      Join[collectDisjunctTerms[p], collectDisjunctTerms[q]]],
    {t}];

litTermToMLit[t_] :=
  If[isNotQ[t], mLit[False, destNot[t]], mLit[True, t]];

mLitToTerm[mLit[True, atom_]]  := atom;
mLitToTerm[mLit[False, atom_]] := mkNotStruct[atom];

buildClauseRecord[clauseThm_] :=
  Module[{lits},
    lits = Map[litTermToMLit, collectDisjunctTerms[concl[clauseThm]]];
    <|
      "thm"     -> clauseThm,
      "mClause" -> mClause[lits],
      "lits"    -> lits,
      "rules"   -> HOL`Auto`PropTaut`clausifyContrapositives[clauseThm]
    |>
  ];

findRecordByMClause[clauseInfos_List, c_] :=
  SelectFirst[clauseInfos, #["mClause"] === c &];

findPivotIdx[record_, pivotLit_] :=
  Module[{stripped, pos},
    stripped = stripTagLit[pivotLit];
    pos = Position[record["lits"], stripped, {1}, 1];
    If[pos === {},
      HOL`Error`holError["meson",
        "findPivotIdx: pivot not in clause record",
        <|"pivot" -> pivotLit, "lits" -> record["lits"]|>]];
    pos[[1, 1]]
  ];

(* From `Γ ⊢ F` (with hyp Lⱼ_term in Γ), derive `Γ\{Lⱼ_term} ⊢ negate(Lⱼ)`. *)
(* atomTerm is the atom of Lⱼ in whatever form (tagged or σ-instantiated)  *)
(* matches the hyp in fThm — i.e. the same form that was ASSUMEd to start  *)
(* the subgoal closure.                                                    *)
fromFalseToNegLitTerm[sign_, atomTerm_, fThm_] :=
  If[sign === True,
    HOL`Bool`NOTINTRO[HOL`Bool`DISCH[atomTerm, fThm]],
    HOL`Bool`CCONTR[atomTerm, fThm]];

(* === Tag-rename and σ helpers (M7-α-4-d-α). =================== *)
(* renameClauseApart appends "@N" to non-bool var names per clause copy.  *)
(* The contrapositive rules (built from un-tagged clauseThms) and the     *)
(* clauseThms themselves must be re-tagged at replay so structural MP     *)
(* against the search's tagged σ bindings goes through.                   *)

(* Apply tag to non-bool var names in a term. Bool vars are propositional *)
(* atoms (rigid in unification) and stay un-tagged.                       *)
applyTagToTerm[t_, ""] := t;
applyTagToTerm[t_, tag_String] :=
  t /. v : var[name_String, ty_] :>
    If[ty === tyApp["bool", {}], v, var[name <> tag, ty]];

applyTagToMLit[mLit[s_, atom_], tag_String] :=
  mLit[s, applyTagToTerm[atom, tag]];

(* Tag-rename a HOL theorem's non-bool free vars via INST. Hyps and concl *)
(* are both rewritten consistently.                                       *)
applyTagToThm[thm_, ""] := thm;
applyTagToThm[thm_, tag_String] :=
  Module[{frees, nonBoolFrees, subst},
    frees = Cases[concl[thm], var[_String, _], {0, Infinity}];
    Do[frees = Union[frees, Cases[h, var[_String, _], {0, Infinity}]],
       {h, hyp[thm]}];
    nonBoolFrees = Select[DeleteDuplicates[frees], typeOf[#] =!= boolTy &];
    subst = Association[
      Map[Function[v, v -> var[v[[1]] <> tag, v[[2]]]], nonBoolFrees]];
    If[Length[subst] === 0, thm, INST[subst, thm]]
  ];

(* σ from the search is keyed by var-name strings; values may themselves  *)
(* contain σ-bound vars (Robinson MGU does only one-level walking inside  *)
(* unify). walkTermFinal applies σ recursively to fixpoint.               *)
walkTermFinal[t_, σ_Association] :=
  If[Length[σ] === 0, t,
    t /. v : var[n_String, ty_] :>
      Module[{val = Lookup[σ, n, $missingMesonSigma]},
        If[val === $missingMesonSigma, v, walkTermFinal[val, σ]]
      ]];

(* Convert a fully-walked σ to an INST-shaped substitution Association,  *)
(* keyed by var (with type taken from the walked value).                 *)
sigmaToInstSubst[σ_Association] :=
  Association[
    KeyValueMap[Function[{n, val},
      With[{walked = walkTermFinal[val, σ]},
        var[n, typeOf[walked]] -> walked
      ]
    ], σ]
  ];

(* Walk through the trace and find the deepest σ — this is σ_final since *)
(* σ accumulates monotonically across siblings and into subtrees.        *)
extractFinalSigma[mProof["start", _, _, subTrees_List]] :=
  If[subTrees === {}, <||>, extractFinalSigma[Last[subTrees]]];
extractFinalSigma[mProof["empty", _]] := <||>;
extractFinalSigma[mProof["extension", _, _, _, _, σ_, subTrees_List]] :=
  If[subTrees === {}, σ, extractFinalSigma[Last[subTrees]]];
extractFinalSigma[mProof["reduction", _, _, σ_]] := σ;

(* After INSTing σ_walked, any tagged free var that wasn't bound during  *)
(* unification (a "free logical variable") still carries its `@N` suffix. *)
(* Rename each back toward its base name, falling back to base_<i> if    *)
(* needed to avoid colliding with another free var already in the thm.   *)
stripVarTag[name_String] :=
  Module[{idx = StringPosition[name, "@"]},
    If[idx === {}, name, StringTake[name, idx[[1, 1]] - 1]]];

untagThm[thm_] :=
  Module[{allFrees, taggedFrees, untaggedNames, subst, used},
    allFrees = Cases[concl[thm], var[_String, _], {0, Infinity}];
    Do[allFrees = Union[allFrees, Cases[h, var[_String, _], {0, Infinity}]],
       {h, hyp[thm]}];
    allFrees      = DeleteDuplicates[allFrees];
    taggedFrees   = Select[allFrees, StringContainsQ[#[[1]], "@"] &];
    untaggedNames = Map[#[[1]] &, Complement[allFrees, taggedFrees]];
    used  = Association[Map[# -> True &, untaggedNames]];
    subst = <||>;
    Do[
      Module[{base = stripVarTag[v[[1]]], cand, i},
        cand = base; i = 0;
        While[KeyExistsQ[used, cand], i++; cand = base <> "_" <> ToString[i]];
        used[cand] = True;
        subst[v]   = var[cand, v[[2]]]
      ],
      {v, taggedFrees}
    ];
    If[Length[subst] === 0, thm, INST[Normal[subst], thm]]
  ];

(* === Replay drivers. ========================================= *)
(* closeLitProp / closeReductionProp / closeExtensionProp each   *)
(* return a single fThm (`Γ ⊢ ⊥`).  No leftover-trace threading: *)
(* every subTree is consumed in full by exactly one call.        *)
(*                                                                *)
(* σ + σInst threading (M7-α-4-d-α): all theorems flowing through *)
(* the replay are pre-INSTed with σ_walked.  litThm is INSTed by  *)
(* the caller before recursion; rules are tag-renamed then INSTed *)
(* at the extension step; subgoal ASSUMEs use σ-instantiated     *)
(* terms so structural MP / DISCH / CCONTR aligns without a       *)
(* second pass.                                                   *)

closeLitProp[lit_, litThm_, ancestorBindings_, trace_, clauseInfos_, σ_, σInst_] :=
  Switch[trace[[1]],
    "reduction",
      closeReductionProp[lit, litThm, ancestorBindings, trace],
    "extension",
      closeExtensionProp[lit, litThm, ancestorBindings, trace, clauseInfos, σ, σInst],
    _,
      HOL`Error`holError["meson",
        "closeLitProp: unexpected trace kind",
        <|"kind" -> trace[[1]]|>]];

closeReductionProp[
    lit_, litThm_, ancestorBindings_,
    mProof["reduction", _, anc_, _]] :=
  Module[{strippedAnc, ancEntry, ancThm},
    strippedAnc = stripTagLit[anc];
    ancEntry = SelectFirst[ancestorBindings, #[[1]] === strippedAnc &];
    If[MissingQ[ancEntry],
      HOL`Error`holError["meson",
        "closeReductionProp: ancestor not bound",
        <|"anc" -> anc|>]];
    ancThm = ancEntry[[2]];
    (* litThm and ancThm are both already σ-INSTed by their callers, so   *)
    (* their atoms must match structurally for NOTELIM/MP to compose.     *)
    If[lit[[1]] === True,
      HOL`Bool`MP[HOL`Bool`NOTELIM[ancThm], litThm],
      HOL`Bool`MP[HOL`Bool`NOTELIM[litThm], ancThm]]
  ];

closeExtensionProp[
    lit_, litThm_, ancestorBindings_,
    mProof["extension", _, c_, cTag_String, pivotLit_, _, subTrees_List],
    clauseInfos_, σ_, σInst_] :=
  Module[{record, pivotIdx, ruleThm, instedRule, subgoalLits,
          currentRule, j, Lj, LjTermInst, LjAssume, fThmJ, negLjThm,
          subAncestors, strippedLit},
    record      = findRecordByMClause[clauseInfos, c];
    pivotIdx    = findPivotIdx[record, pivotLit];
    ruleThm     = record["rules"][[pivotIdx]];
    subgoalLits = Delete[record["lits"], pivotIdx];
    If[Length[subTrees] =!= Length[subgoalLits],
      HOL`Error`holError["meson",
        "closeExtensionProp: subTree/subgoal count mismatch",
        <|"subTrees" -> Length[subTrees], "subgoals" -> Length[subgoalLits]|>]];
    instedRule = instWithSigma[applyTagToThm[ruleThm, cTag], σInst];
    strippedLit  = stripTagLit[lit];
    subAncestors = Prepend[ancestorBindings, {strippedLit, litThm}];
    currentRule  = instedRule;
    Do[
      Lj         = applyTagToMLit[subgoalLits[[j]], cTag];
      LjTermInst = walkTermFinal[mLitToTerm[Lj], σ];
      LjAssume   = ASSUME[LjTermInst];
      fThmJ      = closeLitProp[Lj, LjAssume, subAncestors,
                                subTrees[[j]], clauseInfos, σ, σInst];
      negLjThm   = fromFalseToNegLitTerm[
                     Lj[[1]], walkTermFinal[Lj[[2]], σ], fThmJ];
      currentRule = HOL`Bool`MP[currentRule, negLjThm],
      {j, 1, Length[subgoalLits]}
    ];
    If[pivotLit[[1]] === True,
      HOL`Bool`MP[HOL`Bool`NOTELIM[litThm], currentRule],
      HOL`Bool`MP[HOL`Bool`NOTELIM[currentRule], litThm]]
  ];

instWithSigma[thm_, σInst_Association] :=
  If[Length[σInst] === 0, thm, INST[Normal[σInst], thm]];

(* Build a right-associated disjunction term L_i ∨ L_{i+1} ∨ ⋯ ∨ L_k     *)
(* from a list of mLit values.                                            *)
disjunctionFromMLits[{single_}] := mLitToTerm[single];
disjunctionFromMLits[{first_, rest__}] :=
  mkOrStruct[mLitToTerm[first], disjunctionFromMLits[{rest}]];

(* From per-lit fThms {fThm_1, …, fThm_k} (each: Δ_i ∪ {L_i_term} ⊢ ⊥)   *)
(* and the start clauseThm (Γ ⊢ L_1 ∨ ⋯ ∨ L_k), produce Γ ∪ ⋃Δ_i ⊢ ⊥    *)
(* by right-associated DISJCASES folding.                                 *)
foldDisjCases[clauseThm_, lits_List, fThms_List] :=
  Module[{n, acc, i, disjTerm},
    n = Length[lits];
    If[n === 1, Return[fThms[[1]]]];
    acc = fThms[[n]];
    Do[
      disjTerm = disjunctionFromMLits[Take[lits, {i, n}]];
      acc = HOL`Bool`DISJCASES[ASSUME[disjTerm], fThms[[i]], acc],
      {i, n - 1, 2, -1}
    ];
    HOL`Bool`DISJCASES[clauseThm, fThms[[1]], acc]
  ];

processStartProp[mProof["empty", _], _, _, _] :=
  HOL`Error`holError["meson",
    "mesonProveProp: empty clause not yet handled", <||>];

processStartProp[mProof["start", c_, startTag_String, subTrees_List],
                 clauseInfos_, σ_, σInst_] :=
  Module[{record, lits, k, clauseThm, instedClauseThm, taggedLits, fThms},
    record = findRecordByMClause[clauseInfos, c];
    If[MissingQ[record],
      HOL`Error`holError["meson",
        "processStartProp: start clause not in clauseInfos",
        <|"c" -> c|>]];
    lits      = record["lits"];
    k         = Length[lits];
    clauseThm = record["thm"];
    If[Length[subTrees] =!= k,
      HOL`Error`holError["meson",
        "processStartProp: subTree count != start lit count",
        <|"subTrees" -> Length[subTrees], "k" -> k|>]];
    instedClauseThm = instWithSigma[applyTagToThm[clauseThm, startTag], σInst];
    taggedLits      = Map[applyTagToMLit[#, startTag] &, lits];
    If[k === 1,
      (* Fast path: clauseThm IS the unit literal's thm (after tag+σ). *)
      closeLitProp[taggedLits[[1]], instedClauseThm, {},
                   subTrees[[1]], clauseInfos, σ, σInst],
      (* k > 1: ASSUME each tagged-then-σ-INSTed lit, recursively close,  *)
      (* fold DISJCASES against the INSTed clauseThm.                     *)
      fThms = Table[
        Module[{Li, LiTermInst, LiAssume},
          Li         = taggedLits[[i]];
          LiTermInst = walkTermFinal[mLitToTerm[Li], σ];
          LiAssume   = ASSUME[LiTermInst];
          closeLitProp[Li, LiAssume, {}, subTrees[[i]], clauseInfos, σ, σInst]
        ],
        {i, 1, k}];
      foldDisjCases[instedClauseThm,
                    Map[mLit[#[[1]], walkTermFinal[#[[2]], σ]] &, taggedLits],
                    fThms]
    ]
  ];

(* === FOL clausifier on theorems (M7-α-4-d-β). ================ *)
(* nnfThm already descends into ∀/∃ bodies via DEPTHCONV+SUBCONV, so   *)
(* propositional connectives inside binders get normalized.  What this *)
(* layer adds: top-level ∀ → SPEC fresh, top-level ∧ → CONJUNCT1/2,    *)
(* top-level ∃ → Skolemize (NYI).  Walking is performed AFTER nnfThm   *)
(* so polarities are settled before we eliminate quantifiers.          *)

freshFOLVarName[origin_String, forbidden_List] :=
  Module[{cand = origin, i = 0},
    While[MemberQ[forbidden, cand],
      i++; cand = origin <> "_" <> ToString[i]];
    cand
  ];

HOL`Auto`Meson`specWithFreshName[thm_] :=
  Module[{c, absNode, ty, origin, allFreeNames, forbidden, fresh, freshVar},
    c = concl[thm];
    If[! isForallQ[c],
      HOL`Error`holError["meson",
        "specWithFreshName: expected ⊢ ∀x. φ", <|"concl" -> c|>]];
    absNode = c[[2]];
    ty      = absNode[[1, 2]];
    origin  = absNode[[3]];
    allFreeNames = Cases[c, var[n_String, _] :> n, {0, Infinity}];
    Do[allFreeNames = Union[allFreeNames,
                            Cases[h, var[n_String, _] :> n, {0, Infinity}]],
       {h, hyp[thm]}];
    forbidden = Union[allFreeNames, HOL`Kernel`listConstants[]];
    fresh     = freshFOLVarName[origin, forbidden];
    freshVar  = mkVar[fresh, ty];
    HOL`Bool`SPEC[freshVar, thm]
  ];

(* ∃-Skolemization on theorems.                                          *)
(*                                                                        *)
(* From `Γ ⊢ ∃x:τ. φ` produce `Γ ⊢ φ[sk y₁…yₙ / x]` where:               *)
(*   - y₁…yₙ are the free variables of φ (the "universal scope" — vars   *)
(*     introduced by SPECs of outer ∀'s, or already free in Γ),          *)
(*   - sk is a fresh constant of type τ(y₁) → … → τ(yₙ) → τ,             *)
(*   - sk is defined by `⊢ sk = λy₁…yₙ. @x:τ. φ_open` (ε-Hilbert form).   *)
(* The derivation proceeds via selectAx + CHOOSE: introduce a fresh      *)
(* witness `v`, derive `φ[v/x] ⊢ φ[@P/x]` from selectAx, CHOOSE off `v`  *)
(* to get `Γ ⊢ φ[@P/x]`, then substitute @P → (sk y₁…yₙ) using SYM of    *)
(* the η-expanded definition.                                            *)

skolemizeExists[thm_] :=
  Module[{c, absNode, ty, body, origin, freeVars, n,
          selectTy, selectConst, xName, xVar, bodyAtX, pLambda, epsTerm,
          skName, skTy, skVar, skRhs, defThm, skConst, skTerm,
          selectInst, spec1, vName, vVar, spec2,
          bodyAtV, pLambdaV, pLambdaVBetaEq, plvAssume,
          plEps, pLambdaEps, pLambdaEpsBetaEq, bodyAtEps, chooseResult,
          skEq, allFreeNames, forbiddenNames, cur, rhsBeta},
    c = concl[thm];
    If[! isExistsQ[c],
      HOL`Error`holError["meson",
        "skolemizeExists: expected ⊢ ∃x. φ", <|"concl" -> c|>]];
    absNode = c[[2]];
    ty      = absNode[[1, 2]];
    body    = absNode[[2]];
    origin  = absNode[[3]];
    freeVars = freesIn[body];
    n        = Length[freeVars];

    selectTy    = tyApp["fun", {tyApp["fun", {ty, tyApp["bool", {}]}], ty}];
    selectConst = mkConst["@", selectTy];

    allFreeNames   = Cases[c, var[name_String, _] :> name, {0, Infinity}];
    Do[allFreeNames = Union[allFreeNames,
                            Cases[h, var[name_String, _] :> name, {0, Infinity}]],
       {h, hyp[thm]}];
    forbiddenNames = Union[allFreeNames, HOL`Kernel`listConstants[]];

    xName    = freshFOLVarName[origin, forbiddenNames];
    xVar     = mkVar[xName, ty];
    bodyAtX  = openSubstImpl[body, 0, xVar];
    pLambda  = mkAbs[xVar, bodyAtX];
    epsTerm  = mkComb[selectConst, pLambda];

    skName = freshSkolemName[];
    skTy   = Fold[tyApp["fun", {#2[[2]], #1}] &, ty, Reverse[freeVars]];
    skVar  = mkVar[skName, skTy];
    skRhs  = Fold[mkAbs[#2, #1] &, epsTerm, Reverse[freeVars]];
    defThm = newDefinition[mkEq[skVar, skRhs]];

    skConst = const[skName, skTy];
    skTerm  = Fold[mkComb[#1, #2] &, skConst, freeVars];

    selectInst = INSTTYPE[{tyVar["a"] -> ty}, selectAx];
    spec1      = HOL`Bool`SPEC[pLambda, selectInst];

    vName = freshFOLVarName[origin <> "wit",
                            Union[forbiddenNames, {xName}]];
    vVar  = mkVar[vName, ty];
    spec2 = HOL`Bool`SPEC[vVar, spec1];

    bodyAtV          = openSubstImpl[body, 0, vVar];
    pLambdaV         = mkComb[pLambda, vVar];
    pLambdaVBetaEq   = BETACONV[pLambdaV];
    plvAssume        = EQMP[SYM[pLambdaVBetaEq], ASSUME[bodyAtV]];
    plEps            = HOL`Bool`MP[spec2, plvAssume];
    pLambdaEps       = mkComb[pLambda, epsTerm];
    pLambdaEpsBetaEq = BETACONV[pLambdaEps];
    bodyAtEps        = EQMP[pLambdaEpsBetaEq, plEps];

    chooseResult = HOL`Bool`CHOOSE[vVar, thm, bodyAtEps];

    cur = defThm;
    Do[
      cur = HOL`Equal`APTHM[cur, freeVars[[i]]];
      rhsBeta = BETACONV[concl[cur][[2]]];
      cur = TRANS[cur, rhsBeta],
      {i, 1, n}
    ];
    skEq = cur;

    HOL`Drule`SUBS[{SYM[skEq]}, chooseResult]
  ];

walkClausifyFOL[thm_] :=
  Module[{c = concl[thm]},
    Which[
      isAndQ[c],
        Join[walkClausifyFOL[HOL`Bool`CONJUNCT1[thm]],
             walkClausifyFOL[HOL`Bool`CONJUNCT2[thm]]],
      isForallQ[c],
        walkClausifyFOL[HOL`Auto`Meson`specWithFreshName[thm]],
      isExistsQ[c],
        walkClausifyFOL[skolemizeExists[thm]],
      True,
        HOL`Auto`PropTaut`splitConjThm[HOL`Auto`PropTaut`cnfThm[thm]]
    ]
  ];

HOL`Auto`Meson`clausifyFOLThm[thm_] :=
  walkClausifyFOL[HOL`Auto`PropTaut`nnfThm[thm]];

(* === Top-level. ============================================== *)

HOL`Auto`Meson`mesonProveProp[goalTm_, premiseThms_List] :=
  Module[{negGoal, assumeNeg, premiseInfos, negGoalInfos,
          allClauseInfos, sortedInfos, mClauses, traceResult,
          σRaw, σ, σInst, fThm},
    negGoal   = mkNotStruct[goalTm];
    assumeNeg = ASSUME[negGoal];
    premiseInfos = Flatten[
      Map[Map[buildClauseRecord, HOL`Auto`Meson`clausifyFOLThm[#]] &,
          premiseThms]];
    negGoalInfos = Map[buildClauseRecord,
                       HOL`Auto`Meson`clausifyFOLThm[assumeNeg]];
    allClauseInfos = Join[premiseInfos, negGoalInfos];
    (* Unit clauses first as a search heuristic — k=1 starts skip the     *)
    (* DISJCASES fold and are cheaper to replay.                          *)
    sortedInfos = SortBy[allClauseInfos, Length[#["lits"]] &];
    mClauses = Map[#["mClause"] &, sortedInfos];
    HOL`Auto`Meson`mesonResetState[];
    traceResult = HOL`Auto`Meson`mesonRefute[mClauses, mesonMaxDepth];
    If[traceResult === HOL`Auto`Meson`mesonRefuteFailed,
      HOL`Error`holError["meson",
        "mesonProveProp: no refutation found",
        <|"goal" -> goalTm|>]];
    σRaw  = extractFinalSigma[traceResult];
    σ     = Association[KeyValueMap[#1 -> walkTermFinal[#2, σRaw] &, σRaw]];
    σInst = sigmaToInstSubst[σRaw];
    fThm = processStartProp[traceResult, sortedInfos, σ, σInst];
    HOL`Bool`CCONTR[goalTm, untagThm[fThm]]
  ];

(* ============================================================ *)
(* M7-α-1 stubs preserved.  Tactic-level integration in α-5+.    *)

HOL`Auto`Meson`MESON[thms_List][g_goal] :=
  HOL`Tactics`noTac[g];

HOL`Auto`Meson`mesonProve[tm_, thms_List] :=
  HOL`Error`holError["meson",
    "mesonProve: tactic-level integration not implemented yet (use mesonProveProp)",
    <|"goal" -> tm|>];

End[];
EndPackage[];
