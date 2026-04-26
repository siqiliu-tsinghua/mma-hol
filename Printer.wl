(* ::Package:: *)

BeginPackage["HOL`Printer`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`"}];

formatTerm::usage       = "formatTerm[t] / formatTerm[t, mode] returns a string rendering of term t. mode is \"Unicode\" (default) or \"ASCII\".";
formatThm::usage        = "formatThm[th] / formatThm[th, mode] returns a string rendering of a theorem: \"⊢ p\" or \"[h1; h2; …] ⊢ p\".";
registerOperator::usage = "registerOperator[name, spec] adds or overrides an entry in the operator registry. spec is an Association with keys \"kind\" (\"infix\" / \"prefix\" / \"binder\"), \"prec\" (Integer), \"assoc\" (\"left\" / \"right\" / \"non\", infix only), \"ascii\" (String), \"unicode\" (String).";
lookupOperator::usage   = "lookupOperator[name] returns the registry entry for name, or Missing[\"NotRegistered\", name].";
operatorTable::usage    = "operatorTable[] returns a copy of the full operator registry.";

Begin["`Private`"];

$opRegistry = <||>;

registerOperator[name_String, spec_Association] := ($opRegistry[name] = spec;);

lookupOperator[name_String] := Lookup[$opRegistry, name, Missing["NotRegistered", name]];

operatorTable[] := $opRegistry;

(* --- bootstrap: built-in operators ---
   Precedence table (higher = tighter):
     0  binders (∀ ∃ @ λ)        — render rule is special: extends right; paren when not in right-extending position
    10  ⇒  right
    16  ∨  right
    20  ∧  right
    28  =  right
    30  ¬  prefix
    50  application (left-assoc)
*)
registerOperator["=", <|"kind" -> "infix",  "prec" -> 28, "assoc" -> "right", "ascii" -> "=",   "unicode" -> "="|>];
registerOperator["∧", <|"kind" -> "infix",  "prec" -> 20, "assoc" -> "right", "ascii" -> "/\\", "unicode" -> "∧"|>];
registerOperator["∨", <|"kind" -> "infix",  "prec" -> 16, "assoc" -> "right", "ascii" -> "\\/", "unicode" -> "∨"|>];
registerOperator["⇒", <|"kind" -> "infix",  "prec" -> 10, "assoc" -> "right", "ascii" -> "==>", "unicode" -> "⇒"|>];
registerOperator["¬", <|"kind" -> "prefix", "prec" -> 30,                       "ascii" -> "~",   "unicode" -> "¬"|>];
registerOperator["∀", <|"kind" -> "binder", "prec" -> 0,                        "ascii" -> "!",   "unicode" -> "∀"|>];
registerOperator["∃", <|"kind" -> "binder", "prec" -> 0,                        "ascii" -> "?",   "unicode" -> "∃"|>];
registerOperator["@", <|"kind" -> "binder", "prec" -> 0,                        "ascii" -> "@",   "unicode" -> "@"|>];

$precApp = 50;

opSym[name_String, mode_String] :=
  Module[{spec = $opRegistry[name]},
    If[mode === "ASCII", spec["ascii"], spec["unicode"]]
  ];

lambdaSym["ASCII"]   := "\\";
lambdaSym["Unicode"] := "λ";

turnstile["ASCII"]   := "|-";
turnstile["Unicode"] := "⊢";

binderConstQ[name_String] :=
  MatchQ[$opRegistry[name], _Association] && $opRegistry[name]["kind"] === "binder";
infixConstQ[name_String] :=
  MatchQ[$opRegistry[name], _Association] && $opRegistry[name]["kind"] === "infix";
prefixConstQ[name_String] :=
  MatchQ[$opRegistry[name], _Association] && $opRegistry[name]["kind"] === "prefix";
binderConstQ[_] := False;
infixConstQ[_]  := False;
prefixConstQ[_] := False;

freeNames[t_] := First /@ HOL`Terms`freesIn[t];

freshName[origin_String, dodge_List] :=
  Module[{cur = origin},
    While[MemberQ[dodge, cur], cur = cur <> "'"];
    cur
  ];

(* --- main render walk ---
   renderTerm[t, ctxPrec, rightExt, stack, mode] -> String
     ctxPrec   : minimum prec the term must have to avoid being parenthesized
     rightExt  : True iff the slot can host a binder without parens (top-level,
                 right arg of infix, arg of prefix, body of binder)
     stack     : list of {displayName, type} pairs; index i ↔ bvar[i-1, _]
     mode      : "Unicode" | "ASCII"
*)

renderTerm[var[n_String, _], _, _, _, _] := n;

renderTerm[bvar[k_Integer, _], _, _, stack_, _] :=
  If[k + 1 <= Length[stack],
    stack[[k + 1, 1]],
    StringJoin["<bvar:", ToString[k], ">"]
  ];

renderTerm[const[n_String, _], _, _, _, mode_] :=
  Module[{spec = $opRegistry[n]},
    Which[
      ! AssociationQ[spec], n,
      MemberQ[{"infix", "prefix", "binder"}, spec["kind"]],
        StringJoin["(", opSym[n, mode], ")"],
      True, n
    ]
  ];

(* binder application: comb[const[bs, _], abs[_, _, _]] *)
renderTerm[t : comb[const[bs_String, _], abs[_, _, _]], ctxPrec_, rightExt_, stack_, mode_] /;
    binderConstQ[bs] :=
  renderBinderChain[bs, t, ctxPrec, rightExt, stack, mode];

(* infix two-arg *)
renderTerm[comb[comb[const[op_String, _], a_], b_], ctxPrec_, _, stack_, mode_] /;
    infixConstQ[op] :=
  renderInfix[op, a, b, ctxPrec, stack, mode];

(* prefix one-arg *)
renderTerm[comb[const[op_String, _], a_], ctxPrec_, _, stack_, mode_] /;
    prefixConstQ[op] :=
  renderPrefix[op, a, ctxPrec, stack, mode];

(* generic application *)
renderTerm[comb[f_, x_], ctxPrec_, _, stack_, mode_] :=
  renderApp[f, x, ctxPrec, stack, mode];

(* abs not under any binder constant: λ-chain *)
renderTerm[t : abs[_, _, _], ctxPrec_, rightExt_, stack_, mode_] :=
  renderBinderChain["λ", t, ctxPrec, rightExt, stack, mode];

renderTerm[other_, _, _, _, _] := StringJoin["<?", ToString[other, InputForm], ">"];

renderInfix[op_, a_, b_, ctxPrec_, stack_, mode_] :=
  Module[{spec, p, assoc, sym, lctx, rctx, ls, rs, raw},
    spec  = $opRegistry[op];
    p     = spec["prec"];
    assoc = spec["assoc"];
    sym   = opSym[op, mode];
    {lctx, rctx} = Switch[assoc,
      "right", {p + 1, p},
      "left",  {p, p + 1},
      _,       {p + 1, p + 1}
    ];
    ls = renderTerm[a, lctx, False, stack, mode];
    rs = renderTerm[b, rctx, True,  stack, mode];
    raw = StringJoin[ls, " ", sym, " ", rs];
    If[p < ctxPrec, StringJoin["(", raw, ")"], raw]
  ];

renderPrefix[op_, a_, ctxPrec_, stack_, mode_] :=
  Module[{spec, p, sym, as, raw},
    spec = $opRegistry[op];
    p    = spec["prec"];
    sym  = opSym[op, mode];
    as = renderTerm[a, p, True, stack, mode];
    raw = StringJoin[sym, " ", as];
    If[p < ctxPrec, StringJoin["(", raw, ")"], raw]
  ];

renderApp[f_, x_, ctxPrec_, stack_, mode_] :=
  Module[{fs, xs, raw, p = $precApp},
    fs = renderTerm[f, p,     False, stack, mode];
    xs = renderTerm[x, p + 1, False, stack, mode];
    raw = StringJoin[fs, " ", xs];
    If[p < ctxPrec, StringJoin["(", raw, ")"], raw]
  ];

renderBinderChain[binderSym_String, t_, ctxPrec_, rightExt_, stack_, mode_] :=
  Module[{result, vars, body, st, names, bsym, bodyStr, raw},
    result = peel[binderSym, t, stack];
    vars = result[[1]]; body = result[[2]]; st = result[[3]];
    names = vars[[All, 1]];
    bsym = If[binderSym === "λ", lambdaSym[mode], opSym[binderSym, mode]];
    bodyStr = renderTerm[body, 0, True, st, mode];
    raw = StringJoin[bsym, StringRiffle[names, " "], ". ", bodyStr];
    If[!rightExt, StringJoin["(", raw, ")"], raw]
  ];

(* peel collects (name, type) pairs along a same-binder chain.
   Returns {varspecs (outer→inner), residualBody, finalStack (innermost-first)}. *)

peel[binderSym_String, comb[const[bs_String, _], abs[bvarSlot_, body_, origin_String]], stack_] /;
    bs === binderSym :=
  Module[{ty, dodge, name, st1, deeper},
    ty   = bvarSlot[[2]];
    dodge = Join[stack[[All, 1]], freeNames[body]];
    name = freshName[origin, dodge];
    st1  = Prepend[stack, {name, ty}];
    deeper = peel[binderSym, body, st1];
    {Prepend[deeper[[1]], {name, ty}], deeper[[2]], deeper[[3]]}
  ];

peel["λ", abs[bvarSlot_, body_, origin_String], stack_] :=
  Module[{ty, dodge, name, st1, deeper},
    ty   = bvarSlot[[2]];
    dodge = Join[stack[[All, 1]], freeNames[body]];
    name = freshName[origin, dodge];
    st1  = Prepend[stack, {name, ty}];
    deeper = peel["λ", body, st1];
    {Prepend[deeper[[1]], {name, ty}], deeper[[2]], deeper[[3]]}
  ];

peel[_, t_, stack_] := {{}, t, stack};

(* --- public API --- *)

formatTerm[t_] := renderTerm[t, 0, True, {}, "Unicode"];
formatTerm[t_, "Unicode"] := renderTerm[t, 0, True, {}, "Unicode"];
formatTerm[t_, "ASCII"]   := renderTerm[t, 0, True, {}, "ASCII"];
formatTerm[t_, mode_] :=
  HOL`Error`holError["printer", "formatTerm: invalid mode (use \"Unicode\" or \"ASCII\")",
    <|"mode" -> mode|>];

formatThm[th_] := formatThm[th, "Unicode"];

formatThm[th_, mode_String] /; (mode === "Unicode" || mode === "ASCII") :=
  Module[{hyps, c, hStr, ts},
    hyps = HOL`Kernel`hyp[th];
    c    = HOL`Kernel`concl[th];
    ts   = turnstile[mode];
    If[Length[hyps] === 0,
      StringJoin[ts, " ", renderTerm[c, 0, True, {}, mode]],
      hStr = StringRiffle[renderTerm[#, 0, True, {}, mode] & /@ hyps, "; "];
      StringJoin["[", hStr, "] ", ts, " ", renderTerm[c, 0, True, {}, mode]]
    ]
  ];

formatThm[_, mode_] :=
  HOL`Error`holError["printer", "formatThm: invalid mode (use \"Unicode\" or \"ASCII\")",
    <|"mode" -> mode|>];

End[];
EndPackage[];
