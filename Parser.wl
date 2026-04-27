(* ::Package:: *)

BeginPackage["HOL`Parser`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`", "HOL`Printer`"
}];

parseTerm::usage = "parseTerm[s_String] tokenizes and parses a HOL term, performing Hindley-Milner type inference. Free variables get fresh polymorphic types; registered constants are fresh-instantiated. Bound variables can carry optional type annotations (λx:ty. body). Type ascription (t : ty) constrains a subterm.";
parseType::usage = "parseType[s_String] parses a HOL type. Type variables use the 'a syntax (e.g. 'a, 'b); type constructors must be registered with the kernel (currently bool, ind, fun); fun is written infix as a -> b (right-assoc).";

Begin["`Private`"];

(* ============================================================ *)
(* parser state — single shared, reset on each top-level call.  *)

$tokens = {};
$idx = 1;
$tvCounter = 0;
$freeVarTypes = <||>;

peek[]      := $tokens[[$idx]];
peekKind[]  := $tokens[[$idx, 1]];
peekVal[]   := $tokens[[$idx, 2]];
peekPos[]   := $tokens[[$idx, 3]];

consume[] := ($idx += 1; $tokens[[$idx - 1]]);
consumeVal[] := ($idx += 1; $tokens[[$idx - 1, 2]]);

expectKind[kind_String] :=
  If[peekKind[] === kind, consume[],
    With[{msg = StringJoin["expected ", kind, ", got ", peekKind[]]},
      HOL`Error`holError["parser", msg,
        <|"pos" -> peekPos[], "got" -> peek[]|>]
    ]];

freshTV[] := ($tvCounter += 1; tyVar["?" <> ToString[$tvCounter]]);

(* ============================================================ *)
(* tokenizer                                                    *)

opCanon[s_String] := Switch[s,
  "/\\", "∧",  "\\/", "∨", "==>", "⇒",
  "~",   "¬",  "!",   "∀", "?",   "∃",
  "\\",  "λ",  "->",  "→", "|-",  "⊢",
  _,     s];

threeCharOpStrings = {"==>"};
twoCharOpStrings   = {"/\\", "\\/", "->", "|-"};
singleCharOps      = {"=", "∧", "∨", "⇒", "¬", "∀", "∃", "@", "λ", "→", "⊢", "~", "!", "?", "\\"};

isLetterChar[c_String] := LetterQ[c] && ! MemberQ[singleCharOps, c];
isIdentRest[c_String]  := isLetterChar[c] || DigitQ[c] || c === "'";

tokenize[s_String] :=
  Module[{i = 1, n = StringLength[s], chars, tokens = {}, c, start, t2, t3},
    chars = Characters[s];
    While[i <= n,
      c = chars[[i]];
      t2 = If[i + 1 <= n, chars[[i]] <> chars[[i + 1]], ""];
      t3 = If[i + 2 <= n, chars[[i]] <> chars[[i + 1]] <> chars[[i + 2]], ""];
      Which[
        StringMatchQ[c, Whitespace], i++,
        c === "(", AppendTo[tokens, {"lparen", "(", i}]; i++,
        c === ")", AppendTo[tokens, {"rparen", ")", i}]; i++,
        c === ".", AppendTo[tokens, {"dot",    ".", i}]; i++,
        c === ":", AppendTo[tokens, {"colon",  ":", i}]; i++,
        c === ",", AppendTo[tokens, {"comma",  ",", i}]; i++,
        c === "'",
          start = i + 1;
          While[start <= n && isIdentRest[chars[[start]]], start++];
          If[start === i + 1,
            HOL`Error`holError["parser", "empty type variable",
              <|"pos" -> i|>]];
          AppendTo[tokens, {"tyvar", StringTake[s, {i + 1, start - 1}], i}];
          i = start,
        MemberQ[threeCharOpStrings, t3],
          AppendTo[tokens, {"op", opCanon[t3], i}]; i += 3,
        MemberQ[twoCharOpStrings, t2],
          AppendTo[tokens, {"op", opCanon[t2], i}]; i += 2,
        MemberQ[singleCharOps, c],
          AppendTo[tokens, {"op", opCanon[c], i}]; i++,
        DigitQ[c],
          start = i;
          While[i <= n && DigitQ[chars[[i]]], i++];
          AppendTo[tokens, {"num", StringTake[s, {start, i - 1}], start}],
        isLetterChar[c],
          start = i;
          While[i <= n && isIdentRest[chars[[i]]], i++];
          AppendTo[tokens, {"ident", StringTake[s, {start, i - 1}], start}],
        True,
          HOL`Error`holError["parser", "tokenize: unexpected character",
            <|"char" -> c, "pos" -> i|>]
      ]
    ];
    AppendTo[tokens, {"eof", "", n + 1}];
    tokens
  ];

(* ============================================================ *)
(* type parser                                                  *)

parseTypeExpr[] :=
  Module[{left, right},
    left = parseTypeAtom[];
    If[peekKind[] === "op" && peekVal[] === "→",
      consume[];
      right = parseTypeExpr[];
      tyApp["fun", {left, right}],
      left
    ]
  ];

parseTypeAtom[] :=
  Module[{tok, name, ty, arity, caught},
    tok = peek[];
    Which[
      tok[[1]] === "lparen",
        consume[];
        ty = parseTypeExpr[];
        expectKind["rparen"];
        ty,
      tok[[1]] === "tyvar",
        tyVar[consumeVal[]],
      tok[[1]] === "ident",
        name = consumeVal[];
        arity = Catch[HOL`Kernel`typeArity[name],
          HOL`Error`holErrorTag, Function[{val, tag}, $Failed]];
        If[arity === $Failed,
          HOL`Error`holError["parser", "unknown type constructor",
            <|"name" -> name|>]];
        If[arity =!= 0,
          With[{msg = StringJoin["type constructor ", name, " has arity ",
              ToString[arity], " (only nullary type constructors are supported in this parser)"]},
            HOL`Error`holError["parser", msg, <|"name" -> name, "arity" -> arity|>]
          ]];
        tyApp[name, {}],
      True,
        HOL`Error`holError["parser", "expected type atom",
          <|"got" -> tok|>]
    ]
  ];

(* ============================================================ *)
(* term parser — produces a raw AST.                            *)
(* Raw nodes:                                                   *)
(*   rIdent[name]                                               *)
(*   rConst[name]            -- only emitted by binder expansion *)
(*   rApp[f, x]                                                 *)
(*   rAbs[name, tyOpt, body] -- tyOpt = None | type             *)
(*   rBinder[bs, vars, body] -- vars = list of {name, tyOpt}    *)
(*   rTypeAsc[t, ty]                                            *)

binderOpQ[s_String] := MemberQ[{"∀", "∃", "λ", "@"}, s];

registeredInfixQ[s_String] :=
  Module[{spec = HOL`Printer`lookupOperator[s]},
    AssociationQ[spec] && spec["kind"] === "infix"
  ];

registeredPrefixQ[s_String] :=
  Module[{spec = HOL`Printer`lookupOperator[s]},
    AssociationQ[spec] && spec["kind"] === "prefix"
  ];

atomStartTokenQ[tok_] :=
  MatchQ[tok[[1]], "lparen" | "ident" | "num"] ||
  (tok[[1]] === "op" && (binderOpQ[tok[[2]]] || registeredPrefixQ[tok[[2]]]));

$appPrec = 50;

parseExpr[minPrec_Integer] :=
  Module[{left, tok, opName, spec, p, assoc, right, atom, done = False},
    left = parseAtom[];
    While[! done,
      tok = peek[];
      Which[
        tok[[1]] === "op" && registeredInfixQ[tok[[2]]],
          opName = tok[[2]];
          spec = HOL`Printer`lookupOperator[opName];
          p = spec["prec"]; assoc = spec["assoc"];
          If[p < minPrec, done = True,
            consume[];
            right = parseExpr[If[assoc === "right", p, p + 1]];
            left = rApp[rApp[rConst[opName], left], right]
          ],
        atomStartTokenQ[tok],
          If[$appPrec < minPrec, done = True,
            atom = parseAtom[];
            left = rApp[left, atom]
          ],
        True, done = True
      ]
    ];
    left
  ];

parseAtom[] :=
  Module[{tok, name, e, ty, prefSpec, prefP, arg},
    tok = peek[];
    Which[
      tok[[1]] === "lparen",
        consume[];
        e = parseExpr[0];
        If[peekKind[] === "colon",
          consume[];
          ty = parseTypeExpr[];
          e = rTypeAsc[e, ty]];
        expectKind["rparen"];
        e,
      tok[[1]] === "op" && binderOpQ[tok[[2]]],
        parseBinder[],
      tok[[1]] === "op" && registeredPrefixQ[tok[[2]]],
        consume[];
        prefSpec = HOL`Printer`lookupOperator[tok[[2]]];
        prefP = prefSpec["prec"];
        arg = parseExpr[prefP];
        rApp[rConst[tok[[2]]], arg],
      tok[[1]] === "ident",
        consume[];
        rIdent[tok[[2]]],
      tok[[1]] === "num",
        HOL`Error`holError["parser",
          "numeric literals not yet supported (M7 will introduce a `num` theory)",
          <|"pos" -> tok[[3]], "value" -> tok[[2]]|>],
      True,
        HOL`Error`holError["parser", "expected term atom",
          <|"got" -> tok|>]
    ]
  ];

parseBinder[] :=
  Module[{binderSym, vars = {}, vname, vty, body},
    binderSym = consumeVal[];
    While[peekKind[] === "ident",
      vname = consumeVal[];
      vty = If[peekKind[] === "colon",
        consume[];
        parseTypeExpr[],
        None];
      AppendTo[vars, {vname, vty}]
    ];
    If[Length[vars] === 0,
      HOL`Error`holError["parser", "binder expects at least one variable",
        <|"binder" -> binderSym|>]];
    expectKind["dot"];
    body = parseExpr[0];
    rBinder[binderSym, vars, body]
  ];

(* ============================================================ *)
(* type inference                                               *)
(*   inferImpl[raw, env] -> {shadowTerm, type, constraintList}  *)
(*   shadowTerm uses var[name, ty] in abs binder slot — NOT bvar.*)
(*   canonicalize finalizes via mkAbs etc. at the end.          *)

isRegisteredConstantQ[name_String] :=
  MemberQ[HOL`Kernel`listConstants[], name];

freshInstantiate[ty_] :=
  Module[{tvs, theta},
    tvs = HOL`Types`tyvars[ty];
    theta = Association[(# -> freshTV[]) & /@ tvs];
    HOL`Types`typeSubst[theta, ty]
  ];

inferImpl[rIdent[name_String], env_] :=
  Module[{ty, generic, instTy},
    Which[
      KeyExistsQ[env, name],
        ty = env[name];
        {var[name, ty], ty, {}},
      isRegisteredConstantQ[name],
        generic = HOL`Kernel`constType[name];
        instTy = freshInstantiate[generic];
        {const[name, instTy], instTy, {}},
      True,
        ty = If[KeyExistsQ[$freeVarTypes, name],
          $freeVarTypes[name],
          $freeVarTypes[name] = freshTV[]];
        {var[name, ty], ty, {}}
    ]
  ];

inferImpl[rConst[name_String], env_] :=
  Module[{generic, instTy},
    generic = HOL`Kernel`constType[name];
    instTy = freshInstantiate[generic];
    {const[name, instTy], instTy, {}}
  ];

inferImpl[rApp[f_, x_], env_] :=
  Module[{fRes, xRes, tyR},
    fRes = inferImpl[f, env];
    xRes = inferImpl[x, env];
    tyR = freshTV[];
    {comb[fRes[[1]], xRes[[1]]], tyR,
      Join[fRes[[3]], xRes[[3]],
        {{fRes[[2]], tyApp["fun", {xRes[[2]], tyR}]}}]}
  ];

inferImpl[rAbs[name_String, tyOpt_, body_], env_] :=
  Module[{ty, bodyEnv, bRes},
    ty = If[tyOpt === None, freshTV[], tyOpt];
    bodyEnv = Append[env, name -> ty];
    bRes = inferImpl[body, bodyEnv];
    {abs[var[name, ty], bRes[[1]], name],
      tyApp["fun", {ty, bRes[[2]]}],
      bRes[[3]]}
  ];

inferImpl[rBinder[bs_String, vars_List, body_], env_] :=
  inferImpl[expandBinder[bs, vars, body], env];

inferImpl[rTypeAsc[t_, ty_], env_] :=
  Module[{tRes},
    tRes = inferImpl[t, env];
    {tRes[[1]], ty, Append[tRes[[3]], {tRes[[2]], ty}]}
  ];

expandBinder[bs_String, {{vname_String, vty_}}, body_] :=
  If[bs === "λ",
    rAbs[vname, vty, body],
    rApp[rConst[bs], rAbs[vname, vty, body]]
  ];

expandBinder[bs_String, {{vname_String, vty_}, rest__}, body_] :=
  Module[{inner = expandBinder[bs, {rest}, body]},
    If[bs === "λ",
      rAbs[vname, vty, inner],
      rApp[rConst[bs], rAbs[vname, vty, inner]]
    ]
  ];

(* ============================================================ *)
(* unification                                                  *)

unify[constraints_List] :=
  Module[{σ = <||>, c, lhs, rhs},
    Do[
      lhs = HOL`Types`typeSubst[σ, c[[1]]];
      rhs = HOL`Types`typeSubst[σ, c[[2]]];
      σ = unifyOne[lhs, rhs, σ],
      {c, constraints}
    ];
    σ
  ];

unifyOne[t1_, t2_, σ_] :=
  Which[
    t1 === t2,
      σ,
    MatchQ[t1, tyVar[_String]],
      bindTyVar[t1, t2, σ],
    MatchQ[t2, tyVar[_String]],
      bindTyVar[t2, t1, σ],
    MatchQ[t1, tyApp[_String, _List]] && MatchQ[t2, tyApp[_String, _List]] &&
        t1[[1]] === t2[[1]] && Length[t1[[2]]] === Length[t2[[2]]],
      Fold[
        Function[{accσ, pair},
          unifyOne[
            HOL`Types`typeSubst[accσ, pair[[1]]],
            HOL`Types`typeSubst[accσ, pair[[2]]],
            accσ]
        ],
        σ, Transpose[{t1[[2]], t2[[2]]}]
      ],
    True,
      HOL`Error`holError["parser", "type unification failure",
        <|"left" -> t1, "right" -> t2|>]
  ];

bindTyVar[v_, t_, σ_] :=
  If[v === t,
    σ,
    If[occursIn[v, t],
      HOL`Error`holError["parser", "occurs check failed",
        <|"var" -> v, "in" -> t|>],
      Module[{newSubst, composed},
        newSubst = <|v -> t|>;
        composed = HOL`Types`typeSubst[newSubst, #] & /@ σ;
        Append[composed, v -> t]
      ]
    ]
  ];

occursIn[v_, t_] := MemberQ[HOL`Types`tyvars[t], v];

(* ============================================================ *)
(* apply substitution to term + canonicalize.                   *)

applyToTerm[σ_, t_] :=
  t /. {
    var[n_String, ty_]      :> var[n, HOL`Types`typeSubst[σ, ty]],
    const[n_String, ty_]    :> const[n, HOL`Types`typeSubst[σ, ty]],
    bvar[k_Integer, ty_]    :> bvar[k, HOL`Types`typeSubst[σ, ty]]
  };

canonicalize[v : var[_String, _]] := v;
canonicalize[c : const[n_String, ty_]] := mkConst[n, ty];
canonicalize[bv : bvar[_Integer, _]] := bv;
canonicalize[comb[f_, x_]] := mkComb[canonicalize[f], canonicalize[x]];
canonicalize[abs[var[n_String, ty_], body_, _]] :=
  mkAbs[var[n, ty], canonicalize[body]];

(* ============================================================ *)
(* public API                                                   *)

parseTerm[s_String] :=
  Module[{raw, infResult, σ, applied},
    $tokens = tokenize[s];
    $idx = 1;
    $tvCounter = 0;
    $freeVarTypes = <||>;
    raw = parseExpr[0];
    expectKind["eof"];
    infResult = inferImpl[raw, <||>];
    σ = unify[infResult[[3]]];
    applied = applyToTerm[σ, infResult[[1]]];
    canonicalize[applied]
  ];

parseType[s_String] :=
  Module[{ty},
    $tokens = tokenize[s];
    $idx = 1;
    ty = parseTypeExpr[];
    expectKind["eof"];
    ty
  ];

End[];
EndPackage[];
