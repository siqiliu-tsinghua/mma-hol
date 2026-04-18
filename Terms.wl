(* ::Package:: *)

BeginPackage["HOL`Terms`", {"HOL`Error`", "HOL`Types`"}];

var::usage     = "var[name, type] — variable head. Construct via mkVar.";
const::usage   = "const[name, type] — constant head. Construct via mkConst.";
comb::usage    = "comb[f, x] — application head. Construct via mkComb.";
abs::usage     = "abs[bv, body, origin] — lambda head. Construct via mkAbs.";

mkVar::usage      = "mkVar[name, ty] returns var[name, ty] after validating the name is a nonempty string and not in the reserved _b<digits> bound-variable namespace.";
mkConst::usage    = "mkConst[name, ty] returns const[name, ty] if ty is an instance of the registered generic type for name.";
mkComb::usage     = "mkComb[f, x] returns comb[f, x] if typeOf[f] is fun[dom, rng] and typeOf[x] === dom.";
mkAbs::usage      = "mkAbs[v, body] returns an α-canonical abs. v must be a non-reserved variable; occurrences of v in body are renamed to the canonical bound-variable name for their depth.";

destVar::usage    = "destVar[var[n,t]] returns {n, t}; throws 'term' otherwise.";
destConst::usage  = "destConst[const[n,t]] returns {n, t}; throws 'term' otherwise.";
destComb::usage   = "destComb[comb[f,x]] returns {f, x}; throws 'term' otherwise.";
destAbs::usage    = "destAbs[abs[bv,body,origin]] returns {bv, body, origin}; throws 'term' otherwise.";

isVar::usage      = "isVar[t] — head-arity predicate.";
isConst::usage    = "isConst[t] — head-arity predicate.";
isComb::usage     = "isComb[t] — head-arity predicate.";
isAbs::usage      = "isAbs[t] — head-arity predicate.";

typeOf::usage     = "typeOf[term] returns the type of a well-formed term.";
freesIn::usage    = "freesIn[term] returns the sorted list of distinct free variables (excluding canonical bound-var references).";
vsubst::usage     = "vsubst[theta, term] substitutes terms for variables; theta is keyed by var. Requires type-preserving entries; capture-free by canonical form.";
instType::usage   = "instType[theta, term] applies a type substitution to every type annotation in the term.";
aconv::usage      = "aconv[s, t] tests α-equivalence (ignores origin slots on abs).";

mkEq::usage       = "mkEq[s, t] builds the term (s = t) after checking typeOf[s] === typeOf[t].";
constType::usage  = "constType[name] returns the registered generic type of a constant.";
listConstants::usage = "listConstants[] returns the sorted list of currently registered constant names.";

Begin["`Private`"];

canonicalBoundQ[n_String] := StringMatchQ[n, "_b" ~~ DigitCharacter ..];
decodeBoundIndex[n_String] := FromDigits[StringDrop[n, 2]];

constTypeTable = <||>;

registerConst[name_String, ty_] := (constTypeTable[name] = ty;);

listConstants[] := Sort[Keys[constTypeTable]];

constType[name_String] :=
  Lookup[constTypeTable, name,
    HOL`Error`holError["term", "constType: unknown constant", <|"name" -> name|>]];

With[{alpha = tyVar["a"]},
  registerConst["=", tyFun[alpha, tyFun[alpha, boolTy]]];
];

tyMatch[tyVar[n_String], target_, theta_Association] :=
  Module[{k = tyVar[n]},
    If[KeyExistsQ[theta, k],
      If[theta[k] === target, theta,
        HOL`Error`holError["term", "tyMatch: inconsistent binding",
          <|"var" -> k, "old" -> theta[k], "new" -> target|>]],
      Append[theta, k -> target]
    ]
  ];
tyMatch[tyApp[n_String, pArgs_List], tyApp[m_String, tArgs_List], theta_Association] :=
  If[n =!= m || Length[pArgs] =!= Length[tArgs],
    HOL`Error`holError["term", "tyMatch: type structure mismatch",
      <|"pattern" -> tyApp[n, pArgs], "target" -> tyApp[m, tArgs]|>],
    Fold[tyMatch[#2[[1]], #2[[2]], #1] &, theta, Transpose[{pArgs, tArgs}]]
  ];
tyMatch[p_, t_, _] :=
  HOL`Error`holError["term", "tyMatch: incompatible shapes",
    <|"pattern" -> p, "target" -> t|>];

destFunType[tyApp["fun", {dom_, rng_}]] := {dom, rng};
destFunType[other_] :=
  HOL`Error`holError["term", "destFunType: not a function type", <|"got" -> other|>];

mkVar[n_String, t_] /; StringLength[n] > 0 && ! canonicalBoundQ[n] := var[n, t];
mkVar[n_, t_] :=
  HOL`Error`holError["term", "mkVar: invalid name", <|"name" -> n, "type" -> t|>];

mkConst[name_String, ty_] :=
  Module[{},
    tyMatch[constType[name], ty, <||>];
    const[name, ty]
  ];

mkComb[f_, x_] :=
  Module[{ft, xt, dom, rng},
    ft = typeOf[f];
    xt = typeOf[x];
    {dom, rng} = destFunType[ft];
    If[dom =!= xt,
      HOL`Error`holError["term", "mkComb: argument type mismatch",
        <|"fnType" -> ft, "argType" -> xt, "expected" -> dom|>]];
    comb[f, x]
  ];

mkAbs[v : var[n_String, _], body_] /; ! canonicalBoundQ[n] :=
  Module[{ty = v[[2]], canon, walked},
    canon = var["_b0", ty];
    walked = bindWalk[body, v, 0];
    abs[canon, walked, n]
  ];
mkAbs[var[n_String, _], _] /; canonicalBoundQ[n] :=
  HOL`Error`holError["term", "mkAbs: binder name must not be reserved",
    <|"name" -> n|>];
mkAbs[v_, _] :=
  HOL`Error`holError["term", "mkAbs: first arg must be a var", <|"got" -> v|>];

bindWalk[v : var[_String, _], target_, depth_Integer] :=
  If[v === target, var["_b" <> ToString[depth], v[[2]]], v];
bindWalk[c : const[_, _], _, _] := c;
bindWalk[comb[f_, x_], target_, depth_] :=
  comb[bindWalk[f, target, depth], bindWalk[x, target, depth]];
bindWalk[abs[bv_, body_, o_], target_, depth_] :=
  abs[bv, bindWalk[body, target, depth + 1], o];

destVar[var[n_String, t_]] := {n, t};
destVar[other_] :=
  HOL`Error`holError["term", "destVar: not a var", <|"got" -> other|>];

destConst[const[n_String, t_]] := {n, t};
destConst[other_] :=
  HOL`Error`holError["term", "destConst: not a const", <|"got" -> other|>];

destComb[comb[f_, x_]] := {f, x};
destComb[other_] :=
  HOL`Error`holError["term", "destComb: not a comb", <|"got" -> other|>];

destAbs[abs[bv_, body_, origin_]] := {bv, body, origin};
destAbs[other_] :=
  HOL`Error`holError["term", "destAbs: not an abs", <|"got" -> other|>];

isVar[var[_, _]] := True;
isVar[_] := False;
isConst[const[_, _]] := True;
isConst[_] := False;
isComb[comb[_, _]] := True;
isComb[_] := False;
isAbs[abs[_, _, _]] := True;
isAbs[_] := False;

typeOf[var[_, t_]] := t;
typeOf[const[_, t_]] := t;
typeOf[comb[f_, _]] := destFunType[typeOf[f]][[2]];
typeOf[abs[bv_, body_, _]] := tyFun[typeOf[bv], typeOf[body]];

freesIn[t_] := Sort[DeleteDuplicates[freesWalk[t, 0]]];

freesWalk[var[n_String, t_], depth_Integer] :=
  If[canonicalBoundQ[n] && decodeBoundIndex[n] < depth, {}, {var[n, t]}];
freesWalk[const[_, _], _] := {};
freesWalk[comb[f_, x_], d_] := Join[freesWalk[f, d], freesWalk[x, d]];
freesWalk[abs[_, body_, _], d_] := freesWalk[body, d + 1];

vsubst[theta_Association, t_] := (validateVsubst[theta]; vsubstImpl[theta, t]);
vsubst[theta : {___Rule}, t_] := vsubst[Association[theta], t];

validateVsubst[theta_Association] :=
  KeyValueMap[
    Function[{k, v},
      If[! MatchQ[k, var[_String, _]] || canonicalBoundQ[k[[1]]],
        HOL`Error`holError["term", "vsubst: key must be a non-reserved var",
          <|"key" -> k|>]];
      If[k[[2]] =!= typeOf[v],
        HOL`Error`holError["term", "vsubst: type mismatch",
          <|"var" -> k, "varType" -> k[[2]], "replType" -> typeOf[v]|>]];
    ],
    theta
  ];

vsubstImpl[theta_, v : var[_, _]] := Lookup[theta, v, v];
vsubstImpl[theta_, c : const[_, _]] := c;
vsubstImpl[theta_, comb[f_, x_]] := comb[vsubstImpl[theta, f], vsubstImpl[theta, x]];
vsubstImpl[theta_, abs[bv_, body_, o_]] := abs[bv, vsubstImpl[theta, body], o];

instType[theta_Association, t_] := instTypeImpl[theta, t];
instType[theta : {___Rule}, t_] := instType[Association[theta], t];

instTypeImpl[theta_, var[n_String, t_]] := var[n, typeSubst[theta, t]];
instTypeImpl[theta_, const[n_String, t_]] := const[n, typeSubst[theta, t]];
instTypeImpl[theta_, comb[f_, x_]] := comb[instTypeImpl[theta, f], instTypeImpl[theta, x]];
instTypeImpl[theta_, abs[bv_, body_, o_]] :=
  abs[instTypeImpl[theta, bv], instTypeImpl[theta, body], o];

aconv[s_, t_] := stripOrigin[s] === stripOrigin[t];

stripOrigin[v : var[_, _]] := v;
stripOrigin[c : const[_, _]] := c;
stripOrigin[comb[f_, x_]] := comb[stripOrigin[f], stripOrigin[x]];
stripOrigin[abs[bv_, body_, _]] := abs[bv, stripOrigin[body], "_"];

mkEq[s_, t_] :=
  Module[{ty = typeOf[s]},
    If[ty =!= typeOf[t],
      HOL`Error`holError["term", "mkEq: type mismatch",
        <|"lhsType" -> ty, "rhsType" -> typeOf[t]|>]];
    comb[comb[mkConst["=", tyFun[ty, tyFun[ty, boolTy]]], s], t]
  ];

End[];
EndPackage[];
