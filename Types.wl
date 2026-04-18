(* ::Package:: *)

BeginPackage["HOL`Types`", {"HOL`Error`"}];

tyVar::usage        = "tyVar[name] — type-variable head. Construct via mkVarType.";
tyApp::usage        = "tyApp[name, args] — type-application head. Construct via mkType.";
mkVarType::usage    = "mkVarType[name] validates name is a nonempty String and returns tyVar[name].";
mkType::usage       = "mkType[name, args] checks arity against the internal table and returns tyApp[name, args].";
destVarType::usage  = "destVarType[ty] returns the name of a tyVar; throws 'type' otherwise.";
destType::usage     = "destType[ty] returns {name, args} of a tyApp; throws 'type' otherwise.";
tyvars::usage       = "tyvars[ty] returns the sorted list of distinct tyVar subexpressions of ty.";
typeSubst::usage    = "typeSubst[theta, ty] parallel-substitutes type variables; theta is an Association or list of rules keyed by tyVar.";
typeArity::usage    = "typeArity[name] returns the arity of a type constructor; throws 'type' if unknown.";
boolTy::usage       = "boolTy — the built-in type tyApp[\"bool\", {}].";
indTy::usage        = "indTy — the built-in type tyApp[\"ind\", {}].";
tyFun::usage        = "tyFun[a, b] builds the function type a -> b = tyApp[\"fun\", {a, b}].";

Begin["`Private`"];

arityTable = <|"bool" -> 0, "ind" -> 0, "fun" -> 2|>;

typeArity[n_String] :=
  Lookup[arityTable, n,
    HOL`Error`holError["type", "typeArity: unknown type constructor", <|"name" -> n|>]];

mkVarType[n_String] /; StringLength[n] > 0 := tyVar[n];
mkVarType[n_] :=
  HOL`Error`holError["type", "mkVarType: name must be a nonempty string", <|"got" -> n|>];

mkType[n_String, args_List] :=
  Module[{ar = typeArity[n]},
    If[Length[args] =!= ar,
      HOL`Error`holError["type", "mkType: arity mismatch",
        <|"name" -> n, "expected" -> ar, "got" -> Length[args]|>]];
    tyApp[n, args]
  ];
mkType[n_, args_] :=
  HOL`Error`holError["type", "mkType: bad arguments", <|"name" -> n, "args" -> args|>];

destVarType[tyVar[n_String]] := n;
destVarType[other_] :=
  HOL`Error`holError["type", "destVarType: not a type variable", <|"got" -> other|>];

destType[tyApp[n_String, args_List]] := {n, args};
destType[other_] :=
  HOL`Error`holError["type", "destType: not a type application", <|"got" -> other|>];

tyvars[tyVar[n_String]] := {tyVar[n]};
tyvars[tyApp[_String, args_List]] := Union @@ Append[tyvars /@ args, {}];

typeSubst[theta_Association, ty_] := typeSubstImpl[theta, ty];
typeSubst[theta : {___Rule}, ty_] := typeSubst[Association[theta], ty];

typeSubstImpl[theta_, v : tyVar[_String]] := Lookup[theta, v, v];
typeSubstImpl[theta_, tyApp[n_String, args_List]] :=
  tyApp[n, typeSubstImpl[theta, #] & /@ args];

boolTy = tyApp["bool", {}];
indTy = tyApp["ind", {}];

tyFun[a_, b_] := mkType["fun", {a, b}];

End[];
EndPackage[];
