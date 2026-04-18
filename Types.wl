(* ::Package:: *)

BeginPackage["HOL`Types`", {"HOL`Error`"}];

tyVar::usage        = "tyVar[name] — type-variable head. Construct via mkVarType.";
tyApp::usage        = "tyApp[name, args] — type-application head. Construct via mkType (from HOL`Kernel`).";
mkVarType::usage    = "mkVarType[name] validates name is a nonempty String and returns tyVar[name].";
destVarType::usage  = "destVarType[ty] returns the name of a tyVar; throws 'type' otherwise.";
destType::usage     = "destType[ty] returns {name, args} of a tyApp; throws 'type' otherwise.";
tyvars::usage       = "tyvars[ty] returns the sorted list of distinct tyVar subexpressions of ty.";
typeSubst::usage    = "typeSubst[theta, ty] parallel-substitutes type variables; theta is an Association or list of rules keyed by tyVar.";

Begin["`Private`"];

mkVarType[n_String] /; StringLength[n] > 0 := tyVar[n];
mkVarType[n_] :=
  HOL`Error`holError["type", "mkVarType: name must be a nonempty string", <|"got" -> n|>];

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

End[];
EndPackage[];
