(* ::Package:: *)

BeginPackage["HOL`Kernel`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`"}];

mkType::usage        = "mkType[name, args] checks arity against the kernel's arity table and returns tyApp[name, args].";
typeArity::usage     = "typeArity[name] returns the arity of a type constructor; throws 'type' if unknown.";
boolTy::usage        = "boolTy — the built-in type tyApp[\"bool\", {}].";
indTy::usage         = "indTy — the built-in type tyApp[\"ind\", {}].";
tyFun::usage         = "tyFun[a, b] builds the function type a -> b = tyApp[\"fun\", {a, b}].";
mkConst::usage       = "mkConst[name, ty] returns const[name, ty] if ty is an instance of the kernel-registered generic type for name.";
constType::usage     = "constType[name] returns the kernel-registered generic type of a constant.";
listConstants::usage = "listConstants[] returns the sorted list of currently registered constant names.";
mkEq::usage          = "mkEq[s, t] builds the term (s = t) after checking typeOf[s] === typeOf[t].";

Begin["`Private`"];

Module[{arityTable, constTypeTable, tyMatch, registerConst},

  arityTable = <|"bool" -> 0, "ind" -> 0, "fun" -> 2|>;
  constTypeTable = <||>;

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

  registerConst[name_String, ty_] := (constTypeTable[name] = ty;);

  HOL`Kernel`typeArity[n_String] :=
    Lookup[arityTable, n,
      HOL`Error`holError["type", "typeArity: unknown type constructor", <|"name" -> n|>]];

  HOL`Kernel`mkType[n_String, args_List] :=
    Module[{ar},
      ar = Lookup[arityTable, n,
        HOL`Error`holError["type", "typeArity: unknown type constructor", <|"name" -> n|>]];
      If[Length[args] =!= ar,
        HOL`Error`holError["type", "mkType: arity mismatch",
          <|"name" -> n, "expected" -> ar, "got" -> Length[args]|>]];
      tyApp[n, args]
    ];
  HOL`Kernel`mkType[n_, args_] :=
    HOL`Error`holError["type", "mkType: bad arguments", <|"name" -> n, "args" -> args|>];

  HOL`Kernel`boolTy = tyApp["bool", {}];
  HOL`Kernel`indTy  = tyApp["ind",  {}];
  HOL`Kernel`tyFun[a_, b_] := HOL`Kernel`mkType["fun", {a, b}];

  With[{alpha = tyVar["a"]},
    registerConst["=", tyApp["fun", {alpha, tyApp["fun", {alpha, tyApp["bool", {}]}]}]];
  ];

  HOL`Kernel`constType[name_String] :=
    Lookup[constTypeTable, name,
      HOL`Error`holError["term", "constType: unknown constant", <|"name" -> name|>]];

  HOL`Kernel`listConstants[] := Sort[Keys[constTypeTable]];

  HOL`Kernel`mkConst[name_String, ty_] :=
    Module[{gen},
      gen = HOL`Kernel`constType[name];
      tyMatch[gen, ty, <||>];
      const[name, ty]
    ];

  HOL`Kernel`mkEq[s_, t_] :=
    Module[{ty},
      ty = typeOf[s];
      If[ty =!= typeOf[t],
        HOL`Error`holError["term", "mkEq: type mismatch",
          <|"lhsType" -> ty, "rhsType" -> typeOf[t]|>]];
      comb[
        comb[
          HOL`Kernel`mkConst["=", tyApp["fun", {ty, tyApp["fun", {ty, tyApp["bool", {}]}]}]],
          s],
        t]
    ];
];

End[];
EndPackage[];
