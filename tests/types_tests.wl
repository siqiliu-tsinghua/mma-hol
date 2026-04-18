(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Kernel`"];

HOLTest`runTests["types: construction", Module[{},
  HOLTest`assertEq[mkVarType["a"], tyVar["a"], "mkVarType returns tyVar"];
  HOLTest`assertEq[mkType["bool", {}], tyApp["bool", {}], "mkType bool"];
  HOLTest`assertEq[mkType["ind", {}], tyApp["ind", {}], "mkType ind"];
  HOLTest`assertEq[boolTy, tyApp["bool", {}], "boolTy constant"];
  HOLTest`assertEq[indTy, tyApp["ind", {}], "indTy constant"];
  HOLTest`assertEq[tyFun[boolTy, indTy], tyApp["fun", {boolTy, indTy}], "tyFun structure"];
  HOLTest`assertEq[typeArity["bool"], 0, "typeArity bool"];
  HOLTest`assertEq[typeArity["fun"], 2, "typeArity fun"];
]];

HOLTest`runTests["types: destruction", Module[{a, t},
  a = mkVarType["a"];
  HOLTest`assertEq[destVarType[a], "a", "destVarType roundtrip"];
  t = tyFun[a, a];
  HOLTest`assertEq[destType[t], {"fun", {a, a}}, "destType roundtrip"];
  HOLTest`assertEq[destType[boolTy], {"bool", {}}, "destType bool"];
  HOLTest`assertThrows[destVarType[boolTy], "type", "destVarType rejects tyApp"];
  HOLTest`assertThrows[destType[a], "type", "destType rejects tyVar"];
]];

HOLTest`runTests["types: errors", Module[{},
  HOLTest`assertThrows[mkVarType[""], "type", "empty name rejected"];
  HOLTest`assertThrows[mkVarType[42], "type", "non-string name rejected"];
  HOLTest`assertThrows[mkType["foo", {}], "type", "unknown constructor"];
  HOLTest`assertThrows[mkType["fun", {boolTy}], "type", "arity too low"];
  HOLTest`assertThrows[mkType["fun", {boolTy, boolTy, boolTy}], "type", "arity too high"];
  HOLTest`assertThrows[mkType["bool", {boolTy}], "type", "nullary with args"];
  HOLTest`assertThrows[typeArity["notReal"], "type", "typeArity unknown"];
]];

HOLTest`runTests["types: tyvars", Module[{a, b, t1, t2},
  a = mkVarType["a"];
  b = mkVarType["b"];
  HOLTest`assertEq[tyvars[a], {a}, "tyvars of a variable"];
  HOLTest`assertEq[tyvars[boolTy], {}, "tyvars of nullary"];
  t1 = tyFun[a, b];
  HOLTest`assertEq[tyvars[t1], Sort[{a, b}], "tyvars of a fun"];
  t2 = tyFun[t1, t1];
  HOLTest`assertEq[tyvars[t2], Sort[{a, b}], "tyvars deduplicates across subtrees"];
  HOLTest`assertEq[tyvars[tyFun[boolTy, indTy]], {}, "tyvars of ground type"];
]];

HOLTest`runTests["types: substitution", Module[{a, b, t, theta, result, expected},
  a = mkVarType["a"];
  b = mkVarType["b"];
  t = tyFun[tyFun[a, b], tyFun[a, b]];
  theta = <|a -> boolTy, b -> indTy|>;
  result = typeSubst[theta, t];
  expected = tyFun[tyFun[boolTy, indTy], tyFun[boolTy, indTy]];
  HOLTest`assertEq[result, expected, "typeSubst on (a->b)->a->b"];
  HOLTest`assertEq[typeSubst[<||>, t], t, "typeSubst identity (empty)"];
  HOLTest`assertEq[typeSubst[{a -> boolTy, b -> indTy}, t], expected,
    "typeSubst accepts list of rules"];
  HOLTest`assertEq[
    typeSubst[{a -> b, b -> a}, tyFun[a, b]],
    tyFun[b, a],
    "typeSubst is parallel, not sequential"
  ];
  HOLTest`assertEq[tyvars[result], {}, "substituted ground type has no tyvars"];
  HOLTest`assertEq[
    typeSubst[<|a -> boolTy|>, tyFun[a, b]],
    tyFun[boolTy, b],
    "typeSubst leaves untouched vars alone"
  ];
]];

HOLTest`runTests["types: M1 acceptance", Module[{a, b, t, theta, grounded},
  a = mkVarType["a"];
  b = mkVarType["b"];
  t = tyFun[tyFun[a, b], tyFun[a, b]];
  HOLTest`assertEq[Head[t], tyApp, "outer head is tyApp"];
  HOLTest`assertEq[destType[t][[1]], "fun", "outermost constructor is fun"];
  HOLTest`assertEq[Length[destType[t][[2]]], 2, "fun has two args"];
  theta = <|a -> boolTy, b -> indTy|>;
  grounded = typeSubst[theta, t];
  HOLTest`assertEq[tyvars[grounded], {}, "acceptance: fully grounded after substitution"];
  HOLTest`assertEq[
    grounded,
    tyFun[tyFun[boolTy, indTy], tyFun[boolTy, indTy]],
    "acceptance: concrete shape"
  ];
]];
