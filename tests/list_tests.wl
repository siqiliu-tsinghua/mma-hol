(* ::Package:: *)

(* M7-4-a.1 list tests: type creation + NIL shape. *)

BeginPackage["HOLListTests`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOLTest`",
  "HOL`Stdlib`Num`", "HOL`Stdlib`Option`", "HOL`Stdlib`List`"
}];

Begin["`Private`"];

αTy = mkVarType["A"];
numTy = mkType["num", {}];
optionATy = HOL`Stdlib`Option`optionTy[αTy];
carrierTy = tyFun[numTy, optionATy];
listATy = HOL`Stdlib`List`listTy[αTy];

HOLTest`runTests["stdlib/List: isListP has type (num → α option) → bool",
  Module[{ty},
    ty = HOL`Kernel`constType["isListP"];
    HOLTest`assertEq[ty, tyFun[carrierTy, boolTy],
      "isListP : (num → α option) → bool"];
]];

HOLTest`runTests["stdlib/List: isListPDefThm — concl `isListP = …` with no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`isListPDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["isListP", _]], _]],
      "concl shape ⊢ isListP = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: list type has arity 1",
  HOLTest`assertEq[HOL`Kernel`typeArity["list"], 1, "list has arity 1"];
];

HOLTest`runTests["stdlib/List: ABS_list has type (num → α option) → α list",
  Module[{ty},
    ty = HOL`Kernel`constType["ABS_list"];
    HOLTest`assertEq[ty, tyFun[carrierTy, listATy],
      "ABS_list : (num → α option) → α list"];
]];

HOLTest`runTests["stdlib/List: REP_list has type α list → (num → α option)",
  Module[{ty},
    ty = HOL`Kernel`constType["REP_list"];
    HOLTest`assertEq[ty, tyFun[listATy, carrierTy],
      "REP_list : α list → (num → α option)"];
]];

HOLTest`runTests["stdlib/List: absRepListThm — ⊢ ABS_list (REP_list a) = a, no hyps",
  Module[{c, expected, aV},
    aV = mkVar["a", listATy];
    expected = mkEq[
      mkComb[HOL`Stdlib`List`absListConst[],
        mkComb[HOL`Stdlib`List`repListConst[], aV]],
      aV];
    c = concl[HOL`Stdlib`List`absRepListThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "ABS_list (REP_list a) = a"];
    HOLTest`assertEq[hyp[HOL`Stdlib`List`absRepListThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: NIL has type α list",
  Module[{ty},
    ty = HOL`Kernel`constType["NIL"];
    HOLTest`assertEq[ty, listATy, "NIL : α list"];
]];

HOLTest`runTests["stdlib/List: nilDefThm — concl `NIL = ABS_list (λi. NONE)`, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`List`nilDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["NIL", _]],
              comb[const["ABS_list", _], abs[_, _, _]]]],
      "concl shape ⊢ NIL = ABS_list (λi. NONE)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/List: repNilThm — ⊢ REP_list NIL = (λi. NONE), no hyps",
  Module[{c, dThm, iV, expected, noneTm},
    dThm = HOL`Stdlib`List`repNilThm;
    c = concl[dThm];
    iV = mkVar["i", numTy];
    noneTm = mkConst["NONE", optionATy];
    expected = mkEq[
      mkComb[HOL`Stdlib`List`repListConst[], HOL`Stdlib`List`nilConst[]],
      mkAbs[iV, noneTm]];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "REP_list NIL = (λi. NONE)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

End[];
EndPackage[];
