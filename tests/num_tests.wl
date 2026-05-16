(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Num`"];

(* ===== IND_SUC definition + properties ===== *)

HOLTest`runTests["stdlib/Num: IND_SUC has type ind → ind",
  Module[{ty},
    ty = HOL`Kernel`constType["IND_SUC"];
    HOLTest`assertEq[ty, tyFun[mkType["ind", {}], mkType["ind", {}]],
      "IND_SUC : ind → ind"];
]];

HOLTest`runTests["stdlib/Num: indSuccDefThm has correct shape",
  Module[{c, lhs},
    c = HOL`Kernel`concl[HOL`Stdlib`Num`indSuccDefThm];
    lhs = c[[1, 2]];
    HOLTest`assertEq[lhs, HOL`Stdlib`Num`indSuccConst[],
      "LHS of indSuccDefThm is IND_SUC constant"];
    HOLTest`assertEq[HOL`Kernel`hyp[HOL`Stdlib`Num`indSuccDefThm], {},
      "indSuccDefThm has no hyps"];
]];

HOLTest`runTests["stdlib/Num: indSuccPropThm = ONE_ONE IND_SUC ∧ ¬ ONTO IND_SUC",
  Module[{c, expected, indTy, indFunTy, ind2bool, oneOneAppl, ontoAppl,
          andC, notC},
    indTy = mkType["ind", {}]; indFunTy = tyFun[indTy, indTy];
    ind2bool = tyFun[indFunTy, boolTy];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    oneOneAppl = mkComb[mkConst["ONE_ONE", ind2bool],
                        HOL`Stdlib`Num`indSuccConst[]];
    ontoAppl   = mkComb[mkConst["ONTO", ind2bool],
                        HOL`Stdlib`Num`indSuccConst[]];
    expected = mkComb[mkComb[andC, oneOneAppl], mkComb[notC, ontoAppl]];
    c = HOL`Kernel`concl[HOL`Stdlib`Num`indSuccPropThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "concl is ONE_ONE IND_SUC ∧ ¬ ONTO IND_SUC"];
    HOLTest`assertEq[HOL`Kernel`hyp[HOL`Stdlib`Num`indSuccPropThm], {},
      "indSuccPropThm has no hyps"];
]];

HOLTest`runTests["stdlib/Num: CONJUNCT1/2 give ONE_ONE and ¬ ONTO theorems",
  Module[{indTy, indFunTy, ind2bool, oneOneTm, notOntoTm},
    indTy = mkType["ind", {}]; indFunTy = tyFun[indTy, indTy];
    ind2bool = tyFun[indFunTy, boolTy];
    oneOneTm = mkComb[mkConst["ONE_ONE", ind2bool],
                      HOL`Stdlib`Num`indSuccConst[]];
    notOntoTm = mkComb[mkConst["¬", tyFun[boolTy, boolTy]],
      mkComb[mkConst["ONTO", ind2bool], HOL`Stdlib`Num`indSuccConst[]]];
    HOLTest`assertTrue[
      HOL`Terms`aconv[concl[HOL`Stdlib`Num`indSuccOneOneThm], oneOneTm],
      "indSuccOneOneThm: ⊢ ONE_ONE IND_SUC"];
    HOLTest`assertTrue[
      HOL`Terms`aconv[concl[HOL`Stdlib`Num`indSuccNotOntoThm], notOntoTm],
      "indSuccNotOntoThm: ⊢ ¬ ONTO IND_SUC"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`indSuccOneOneThm], {}, "no hyps"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`indSuccNotOntoThm], {}, "no hyps"];
]];

(* ===== IND_0 definition + property ===== *)

HOLTest`runTests["stdlib/Num: IND_0 has type ind",
  Module[{ty},
    ty = HOL`Kernel`constType["IND_0"];
    HOLTest`assertEq[ty, mkType["ind", {}], "IND_0 : ind"];
]];

HOLTest`runTests["stdlib/Num: ind0DefThm has correct shape",
  Module[{c, lhs},
    c = concl[HOL`Stdlib`Num`ind0DefThm];
    lhs = c[[1, 2]];
    HOLTest`assertEq[lhs, HOL`Stdlib`Num`ind0Const[],
      "LHS of ind0DefThm is IND_0 constant"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`ind0DefThm], {},
      "ind0DefThm has no hyps"];
]];

HOLTest`runTests["stdlib/Num: ind0NotInRangeThm = ¬ ∃x. IND_0 = IND_SUC x",
  Module[{c, expected, indTy, xV, ind0Tm, indSucTm, eqInner, exInner},
    indTy = mkType["ind", {}];
    xV = mkVar["x", indTy];
    ind0Tm = HOL`Stdlib`Num`ind0Const[];
    indSucTm = HOL`Stdlib`Num`indSuccConst[];
    eqInner = mkEq[ind0Tm, mkComb[indSucTm, xV]];
    exInner = mkComb[
      mkConst["∃", tyFun[tyFun[indTy, boolTy], boolTy]],
      mkAbs[xV, eqInner]];
    expected = mkComb[mkConst["¬", tyFun[boolTy, boolTy]], exInner];
    c = concl[HOL`Stdlib`Num`ind0NotInRangeThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "concl is ¬ ∃x. IND_0 = IND_SUC x"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`ind0NotInRangeThm], {}, "no hyps"];
]];
