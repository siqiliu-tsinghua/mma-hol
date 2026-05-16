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

(* ===== NUM_REP + num type ===== *)

HOLTest`runTests["stdlib/Num: NUM_REP : ind → bool",
  Module[{ty, indTy},
    indTy = mkType["ind", {}];
    ty = HOL`Kernel`constType["NUM_REP"];
    HOLTest`assertEq[ty, tyFun[indTy, boolTy], "NUM_REP : ind → bool"];
]];

HOLTest`runTests["stdlib/Num: numRepDefThm LHS is NUM_REP constant",
  Module[{c, lhs},
    c = concl[HOL`Stdlib`Num`numRepDefThm];
    lhs = c[[1, 2]];
    HOLTest`assertEq[lhs, HOL`Stdlib`Num`numRepConst[],
      "LHS of numRepDefThm is NUM_REP constant"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numRepDefThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: numRepIND0Witness has shape `predicate IND_0`",
  Module[{c, indTy},
    indTy = mkType["ind", {}];
    c = concl[HOL`Stdlib`Num`numRepIND0Witness];
    HOLTest`assertTrue[
      MatchQ[c, comb[abs[bvar[0, _], _, _String],
                     const["IND_0", _]]],
      "concl is `(λn. …) IND_0` — un-β form for newBasicTypeDefinition"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numRepIND0Witness], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: num type arity 0",
  HOLTest`assertEq[HOL`Kernel`typeArity["num"], 0,
    "num is a monomorphic ground type"];
];

HOLTest`runTests["stdlib/Num: ABS_num and REP_num have right types",
  Module[{indTy, numTy},
    indTy = mkType["ind", {}]; numTy = mkType["num", {}];
    HOLTest`assertEq[HOL`Kernel`constType["ABS_num"], tyFun[indTy, numTy],
      "ABS_num : ind → num"];
    HOLTest`assertEq[HOL`Kernel`constType["REP_num"], tyFun[numTy, indTy],
      "REP_num : num → ind"];
]];

HOLTest`runTests["stdlib/Num: absRepNumThm = ∀-stripped ABS (REP a) = a",
  Module[{c, indTy, numTy, aV, expected},
    indTy = mkType["ind", {}]; numTy = mkType["num", {}];
    aV = mkVar["a", numTy];
    expected = mkEq[
      mkComb[HOL`Stdlib`Num`absNumConst[],
        mkComb[HOL`Stdlib`Num`repNumConst[], aV]],
      aV];
    c = concl[HOL`Stdlib`Num`absRepNumThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "absRepNumThm: ⊢ ABS_num (REP_num a) = a"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`absRepNumThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: repAbsNumThm is `predicate r = (REP (ABS r) = r)`",
  Module[{c},
    c = concl[HOL`Stdlib`Num`repAbsNumThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], comb[abs[_, _, _String], var["r", _]]],
                     comb[comb[const["=", _],
                               comb[const["REP_num", _],
                                    comb[const["ABS_num", _], var["r", _]]]],
                          var["r", _]]]],
      "shape: (λn. body) r = (REP_num (ABS_num r) = r)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`repAbsNumThm], {}, "no hyps"];
]];

(* ===== 0 and SUC ===== *)

HOLTest`runTests["stdlib/Num: 0 : num and SUC : num → num",
  Module[{numTy},
    numTy = mkType["num", {}];
    HOLTest`assertEq[HOL`Kernel`constType["0"], numTy, "0 : num"];
    HOLTest`assertEq[HOL`Kernel`constType["SUC"], tyFun[numTy, numTy],
      "SUC : num → num"];
]];

HOLTest`runTests["stdlib/Num: zeroDefThm = ⊢ 0 = ABS_num IND_0",
  Module[{c, expected},
    expected = mkEq[
      HOL`Stdlib`Num`zeroConst[],
      mkComb[HOL`Stdlib`Num`absNumConst[], HOL`Stdlib`Num`ind0Const[]]];
    c = concl[HOL`Stdlib`Num`zeroDefThm];
    HOLTest`assertEq[c, expected, "concl is ⊢ 0 = ABS_num IND_0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`zeroDefThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: sucDefThm has LHS = SUC constant",
  Module[{c, lhs},
    c = concl[HOL`Stdlib`Num`sucDefThm];
    lhs = c[[1, 2]];
    HOLTest`assertEq[lhs, HOL`Stdlib`Num`sucConst[],
      "LHS of sucDefThm is SUC constant"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`sucDefThm], {}, "no hyps"];
]];
