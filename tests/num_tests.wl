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

(* ===== NUM_REP intro rules ===== *)

HOLTest`runTests["stdlib/Num: numRepInd0Thm = ⊢ NUM_REP IND_0",
  Module[{c, expected},
    expected = mkComb[HOL`Stdlib`Num`numRepConst[], HOL`Stdlib`Num`ind0Const[]];
    c = concl[HOL`Stdlib`Num`numRepInd0Thm];
    HOLTest`assertEq[c, expected, "concl is NUM_REP IND_0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numRepInd0Thm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: numRepSucThm = ⊢ ∀m. NUM_REP m ⇒ NUM_REP (IND_SUC m)",
  Module[{c, indTy, mV, expected},
    indTy = mkType["ind", {}];
    mV = mkVar["m", indTy];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[indTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[mkComb[
          mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
          mkComb[HOL`Stdlib`Num`numRepConst[], mV]],
          mkComb[HOL`Stdlib`Num`numRepConst[],
            mkComb[HOL`Stdlib`Num`indSuccConst[], mV]]]]];
    c = concl[HOL`Stdlib`Num`numRepSucThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "concl is ∀m. NUM_REP m ⇒ NUM_REP (IND_SUC m)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numRepSucThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: numRepRepNumThm = ⊢ NUM_REP (REP_num n)",
  Module[{c, numTy, nV, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    expected = mkComb[HOL`Stdlib`Num`numRepConst[],
      mkComb[HOL`Stdlib`Num`repNumConst[], nV]];
    c = concl[HOL`Stdlib`Num`numRepRepNumThm];
    HOLTest`assertEq[c, expected, "NUM_REP (REP_num n) for free n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numRepRepNumThm], {}, "no hyps"];
]];

(* ===== REP_num computation rules ===== *)

HOLTest`runTests["stdlib/Num: repZeroThm = ⊢ REP_num 0 = IND_0",
  Module[{c, expected},
    expected = mkEq[
      mkComb[HOL`Stdlib`Num`repNumConst[], HOL`Stdlib`Num`zeroConst[]],
      HOL`Stdlib`Num`ind0Const[]];
    c = concl[HOL`Stdlib`Num`repZeroThm];
    HOLTest`assertEq[c, expected, "REP_num 0 = IND_0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`repZeroThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: repSucThm = ⊢ REP_num (SUC n) = IND_SUC (REP_num n)",
  Module[{c, numTy, nV, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    expected = mkEq[
      mkComb[HOL`Stdlib`Num`repNumConst[],
        mkComb[HOL`Stdlib`Num`sucConst[], nV]],
      mkComb[HOL`Stdlib`Num`indSuccConst[],
        mkComb[HOL`Stdlib`Num`repNumConst[], nV]]];
    c = concl[HOL`Stdlib`Num`repSucThm];
    HOLTest`assertEq[c, expected, "REP_num (SUC n) = IND_SUC (REP_num n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`repSucThm], {}, "no hyps"];
]];

(* ===== Peano: SUC ≠ 0 and SUC injective ===== *)

HOLTest`runTests["stdlib/Num: sucNotZeroThm = ⊢ ∀n. ¬ (SUC n = 0)",
  Module[{c, numTy, nV, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV,
        mkComb[mkConst["¬", tyFun[boolTy, boolTy]],
          mkEq[mkComb[HOL`Stdlib`Num`sucConst[], nV],
               HOL`Stdlib`Num`zeroConst[]]]]];
    c = concl[HOL`Stdlib`Num`sucNotZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. ¬ (SUC n = 0)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`sucNotZeroThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: sucInjThm = ⊢ ∀m n. SUC m = SUC n ⇒ m = n",
  Module[{c, numTy, mV, nV, expected},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[nV,
            mkComb[mkComb[
              mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
              mkEq[mkComb[HOL`Stdlib`Num`sucConst[], mV],
                   mkComb[HOL`Stdlib`Num`sucConst[], nV]]],
              mkEq[mV, nV]]]]]];
    c = concl[HOL`Stdlib`Num`sucInjThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. SUC m = SUC n ⇒ m = n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`sucInjThm], {}, "no hyps"];
]];

(* ===== Peano: induction (capstone) ===== *)

HOLTest`runTests["stdlib/Num: numInductionThm — shape `∀P. P 0 ∧ … ⇒ ∀n. P n`",
  Module[{c, numTy},
    numTy = mkType["num", {}];
    c = concl[HOL`Stdlib`Num`numInductionThm];
    HOLTest`assertTrue[
      MatchQ[c,
        comb[const["∀", _],
          abs[bvar[0, tyApp["fun", {tyApp["num", {}], tyApp["bool", {}]}]],
            comb[comb[const["⇒", _],
              comb[comb[const["∧", _], _], _]],  (* antecedent: P 0 ∧ step *)
              comb[const["∀", _],                (* ∀n. P n *)
                abs[bvar[0, tyApp["num", {}]], _, _String]]],
            _String]]],
      "shape: ∀P. (P 0 ∧ ∀n. P n ⇒ P (SUC n)) ⇒ ∀n. P n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numInductionThm], {}, "no hyps"];
]];

(* ===== M7-3-d: ITER + iteration theorem ===== *)

HOLTest`runTests["stdlib/Num: ITER_GRAPH has type A → (A→A) → ind → A → bool",
  Module[{ty, aTy, indTy},
    aTy = mkVarType["A"]; indTy = mkType["ind", {}];
    ty = HOL`Kernel`constType["ITER_GRAPH"];
    HOLTest`assertEq[ty,
      tyFun[aTy, tyFun[tyFun[aTy, aTy],
        tyFun[indTy, tyFun[aTy, boolTy]]]],
      "ITER_GRAPH : A → (A → A) → ind → A → bool"];
]];

HOLTest`runTests["stdlib/Num: ITER has type A → (A→A) → num → A",
  Module[{ty, aTy, numTy},
    aTy = mkVarType["A"]; numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["ITER"];
    HOLTest`assertEq[ty,
      tyFun[aTy, tyFun[tyFun[aTy, aTy], tyFun[numTy, aTy]]],
      "ITER : A → (A → A) → num → A"];
]];

HOLTest`runTests["stdlib/Num: iterZeroEqThm = ⊢ ITER e f 0 = e",
  Module[{c, aTy, numTy, funATy, eV, fV, expected},
    aTy = mkVarType["A"]; numTy = mkType["num", {}];
    funATy = tyFun[aTy, aTy];
    eV = mkVar["e", aTy]; fV = mkVar["f", funATy];
    expected = mkEq[
      mkComb[mkComb[mkComb[HOL`Stdlib`Num`iterConst[], eV], fV],
        HOL`Stdlib`Num`zeroConst[]],
      eV];
    c = concl[HOL`Stdlib`Num`iterZeroEqThm];
    HOLTest`assertEq[c, expected, "ITER e f 0 = e"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`iterZeroEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: iterSucEqThm = ⊢ ∀n. ITER e f (SUC n) = f (ITER e f n)",
  Module[{c, aTy, numTy, funATy, eV, fV, nV, expected},
    aTy = mkVarType["A"]; numTy = mkType["num", {}];
    funATy = tyFun[aTy, aTy];
    eV = mkVar["e", aTy]; fV = mkVar["f", funATy];
    nV = mkVar["n", numTy];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV,
        mkEq[
          mkComb[mkComb[mkComb[HOL`Stdlib`Num`iterConst[], eV], fV],
            mkComb[HOL`Stdlib`Num`sucConst[], nV]],
          mkComb[fV,
            mkComb[mkComb[mkComb[HOL`Stdlib`Num`iterConst[], eV], fV], nV]]]]];
    c = concl[HOL`Stdlib`Num`iterSucEqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. ITER e f (SUC n) = f (ITER e f n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`iterSucEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: numIterationThm shape — ∀e f. ∃g. g 0 = e ∧ …",
  Module[{c, aTy, numTy, funATy},
    aTy = mkVarType["A"]; numTy = mkType["num", {}];
    funATy = tyFun[aTy, aTy];
    c = concl[HOL`Stdlib`Num`numIterationThm];
    HOLTest`assertTrue[
      MatchQ[c,
        comb[const["∀", _],
          abs[bvar[0, tyVar["A"]],
            comb[const["∀", _],
              abs[bvar[0, tyApp["fun", {tyVar["A"], tyVar["A"]}]],
                comb[const["∃", _],
                  abs[bvar[0, tyApp["fun", {tyApp["num", {}], tyVar["A"]}]],
                    _, _String]],
                _String]],
            _String]]],
      "shape: ∀e:A. ∀f:A→A. ∃g:num→A. (body)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numIterationThm], {}, "no hyps"];
]];

(* ===== M7-3-e: + and * ===== *)

HOLTest`runTests["stdlib/Num: + has type num → num → num",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["+"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, numTy]],
      "+ : num → num → num"];
]];

HOLTest`runTests["stdlib/Num: * has type num → num → num",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["*"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, numTy]],
      "* : num → num → num"];
]];

HOLTest`runTests["stdlib/Num: plusZeroEqThm = ⊢ ∀m. m + 0 = m",
  Module[{c, numTy, mV, plusTm, expected},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy];
    plusTm = mkComb[mkComb[mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]],
      mV], HOL`Stdlib`Num`zeroConst[]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV, mkEq[plusTm, mV]]];
    c = concl[HOL`Stdlib`Num`plusZeroEqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m. m + 0 = m"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`plusZeroEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: plusSucEqThm = ⊢ ∀m n. m + (SUC n) = SUC (m + n)",
  Module[{c, numTy, mV, nV, expected, plusC, sucC},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    sucC = HOL`Stdlib`Num`sucConst[];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[nV,
            mkEq[
              mkComb[mkComb[plusC, mV], mkComb[sucC, nV]],
              mkComb[sucC, mkComb[mkComb[plusC, mV], nV]]]]]]];
    c = concl[HOL`Stdlib`Num`plusSucEqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. m + (SUC n) = SUC (m + n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`plusSucEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: addLeftZeroThm = ⊢ ∀n. 0 + n = n",
  Module[{c, numTy, nV, expected, plusConst},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    plusConst = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV,
        mkEq[
          mkComb[mkComb[plusConst, HOL`Stdlib`Num`zeroConst[]], nV],
          nV]]];
    c = concl[HOL`Stdlib`Num`addLeftZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. 0 + n = n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`addLeftZeroThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: timesZeroEqThm = ⊢ ∀m. m * 0 = 0",
  Module[{c, numTy, mV, expected, timesConst},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy];
    timesConst = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkEq[
          mkComb[mkComb[timesConst, mV], HOL`Stdlib`Num`zeroConst[]],
          HOL`Stdlib`Num`zeroConst[]]]];
    c = concl[HOL`Stdlib`Num`timesZeroEqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m. m * 0 = 0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesZeroEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: timesSucEqThm = ⊢ ∀m n. m * (SUC n) = m * n + m",
  Module[{c, numTy, mV, nV, expected, plusC, timesC, sucC},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    sucC = HOL`Stdlib`Num`sucConst[];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[nV,
            mkEq[
              mkComb[mkComb[timesC, mV], mkComb[sucC, nV]],
              mkComb[
                mkComb[plusC,
                  mkComb[mkComb[timesC, mV], nV]],
                mV]]]]]];
    c = concl[HOL`Stdlib`Num`timesSucEqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. m * (SUC n) = m * n + m"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesSucEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: timesLeftZeroThm = ⊢ ∀n. 0 * n = 0",
  Module[{c, numTy, nV, expected, timesConst},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    timesConst = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV,
        mkEq[
          mkComb[mkComb[timesConst, HOL`Stdlib`Num`zeroConst[]], nV],
          HOL`Stdlib`Num`zeroConst[]]]];
    c = concl[HOL`Stdlib`Num`timesLeftZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. 0 * n = 0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesLeftZeroThm], {}, "no hyps"];
]];
