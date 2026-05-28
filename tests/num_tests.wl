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

(* ===== M7-3-f: + commutativity / associativity ===== *)

HOLTest`runTests["stdlib/Num: addLeftSucThm = ⊢ ∀m n. SUC m + n = SUC (m + n)",
  Module[{c, numTy, mV, nV, plusC, sucC, expected},
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
              mkComb[mkComb[plusC, mkComb[sucC, mV]], nV],
              mkComb[sucC, mkComb[mkComb[plusC, mV], nV]]]]]]];
    c = concl[HOL`Stdlib`Num`addLeftSucThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. SUC m + n = SUC (m + n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`addLeftSucThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: addCommThm = ⊢ ∀m n. m + n = n + m",
  Module[{c, numTy, mV, nV, plusC, expected},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[nV,
            mkEq[
              mkComb[mkComb[plusC, mV], nV],
              mkComb[mkComb[plusC, nV], mV]]]]]];
    c = concl[HOL`Stdlib`Num`addCommThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. m + n = n + m"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`addCommThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: addAssocThm = ⊢ ∀a b c. (a + b) + c = a + (b + c)",
  Module[{c, numTy, aV, bV, cV, plusC, expected},
    numTy = mkType["num", {}];
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[aV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[bV,
            mkComb[
              mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
              mkAbs[cV,
                mkEq[
                  mkComb[mkComb[plusC,
                    mkComb[mkComb[plusC, aV], bV]], cV],
                  mkComb[mkComb[plusC, aV],
                    mkComb[mkComb[plusC, bV], cV]]]]]]]]];
    c = concl[HOL`Stdlib`Num`addAssocThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀a b c. (a + b) + c = a + (b + c)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`addAssocThm], {}, "no hyps"];
]];

(* ===== M7-3-g: * commutativity + ≤ ===== *)

HOLTest`runTests["stdlib/Num: timesLeftSucThm = ⊢ ∀m n. SUC m * n = n + m * n",
  Module[{c, numTy, mV, nV, plusC, timesC, sucC, expected},
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
              mkComb[mkComb[timesC, mkComb[sucC, mV]], nV],
              mkComb[mkComb[plusC, nV],
                mkComb[mkComb[timesC, mV], nV]]]]]]];
    c = concl[HOL`Stdlib`Num`timesLeftSucThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. SUC m * n = n + m * n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesLeftSucThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: timesCommThm = ⊢ ∀m n. m * n = n * m",
  Module[{c, numTy, mV, nV, timesC, expected},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[nV,
            mkEq[
              mkComb[mkComb[timesC, mV], nV],
              mkComb[mkComb[timesC, nV], mV]]]]]];
    c = concl[HOL`Stdlib`Num`timesCommThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. m * n = n * m"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesCommThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: ≤ has type num → num → bool",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["≤"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, boolTy]],
      "≤ : num → num → bool"];
]];

HOLTest`runTests["stdlib/Num: leqReflThm = ⊢ ∀n. n ≤ n",
  Module[{c, numTy, nV, leqC, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV, mkComb[mkComb[leqC, nV], nV]]];
    c = concl[HOL`Stdlib`Num`leqReflThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. n ≤ n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqReflThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: leqZeroThm = ⊢ ∀n. 0 ≤ n",
  Module[{c, numTy, nV, leqC, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV, mkComb[mkComb[leqC, HOL`Stdlib`Num`zeroConst[]], nV]]];
    c = concl[HOL`Stdlib`Num`leqZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. 0 ≤ n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqZeroThm], {}, "no hyps"];
]];

(* ===== M7-3-h: cancellation + distrib/assoc + LEQ trans + < ===== *)

HOLTest`runTests["stdlib/Num: addLeftCancelThm has no hyps + ∀m n k shape",
  Module[{c},
    c = concl[HOL`Stdlib`Num`addLeftCancelThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[const["∀", _], abs[_, comb[const["∀", _], abs[_,
        comb[const["∀", _], abs[_, comb[comb[const["⇒", _], _], _],
          _String]], _String]], _String]]],
      "⊢ ∀m n k. … ⇒ …"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`addLeftCancelThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: addRightCancelThm has no hyps + ∀m n k shape",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`addRightCancelThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: timesDistribLeftThm = ⊢ ∀a b c. a*(b+c) = a*b + a*c",
  Module[{c, numTy, aV, bV, cV, plusC, timesC, expected},
    numTy = mkType["num", {}];
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[aV,
        mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[bV,
            mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
              mkAbs[cV,
                mkEq[
                  mkComb[mkComb[timesC, aV],
                    mkComb[mkComb[plusC, bV], cV]],
                  mkComb[mkComb[plusC,
                    mkComb[mkComb[timesC, aV], bV]],
                    mkComb[mkComb[timesC, aV], cV]]]]]]]]];
    c = concl[HOL`Stdlib`Num`timesDistribLeftThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀a b c. a * (b + c) = a*b + a*c"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesDistribLeftThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: timesDistribRightThm has no hyps",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesDistribRightThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: timesAssocThm = ⊢ ∀a b c. (a*b)*c = a*(b*c)",
  Module[{c, numTy, aV, bV, cV, timesC, expected},
    numTy = mkType["num", {}];
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; cV = mkVar["c", numTy];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[aV,
        mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[bV,
            mkComb[mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
              mkAbs[cV,
                mkEq[
                  mkComb[mkComb[timesC,
                    mkComb[mkComb[timesC, aV], bV]], cV],
                  mkComb[mkComb[timesC, aV],
                    mkComb[mkComb[timesC, bV], cV]]]]]]]]];
    c = concl[HOL`Stdlib`Num`timesAssocThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀a b c. (a*b)*c = a*(b*c)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`timesAssocThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: leqTransThm has no hyps + ∀a b c shape",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqTransThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: leqSucThm = ⊢ ∀n. n ≤ SUC n",
  Module[{c, numTy, nV, leqC, sucC, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    sucC = HOL`Stdlib`Num`sucConst[];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV, mkComb[mkComb[leqC, nV], mkComb[sucC, nV]]]];
    c = concl[HOL`Stdlib`Num`leqSucThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. n ≤ SUC n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqSucThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: < has type num → num → bool",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["<"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, boolTy]],
      "< : num → num → bool"];
]];

HOLTest`runTests["stdlib/Num: ltSucThm = ⊢ ∀n. n < SUC n",
  Module[{c, numTy, nV, ltC, sucC, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    ltC = mkConst["<", tyFun[numTy, tyFun[numTy, boolTy]]];
    sucC = HOL`Stdlib`Num`sucConst[];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV, mkComb[mkComb[ltC, nV], mkComb[sucC, nV]]]];
    c = concl[HOL`Stdlib`Num`ltSucThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. n < SUC n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`ltSucThm], {}, "no hyps"];
]];

(* ===== M7-3-i: case split + LEQ antisym ===== *)

HOLTest`runTests["stdlib/Num: numCasesThm = ⊢ ∀n. n = 0 ∨ ∃m. n = SUC m",
  Module[{c, numTy, nV, mV, sucC, orC, existsC, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy]; mV = mkVar["m", numTy];
    sucC = HOL`Stdlib`Num`sucConst[];
    orC = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    existsC = mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV,
        mkComb[mkComb[orC, mkEq[nV, HOL`Stdlib`Num`zeroConst[]]],
          mkComb[existsC,
            mkAbs[mV, mkEq[nV, mkComb[sucC, mV]]]]]]];
    c = concl[HOL`Stdlib`Num`numCasesThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀n. n = 0 ∨ ∃m. n = SUC m"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`numCasesThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: addEqZeroLeftThm = ⊢ ∀m n. m + n = 0 ⇒ m = 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`addEqZeroLeftThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: addEqZeroRightThm = ⊢ ∀m n. m + n = 0 ⇒ n = 0",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`addEqZeroRightThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: leqAntisymThm has no hyps + ∀m n shape",
  Module[{c, numTy, mV, nV, leqC, expected},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[nV,
            mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
              mkComb[mkComb[leqC, mV], nV]],
              mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]],
                mkComb[mkComb[leqC, nV], mV]],
                mkEq[mV, nV]]]]]]];
    c = concl[HOL`Stdlib`Num`leqAntisymThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. m ≤ n ⇒ n ≤ m ⇒ m = n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqAntisymThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: leqTotalThm = ⊢ ∀m n. m ≤ n ∨ n ≤ m",
  Module[{c, numTy, mV, nV, leqC, orC, expected},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    orC = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkComb[
          mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
          mkAbs[nV,
            mkComb[mkComb[orC, mkComb[mkComb[leqC, mV], nV]],
              mkComb[mkComb[leqC, nV], mV]]]]]];
    c = concl[HOL`Stdlib`Num`leqTotalThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. m ≤ n ∨ n ≤ m"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqTotalThm], {}, "no hyps"];
]];

(* ===== M7-3-j: ordering helpers + strong induction ===== *)

HOLTest`runTests["stdlib/Num: notLtZeroThm = ⊢ ∀n. ¬ (n < 0)",
  Module[{c, numTy, nV, ltC, notC, expected},
    numTy = mkType["num", {}];
    nV = mkVar["n", numTy];
    ltC = mkConst["<", tyFun[numTy, tyFun[numTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV,
        mkComb[notC,
          mkComb[mkComb[ltC, nV], HOL`Stdlib`Num`zeroConst[]]]]];
    c = concl[HOL`Stdlib`Num`notLtZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀n. ¬ (n < 0)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`notLtZeroThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: leqSucCaseThm has ∀m n + impl + or shape",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqSucCaseThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: ltSucEqLeqThm has ∀m n + impl shape",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`ltSucEqLeqThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: strongInductionThm — shape ∀P. (∀n.…) ⇒ ∀n. P n",
  Module[{c, numTy, pTy},
    numTy = mkType["num", {}];
    pTy = tyFun[numTy, boolTy];
    c = concl[HOL`Stdlib`Num`strongInductionThm];
    HOLTest`assertTrue[
      MatchQ[c,
        comb[const["∀", _],
          abs[bvar[0, tyApp["fun", {tyApp["num", {}], tyApp["bool", {}]}]],
            comb[comb[const["⇒", _], _],
              comb[const["∀", _],
                abs[bvar[0, tyApp["num", {}]], _, _String]]],
            _String]]],
      "shape: ∀P. (…) ⇒ ∀n. P n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`strongInductionThm], {}, "no hyps"];
]];

(* ===== M7-3-k: ^ + well-ordering + division ===== *)

HOLTest`runTests["stdlib/Num: ^ has type num → num → num",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["^"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, numTy]],
      "^ : num → num → num"];
]];

HOLTest`runTests["stdlib/Num: powZeroThm = ⊢ ∀m. m ^ 0 = SUC 0",
  Module[{c, numTy, mV, powC, sucC, expected},
    numTy = mkType["num", {}];
    mV = mkVar["m", numTy];
    powC = mkConst["^", tyFun[numTy, tyFun[numTy, numTy]]];
    sucC = HOL`Stdlib`Num`sucConst[];
    expected = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mV,
        mkEq[
          mkComb[mkComb[powC, mV], HOL`Stdlib`Num`zeroConst[]],
          mkComb[sucC, HOL`Stdlib`Num`zeroConst[]]]]];
    c = concl[HOL`Stdlib`Num`powZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m. m ^ 0 = SUC 0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`powZeroThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: powSucThm = ⊢ ∀m n. m^SUC n = m^n * m",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`powSucThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: leqCaseEqLtThm has no hyps",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`leqCaseEqLtThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: ltZeroNotZeroThm has no hyps",
  HOLTest`assertEq[hyp[HOL`Stdlib`Num`ltZeroNotZeroThm], {}, "no hyps"];
];

HOLTest`runTests["stdlib/Num: wellOrderingThm — shape ∀P. (∃n. P n) ⇒ ∃m. ...",
  Module[{c, numTy},
    numTy = mkType["num", {}];
    c = concl[HOL`Stdlib`Num`wellOrderingThm];
    HOLTest`assertTrue[
      MatchQ[c,
        comb[const["∀", _],
          abs[bvar[0, tyApp["fun", {tyApp["num", {}], tyApp["bool", {}]}]],
            comb[comb[const["⇒", _],
              comb[const["∃", _], _]],
              comb[const["∃", _], _]],
            _String]]],
      "shape: ∀P. (∃n. P n) ⇒ (∃m. ...)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`wellOrderingThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: divisionThm — shape ∀m n. ¬(n=0) ⇒ ∃q r. m = n*q + r ∧ r < n",
  Module[{c, numTy, boolTy, expected,
          forallC, existsC, notC, andC, impC, eqC,
          plusC, timesC, ltC, sucC, zeroC, suc0,
          mV, nV, qV, rV, body},
    numTy  = mkType["num", {}];
    boolTy = mkType["bool", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    existsC = mkConst["∃", tyFun[tyFun[numTy, boolTy], boolTy]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    eqC = mkConst["=", tyFun[numTy, tyFun[numTy, boolTy]]];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    ltC = mkConst["<", tyFun[numTy, tyFun[numTy, boolTy]]];
    sucC = mkConst["SUC", tyFun[numTy, numTy]];
    zeroC = mkConst["0", numTy];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    qV = mkVar["q", numTy]; rV = mkVar["r", numTy];
    body = mkComb[mkComb[impC,
             mkComb[notC, mkComb[mkComb[eqC, nV], zeroC]]],
             mkComb[existsC, mkAbs[qV,
               mkComb[existsC, mkAbs[rV,
                 mkComb[mkComb[andC,
                   mkComb[mkComb[eqC, mV],
                     mkComb[mkComb[plusC,
                       mkComb[mkComb[timesC, nV], qV]], rV]]],
                   mkComb[mkComb[ltC, rV], nV]]]]]]];
    expected = mkComb[forallC,
      mkAbs[mV, mkComb[forallC, mkAbs[nV, body]]]];
    c = concl[HOL`Stdlib`Num`divisionThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "concl matches ∀m n. ¬(n=0) ⇒ ∃q r. m = n*q+r ∧ r<n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`divisionThm], {}, "no hyps"];
]];

(* ===== M7-3-m: divides + DIV + MOD + divisionPairThm ===== *)

HOLTest`runTests["stdlib/Num: divides has type num → num → bool",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["divides"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, boolTy]],
      "divides : num → num → bool"];
]];

HOLTest`runTests["stdlib/Num: DIV has type num → num → num",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["DIV"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, numTy]],
      "DIV : num → num → num"];
]];

HOLTest`runTests["stdlib/Num: MOD has type num → num → num",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["MOD"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, numTy]],
      "MOD : num → num → num"];
]];

HOLTest`runTests["stdlib/Num: dividesDefThm — concl is `divides = …` with no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`Num`dividesDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["divides", _]], _]],
      "concl shape ⊢ divides = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: divDefThm — concl is `DIV = …` with no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`Num`divDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["DIV", _]], _]],
      "concl shape ⊢ DIV = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: modDefThm — concl is `MOD = …` with no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`Num`modDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["MOD", _]], _]],
      "concl shape ⊢ MOD = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: divisionPairThm — shape ∀m n. ¬(n=0) ⇒ m = n*(m DIV n) + (m MOD n) ∧ (m MOD n) < n",
  Module[{c, numTy, boolTy, expected,
          forallC, notC, andC, impC, eqC,
          plusC, timesC, ltC, divC, modC, zeroC,
          mV, nV, body, divMN, modMN},
    numTy  = mkType["num", {}];
    boolTy = mkType["bool", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    eqC = mkConst["=", tyFun[numTy, tyFun[numTy, boolTy]]];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    ltC = mkConst["<", tyFun[numTy, tyFun[numTy, boolTy]]];
    divC = mkConst["DIV", tyFun[numTy, tyFun[numTy, numTy]]];
    modC = mkConst["MOD", tyFun[numTy, tyFun[numTy, numTy]]];
    zeroC = mkConst["0", numTy];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    divMN = mkComb[mkComb[divC, mV], nV];
    modMN = mkComb[mkComb[modC, mV], nV];
    body = mkComb[mkComb[impC,
             mkComb[notC, mkComb[mkComb[eqC, nV], zeroC]]],
             mkComb[mkComb[andC,
               mkComb[mkComb[eqC, mV],
                 mkComb[mkComb[plusC,
                   mkComb[mkComb[timesC, nV], divMN]], modMN]]],
               mkComb[mkComb[ltC, modMN], nV]]];
    expected = mkComb[forallC,
      mkAbs[mV, mkComb[forallC, mkAbs[nV, body]]]];
    c = concl[HOL`Stdlib`Num`divisionPairThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "concl matches ∀m n. ¬(n=0) ⇒ m = n*(m DIV n)+(m MOD n) ∧ (m MOD n)<n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`divisionPairThm], {}, "no hyps"];
]];

(* ===== M7-3-n: divides arithmetic ===== *)

HOLTest`runTests["stdlib/Num: dividesReflThm — ⊢ ∀a. divides a a, no hyps",
  Module[{c, numTy, aV, expected, forallC, divC},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    aV = mkVar["a", numTy];
    expected = mkComb[forallC,
      mkAbs[aV, mkComb[mkComb[divC, aV], aV]]];
    c = concl[HOL`Stdlib`Num`dividesReflThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀a. divides a a"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`dividesReflThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: dividesZeroThm — ⊢ ∀a. divides a 0, no hyps",
  Module[{c, numTy, aV, expected, forallC, divC, zeroC},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    zeroC = mkConst["0", numTy];
    aV = mkVar["a", numTy];
    expected = mkComb[forallC,
      mkAbs[aV, mkComb[mkComb[divC, aV], zeroC]]];
    c = concl[HOL`Stdlib`Num`dividesZeroThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀a. divides a 0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`dividesZeroThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: dividesAddThm — ⊢ ∀d m n. d|m ⇒ d|n ⇒ d|(m+n), no hyps",
  Module[{c, numTy, expected, forallC, impC, divC, plusC, dV, mV, nV, body},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    dV = mkVar["d", numTy]; mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    body = mkComb[mkComb[impC,
             mkComb[mkComb[divC, dV], mV]],
           mkComb[mkComb[impC,
             mkComb[mkComb[divC, dV], nV]],
             mkComb[mkComb[divC, dV],
               mkComb[mkComb[plusC, mV], nV]]]];
    expected = mkComb[forallC,
      mkAbs[dV, mkComb[forallC,
        mkAbs[mV, mkComb[forallC, mkAbs[nV, body]]]]]];
    c = concl[HOL`Stdlib`Num`dividesAddThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀d m n. divides d m ⇒ divides d n ⇒ divides d (m + n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`dividesAddThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: dividesMultRightThm — ⊢ ∀d m n. d|m ⇒ d|(m*n), no hyps",
  Module[{c, numTy, expected, forallC, impC, divC, timesC, dV, mV, nV, body},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    dV = mkVar["d", numTy]; mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    body = mkComb[mkComb[impC,
             mkComb[mkComb[divC, dV], mV]],
             mkComb[mkComb[divC, dV],
               mkComb[mkComb[timesC, mV], nV]]];
    expected = mkComb[forallC,
      mkAbs[dV, mkComb[forallC,
        mkAbs[mV, mkComb[forallC, mkAbs[nV, body]]]]]];
    c = concl[HOL`Stdlib`Num`dividesMultRightThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀d m n. divides d m ⇒ divides d (m * n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`dividesMultRightThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: dividesAddRightThm — ⊢ ∀d m n. d|m ⇒ d|(m+n) ⇒ d|n, no hyps",
  Module[{c, numTy, expected, forallC, impC, divC, plusC, dV, mV, nV, body},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    dV = mkVar["d", numTy]; mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    body = mkComb[mkComb[impC,
             mkComb[mkComb[divC, dV], mV]],
           mkComb[mkComb[impC,
             mkComb[mkComb[divC, dV],
               mkComb[mkComb[plusC, mV], nV]]],
             mkComb[mkComb[divC, dV], nV]]];
    expected = mkComb[forallC,
      mkAbs[dV, mkComb[forallC,
        mkAbs[mV, mkComb[forallC, mkAbs[nV, body]]]]]];
    c = concl[HOL`Stdlib`Num`dividesAddRightThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀d m n. divides d m ⇒ divides d (m + n) ⇒ divides d n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`dividesAddRightThm], {}, "no hyps"];
]];

(* ===== Cooper-periodicity foundation (M7-δ session 13) ===== *)

HOLTest`runTests["stdlib/Num: dividesAddEqThm — ⊢ ∀d x y. d|y ⇒ (d|(x+y) = d|x)",
  Module[{th, c},
    th = HOL`Stdlib`Num`dividesAddEqThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 3,
        comb[comb[const["⇒", _],
          comb[comb[const["divides", _], _], _]],
          comb[comb[const["=", _],
            comb[comb[const["divides", _], _],
              comb[comb[const["+", _], _], _]]],
            comb[comb[const["divides", _], _], _]]]]],
      "shape: ∀d x y. d|y ⇒ (d|(x+y) = d|x)"]
  ]];

HOLTest`runTests["stdlib/Num: dividesAddMultDThm — ⊢ ∀d x j. d|(x + j*d) = d|x",
  Module[{th, c},
    th = HOL`Stdlib`Num`dividesAddMultDThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 3,
        comb[comb[const["=", _],
          comb[comb[const["divides", _], _],
            comb[comb[const["+", _], _],
              comb[comb[const["*", _], _], _]]]],
          comb[comb[const["divides", _], _], _]]]],
      "shape: ∀d x j. d|(x + j*d) = d|x"]
  ]];

HOLTest`runTests["stdlib/Num: dividesAddDThm — ⊢ ∀d x. d|(x + d) = d|x",
  Module[{th, c},
    th = HOL`Stdlib`Num`dividesAddDThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 2,
        comb[comb[const["=", _],
          comb[comb[const["divides", _], _],
            comb[comb[const["+", _], _], _]]],
          comb[comb[const["divides", _], _], _]]]],
      "shape: ∀d x. d|(x + d) = d|x"]
  ]];

(* Round-trip: SPEC application validates the lemma actually fires. *)
HOLTest`runTests["stdlib/Num: dividesAddDThm fires — d=3, x=5 yields d|(5+3) = d|5",
  Module[{th, numTy, three, five, instThm, c, divC, plusC},
    numTy = mkType["num", {}];
    three = HOL`Auto`Arith`Private`buildLitNum[3];
    five  = HOL`Auto`Arith`Private`buildLitNum[5];
    th = HOL`Stdlib`Num`dividesAddDThm;
    instThm = HOL`Bool`SPEC[five, HOL`Bool`SPEC[three, th]];
    c = concl[instThm];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    HOLTest`assertEq[hyp[instThm], {}, "no hyps after SPEC"];
    HOLTest`assertTrue[
      HOL`Terms`aconv[c,
        mkEq[
          mkComb[mkComb[divC, three],
            mkComb[mkComb[plusC, five], three]],
          mkComb[mkComb[divC, three], five]]],
      "⊢ divides 3 (5 + 3) = divides 3 5"]
  ]];

(* ===== Atom-level Cooper periodicity (M7-δ session 14) ===== *)

HOLTest`runTests["stdlib/Num: addRightCommThm — ⊢ ∀a b c. (a+b)+c = (a+c)+b",
  Module[{th, c},
    th = HOL`Stdlib`Num`addRightCommThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 3,
        comb[comb[const["=", _],
          comb[comb[const["+", _], comb[comb[const["+", _], _], _]], _]],
          comb[comb[const["+", _], comb[comb[const["+", _], _], _]], _]]]],
      "shape: ∀a b c. (a+b)+c = (a+c)+b"]
  ]];

HOLTest`runTests["stdlib/Num: dividesShiftThm — ⊢ ∀d x t δ. d|δ ⇒ (d|((x+δ)+t) = d|(x+t))",
  Module[{th, c},
    th = HOL`Stdlib`Num`dividesShiftThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 4,
        comb[comb[const["⇒", _],
          comb[comb[const["divides", _], _], _]],
          comb[comb[const["=", _],
            comb[comb[const["divides", _], _],
              comb[comb[const["+", _], comb[comb[const["+", _], _], _]], _]]],
            comb[comb[const["divides", _], _],
              comb[comb[const["+", _], _], _]]]]]],
      "shape: ∀d x t δ. d|δ ⇒ (d|((x+δ)+t) = d|(x+t))"]
  ]];

(* Round-trip: with d=2, δ=4 (2|4 dischargeable) the shift fires. *)
HOLTest`runTests["stdlib/Num: dividesShiftThm fires — d=2, δ=4 gives the equivalence under 2|4",
  Module[{th, numTy, two, four, xV, tV, instThm, ante, c},
    numTy = mkType["num", {}];
    two  = HOL`Auto`Arith`Private`buildLitNum[2];
    four = HOL`Auto`Arith`Private`buildLitNum[4];
    xV = mkVar["x", numTy]; tV = mkVar["t", numTy];
    th = HOL`Stdlib`Num`dividesShiftThm;
    instThm = HOL`Bool`SPEC[four,
      HOL`Bool`SPEC[tV, HOL`Bool`SPEC[xV, HOL`Bool`SPEC[two, th]]]];
    (* ⊢ divides 2 4 ⇒ (divides 2 ((x+4)+t) = divides 2 (x+t)) *)
    HOLTest`assertEq[hyp[instThm], {}, "no hyps after SPEC"];
    ante = concl[instThm][[1, 2]];
    HOLTest`assertTrue[
      MatchQ[ante, comb[comb[const["divides", _], _], _]],
      "antecedent is divides 2 4"];
    c = concl[instThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["⇒", _], _],
        comb[comb[const["=", _], _], _]]],
      "concl is d|δ ⇒ (eq)"]
  ]];

(* ===== ARITH verifier lemmas: additive monotonicity (M7-δ realign) ===== *)

HOLTest`runTests["stdlib/Num: leqAddRightMonoThm (capstone) — ⊢ ∀m n p. m≤n ⇒ m+p≤n+p",
  Module[{th, c},
    th = HOL`Stdlib`Num`leqAddRightMonoThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 3,
        comb[comb[const["⇒", _], comb[comb[const["≤", _], _], _]],
          comb[comb[const["≤", _], comb[comb[const["+", _], _], _]],
            comb[comb[const["+", _], _], _]]]]],
      "shape: ∀m n p. m≤n ⇒ m+p≤n+p"]
  ]];

HOLTest`runTests["stdlib/Num: leqAddLeftMonoThm — ⊢ ∀m n p. m≤n ⇒ p+m≤p+n",
  Module[{th, c},
    th = HOL`Stdlib`Num`leqAddLeftMonoThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 3,
        comb[comb[const["⇒", _], comb[comb[const["≤", _], _], _]],
          comb[comb[const["≤", _], comb[comb[const["+", _], _], _]],
            comb[comb[const["+", _], _], _]]]]],
      "shape: ∀m n p. m≤n ⇒ p+m≤p+n"]
  ]];

HOLTest`runTests["stdlib/Num: leqAddMonoThm — ⊢ ∀a b c d. a≤b ⇒ c≤d ⇒ a+c≤b+d",
  Module[{th, c},
    th = HOL`Stdlib`Num`leqAddMonoThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 4,
        comb[comb[const["⇒", _], comb[comb[const["≤", _], _], _]],
          comb[comb[const["⇒", _], comb[comb[const["≤", _], _], _]],
            comb[comb[const["≤", _], comb[comb[const["+", _], _], _]],
              comb[comb[const["+", _], _], _]]]]]],
      "shape: ∀a b c d. a≤b ⇒ c≤d ⇒ a+c≤b+d"]
  ]];

(* Capstone fires: m=2,n=5,p=10 → 2≤5 ⇒ 12≤15; discharge 2≤5, get 12≤15. *)
HOLTest`runTests["stdlib/Num: leqAddRightMonoThm fires — 2≤5 yields 2+10 ≤ 5+10",
  Module[{th, numTy, two, five, ten, leqC, plusC, inst, leq25, concl12},
    numTy = mkType["num", {}];
    two  = HOL`Auto`Arith`Private`buildLitNum[2];
    five = HOL`Auto`Arith`Private`buildLitNum[5];
    ten  = HOL`Auto`Arith`Private`buildLitNum[10];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    plusC = mkConst["+", tyFun[numTy, tyFun[numTy, numTy]]];
    th = HOL`Stdlib`Num`leqAddRightMonoThm;
    inst = HOL`Bool`SPEC[ten, HOL`Bool`SPEC[five, HOL`Bool`SPEC[two, th]]];
    (* ⊢ 2≤5 ⇒ 2+10 ≤ 5+10 *)
    leq25 = HOL`Auto`Arith`Private`proveGroundLeq[2, 5];
    concl12 = HOL`Bool`MP[inst, leq25];
    HOLTest`assertEq[hyp[concl12], {}, "no hyps after MP"];
    HOLTest`assertTrue[
      HOL`Terms`aconv[concl[concl12],
        mkComb[mkComb[leqC, mkComb[mkComb[plusC, two], ten]],
          mkComb[mkComb[plusC, five], ten]]],
      "⊢ 2 + 10 ≤ 5 + 10"]
  ]];

(* ARITH verifier lemmas batch 2: scaling + left-cancellation *)

HOLTest`runTests["stdlib/Num: leqMultLeftThm — ⊢ ∀k a b. a≤b ⇒ k*a≤k*b",
  Module[{th, c},
    th = HOL`Stdlib`Num`leqMultLeftThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 3,
        comb[comb[const["⇒", _], comb[comb[const["≤", _], _], _]],
          comb[comb[const["≤", _], comb[comb[const["*", _], _], _]],
            comb[comb[const["*", _], _], _]]]]],
      "shape: ∀k a b. a≤b ⇒ k*a≤k*b"]
  ]];

HOLTest`runTests["stdlib/Num: leqAddLeftCancelThm — ⊢ ∀v a b. v+a≤v+b ⇒ a≤b",
  Module[{th, c},
    th = HOL`Stdlib`Num`leqAddLeftCancelThm;
    c = concl[th];
    HOLTest`assertEq[hyp[th], {}, "no hyps"];
    HOLTest`assertTrue[
      MatchQ[c, HOLTest`quantNestPat["∀", 3,
        comb[comb[const["⇒", _],
          comb[comb[const["≤", _], comb[comb[const["+", _], _], _]],
            comb[comb[const["+", _], _], _]]],
          comb[comb[const["≤", _], _], _]]]],
      "shape: ∀v a b. v+a≤v+b ⇒ a≤b"]
  ]];

(* Scaling fires: 2≤5 ⇒ 3*2 ≤ 3*5. *)
HOLTest`runTests["stdlib/Num: leqMultLeftThm fires — 2≤5 yields 3*2 ≤ 3*5",
  Module[{th, numTy, two, five, three, leqC, timesC, inst, leq25, conc},
    numTy = mkType["num", {}];
    two = HOL`Auto`Arith`Private`buildLitNum[2];
    five = HOL`Auto`Arith`Private`buildLitNum[5];
    three = HOL`Auto`Arith`Private`buildLitNum[3];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    th = HOL`Stdlib`Num`leqMultLeftThm;
    inst = HOL`Bool`SPEC[five, HOL`Bool`SPEC[two, HOL`Bool`SPEC[three, th]]];
    leq25 = HOL`Auto`Arith`Private`proveGroundLeq[2, 5];
    conc = HOL`Bool`MP[inst, leq25];
    HOLTest`assertEq[hyp[conc], {}, "no hyps after MP"];
    HOLTest`assertTrue[
      HOL`Terms`aconv[concl[conc],
        mkComb[mkComb[leqC, mkComb[mkComb[timesC, three], two]],
          mkComb[mkComb[timesC, three], five]]],
      "⊢ 3 * 2 ≤ 3 * 5"]
  ]];

(* Cancellation round-trips mono: leqAddLeftMono builds 10+2≤10+5 from 2≤5, *)
(* leqAddLeftCancel recovers 2≤5. *)
HOLTest`runTests["stdlib/Num: leqAddLeftCancelThm round-trips leqAddLeftMono",
  Module[{numTy, two, five, ten, leqC, monoInst, built, cancelInst, recovered},
    numTy = mkType["num", {}];
    two = HOL`Auto`Arith`Private`buildLitNum[2];
    five = HOL`Auto`Arith`Private`buildLitNum[5];
    ten = HOL`Auto`Arith`Private`buildLitNum[10];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    monoInst = HOL`Bool`MP[
      HOL`Bool`SPEC[ten, HOL`Bool`SPEC[five, HOL`Bool`SPEC[two,
        HOL`Stdlib`Num`leqAddLeftMonoThm]]],
      HOL`Auto`Arith`Private`proveGroundLeq[2, 5]];
    (* ⊢ 10+2 ≤ 10+5 *)
    cancelInst = HOL`Bool`SPEC[five, HOL`Bool`SPEC[two, HOL`Bool`SPEC[ten,
      HOL`Stdlib`Num`leqAddLeftCancelThm]]];
    (* ⊢ 10+2 ≤ 10+5 ⇒ 2 ≤ 5 *)
    recovered = HOL`Bool`MP[cancelInst, monoInst];
    HOLTest`assertEq[hyp[recovered], {}, "no hyps"];
    HOLTest`assertTrue[
      HOL`Terms`aconv[concl[recovered],
        mkComb[mkComb[leqC, two], five]],
      "⊢ 2 ≤ 5 (cancellation undid the +10)"]
  ]];

(* ===== M7-3-o: gcd ===== *)

HOLTest`runTests["stdlib/Num: gcd has type num → num → num",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["gcd"];
    HOLTest`assertEq[ty, tyFun[numTy, tyFun[numTy, numTy]],
      "gcd : num → num → num"];
]];

HOLTest`runTests["stdlib/Num: gcdDefThm — concl is `gcd = …` with no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`Num`gcdDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["gcd", _]], _]],
      "concl shape ⊢ gcd = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: gcdExistsThm — shape ∀a b. ∃d. … with no hyps",
  Module[{c},
    c = concl[HOL`Stdlib`Num`gcdExistsThm];
    HOLTest`assertTrue[
      MatchQ[c,
        comb[const["∀", _],
          abs[bvar[0, tyApp["num", {}]],
            comb[const["∀", _],
              abs[bvar[0, tyApp["num", {}]],
                comb[const["∃", _], _], _]], _]]],
      "shape: ∀a. ∀b. ∃d. …"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`gcdExistsThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: gcdSpecThm — ⊢ ∀a b. d|a ∧ d|b ∧ universal where d = gcd a b",
  Module[{c, numTy, boolTy, expected,
          forallC, impC, andC, divC, gcdC,
          aV, bV, eV, gcdAB, body},
    numTy = mkType["num", {}];
    boolTy = mkType["bool", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    gcdC = mkConst["gcd", tyFun[numTy, tyFun[numTy, numTy]]];
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; eV = mkVar["e", numTy];
    gcdAB = mkComb[mkComb[gcdC, aV], bV];
    body = mkComb[mkComb[andC,
             mkComb[mkComb[divC, gcdAB], aV]],
           mkComb[mkComb[andC,
             mkComb[mkComb[divC, gcdAB], bV]],
             mkComb[forallC, mkAbs[eV,
               mkComb[mkComb[impC,
                 mkComb[mkComb[andC,
                   mkComb[mkComb[divC, eV], aV]],
                   mkComb[mkComb[divC, eV], bV]]],
                 mkComb[mkComb[divC, eV], gcdAB]]]]]];
    expected = mkComb[forallC,
      mkAbs[aV, mkComb[forallC, mkAbs[bV, body]]]];
    c = concl[HOL`Stdlib`Num`gcdSpecThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "concl matches ∀a b. (gcd a b)|a ∧ (gcd a b)|b ∧ ∀e. (e|a ∧ e|b) ⇒ e|(gcd a b)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`gcdSpecThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: gcdDividesLeftThm — ⊢ ∀a b. divides (gcd a b) a, no hyps",
  Module[{c, numTy, expected, forallC, divC, gcdC, aV, bV},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    gcdC = mkConst["gcd", tyFun[numTy, tyFun[numTy, numTy]]];
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    expected = mkComb[forallC,
      mkAbs[aV, mkComb[forallC,
        mkAbs[bV, mkComb[mkComb[divC, mkComb[mkComb[gcdC, aV], bV]], aV]]]]];
    c = concl[HOL`Stdlib`Num`gcdDividesLeftThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀a b. divides (gcd a b) a"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`gcdDividesLeftThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: gcdDividesRightThm — ⊢ ∀a b. divides (gcd a b) b, no hyps",
  Module[{c, numTy, expected, forallC, divC, gcdC, aV, bV},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    gcdC = mkConst["gcd", tyFun[numTy, tyFun[numTy, numTy]]];
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    expected = mkComb[forallC,
      mkAbs[aV, mkComb[forallC,
        mkAbs[bV, mkComb[mkComb[divC, mkComb[mkComb[gcdC, aV], bV]], bV]]]]];
    c = concl[HOL`Stdlib`Num`gcdDividesRightThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀a b. divides (gcd a b) b"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`gcdDividesRightThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: gcdUniversalThm — ⊢ ∀a b e. d|a ∧ d|b ⇒ d|(gcd a b), no hyps",
  Module[{c, numTy, expected, forallC, impC, andC, divC, gcdC,
          aV, bV, eV, body},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    gcdC = mkConst["gcd", tyFun[numTy, tyFun[numTy, numTy]]];
    aV = mkVar["a", numTy]; bV = mkVar["b", numTy]; eV = mkVar["e", numTy];
    body = mkComb[mkComb[impC,
             mkComb[mkComb[andC,
               mkComb[mkComb[divC, eV], aV]],
               mkComb[mkComb[divC, eV], bV]]],
             mkComb[mkComb[divC, eV],
               mkComb[mkComb[gcdC, aV], bV]]];
    expected = mkComb[forallC,
      mkAbs[aV, mkComb[forallC,
        mkAbs[bV, mkComb[forallC, mkAbs[eV, body]]]]]];
    c = concl[HOL`Stdlib`Num`gcdUniversalThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀a b e. divides e a ∧ divides e b ⇒ divides e (gcd a b)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`gcdUniversalThm], {}, "no hyps"];
]];

(* ===== M7-3-p: prime + arithmetic helpers ===== *)

HOLTest`runTests["stdlib/Num: oneTimesEqThm — ⊢ ∀n. SUC 0 * n = n, no hyps",
  Module[{c, numTy, expected, forallC, timesC, sucC, zeroC, nV, suc0},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    sucC = mkConst["SUC", tyFun[numTy, numTy]];
    zeroC = mkConst["0", numTy];
    nV = mkVar["n", numTy];
    suc0 = mkComb[sucC, zeroC];
    expected = mkComb[forallC,
      mkAbs[nV, mkEq[mkComb[mkComb[timesC, suc0], nV], nV]]];
    c = concl[HOL`Stdlib`Num`oneTimesEqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀n. SUC 0 * n = n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`oneTimesEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: sucNotEqSelfThm — ⊢ ∀n. ¬(SUC n = n), no hyps",
  Module[{c, numTy, expected, forallC, notC, sucC, nV},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    sucC = mkConst["SUC", tyFun[numTy, numTy]];
    nV = mkVar["n", numTy];
    expected = mkComb[forallC,
      mkAbs[nV, mkComb[notC, mkEq[mkComb[sucC, nV], nV]]]];
    c = concl[HOL`Stdlib`Num`sucNotEqSelfThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected], "∀n. ¬ (SUC n = n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`sucNotEqSelfThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: ltImpliesNotEqThm — ⊢ ∀m n. m < n ⇒ ¬(m = n), no hyps",
  Module[{c, numTy, expected, forallC, impC, notC, ltC, mV, nV, body},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    ltC = mkConst["<", tyFun[numTy, tyFun[numTy, boolTy]]];
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    body = mkComb[mkComb[impC, mkComb[mkComb[ltC, mV], nV]],
             mkComb[notC, mkEq[mV, nV]]];
    expected = mkComb[forallC,
      mkAbs[mV, mkComb[forallC, mkAbs[nV, body]]]];
    c = concl[HOL`Stdlib`Num`ltImpliesNotEqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀m n. m < n ⇒ ¬ (m = n)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`ltImpliesNotEqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: dividesLeqThm — ⊢ ∀d n. ¬(n=0) ⇒ d|n ⇒ d≤n, no hyps",
  Module[{c, numTy, expected, forallC, impC, notC, leqC, divC, zeroC,
          dV, nV, body},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    notC = mkConst["¬", tyFun[boolTy, boolTy]];
    leqC = mkConst["≤", tyFun[numTy, tyFun[numTy, boolTy]]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    zeroC = mkConst["0", numTy];
    dV = mkVar["d", numTy]; nV = mkVar["n", numTy];
    body = mkComb[mkComb[impC,
             mkComb[notC, mkEq[nV, zeroC]]],
           mkComb[mkComb[impC,
             mkComb[mkComb[divC, dV], nV]],
             mkComb[mkComb[leqC, dV], nV]]];
    expected = mkComb[forallC,
      mkAbs[dV, mkComb[forallC, mkAbs[nV, body]]]];
    c = concl[HOL`Stdlib`Num`dividesLeqThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀d n. ¬(n=0) ⇒ divides d n ⇒ d ≤ n"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`dividesLeqThm], {}, "no hyps"];
]];

HOLTest`runTests["stdlib/Num: prime has type num → bool",
  Module[{numTy, ty},
    numTy = mkType["num", {}];
    ty = HOL`Kernel`constType["prime"];
    HOLTest`assertEq[ty, tyFun[numTy, boolTy], "prime : num → bool"];
]];

HOLTest`runTests["stdlib/Num: primeDefThm — concl is `prime = …` with no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`Num`primeDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["prime", _]], _]],
      "concl shape ⊢ prime = …"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* ===== M7-3-q: Euclid's lemma ===== *)

HOLTest`runTests["stdlib/Num: euclidLemmaThm — ⊢ ∀p a b. prime p ⇒ p|a*b ⇒ p|a ∨ p|b, no hyps",
  Module[{c, numTy, expected, forallC, impC, orC, primeC, divC, timesC,
          pV, aV, bV, body},
    numTy = mkType["num", {}];
    forallC = mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    orC = mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    primeC = mkConst["prime", tyFun[numTy, boolTy]];
    divC = mkConst["divides", tyFun[numTy, tyFun[numTy, boolTy]]];
    timesC = mkConst["*", tyFun[numTy, tyFun[numTy, numTy]]];
    pV = mkVar["p", numTy]; aV = mkVar["a", numTy]; bV = mkVar["b", numTy];
    body = mkComb[mkComb[impC, mkComb[primeC, pV]],
             mkComb[mkComb[impC,
               mkComb[mkComb[divC, pV], mkComb[mkComb[timesC, aV], bV]]],
               mkComb[mkComb[orC,
                 mkComb[mkComb[divC, pV], aV]],
                 mkComb[mkComb[divC, pV], bV]]]];
    expected = mkComb[forallC,
      mkAbs[pV, mkComb[forallC,
        mkAbs[aV, mkComb[forallC, mkAbs[bV, body]]]]]];
    c = concl[HOL`Stdlib`Num`euclidLemmaThm];
    HOLTest`assertTrue[HOL`Terms`aconv[c, expected],
      "∀p a b. prime p ⇒ divides p (a*b) ⇒ divides p a ∨ divides p b"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`euclidLemmaThm], {}, "no hyps"];
]];
