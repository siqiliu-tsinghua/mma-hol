(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Pair`"];
Needs["HOL`Stdlib`Num`"];
Needs["HOL`Stdlib`Int`"];

numTy = mkType["num", {}];
numPairTy = HOL`Stdlib`Pair`prodTy[numTy, numTy];
numPairCons[a_, b_] :=
  mkComb[mkComb[mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]], a], b];

(* ===== Stage a: int type carving ===== *)

HOLTest`runTests["stdlib/Int: int type and ABS/REP constant types",
  Module[{},
    HOLTest`assertEq[HOL`Stdlib`Int`intTy, mkType["int", {}], "intTy = int"];
    HOLTest`assertEq[constType["ABS_int"], tyFun[numPairTy, HOL`Stdlib`Int`intTy],
      "ABS_int : num × num → int"];
    HOLTest`assertEq[constType["REP_int"], tyFun[HOL`Stdlib`Int`intTy, numPairTy],
      "REP_int : int → num × num"]
  ]];

HOLTest`runTests["stdlib/Int: INT_REP (0, 0) witness",
  Module[{c, expected, zeroPair},
    zeroPair = numPairCons[
      HOL`Stdlib`Num`zeroConst[], HOL`Stdlib`Num`zeroConst[]];
    expected = mkComb[HOL`Stdlib`Int`intRepConst[], zeroPair];
    c = concl[HOL`Stdlib`Int`intRepZeroPairThm];
    HOLTest`assertEq[c, expected, "⊢ INT_REP (0, 0)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intRepZeroPairThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: round-trip ABS_int (REP_int a) = a",
  Module[{aV, c},
    aV = mkVar["a", HOL`Stdlib`Int`intTy];
    c = concl[HOL`Stdlib`Int`absRepIntThm];
    HOLTest`assertEq[c,
      mkEq[mkComb[HOL`Stdlib`Int`absIntConst[],
             mkComb[HOL`Stdlib`Int`repIntConst[], aV]], aV],
      "⊢ ABS_int (REP_int a) = a"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`absRepIntThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: repAbsIntThm characterizes the image",
  Module[{c},
    c = concl[HOL`Stdlib`Int`repAbsIntThm];
    (* ⊢ INT_REP r = (REP_int (ABS_int r) = r) *)
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], comb[const["INT_REP", _], _]],
                     comb[comb[const["=", _], _], _]]],
      "shape: INT_REP r = (REP_int (ABS_int r) = r)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`repAbsIntThm], {}, "no hyps"]
  ]];

(* ===== Stage b: &ℤ embedding ===== *)

HOLTest`runTests["stdlib/Int: REP_int (&ℤ n) = (n, 0)",
  Module[{nV, c, expected},
    nV = mkVar["n", numTy];
    expected = mkEq[
      mkComb[HOL`Stdlib`Int`repIntConst[],
        mkComb[HOL`Stdlib`Int`intOfNumConst[], nV]],
      numPairCons[nV, HOL`Stdlib`Num`zeroConst[]]];
    c = concl[HOL`Stdlib`Int`repIntOfNumThm];
    HOLTest`assertEq[c, expected, "⊢ REP_int (&ℤ n) = (n, 0)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`repIntOfNumThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: &ℤ is injective (functional check)",
  Module[{one, inj2, refl1, mp},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    (* SPEC m := SUC 0, n := SUC 0; MP with reflexivity ⇒ SUC 0 = SUC 0 *)
    inj2 = HOL`Bool`SPEC[one, HOL`Bool`SPEC[one,
      HOL`Stdlib`Int`intOfNumInjThm]];
    refl1 = REFL[mkComb[HOL`Stdlib`Int`intOfNumConst[], one]];
    mp = HOL`Bool`MP[inj2, refl1];
    HOLTest`assertEq[concl[mp], mkEq[one, one],
      "⊢ SUC 0 = SUC 0 from &ℤ injectivity"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intOfNumInjThm], {}, "no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intRepNatPairThm],
      "intRepNatPairThm is a theorem"]
  ]];

(* ===== Stage c: intNeg (negation) ===== *)

HOLTest`runTests["stdlib/Int: intNeg involution (intNeg (intNeg z) = z)",
  Module[{one, z1, specZ, neg, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];   (* &ℤ (SUC 0) *)
    specZ = HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intNegNegThm];
    neg[t_] := mkComb[HOL`Stdlib`Int`intNegConst[], t];
    expected = mkEq[neg[neg[z1]], z1];
    HOLTest`assertEq[concl[specZ], expected,
      "⊢ intNeg (intNeg (&ℤ 1)) = &ℤ 1"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intNegNegThm], {}, "no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intRepRepThm] &&
        hyp[HOL`Stdlib`Int`intRepRepThm] === {},
      "intRepRepThm is a hyp-free theorem"]
  ]];
