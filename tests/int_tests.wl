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

(* ===== Stage d (part 1): intCanon canonicalizer ===== *)

HOLTest`runTests["stdlib/Int: INT_REP (intCanon p)",
  Module[{pV, expected},
    pV = mkVar["p", numPairTy];
    expected = mkComb[HOL`Stdlib`Int`intRepConst[],
      mkComb[HOL`Stdlib`Int`intCanonConst[], pV]];
    HOLTest`assertEq[concl[HOL`Stdlib`Int`intRepCanonThm], expected,
      "⊢ INT_REP (intCanon p)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intRepCanonThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: intAdd commutativity (functional check)",
  Module[{one, z0, z1, specZW, addTm, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z0 = mkComb[HOL`Stdlib`Int`intOfNumConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    specZW = HOL`Bool`SPEC[z0, HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intAddCommThm]];
    addTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
    expected = mkEq[addTm[z1, z0], addTm[z0, z1]];
    HOLTest`assertEq[concl[specZW], expected,
      "⊢ intAdd (&ℤ 1) (&ℤ 0) = intAdd (&ℤ 0) (&ℤ 1)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intAddCommThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: intAdd right identity (intAdd z (&ℤ 0) = z)",
  Module[{one, z0, z1, specZ0, specZ1, addTm, zZero, expected0, expected1},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z0 = mkComb[HOL`Stdlib`Int`intOfNumConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    zZero = z0;   (* &ℤ 0 *)
    addTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
    specZ0 = HOL`Bool`SPEC[z0, HOL`Stdlib`Int`intAddZeroThm];
    specZ1 = HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intAddZeroThm];
    expected0 = mkEq[addTm[z0, zZero], z0];
    expected1 = mkEq[addTm[z1, zZero], z1];
    HOLTest`assertEq[concl[specZ0], expected0, "⊢ intAdd (&ℤ 0) (&ℤ 0) = &ℤ 0"];
    HOLTest`assertEq[concl[specZ1], expected1, "⊢ intAdd (&ℤ 1) (&ℤ 0) = &ℤ 1"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intAddZeroThm], {}, "no hyps"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`intCanonIdThm] &&
        hyp[HOL`Stdlib`Int`intCanonIdThm] === {},
      "intCanonIdThm is a hyp-free theorem"]
  ]];

HOLTest`runTests["stdlib/Int: intAdd right inverse (intAdd z (intNeg z) = &ℤ 0)",
  Module[{one, z1, specZ1, addTm, neg, zZero, expected1},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];   (* &ℤ 1 *)
    zZero = mkComb[HOL`Stdlib`Int`intOfNumConst[], HOL`Stdlib`Num`zeroConst[]];
    addTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
    neg[t_] := mkComb[HOL`Stdlib`Int`intNegConst[], t];
    specZ1 = HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intAddNegThm];
    expected1 = mkEq[addTm[z1, neg[z1]], zZero];
    HOLTest`assertEq[concl[specZ1], expected1,
      "⊢ intAdd (&ℤ 1) (intNeg (&ℤ 1)) = &ℤ 0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intAddNegThm], {}, "no hyps"]
  ]];

(* ===== Stage d (part 4): additive associativity ===== *)

HOLTest`runTests["stdlib/Int: canon equivalence-class lemmas are hyp-free",
  Module[{},
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`canonEquivThm] &&
        hyp[HOL`Stdlib`Int`canonEquivThm] === {}, "canonEquivThm"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`canonInjThm] &&
        hyp[HOL`Stdlib`Int`canonInjThm] === {}, "canonInjThm"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`canonRespectsThm] &&
        hyp[HOL`Stdlib`Int`canonRespectsThm] === {}, "canonRespectsThm"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`repIntAddThm] &&
        hyp[HOL`Stdlib`Int`repIntAddThm] === {}, "repIntAddThm"]
  ]];

HOLTest`runTests["stdlib/Int: intAdd associativity (functional check)",
  Module[{one, two, z0, z1, z2, addTm, specZWV, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    two = mkComb[HOL`Stdlib`Num`sucConst[], one];
    z0 = mkComb[HOL`Stdlib`Int`intOfNumConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    z2 = mkComb[HOL`Stdlib`Int`intOfNumConst[], two];
    addTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
    specZWV = HOL`Bool`SPEC[z2, HOL`Bool`SPEC[z1,
      HOL`Bool`SPEC[z0, HOL`Stdlib`Int`intAddAssocThm]]];
    expected = mkEq[addTm[addTm[z0, z1], z2], addTm[z0, addTm[z1, z2]]];
    HOLTest`assertEq[concl[specZWV], expected,
      "⊢ intAdd (intAdd (&ℤ 0) (&ℤ 1)) (&ℤ 2) = intAdd (&ℤ 0) (intAdd (&ℤ 1) (&ℤ 2))"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intAddAssocThm], {}, "no hyps"]
  ]];

(* ===== Stage d (part 5): intSucc / intPred ===== *)

HOLTest`runTests["stdlib/Int: intSucc/intPred constant types",
  Module[{},
    HOLTest`assertEq[constType["intSucc"], tyFun[HOL`Stdlib`Int`intTy, HOL`Stdlib`Int`intTy],
      "intSucc : int → int"];
    HOLTest`assertEq[constType["intPred"], tyFun[HOL`Stdlib`Int`intTy, HOL`Stdlib`Int`intTy],
      "intPred : int → int"]
  ]];

HOLTest`runTests["stdlib/Int: intPred (intSucc z) = z (round-trip)",
  Module[{one, z1, specZ, succT, predT, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];   (* &ℤ 1 *)
    succT[t_] := mkComb[HOL`Stdlib`Int`intSuccConst[], t];
    predT[t_] := mkComb[HOL`Stdlib`Int`intPredConst[], t];
    specZ = HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intPredSuccThm];
    expected = mkEq[predT[succT[z1]], z1];
    HOLTest`assertEq[concl[specZ], expected,
      "⊢ intPred (intSucc (&ℤ 1)) = &ℤ 1"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intPredSuccThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: intSucc (intPred z) = z (round-trip)",
  Module[{one, z1, specZ, succT, predT, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    succT[t_] := mkComb[HOL`Stdlib`Int`intSuccConst[], t];
    predT[t_] := mkComb[HOL`Stdlib`Int`intPredConst[], t];
    specZ = HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intSuccPredThm];
    expected = mkEq[succT[predT[z1]], z1];
    HOLTest`assertEq[concl[specZ], expected,
      "⊢ intSucc (intPred (&ℤ 1)) = &ℤ 1"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intSuccPredThm], {}, "no hyps"]
  ]];

(* ===== Stage e (part 1): intMul — def, comm, identity, zero ===== *)

HOLTest`runTests["stdlib/Int: intMul constant type + repIntMulThm",
  Module[{},
    HOLTest`assertEq[constType["intMul"],
      tyFun[HOL`Stdlib`Int`intTy, tyFun[HOL`Stdlib`Int`intTy, HOL`Stdlib`Int`intTy]],
      "intMul : int → int → int"];
    HOLTest`assertTrue[isThm[HOL`Stdlib`Int`repIntMulThm] &&
        hyp[HOL`Stdlib`Int`repIntMulThm] === {}, "repIntMulThm hyp-free"]
  ]];

HOLTest`runTests["stdlib/Int: intMul commutativity (functional check)",
  Module[{one, two, z1, z2, mulTm, specZW, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    two = mkComb[HOL`Stdlib`Num`sucConst[], one];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    z2 = mkComb[HOL`Stdlib`Int`intOfNumConst[], two];
    mulTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
    specZW = HOL`Bool`SPEC[z2, HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intMulCommThm]];
    expected = mkEq[mulTm[z1, z2], mulTm[z2, z1]];
    HOLTest`assertEq[concl[specZW], expected,
      "⊢ intMul (&ℤ 1) (&ℤ 2) = intMul (&ℤ 2) (&ℤ 1)"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intMulCommThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: intMul right identity / zero (functional checks)",
  Module[{one, two, z2, intOne, intZero, mulTm, specOne, specZero, expOne, expZero},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    two = mkComb[HOL`Stdlib`Num`sucConst[], one];
    z2 = mkComb[HOL`Stdlib`Int`intOfNumConst[], two];
    intOne = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    intZero = mkComb[HOL`Stdlib`Int`intOfNumConst[], HOL`Stdlib`Num`zeroConst[]];
    mulTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
    specOne = HOL`Bool`SPEC[z2, HOL`Stdlib`Int`intMulOneThm];
    specZero = HOL`Bool`SPEC[z2, HOL`Stdlib`Int`intMulZeroThm];
    expOne = mkEq[mulTm[z2, intOne], z2];
    expZero = mkEq[mulTm[z2, intZero], intZero];
    HOLTest`assertEq[concl[specOne], expOne, "⊢ intMul (&ℤ 2) (&ℤ 1) = &ℤ 2"];
    HOLTest`assertEq[concl[specZero], expZero, "⊢ intMul (&ℤ 2) (&ℤ 0) = &ℤ 0"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intMulOneThm], {}, "intMulOne no hyps"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intMulZeroThm], {}, "intMulZero no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: intMul left distributivity (functional check)",
  Module[{one, two, three, z1, z2, z3, mulTm, addTm, specZWV, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    two = mkComb[HOL`Stdlib`Num`sucConst[], one];
    three = mkComb[HOL`Stdlib`Num`sucConst[], two];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    z2 = mkComb[HOL`Stdlib`Int`intOfNumConst[], two];
    z3 = mkComb[HOL`Stdlib`Int`intOfNumConst[], three];
    mulTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
    addTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
    specZWV = HOL`Bool`SPEC[z3, HOL`Bool`SPEC[z2,
      HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intMulDistribThm]]];
    expected = mkEq[mulTm[z1, addTm[z2, z3]],
      addTm[mulTm[z1, z2], mulTm[z1, z3]]];
    HOLTest`assertEq[concl[specZWV], expected,
      "⊢ intMul (&ℤ 1) (intAdd (&ℤ 2) (&ℤ 3)) = intAdd (intMul (&ℤ 1) (&ℤ 2)) (intMul (&ℤ 1) (&ℤ 3))"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intMulDistribThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: intMul associativity (functional check)",
  Module[{one, two, three, z1, z2, z3, mulTm, specZWV, expected},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    two = mkComb[HOL`Stdlib`Num`sucConst[], one];
    three = mkComb[HOL`Stdlib`Num`sucConst[], two];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    z2 = mkComb[HOL`Stdlib`Int`intOfNumConst[], two];
    z3 = mkComb[HOL`Stdlib`Int`intOfNumConst[], three];
    mulTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
    specZWV = HOL`Bool`SPEC[z3, HOL`Bool`SPEC[z2,
      HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intMulAssocThm]]];
    expected = mkEq[mulTm[mulTm[z1, z2], z3], mulTm[z1, mulTm[z2, z3]]];
    HOLTest`assertEq[concl[specZWV], expected,
      "⊢ intMul (intMul (&ℤ 1) (&ℤ 2)) (&ℤ 3) = intMul (&ℤ 1) (intMul (&ℤ 2) (&ℤ 3))"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intMulAssocThm], {}, "no hyps"]
  ]];

HOLTest`runTests["stdlib/Int: intMulEqZeroThm — no zero divisors (integral domain)",
  Module[{two, z2, intZero, mulTm, specZW, expected},
    two = mkComb[HOL`Stdlib`Num`sucConst[],
      mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]]];
    z2 = mkComb[HOL`Stdlib`Int`intOfNumConst[], two];
    intZero = mkComb[HOL`Stdlib`Int`intOfNumConst[], HOL`Stdlib`Num`zeroConst[]];
    mulTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intMulEqZeroThm], {}, "no hyps"];
    (* SPEC z:=&ℤ2, w:=&ℤ0 → (intMul (&ℤ2)(&ℤ0)=&ℤ0) ⇒ &ℤ2=&ℤ0 ∨ &ℤ0=&ℤ0 *)
    specZW = HOL`Bool`SPEC[intZero, HOL`Bool`SPEC[z2, HOL`Stdlib`Int`intMulEqZeroThm]];
    expected = mkComb[mkComb[mkConst["\[DoubleRightArrow]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
        mkEq[mulTm[z2, intZero], intZero]],
      mkComb[mkComb[mkConst["\[Or]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
        mkEq[z2, intZero]], mkEq[intZero, intZero]]];
    HOLTest`assertEq[concl[specZW], expected,
      "⊢ intMul (&ℤ 2) (&ℤ 0) = &ℤ 0 ⇒ &ℤ 2 = &ℤ 0 ∨ &ℤ 0 = &ℤ 0"]
  ]];

(* ===== Stage f (part 1): order intLe / intLt ===== *)

HOLTest`runTests["stdlib/Int: intLe/intLt constant types + order axioms hyp-free",
  Module[{},
    HOLTest`assertEq[constType["intLe"],
      tyFun[HOL`Stdlib`Int`intTy, tyFun[HOL`Stdlib`Int`intTy, boolTy]],
      "intLe : int → int → bool"];
    HOLTest`assertEq[constType["intLt"],
      tyFun[HOL`Stdlib`Int`intTy, tyFun[HOL`Stdlib`Int`intTy, boolTy]],
      "intLt : int → int → bool"];
    Scan[Function[t,
      HOLTest`assertTrue[isThm[t] && hyp[t] === {}, "hyp-free"]],
      {HOL`Stdlib`Int`intLeReflThm, HOL`Stdlib`Int`intLeAntisymThm,
       HOL`Stdlib`Int`intLeTransThm, HOL`Stdlib`Int`intLeTotalThm,
       HOL`Stdlib`Int`intLtNotLeThm}]
  ]];

HOLTest`runTests["stdlib/Int: intLe reflexivity + antisymmetry (functional checks)",
  Module[{one, z1, leTm, eqTm, specRefl, specAnti},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];   (* &ℤ 1 *)
    leTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intLeConst[], a], b];
    specRefl = HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intLeReflThm];
    HOLTest`assertEq[concl[specRefl], leTm[z1, z1], "⊢ intLe (&ℤ 1) (&ℤ 1)"];
    (* antisym SPEC z:=&ℤ1, w:=&ℤ1 → intLe ⇒ intLe ⇒ &ℤ1 = &ℤ1 *)
    specAnti = HOL`Bool`SPEC[z1, HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intLeAntisymThm]];
    HOLTest`assertTrue[
      MatchQ[concl[specAnti], comb[comb[const["\[DoubleRightArrow]", _], _],
        comb[comb[const["\[DoubleRightArrow]", _], _],
          comb[comb[const["=", _], _], _]]]],
      "⊢ intLe ⇒ intLe ⇒ = shape"]
  ]];

HOLTest`runTests["stdlib/Int: order/arith compatibility (functional checks)",
  Module[{one, z1, leTm, addTm, negTm, specAdd, specNeg, expAdd, expNeg},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];   (* &ℤ 1 *)
    leTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intLeConst[], a], b];
    addTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
    negTm[a_] := mkComb[HOL`Stdlib`Int`intNegConst[], a];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intLeAddMonoThm], {}, "addMono no hyps"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intLeNegThm], {}, "neg no hyps"];
    (* addMono SPEC z:=w:=u:=&ℤ1 → intLe (&ℤ1)(&ℤ1) ⇒ intLe (1+1)(1+1) *)
    specAdd = HOL`Bool`SPEC[z1, HOL`Bool`SPEC[z1, HOL`Bool`SPEC[z1,
      HOL`Stdlib`Int`intLeAddMonoThm]]];
    expAdd = mkComb[mkComb[mkConst["\[DoubleRightArrow]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
        leTm[z1, z1]], leTm[addTm[z1, z1], addTm[z1, z1]]];
    HOLTest`assertEq[concl[specAdd], expAdd,
      "⊢ intLe (&ℤ1)(&ℤ1) ⇒ intLe (intAdd (&ℤ1)(&ℤ1)) (intAdd (&ℤ1)(&ℤ1))"];
    specNeg = HOL`Bool`SPEC[z1, HOL`Bool`SPEC[z1, HOL`Stdlib`Int`intLeNegThm]];
    expNeg = mkComb[mkComb[mkConst["\[DoubleRightArrow]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
        leTm[z1, z1]], leTm[negTm[z1], negTm[z1]]];
    HOLTest`assertEq[concl[specNeg], expNeg,
      "⊢ intLe (&ℤ1)(&ℤ1) ⇒ intLe (intNeg (&ℤ1)) (intNeg (&ℤ1))"]
  ]];

HOLTest`runTests["stdlib/Int: mult-by-nonneg monotonicity + ℕ crossMultLeqThm hyp-free",
  Module[{one, z1, intZero, leTm, mulTm, specMul, expMul},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    z1 = mkComb[HOL`Stdlib`Int`intOfNumConst[], one];
    intZero = mkComb[HOL`Stdlib`Int`intOfNumConst[], HOL`Stdlib`Num`zeroConst[]];
    leTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intLeConst[], a], b];
    mulTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
    HOLTest`assertEq[hyp[HOL`Stdlib`Num`crossMultLeqThm], {}, "crossMult no hyps"];
    HOLTest`assertEq[hyp[HOL`Stdlib`Int`intLeMulNonnegThm], {}, "mulNonneg no hyps"];
    (* SPEC z:=w:=u:=&ℤ1 → intLe(&ℤ0)(&ℤ1) ⇒ intLe(&ℤ1)(&ℤ1) ⇒ intLe (1*1)(1*1) *)
    specMul = HOL`Bool`SPEC[z1, HOL`Bool`SPEC[z1, HOL`Bool`SPEC[z1,
      HOL`Stdlib`Int`intLeMulNonnegThm]]];
    expMul = mkComb[mkComb[mkConst["\[DoubleRightArrow]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
        leTm[intZero, z1]],
      mkComb[mkComb[mkConst["\[DoubleRightArrow]", tyFun[boolTy, tyFun[boolTy, boolTy]]],
        leTm[z1, z1]], leTm[mulTm[z1, z1], mulTm[z1, z1]]]];
    HOLTest`assertEq[concl[specMul], expMul,
      "⊢ intLe (&ℤ0)(&ℤ1) ⇒ intLe (&ℤ1)(&ℤ1) ⇒ intLe (intMul (&ℤ1)(&ℤ1)) (intMul (&ℤ1)(&ℤ1))"]
  ]];

(* ===== Stage g: &ℤ homomorphism + intAbs ===== *)

HOLTest`runTests["stdlib/Int: &ℤ ring/order homomorphism (functional checks)",
  Module[{mV, nV, ofNum, addTm, mulTm, leTm, plusN, timesN, leqN, specAdd, specMul, specLe},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    ofNum[t_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], t];
    addTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intAddConst[], a], b];
    mulTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intMulConst[], a], b];
    leTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Int`intLeConst[], a], b];
    plusN[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`plusConst[], a], b];
    timesN[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`timesConst[], a], b];
    leqN[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];
    specAdd = HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, HOL`Stdlib`Int`intOfNumAddThm]];
    HOLTest`assertEq[concl[specAdd],
      mkEq[ofNum[plusN[mV, nV]], addTm[ofNum[mV], ofNum[nV]]],
      "⊢ &ℤ(m+n) = intAdd (&ℤ m) (&ℤ n)"];
    specMul = HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, HOL`Stdlib`Int`intOfNumMulThm]];
    HOLTest`assertEq[concl[specMul],
      mkEq[ofNum[timesN[mV, nV]], mulTm[ofNum[mV], ofNum[nV]]],
      "⊢ &ℤ(m*n) = intMul (&ℤ m) (&ℤ n)"];
    specLe = HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, HOL`Stdlib`Int`intOfNumLeThm]];
    HOLTest`assertEq[concl[specLe],
      mkEq[leTm[ofNum[mV], ofNum[nV]], leqN[mV, nV]],
      "⊢ intLe (&ℤ m) (&ℤ n) = (m ≤ n)"];
    Scan[Function[t, HOLTest`assertEq[hyp[t], {}, "no hyps"]],
      {HOL`Stdlib`Int`intOfNumAddThm, HOL`Stdlib`Int`intOfNumMulThm,
       HOL`Stdlib`Int`intOfNumLeThm}]
  ]];

HOLTest`runTests["stdlib/Int: intAbs (type + lemmas hyp-free + functional check)",
  Module[{one, z1, absTm, negTm, ofNum, specNum, expNum},
    one = mkComb[HOL`Stdlib`Num`sucConst[], HOL`Stdlib`Num`zeroConst[]];
    ofNum[t_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], t];
    z1 = ofNum[one];
    absTm[a_] := mkComb[HOL`Stdlib`Int`intAbsConst[], a];
    HOLTest`assertEq[constType["intAbs"],
      tyFun[HOL`Stdlib`Int`intTy, HOL`Stdlib`Int`intTy], "intAbs : int → int"];
    Scan[Function[t, HOLTest`assertEq[hyp[t], {}, "no hyps"]],
      {HOL`Stdlib`Int`intAbsNumThm, HOL`Stdlib`Int`intAbsNegThm,
       HOL`Stdlib`Int`intAbsNonnegThm}];
    (* intAbs (&ℤ 1) = &ℤ 1 *)
    specNum = HOL`Bool`SPEC[one, HOL`Stdlib`Int`intAbsNumThm];
    HOLTest`assertEq[concl[specNum], mkEq[absTm[z1], z1], "⊢ intAbs (&ℤ 1) = &ℤ 1"]
  ]];
