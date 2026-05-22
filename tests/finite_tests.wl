(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];
Needs["HOL`Equal`"];
Needs["HOL`Bool`"];
Needs["HOL`Stdlib`Set`"];
Needs["HOL`Stdlib`Finite`"];

αTy = mkVarType["A"];
setTy = tyFun[αTy, boolTy];

HOLTest`runTests["finite: FINITE has type (α → bool) → bool",
  HOLTest`assertEq[HOL`Kernel`constType["FINITE"], tyFun[setTy, boolTy],
    "FINITE : set → bool"]];

HOLTest`runTests["finite: finiteDefThm is an equation, no hyps",
  Module[{c, dThm},
    dThm = HOL`Stdlib`Finite`finiteDefThm;
    c = concl[dThm];
    HOLTest`assertTrue[
      MatchQ[c, comb[comb[const["=", _], const["FINITE", _]], _]],
      "FINITE = <lambda>"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["finite: finiteEmptyThm — ⊢ FINITE EMPTY, no hyps",
  Module[{dThm},
    dThm = HOL`Stdlib`Finite`finiteEmptyThm;
    HOLTest`assertEq[concl[dThm],
      HOL`Stdlib`Finite`finiteAppTerm[HOL`Stdlib`Set`emptyConst[]],
      "⊢ FINITE EMPTY"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["finite: finiteInsertThm — ⊢ ∀x s. FINITE s ⇒ FINITE (x INSERT s)",
  Module[{dThm, x, s, expected, impC, finC, insT},
    dThm = HOL`Stdlib`Finite`finiteInsertThm;
    x = mkVar["x", αTy]; s = mkVar["s", setTy];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    finC = HOL`Stdlib`Finite`finiteAppTerm;
    insT = HOL`Stdlib`Set`insertTerm[x, s];
    expected = mkComb[mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]],
      mkAbs[x, mkComb[mkConst["∀", tyFun[tyFun[setTy, boolTy], boolTy]],
        mkAbs[s, mkComb[mkComb[impC, finC[s]], finC[insT]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[dThm], expected],
      "⊢ ∀x s. FINITE s ⇒ FINITE (x INSERT s)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["finite: finiteSingThm — ⊢ ∀x. FINITE (SING x)",
  Module[{dThm, x, expected, finC},
    dThm = HOL`Stdlib`Finite`finiteSingThm;
    x = mkVar["x", αTy];
    finC = HOL`Stdlib`Finite`finiteAppTerm;
    expected = mkComb[mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]],
      mkAbs[x, finC[HOL`Stdlib`Set`singTerm[x]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[dThm], expected],
      "⊢ ∀x. FINITE (SING x)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["finite: finiteInductThm — ⊢ ∀P. P ∅ ∧ step ⇒ ∀s. FINITE s ⇒ P s",
  Module[{dThm, predTy, pV, x, s, andC, impC, finC, pAt, emp,
          faA, faSet, faPred, step, ante, concl2, expected},
    dThm = HOL`Stdlib`Finite`finiteInductThm;
    predTy = tyFun[setTy, boolTy];
    pV = mkVar["P", predTy]; x = mkVar["x", αTy]; s = mkVar["s", setTy];
    andC = mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    finC = HOL`Stdlib`Finite`finiteAppTerm;
    emp = HOL`Stdlib`Set`emptyConst[];
    pAt[t_] := mkComb[pV, t];
    faA = mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]];
    faSet = mkConst["∀", tyFun[tyFun[setTy, boolTy], boolTy]];
    faPred = mkConst["∀", tyFun[tyFun[predTy, boolTy], boolTy]];
    step = mkComb[faA, mkAbs[x, mkComb[faSet, mkAbs[s,
      mkComb[mkComb[impC,
        mkComb[mkComb[andC, finC[s]], pAt[s]]],
        pAt[HOL`Stdlib`Set`insertTerm[x, s]]]]]]];
    ante = mkComb[mkComb[andC, pAt[emp]], step];
    concl2 = mkComb[faSet, mkAbs[s, mkComb[mkComb[impC, finC[s]], pAt[s]]]];
    expected = mkComb[faPred, mkAbs[pV, mkComb[mkComb[impC, ante], concl2]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[dThm], expected],
      "⊢ ∀P. P ∅ ∧ (∀x s. FINITE s ∧ P s ⇒ P (x INSERT s)) ⇒ ∀s. FINITE s ⇒ P s"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

(* Derived: FINITE of a concrete two-element insert chain. *)
HOLTest`runTests["finite: FINITE (a INSERT (b INSERT EMPTY)) by the rules",
  Module[{a, b, emp, ins1, ins2, fin1, fin2},
    a = mkVar["a", αTy]; b = mkVar["b", αTy];
    emp = HOL`Stdlib`Set`emptyConst[];
    ins1 = HOL`Stdlib`Set`insertTerm[b, emp];
    ins2 = HOL`Stdlib`Set`insertTerm[a, ins1];
    (* FINITE (b INSERT EMPTY) *)
    fin1 = MP[SPEC[emp, SPEC[b, HOL`Stdlib`Finite`finiteInsertThm]],
      HOL`Stdlib`Finite`finiteEmptyThm];
    (* FINITE (a INSERT (b INSERT EMPTY)) *)
    fin2 = MP[SPEC[ins1, SPEC[a, HOL`Stdlib`Finite`finiteInsertThm]], fin1];
    HOLTest`assertEq[concl[fin2], HOL`Stdlib`Finite`finiteAppTerm[ins2],
      "⊢ FINITE (a INSERT (b INSERT EMPTY))"];
    HOLTest`assertEq[hyp[fin2], {}, "no hyps"];
]];

HOLTest`runTests["finite: finiteUnionThm — ⊢ ∀s t. FINITE s ⇒ FINITE t ⇒ FINITE (s ∪ t)",
  Module[{dThm, s, t, impC, finC, expected},
    dThm = HOL`Stdlib`Finite`finiteUnionThm;
    s = mkVar["s", setTy]; t = mkVar["t", setTy];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    finC = HOL`Stdlib`Finite`finiteAppTerm;
    expected = mkComb[mkConst["∀", tyFun[tyFun[setTy, boolTy], boolTy]],
      mkAbs[s, mkComb[mkConst["∀", tyFun[tyFun[setTy, boolTy], boolTy]],
        mkAbs[t, mkComb[mkComb[impC, finC[s]],
          mkComb[mkComb[impC, finC[t]],
            finC[HOL`Stdlib`Set`unionTerm[s, t]]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[dThm], expected],
      "⊢ ∀s t. FINITE s ⇒ FINITE t ⇒ FINITE (s ∪ t)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["finite: FINITE (SING a ∪ SING b) via finiteUnionThm",
  Module[{a, b, sa, sb, finUnion},
    a = mkVar["a", αTy]; b = mkVar["b", αTy];
    sa = HOL`Stdlib`Set`singTerm[a]; sb = HOL`Stdlib`Set`singTerm[b];
    finUnion = MP[MP[
        SPEC[sb, SPEC[sa, HOL`Stdlib`Finite`finiteUnionThm]],
        SPEC[a, HOL`Stdlib`Finite`finiteSingThm]],
      SPEC[b, HOL`Stdlib`Finite`finiteSingThm]];
    HOLTest`assertEq[concl[finUnion],
      HOL`Stdlib`Finite`finiteAppTerm[HOL`Stdlib`Set`unionTerm[sa, sb]],
      "⊢ FINITE (SING a ∪ SING b)"];
    HOLTest`assertEq[hyp[finUnion], {}, "no hyps"];
]];

HOLTest`runTests["finite: finiteSubsetThm — ⊢ ∀s. FINITE s ⇒ ∀t. t ⊆ s ⇒ FINITE t",
  Module[{dThm, s, t, impC, finC, faSet, expected},
    dThm = HOL`Stdlib`Finite`finiteSubsetThm;
    s = mkVar["s", setTy]; t = mkVar["t", setTy];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    finC = HOL`Stdlib`Finite`finiteAppTerm;
    faSet = mkConst["∀", tyFun[tyFun[setTy, boolTy], boolTy]];
    expected = mkComb[faSet, mkAbs[s, mkComb[mkComb[impC, finC[s]],
      mkComb[faSet, mkAbs[t, mkComb[mkComb[impC,
        HOL`Stdlib`Set`subsetTerm[t, s]], finC[t]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[dThm], expected],
      "⊢ ∀s. FINITE s ⇒ ∀t. t ⊆ s ⇒ FINITE t"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["finite: finiteDeleteThm — ⊢ ∀s x. FINITE s ⇒ FINITE (DELETE s x)",
  Module[{dThm, s, x, impC, finC, expected},
    dThm = HOL`Stdlib`Finite`finiteDeleteThm;
    s = mkVar["s", setTy]; x = mkVar["x", αTy];
    impC = mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
    finC = HOL`Stdlib`Finite`finiteAppTerm;
    expected = mkComb[mkConst["∀", tyFun[tyFun[setTy, boolTy], boolTy]],
      mkAbs[s, mkComb[mkConst["∀", tyFun[tyFun[αTy, boolTy], boolTy]],
        mkAbs[x, mkComb[mkComb[impC, finC[s]],
          finC[HOL`Stdlib`Set`deleteTerm[s, x]]]]]]];
    HOLTest`assertTrue[HOL`Terms`aconv[concl[dThm], expected],
      "⊢ ∀s x. FINITE s ⇒ FINITE (DELETE s x)"];
    HOLTest`assertEq[hyp[dThm], {}, "no hyps"];
]];

HOLTest`runTests["finite: FINITE (DELETE (SING a) b) via finiteDeleteThm",
  Module[{a, b, sa, finDel},
    a = mkVar["a", αTy]; b = mkVar["b", αTy];
    sa = HOL`Stdlib`Set`singTerm[a];
    finDel = MP[SPEC[b, SPEC[sa, HOL`Stdlib`Finite`finiteDeleteThm]],
      SPEC[a, HOL`Stdlib`Finite`finiteSingThm]];
    HOLTest`assertEq[concl[finDel],
      HOL`Stdlib`Finite`finiteAppTerm[HOL`Stdlib`Set`deleteTerm[sa, b]],
      "⊢ FINITE (DELETE (SING a) b)"];
    HOLTest`assertEq[hyp[finDel], {}, "no hyps"];
]];
