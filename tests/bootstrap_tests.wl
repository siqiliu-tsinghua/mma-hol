(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];
Needs["HOL`Bootstrap`"];

HOLTest`runTests["bootstrap: definitions produced theorems", Module[{},
  HOLTest`assertEq[isThm[tDef], True, "tDef is a thm"];
  HOLTest`assertEq[isThm[forallDef], True, "forallDef is a thm"];
  HOLTest`assertEq[isThm[andDef], True, "andDef is a thm"];
  HOLTest`assertEq[isThm[impliesDef], True, "impliesDef is a thm"];
  HOLTest`assertEq[isThm[existsDef], True, "existsDef is a thm"];
  HOLTest`assertEq[isThm[fDef], True, "fDef is a thm"];
  HOLTest`assertEq[isThm[notDef], True, "notDef is a thm"];
  HOLTest`assertEq[isThm[oneOneDef], True, "oneOneDef is a thm"];
  HOLTest`assertEq[isThm[ontoDef], True, "ontoDef is a thm"];
  HOLTest`assertEq[hyp[tDef], {}, "tDef has no hyps"];
]];

HOLTest`runTests["bootstrap: constants registered with correct types",
  Module[{names, alpha, beta, afnTy, bfnTy},
  alpha = mkVarType["a"];
  beta  = mkVarType["b"];
  names = listConstants[];
  HOLTest`assertTrue[MemberQ[names, "T"], "T registered"];
  HOLTest`assertTrue[MemberQ[names, "F"], "F registered"];
  HOLTest`assertTrue[MemberQ[names, "∀"], "∀ registered"];
  HOLTest`assertTrue[MemberQ[names, "∃"], "∃ registered"];
  HOLTest`assertTrue[MemberQ[names, "∧"], "∧ registered"];
  HOLTest`assertTrue[MemberQ[names, "⇒"], "⇒ registered"];
  HOLTest`assertTrue[MemberQ[names, "¬"], "¬ registered"];
  HOLTest`assertTrue[MemberQ[names, "@"], "@ registered"];
  HOLTest`assertTrue[MemberQ[names, "ONE_ONE"], "ONE_ONE registered"];
  HOLTest`assertTrue[MemberQ[names, "ONTO"], "ONTO registered"];
  HOLTest`assertEq[constType["T"], boolTy, "T : bool"];
  HOLTest`assertEq[constType["F"], boolTy, "F : bool"];
  HOLTest`assertEq[constType["∀"], tyFun[tyFun[alpha, boolTy], boolTy],
    "∀ : (α→bool)→bool"];
  HOLTest`assertEq[constType["∃"], tyFun[tyFun[alpha, boolTy], boolTy],
    "∃ : (α→bool)→bool"];
  HOLTest`assertEq[constType["∧"], tyFun[boolTy, tyFun[boolTy, boolTy]],
    "∧ : bool→bool→bool"];
  HOLTest`assertEq[constType["⇒"], tyFun[boolTy, tyFun[boolTy, boolTy]],
    "⇒ : bool→bool→bool"];
  HOLTest`assertEq[constType["¬"], tyFun[boolTy, boolTy], "¬ : bool→bool"];
  HOLTest`assertEq[constType["@"], tyFun[tyFun[alpha, boolTy], alpha],
    "@ : (α→bool)→α"];
  afnTy = tyFun[alpha, beta];
  HOLTest`assertEq[constType["ONE_ONE"], tyFun[afnTy, boolTy],
    "ONE_ONE : (α→β)→bool"];
  HOLTest`assertEq[constType["ONTO"], tyFun[afnTy, boolTy],
    "ONTO : (α→β)→bool"];
]];

HOLTest`runTests["bootstrap: axioms", Module[{axs},
  HOLTest`assertEq[isThm[etaAx], True, "etaAx is a thm"];
  HOLTest`assertEq[isThm[selectAx], True, "selectAx is a thm"];
  HOLTest`assertEq[isThm[infinityAx], True, "infinityAx is a thm"];
  HOLTest`assertEq[hyp[etaAx], {}, "etaAx has no hyps"];
  HOLTest`assertEq[hyp[selectAx], {}, "selectAx has no hyps"];
  HOLTest`assertEq[hyp[infinityAx], {}, "infinityAx has no hyps"];
  axs = listAxioms[];
  (* pre-bootstrap kernel_tests also used newAxiom, so we check the last 3. *)
  HOLTest`assertTrue[Length[axs] >= 3, "at least 3 axioms posted"];
  HOLTest`assertEq[axs[[-3]], concl[etaAx],      "third-to-last axiom is ETA"];
  HOLTest`assertEq[axs[[-2]], concl[selectAx],   "second-to-last axiom is SELECT"];
  HOLTest`assertEq[axs[[-1]], concl[infinityAx], "last axiom is INFINITY"];
]];

HOLTest`runTests["bootstrap: newAxiom is closed after lockAxioms",
  Module[{p},
  p = mkVar["shouldFail", boolTy];
  HOLTest`assertThrows[newAxiom[p], "kernel",
    "newAxiom throws after lockAxioms"];
]];

(* Capstone: ⊢ T derivable from primitives + tDef. *)

symThm[th_] := Module[{h, c, a, b, reflA, eqAB, mid, refl},
  {h, c} = destThm[th];
  {a, b} = destThm[th][[2]] /. comb[comb[const["=", _], x_], y_] :> {x, y};
  refl = REFL[a];
  eqAB = MKCOMB[REFL[mkConst["=", tyFun[typeOf[a], tyFun[typeOf[a], boolTy]]]], th];
  mid  = MKCOMB[eqAB, REFL[a]];
  EQMP[mid, refl]
];

HOLTest`runTests["bootstrap: capstone ⊢ T", Module[{xVar, body, tTerm, reflBody, symTDef, tThm},
  xVar = mkVar["x", boolTy];
  body = mkAbs[xVar, xVar];
  tTerm = mkEq[body, body];
  reflBody = REFL[body];
  HOLTest`assertEq[concl[reflBody], tTerm, "REFL[λx.x] = (tTerm)"];
  symTDef = symThm[tDef];
  HOLTest`assertEq[concl[symTDef],
    mkEq[tTerm, mkConst["T", boolTy]],
    "sym(tDef) swaps sides"];
  tThm = EQMP[symTDef, reflBody];
  HOLTest`assertEq[concl[tThm], mkConst["T", boolTy], "⊢ T derived"];
  HOLTest`assertEq[hyp[tThm], {}, "⊢ T has no hyps"];
]];
