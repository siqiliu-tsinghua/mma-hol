(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];

(* ========= thm opacity / unforgeability ========= *)

HOLTest`runTests["kernel: thm opacity", Module[{},
  HOLTest`assertEq[isThm[42], False, "isThm rejects integer"];
  HOLTest`assertEq[isThm["not a thm"], False, "isThm rejects string"];
  HOLTest`assertEq[isThm[<|"hyps" -> {}, "concl" -> True|>], False, "isThm rejects assoc"];
  HOLTest`assertEq[isThm[{{}, True}], False, "isThm rejects bare list pair"];
  HOLTest`assertThrows[destThm[42], "rule", "destThm rejects integer"];
  HOLTest`assertThrows[destThm[<|"hyps" -> {}, "concl" -> True|>], "rule", "destThm rejects assoc"];
  HOLTest`assertThrows[hyp[42], "rule", "hyp rejects non-thm"];
  HOLTest`assertThrows[concl[42], "rule", "concl rejects non-thm"];
]];

(* ========= REFL ========= *)

HOLTest`runTests["kernel: REFL", Module[{alpha, x, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  th = REFL[x];
  HOLTest`assertEq[isThm[th], True, "REFL produces a thm"];
  HOLTest`assertEq[hyp[th], {}, "REFL has no hypotheses"];
  HOLTest`assertEq[concl[th], mkEq[x, x], "REFL conclusion is t=t"];
]];

(* ========= TRANS ========= *)

HOLTest`runTests["kernel: TRANS", Module[{alpha, x, y, z, w, eq1, eq2, eq3, chain},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha]; z = mkVar["z", alpha]; w = mkVar["w", alpha];
  eq1 = ASSUME[mkEq[x, y]];
  eq2 = ASSUME[mkEq[y, z]];
  eq3 = ASSUME[mkEq[z, w]];
  chain = TRANS[eq1, eq2];
  HOLTest`assertEq[concl[chain], mkEq[x, z], "TRANS: x=y, y=z ⊢ x=z"];
  HOLTest`assertEq[Length[hyp[chain]], 2, "TRANS merges hypotheses"];
  HOLTest`assertEq[concl[TRANS[chain, eq3]], mkEq[x, w], "TRANS chains to x=w"];
  HOLTest`assertThrows[
    TRANS[ASSUME[mkEq[x, y]], ASSUME[mkEq[z, w]]],
    "rule", "TRANS: middle mismatch rejected"];
  HOLTest`assertThrows[TRANS[42, eq2], "rule", "TRANS rejects non-thm"];
  HOLTest`assertThrows[TRANS[eq1, "nope"], "rule", "TRANS rejects non-thm on right"];
]];

(* ========= MKCOMB ========= *)

HOLTest`runTests["kernel: MKCOMB", Module[{alpha, beta, f, g, x, y, fx, gy, th},
  alpha = mkVarType["a"]; beta = mkVarType["b"];
  f = mkVar["f", tyFun[alpha, beta]]; g = mkVar["g", tyFun[alpha, beta]];
  x = mkVar["x", alpha];              y = mkVar["y", alpha];
  th = MKCOMB[REFL[f], REFL[x]];
  HOLTest`assertEq[concl[th], mkEq[mkComb[f, x], mkComb[f, x]], "MKCOMB reflexive case"];
  th = MKCOMB[ASSUME[mkEq[f, g]], ASSUME[mkEq[x, y]]];
  HOLTest`assertEq[concl[th], mkEq[mkComb[f, x], mkComb[g, y]], "MKCOMB combines"];
  HOLTest`assertEq[Length[hyp[th]], 2, "MKCOMB merges hypotheses"];
  HOLTest`assertThrows[MKCOMB[REFL[f], 42], "rule", "MKCOMB rejects non-thm"];
]];

(* ========= ABS ========= *)

HOLTest`runTests["kernel: ABS", Module[{alpha, x, y, eq, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  eq = REFL[x];
  th = ABS[y, eq];
  HOLTest`assertEq[concl[th], mkEq[mkAbs[y, x], mkAbs[y, x]], "ABS over non-free var"];
  th = ABS[x, REFL[x]];
  HOLTest`assertEq[concl[th], mkEq[mkAbs[x, x], mkAbs[x, x]], "ABS over the var itself"];
  HOLTest`assertThrows[
    ABS[x, ASSUME[mkEq[x, y]]],
    "rule", "ABS rejects binder free in hyps"];
  HOLTest`assertThrows[ABS[mkVar["_b0", alpha], REFL[x]], "term", "ABS via mkVar: reserved name rejected earlier"];
]];

(* ========= BETA ========= *)

HOLTest`runTests["kernel: BETA", Module[{alpha, x, y, idAbs, constAbs, redex1, redex2, th1, th2},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  idAbs    = mkAbs[x, x];
  constAbs = mkAbs[x, y];
  redex1 = mkComb[idAbs, x];
  redex2 = mkComb[constAbs, x];
  th1 = BETA[redex1];
  th2 = BETA[redex2];
  HOLTest`assertEq[concl[th1], mkEq[redex1, x], "BETA: (λx.x) x = x"];
  HOLTest`assertEq[concl[th2], mkEq[redex2, y], "BETA: (λx.y) x = y"];
  HOLTest`assertEq[hyp[th1], {}, "BETA produces no hyps"];
  HOLTest`assertThrows[BETA[x], "rule", "BETA rejects non-redex"];
  HOLTest`assertThrows[BETA[mkComb[idAbs, y]], "rule", "BETA rejects wrong argument name"];
]];

(* ========= ASSUME ========= *)

HOLTest`runTests["kernel: ASSUME", Module[{alpha, x, y, p, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha];
  p = mkEq[x, y];
  th = ASSUME[p];
  HOLTest`assertEq[hyp[th], {p}, "ASSUME places p in hyps"];
  HOLTest`assertEq[concl[th], p, "ASSUME conclusion is p"];
  HOLTest`assertThrows[ASSUME[x], "rule", "ASSUME rejects non-bool term"];
]];

(* ========= EQMP ========= *)

HOLTest`runTests["kernel: EQMP", Module[{x, y, eq, assum, th},
  x = mkVar["x", boolTy]; y = mkVar["y", boolTy];
  eq = ASSUME[mkEq[x, y]];
  assum = ASSUME[x];
  th = EQMP[eq, assum];
  HOLTest`assertEq[concl[th], y, "EQMP yields RHS"];
  HOLTest`assertEq[Length[hyp[th]], 2, "EQMP merges hyps"];
  HOLTest`assertThrows[EQMP[eq, ASSUME[y]], "rule", "EQMP rejects LHS mismatch"];
  HOLTest`assertThrows[EQMP[REFL[x], 7], "rule", "EQMP rejects non-thm"];
]];

(* ========= DEDUCTANTISYM ========= *)

HOLTest`runTests["kernel: DEDUCTANTISYM", Module[{p, q, thp, thq, th},
  p = mkVar["p", boolTy]; q = mkVar["q", boolTy];
  thp = ASSUME[p];
  thq = ASSUME[q];
  th = DEDUCTANTISYM[thp, thq];
  HOLTest`assertEq[concl[th], mkEq[p, q], "DEDUCTANTISYM yields p=q"];
  HOLTest`assertEq[hyp[th], Sort[{p, q}], "DEDUCTANTISYM merges remaining hyps"];
  (* self-antisym: Γ⊢p, Γ⊢p → ⊢ p=p (both hyps strip away) *)
  HOLTest`assertEq[hyp[DEDUCTANTISYM[thp, thp]], {}, "DEDUCTANTISYM drops matching hyps"];
]];

(* ========= INST ========= *)

HOLTest`runTests["kernel: INST", Module[{alpha, x, y, z, eq, th},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha]; y = mkVar["y", alpha]; z = mkVar["z", alpha];
  eq = ASSUME[mkEq[x, y]];
  th = INST[<|x -> z|>, eq];
  HOLTest`assertEq[concl[th], mkEq[z, y], "INST substitutes in concl"];
  HOLTest`assertEq[hyp[th], {mkEq[z, y]}, "INST substitutes in hyps"];
  th = INST[{x -> z}, eq];
  HOLTest`assertEq[concl[th], mkEq[z, y], "INST accepts list of rules"];
  HOLTest`assertThrows[INST[<|x -> z|>, 42], "rule", "INST rejects non-thm"];
]];

(* ========= INSTTYPE ========= *)

HOLTest`runTests["kernel: INSTTYPE", Module[{alpha, beta, xA, yA, eq, th},
  alpha = mkVarType["a"]; beta = mkVarType["b"];
  xA = mkVar["x", alpha]; yA = mkVar["y", alpha];
  eq = REFL[xA];
  th = INSTTYPE[<|alpha -> beta|>, eq];
  HOLTest`assertEq[concl[th], mkEq[mkVar["x", beta], mkVar["x", beta]],
    "INSTTYPE retypes term"];
  th = INSTTYPE[{alpha -> boolTy}, eq];
  HOLTest`assertEq[concl[th], mkEq[mkVar["x", boolTy], mkVar["x", boolTy]],
    "INSTTYPE accepts list of rules"];
  HOLTest`assertThrows[INSTTYPE[<|alpha -> beta|>, "nope"], "rule",
    "INSTTYPE rejects non-thm"];
]];

(* ========= newConstant ========= *)

HOLTest`runTests["kernel: newConstant", Module[{alpha, c, cty},
  alpha = mkVarType["a"];
  newConstant["kcTestConst", tyFun[alpha, boolTy]];
  HOLTest`assertEq[constType["kcTestConst"], tyFun[alpha, boolTy],
    "newConstant registered"];
  cty = tyFun[boolTy, boolTy];
  c = mkConst["kcTestConst", cty];
  HOLTest`assertEq[c, const["kcTestConst", cty], "mkConst works post-registration"];
  HOLTest`assertThrows[newConstant["kcTestConst", boolTy], "kernel",
    "newConstant rejects duplicate name"];
  HOLTest`assertThrows[newConstant[42, boolTy], "kernel",
    "newConstant rejects non-string name"];
]];

(* ========= newType ========= *)

HOLTest`runTests["kernel: newType", Module[{t},
  newType["kcTestTy", 1];
  HOLTest`assertEq[typeArity["kcTestTy"], 1, "newType registered"];
  t = mkType["kcTestTy", {boolTy}];
  HOLTest`assertEq[t, tyApp["kcTestTy", {boolTy}], "mkType works post-newType"];
  HOLTest`assertThrows[newType["kcTestTy", 2], "kernel", "newType rejects duplicate name"];
  HOLTest`assertThrows[newType["kcTestTy2", -1], "kernel", "newType rejects negative arity"];
]];

(* ========= newDefinition ========= *)

HOLTest`runTests["kernel: newDefinition", Module[{cvar, rhs, defTm, th, cconst},
  cvar = mkVar["kcDefOne", boolTy];
  rhs  = mkEq[mkAbs[mkVar["z", boolTy], mkVar["z", boolTy]],
              mkAbs[mkVar["z", boolTy], mkVar["z", boolTy]]];
  defTm = mkEq[cvar, rhs];
  th = newDefinition[defTm];
  HOLTest`assertEq[isThm[th], True, "newDefinition returns a thm"];
  HOLTest`assertEq[hyp[th], {}, "newDefinition has no hyps"];
  cconst = const["kcDefOne", boolTy];
  HOLTest`assertEq[concl[th], mkEq[cconst, rhs], "newDefinition conclusion"];
  HOLTest`assertEq[constType["kcDefOne"], boolTy, "newDefinition registers constant"];
  HOLTest`assertThrows[newDefinition[defTm], "kernel",
    "newDefinition rejects duplicate name"];
  HOLTest`assertThrows[
    newDefinition[mkEq[mkVar["kcDefBad", boolTy], mkVar["free", boolTy]]],
    "kernel", "newDefinition rejects open RHS"];
]];

(* ========= newBasicTypeDefinition ========= *)

HOLTest`runTests["kernel: newBasicTypeDefinition", Module[{y, P, x, axThm, pair, absThm, repThm},
  y = mkVar["y", boolTy];
  P = mkAbs[y, mkEq[y, y]];
  x = mkVar["kcWitness", boolTy];
  axThm = newAxiom[mkComb[P, x]];
  pair = newBasicTypeDefinition["kcTyA", "kcAbsA", "kcRepA", axThm];
  {absThm, repThm} = pair;
  HOLTest`assertEq[isThm[absThm], True, "abs-rep theorem is a thm"];
  HOLTest`assertEq[isThm[repThm], True, "rep-abs theorem is a thm"];
  HOLTest`assertEq[typeArity["kcTyA"], 0, "new type has arity 0 (no tyvars in P)"];
  HOLTest`assertEq[constType["kcAbsA"], tyFun[boolTy, tyApp["kcTyA", {}]],
    "abs constant has type bool → kcTyA"];
  HOLTest`assertEq[constType["kcRepA"], tyFun[tyApp["kcTyA", {}], boolTy],
    "rep constant has type kcTyA → bool"];
]];

(* ========= newAxiom + lockAxioms (LAST — one-way door) ========= *)

HOLTest`runTests["kernel: newAxiom + lockAxioms", Module[{p, th, before, after},
  p = mkVar["kcAxP", boolTy];
  before = Length[listAxioms[]];
  th = newAxiom[p];
  HOLTest`assertEq[isThm[th], True, "newAxiom yields a thm"];
  HOLTest`assertEq[concl[th], p, "newAxiom concl is the posted term"];
  HOLTest`assertEq[hyp[th], {}, "newAxiom has no hyps"];
  after = Length[listAxioms[]];
  HOLTest`assertEq[after - before, 1, "listAxioms grows by 1"];
  HOLTest`assertThrows[newAxiom[mkVar["x", mkVarType["a"]]], "rule",
    "newAxiom rejects non-bool"];
  (* LOCK — must be the last interaction with newAxiom *)
  lockAxioms[];
  HOLTest`assertThrows[newAxiom[mkVar["kcAxPost", boolTy]], "kernel",
    "newAxiom throws after lockAxioms"];
]];
