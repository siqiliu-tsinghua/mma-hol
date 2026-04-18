(* ::Package:: *)

Needs["HOLTest`"];
Needs["HOL`Error`"];
Needs["HOL`Types`"];
Needs["HOL`Terms`"];
Needs["HOL`Kernel`"];

HOLTest`runTests["terms: mkVar", Module[{alpha},
  alpha = mkVarType["a"];
  HOLTest`assertEq[mkVar["x", alpha], var["x", alpha], "mkVar basic"];
  HOLTest`assertEq[mkVar["y", boolTy], var["y", boolTy], "mkVar on bool"];
  HOLTest`assertThrows[mkVar["", alpha], "term", "empty name rejected"];
  HOLTest`assertThrows[mkVar[42, alpha], "term", "non-string rejected"];
  HOLTest`assertThrows[mkVar["_b0", alpha], "term", "reserved _b0 rejected"];
  HOLTest`assertThrows[mkVar["_b123", alpha], "term", "reserved _b123 rejected"];
]];

HOLTest`runTests["terms: mkConst and '=' pre-registration", Module[{alpha, beta, eq},
  alpha = mkVarType["a"];
  beta = mkVarType["b"];
  HOLTest`assertEq[
    listConstants[], {"="},
    "only '=' pre-registered"
  ];
  HOLTest`assertEq[
    constType["="], tyFun[alpha, tyFun[alpha, boolTy]],
    "'=' generic type"
  ];
  eq = mkConst["=", tyFun[boolTy, tyFun[boolTy, boolTy]]];
  HOLTest`assertEq[
    eq, const["=", tyFun[boolTy, tyFun[boolTy, boolTy]]],
    "'=' at bool instance"
  ];
  HOLTest`assertEq[
    mkConst["=", tyFun[beta, tyFun[beta, boolTy]]],
    const["=", tyFun[beta, tyFun[beta, boolTy]]],
    "'=' at β instance (still polymorphic)"
  ];
  HOLTest`assertThrows[
    mkConst["nope", boolTy],
    "term", "unknown constant"
  ];
  HOLTest`assertThrows[
    mkConst["=", boolTy],
    "term", "type not an instance"
  ];
  HOLTest`assertThrows[
    mkConst["=", tyFun[alpha, tyFun[boolTy, boolTy]]],
    "term", "inconsistent tyvar binding"
  ];
]];

HOLTest`runTests["terms: mkComb", Module[{alpha, xt, ft, x, f, app},
  alpha = mkVarType["a"];
  xt = mkVar["x", alpha];
  ft = mkVar["f", tyFun[alpha, boolTy]];
  app = mkComb[ft, xt];
  HOLTest`assertEq[app, comb[ft, xt], "mkComb basic"];
  HOLTest`assertEq[typeOf[app], boolTy, "mkComb result type"];
  HOLTest`assertThrows[mkComb[xt, xt], "term", "non-fun operator"];
  HOLTest`assertThrows[
    mkComb[ft, mkVar["y", boolTy]],
    "term", "arg type mismatch"
  ];
]];

HOLTest`runTests["terms: mkAbs canonicalization", Module[{alpha, beta, x, y, idα, t2, expected2},
  alpha = mkVarType["a"];
  beta = mkVarType["b"];
  x = mkVar["x", alpha];
  idα = mkAbs[x, x];
  HOLTest`assertEq[
    idα, abs[var["_b0", alpha], var["_b0", alpha], "x"],
    "λx:α.x canonicalizes both slots"
  ];
  HOLTest`assertEq[
    destAbs[idα], {var["_b0", alpha], var["_b0", alpha], "x"},
    "destAbs returns all three slots"
  ];
  y = mkVar["y", beta];
  t2 = mkAbs[x, mkAbs[y, x]];
  expected2 = abs[
    var["_b0", alpha],
    abs[var["_b0", beta], var["_b1", alpha], "y"],
    "x"
  ];
  HOLTest`assertEq[t2, expected2, "λx.λy.x uses _b1 for outer reference"];
  HOLTest`assertThrows[
    mkAbs[var["_b0", alpha], x],
    "term", "reserved binder name rejected"
  ];
  HOLTest`assertThrows[
    mkAbs[boolTy, x],
    "term", "non-var binder rejected"
  ];
]];

HOLTest`runTests["terms: destructors and predicates", Module[{alpha, x, c, f, a, l},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  c = mkConst["=", tyFun[alpha, tyFun[alpha, boolTy]]];
  f = mkVar["f", tyFun[alpha, alpha]];
  a = mkComb[f, x];
  l = mkAbs[x, x];
  HOLTest`assertEq[destVar[x], {"x", alpha}, "destVar"];
  HOLTest`assertEq[destConst[c], {"=", tyFun[alpha, tyFun[alpha, boolTy]]}, "destConst"];
  HOLTest`assertEq[destComb[a], {f, x}, "destComb"];
  HOLTest`assertEq[destAbs[l][[3]], "x", "destAbs origin"];
  HOLTest`assertTrue[isVar[x], "isVar var"];
  HOLTest`assertTrue[isConst[c], "isConst const"];
  HOLTest`assertTrue[isComb[a], "isComb comb"];
  HOLTest`assertTrue[isAbs[l], "isAbs abs"];
  HOLTest`assertEq[isVar[c], False, "isVar not var"];
  HOLTest`assertEq[isConst[x], False, "isConst not const"];
  HOLTest`assertThrows[destVar[c], "term", "destVar rejects const"];
  HOLTest`assertThrows[destConst[x], "term", "destConst rejects var"];
  HOLTest`assertThrows[destComb[x], "term", "destComb rejects var"];
  HOLTest`assertThrows[destAbs[x], "term", "destAbs rejects var"];
]];

HOLTest`runTests["terms: typeOf", Module[{alpha, x, f, idα},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  HOLTest`assertEq[typeOf[x], alpha, "typeOf var"];
  f = mkVar["f", tyFun[alpha, boolTy]];
  HOLTest`assertEq[typeOf[mkComb[f, x]], boolTy, "typeOf comb codomain"];
  idα = mkAbs[x, x];
  HOLTest`assertEq[typeOf[idα], tyFun[alpha, alpha], "typeOf λx.x"];
  HOLTest`assertEq[
    typeOf[mkAbs[x, mkAbs[mkVar["y", boolTy], x]]],
    tyFun[alpha, tyFun[boolTy, alpha]],
    "typeOf nested abs"
  ];
]];

HOLTest`runTests["terms: freesIn", Module[{alpha, beta, x, y, f, app, lam, lamXY},
  alpha = mkVarType["a"];
  beta = mkVarType["b"];
  x = mkVar["x", alpha];
  y = mkVar["y", beta];
  f = mkVar["f", tyFun[alpha, beta]];
  app = mkComb[f, x];
  HOLTest`assertEq[freesIn[x], {x}, "freesIn var"];
  HOLTest`assertEq[freesIn[mkConst["=", tyFun[alpha, tyFun[alpha, boolTy]]]], {},
    "freesIn const is empty"];
  HOLTest`assertEq[freesIn[app], Sort[{f, x}], "freesIn comb"];
  lam = mkAbs[x, x];
  HOLTest`assertEq[freesIn[lam], {}, "freesIn λx.x is closed"];
  lamXY = mkAbs[x, y];
  HOLTest`assertEq[freesIn[lamXY], {y}, "freesIn λx.y keeps y free"];
  HOLTest`assertEq[
    freesIn[mkAbs[x, mkComb[f, x]]],
    {f},
    "freesIn λx. f x leaves f free"
  ];
  HOLTest`assertEq[
    freesIn[mkAbs[x, mkAbs[y, mkComb[f, x]]]],
    {f},
    "freesIn λx.λy.f x leaves f free"
  ];
]];

HOLTest`runTests["terms: vsubst capture-avoidance", Module[{alpha, x, y, lamYx, subbed},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  y = mkVar["y", alpha];
  (* classical capture example: substitute y for x in (λy. x) *)
  lamYx = mkAbs[y, x];
  HOLTest`assertEq[
    lamYx,
    abs[var["_b0", alpha], x, "y"],
    "λy.x canonical form (x free inside)"
  ];
  subbed = vsubst[<|x -> y|>, lamYx];
  HOLTest`assertEq[
    subbed,
    abs[var["_b0", alpha], y, "y"],
    "substituted (bound var is _b0, origin 'y' is only a label)"
  ];
  HOLTest`assertEq[
    freesIn[subbed], {y},
    "result has y free — no capture by canonical form"
  ];
]];

HOLTest`runTests["terms: vsubst basics", Module[{alpha, x, y, f, app, r},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  y = mkVar["y", alpha];
  f = mkVar["f", tyFun[alpha, alpha]];
  app = mkComb[f, x];
  r = vsubst[<|x -> y|>, app];
  HOLTest`assertEq[r, mkComb[f, y], "simple subst in comb"];
  HOLTest`assertEq[vsubst[<||>, app], app, "empty theta is identity"];
  HOLTest`assertThrows[
    vsubst[<|x -> mkVar["z", boolTy]|>, x],
    "term", "type-mismatched entry rejected"
  ];
  HOLTest`assertThrows[
    vsubst[<|var["_b0", alpha] -> y|>, x],
    "term", "reserved LHS rejected"
  ];
]];

HOLTest`runTests["terms: instType", Module[{alpha, beta, x, lam, theta, result},
  alpha = mkVarType["a"];
  beta = mkVarType["b"];
  x = mkVar["x", alpha];
  lam = mkAbs[x, x];
  theta = <|alpha -> boolTy|>;
  result = instType[theta, lam];
  HOLTest`assertEq[
    result,
    abs[var["_b0", boolTy], var["_b0", boolTy], "x"],
    "instType on λx:α.x → λx:bool.x"
  ];
  HOLTest`assertEq[typeOf[result], tyFun[boolTy, boolTy], "type after inst"];
  HOLTest`assertEq[
    instType[{alpha -> beta}, x],
    var["x", beta],
    "instType accepts list of rules"
  ];
]];

HOLTest`runTests["terms: aconv", Module[{alpha, beta, x, y, u, v, t1, t2, t3, t4},
  alpha = mkVarType["a"];
  beta = mkVarType["b"];
  x = mkVar["x", alpha];
  y = mkVar["y", alpha];
  u = mkVar["u", alpha];
  v = mkVar["v", beta];
  t1 = mkAbs[x, x];
  t2 = mkAbs[y, y];
  HOLTest`assertTrue[aconv[t1, t2], "λx.x ≈ λy.y"];
  HOLTest`assertEq[t1 === t2, False, "=== distinguishes origin"];
  t3 = mkAbs[x, mkAbs[mkVar["z", beta], x]];
  t4 = mkAbs[u, mkAbs[v, u]];
  HOLTest`assertTrue[aconv[t3, t4], "λx.λz.x ≈ λu.λv.u"];
  HOLTest`assertEq[
    aconv[mkAbs[x, x], mkAbs[x, y]], False,
    "λx.x not aconv λx.y"
  ];
  HOLTest`assertEq[
    aconv[mkVar["a", alpha], mkVar["b", alpha]], False,
    "distinct free vars are not aconv"
  ];
]];

HOLTest`runTests["terms: mkEq", Module[{alpha, x, y, eq},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  y = mkVar["y", alpha];
  eq = mkEq[x, y];
  HOLTest`assertEq[typeOf[eq], boolTy, "mkEq yields bool"];
  HOLTest`assertEq[
    destComb[eq][[2]], y,
    "mkEq rhs"
  ];
  HOLTest`assertEq[
    destComb[destComb[eq][[1]]][[2]], x,
    "mkEq lhs"
  ];
  HOLTest`assertThrows[
    mkEq[x, mkVar["z", boolTy]], "term", "mkEq type mismatch"
  ];
]];

HOLTest`runTests["terms: M2 acceptance", Module[{alpha, x, idα, theta, grounded, captureLam, captureResult},
  alpha = mkVarType["a"];
  x = mkVar["x", alpha];
  idα = mkAbs[x, x];
  HOLTest`assertEq[typeOf[idα], tyFun[alpha, alpha], "typeOf λx:α.x is α→α"];
  HOLTest`assertTrue[
    aconv[idα, mkAbs[mkVar["q", alpha], mkVar["q", alpha]]],
    "λx.x ≈ λq.q"
  ];
  captureLam = mkAbs[mkVar["y", alpha], x];
  captureResult = vsubst[<|x -> mkVar["y", alpha]|>, captureLam];
  HOLTest`assertEq[
    freesIn[captureResult], {mkVar["y", alpha]},
    "acceptance: substitute y for x in λy.x; y remains free (no capture)"
  ];
]];
