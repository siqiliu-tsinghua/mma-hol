(* ::Package:: *)

BeginPackage["HOL`Bool`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
                           "HOL`Bootstrap`", "HOL`Equal`"}];

TRUTH::usage    = "TRUTH — ⊢ T, derived once from tDef + REFL.";
EQTINTRO::usage = "EQTINTRO[th] — from Γ ⊢ p, derive Γ ⊢ p = T.";
EQTELIM::usage  = "EQTELIM[th] — from Γ ⊢ p = T, derive Γ ⊢ p.";
GEN::usage      = "GEN[x, th] — from Γ ⊢ p with x not free in Γ, derive Γ ⊢ ∀x. p.";
SPEC::usage     = "SPEC[t, th] — from Γ ⊢ ∀(λx. p), derive Γ ⊢ p[t/x].";

Begin["`Private`"];

destEqTh[th_] :=
  Module[{c},
    c = concl[th];
    If[! MatchQ[c, comb[comb[const["=", _], _], _]],
      HOL`Error`holError["rule", "Bool: conclusion is not an equation",
        <|"concl" -> c|>]];
    {c[[1, 2]], c[[2]]}
  ];

rhsOfConcl[th_] := destEqTh[th][[2]];

Module[{x, body, sym},
  x = mkVar["x", boolTy];
  body = mkAbs[x, x];
  sym = SYM[tDef];
  HOL`Bool`TRUTH = EQMP[sym, REFL[body]];
];

HOL`Bool`EQTELIM[th_] := EQMP[SYM[th], HOL`Bool`TRUTH];

HOL`Bool`EQTINTRO[th_] := DEDUCTANTISYM[th, HOL`Bool`TRUTH];

HOL`Bool`GEN[x : var[_String, xTy_], th_] :=
  Module[{p, eqth, absth, fdefInst, lamTm, aptm, betaTh, unfoldEq},
    p = concl[th];
    eqth = HOL`Bool`EQTINTRO[th];
    absth = ABS[x, eqth];
    fdefInst = INSTTYPE[{tyVar["a"] -> xTy}, forallDef];
    lamTm = mkAbs[x, p];
    aptm = APTHM[fdefInst, lamTm];
    betaTh = BETACONV[rhsOfConcl[aptm]];
    unfoldEq = TRANS[aptm, betaTh];
    EQMP[SYM[unfoldEq], absth]
  ];
HOL`Bool`GEN[other_, _] :=
  HOL`Error`holError["rule", "GEN: first arg must be a non-reserved var",
    <|"got" -> other|>];

HOL`Bool`SPEC[t_, th_] :=
  Module[{c, lamTm, bv, xTy, fdefInst, aptm, betaTh, unfoldEq,
          step1, step2, leftBeta, rightBeta, chain},
    c = concl[th];
    If[! MatchQ[c, comb[const["∀", _], abs[var["_b0", _], _, _String]]],
      HOL`Error`holError["rule", "SPEC: expected ⊢ ∀(λx. p)",
        <|"concl" -> c|>]];
    lamTm = c[[2]];
    {bv, _, _} = destAbs[lamTm];
    xTy = typeOf[bv];
    If[typeOf[t] =!= xTy,
      HOL`Error`holError["rule", "SPEC: term type does not match binder",
        <|"binderType" -> xTy, "termType" -> typeOf[t]|>]];
    fdefInst = INSTTYPE[{tyVar["a"] -> xTy}, forallDef];
    aptm = APTHM[fdefInst, lamTm];
    betaTh = BETACONV[rhsOfConcl[aptm]];
    unfoldEq = TRANS[aptm, betaTh];
    step1 = EQMP[unfoldEq, th];
    step2 = APTHM[step1, t];
    leftBeta  = BETACONV[destEqTh[step2][[1]]];
    rightBeta = BETACONV[destEqTh[step2][[2]]];
    chain = TRANS[TRANS[SYM[leftBeta], step2], rightBeta];
    HOL`Bool`EQTELIM[chain]
  ];

End[];
EndPackage[];
