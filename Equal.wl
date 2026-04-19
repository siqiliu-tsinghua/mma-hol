(* ::Package:: *)

BeginPackage["HOL`Equal`", {"HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`"}];

SYM::usage      = "SYM[th] — from ⊢ a = b, derive ⊢ b = a.";
APTERM::usage   = "APTERM[f, th] — from ⊢ x = y and term f, derive ⊢ f x = f y.";
APTHM::usage    = "APTHM[th, x] — from ⊢ f = g and term x, derive ⊢ f x = g x.";
BETACONV::usage = "BETACONV[(λx. body) arg] — β-reduces any redex, not just the trivial case BETA accepts.";

Begin["`Private`"];

destEqConcl[th_] :=
  Module[{c},
    c = concl[th];
    If[! MatchQ[c, comb[comb[const["=", _], _], _]],
      HOL`Error`holError["rule", "Equal: conclusion is not an equation",
        <|"concl" -> c|>]];
    {c[[1, 2]], c[[2]]}
  ];

HOL`Equal`SYM[th_] :=
  Module[{a, b, aTy, eqC, step1, step2},
    {a, b} = destEqConcl[th];
    aTy = typeOf[a];
    eqC = mkConst["=", tyFun[aTy, tyFun[aTy, boolTy]]];
    step1 = MKCOMB[REFL[eqC], th];
    step2 = MKCOMB[step1, REFL[a]];
    EQMP[step2, REFL[a]]
  ];

HOL`Equal`APTERM[f_, th_] := MKCOMB[REFL[f], th];

HOL`Equal`APTHM[th_, x_] := MKCOMB[th, REFL[x]];

reservedQ[n_String] := StringMatchQ[n, "_b" ~~ DigitCharacter ..];

pickFresh[preferred_String, forbidden_List] :=
  Module[{i, candidate},
    If[! reservedQ[preferred] && ! MemberQ[forbidden, preferred],
      Return[preferred]];
    i = 0;
    candidate = "z";
    While[reservedQ[candidate] || MemberQ[forbidden, candidate],
      i++;
      candidate = "z" <> ToString[i]
    ];
    candidate
  ];

HOL`Equal`BETACONV[redex : comb[abs[var["_b0", bty_], body_, origin_String], arg_]] :=
  Module[{argTy, forbiddenNames, name, v, th0},
    argTy = typeOf[arg];
    If[argTy =!= bty,
      HOL`Error`holError["rule", "BETACONV: argument type does not match binder",
        <|"binderType" -> bty, "argType" -> argTy|>]];
    forbiddenNames = Map[First, Join[freesIn[body], freesIn[arg]]];
    name = pickFresh[origin, forbiddenNames];
    v = mkVar[name, bty];
    th0 = BETA[comb[abs[var["_b0", bty], body, name], v]];
    INST[{v -> arg}, th0]
  ];
HOL`Equal`BETACONV[other_] :=
  HOL`Error`holError["rule", "BETACONV: not a β-redex", <|"got" -> other|>];

End[];
EndPackage[];
