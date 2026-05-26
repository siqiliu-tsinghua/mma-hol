(* ::Package:: *)

(* M7-δ auto/Arith.wl — Presburger linear arithmetic for ℕ.

   *Session 1 status*: scaffold only. We lay down the internal AST
   (linear terms as Association-backed `<const, vars>` records) and
   the bidirectional HOL ↔ AST conversions. Subsequent sessions add
   atom/formula AST + NNF + the Cooper quantifier-elimination engine
   + HOL proof reconstruction.

   Decision-procedure design (target): for closed Presburger formulas
   over ℕ (built from +, *literal, SUC, ≤, =, <, ¬, ∧, ∨, ∀, ∃),
   we run Cooper's algorithm to reduce to a ground propositional
   instance, evaluate, and reconstruct the equivalence chain
   ⊢ formula = T (or F) in HOL. The "oracle" is Cooper running
   purely in Wolfram; the verifier replays each rewrite via kernel
   rules. This file currently exposes only the AST layer.

   Trust boundary: every HOL theorem produced (once Cooper is wired
   in) flows through the 10 primitive rules. The AST layer is
   untrusted scaffolding — a bug here can at worst leave a true
   theorem unproved.

   Term language (linear over ℕ):
     – `0`, SUC-stacked literals (e.g. SUC (SUC 0) for the literal 2)
     – free variables `var[name, num]`
     – `m + n` (commutative, associative)
     – `c * x` where exactly one side is a numeric literal
       (variable × variable is non-linear and rejected)

   Canonical form emitted by buildLin:
     c_0 + c_1 * x_1 + … + c_k * x_k
   with variables in lexicographic order, no zero coefficients, and
   the bare numeric `0` if the term is the zero linear form.
*)

BeginPackage["HOL`Auto`Arith`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`",
  "HOL`Stdlib`Num`"
}];

arithProve::usage =
  "arithProve[goalTm] — Presburger ℕ decision procedure. " <>
  "*Skeleton*: in the current session this is a stub that always " <>
  "throws holError tagged \"arith-stub\". The full implementation " <>
  "will close ground Presburger formulas via Cooper QE and kernel-" <>
  "level certificate replay.";

ARITH::usage =
  "ARITH[][goal] — tactic stub for arithProve. Currently fails on " <>
  "every goal — sits here to reserve the public API for the eventual " <>
  "decision procedure.";

Begin["`Private`"];

numTy = mkType["num", {}];

(* ============================================================ *)
(* Linear term AST                                              *)
(*                                                              *)
(* Representation: linTerm[const, varAssoc] with:                *)
(*   const     ∈ ℤ (Wolfram Integer). For pure-ℕ Presburger      *)
(*               we keep const ≥ 0 on the way in; signed values  *)
(*               appear once the Cooper engine starts moving     *)
(*               terms across ≤ / =.                              *)
(*   varAssoc  : Association[varName_String → coef_Integer].      *)
(*               Zero coefficients are filtered out at every     *)
(*               smart constructor, so Keys[varAssoc] are exactly *)
(*               the variables that actually appear.              *)
(*                                                              *)
(* All construction goes through the smart constructors below.   *)
(* ============================================================ *)

filterZeros[a_Association] := KeySelect[a, a[#] =!= 0 &];

linZero[] := linTerm[0, Association[]];

linConst[c_Integer] := linTerm[c, Association[]];

linVar[name_String] := linTerm[0, Association[name -> 1]];

linAdd[linTerm[c1_, v1_], linTerm[c2_, v2_]] :=
  linTerm[c1 + c2, filterZeros[Merge[{v1, v2}, Total]]];

linScale[k_Integer, linTerm[c_, vs_]] :=
  If[k === 0,
    linZero[],
    linTerm[k * c, filterZeros[
      Association[KeyValueMap[#1 -> k * #2 &, vs]]]]];

linNeg[lt_] := linScale[-1, lt];

linSub[a_, b_] := linAdd[a, linNeg[b]];

(* Predicate: linTerm carries no variables (i.e. a bare Integer). *)
linIsConst[linTerm[_, vs_Association]] := Length[vs] === 0;

linConstValue[linTerm[c_, _Association]] := c;

(* ============================================================ *)
(* HOL ℕ numeric literal ↔ Integer                              *)
(*                                                              *)
(* A literal is 0 or SUC^k applied to 0. parseLitNum walks down  *)
(* the SUC stack; buildLitNum builds it back up.                  *)
(* ============================================================ *)

litNumQ[const["0", _]] := True;
litNumQ[comb[const["SUC", _], n_]] := litNumQ[n];
litNumQ[_] := False;

parseLitNum[const["0", _]] := 0;
parseLitNum[comb[const["SUC", _], n_]] := 1 + parseLitNum[n];

buildLitNum[0] := zeroConst[];
buildLitNum[n_Integer /; n > 0] := mkComb[sucConst[], buildLitNum[n - 1]];

(* ============================================================ *)
(* parseLin: HOL ℕ term → linTerm                                *)
(*                                                              *)
(* Recursive descent over the recognized arithmetic spine. Any   *)
(* form we cannot map (e.g. product of two variables, division,  *)
(* an unknown constant) throws holError so callers can fall      *)
(* back to a more general tactic. The error tag is "arith-       *)
(* parse" with the offending sub-term in the payload.            *)
(* ============================================================ *)

parseLin[t_] := parseLinAux[t];

parseLinAux[t_const /; litNumQ[t]] := linConst[parseLitNum[t]];

parseLinAux[t_comb /; litNumQ[t]] := linConst[parseLitNum[t]];

parseLinAux[var[name_String, ty_]] :=
  If[ty === numTy,
    linVar[name],
    HOL`Error`holError["arith-parse",
      "linear-term variable must have type num",
      <|"name" -> name, "type" -> ty|>]];

parseLinAux[comb[comb[const["+", _], a_], b_]] :=
  linAdd[parseLinAux[a], parseLinAux[b]];

parseLinAux[comb[comb[const["*", _], a_], b_]] :=
  Module[{aLin, bLin},
    aLin = parseLinAux[a];
    bLin = parseLinAux[b];
    Which[
      linIsConst[aLin], linScale[linConstValue[aLin], bLin],
      linIsConst[bLin], linScale[linConstValue[bLin], aLin],
      True, HOL`Error`holError["arith-parse",
        "non-linear: product of two non-constant terms",
        <|"left" -> a, "right" -> b|>]
    ]
  ];

parseLinAux[t_] :=
  HOL`Error`holError["arith-parse",
    "term not recognized as a linear ℕ expression",
    <|"got" -> t|>];

(* ============================================================ *)
(* buildLin: linTerm → HOL ℕ term (canonical form)              *)
(*                                                              *)
(* Variables are placed in lex-sorted order, each as either      *)
(*   x_i           (coef = 1)                                    *)
(*   c_i * x_i     (coef > 1)                                    *)
(* The constant slot is prepended only when nonzero, except for  *)
(* the all-zero term which renders as the bare numeral `0`.       *)
(* ============================================================ *)

buildLin[lt : linTerm[c_, vs_]] :=
  Module[{names, varParts, mkVarPart, summands},
    names = Sort[Keys[vs]];

    mkVarPart[name_] :=
      With[{coef = vs[name]},
        If[coef === 1,
          var[name, numTy],
          mkComb[mkComb[timesConst[], buildLitNum[coef]],
                 var[name, numTy]]]];

    varParts = mkVarPart /@ names;

    summands = Which[
      c =!= 0,            Prepend[varParts, buildLitNum[c]],
      varParts === {},    {zeroConst[]},
      True,               varParts];

    (* Right-associate `+`: 2 + (x + (3·y)). Iterate the accumulator *)
    (* on the right side of each mkPlus.                              *)
    Fold[
      mkComb[mkComb[plusConst[], #2], #1] &,
      Last[summands],
      Reverse[Most[summands]]
    ]
  ];

(* ============================================================ *)
(* Public stubs                                                  *)
(* ============================================================ *)

arithProve[goalTm_] :=
  HOL`Error`holError["arith-stub",
    "Cooper QE not yet implemented — call from a future session",
    <|"goal" -> goalTm|>];

ARITH[][goal_] :=
  HOL`Error`holError["arith-stub",
    "ARITH tactic not yet implemented",
    <|"goal" -> goal|>];

End[];
EndPackage[];
