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
(* Atom + Formula AST                                            *)
(*                                                              *)
(* Atoms over ℕ are surface-form comparisons of two linear        *)
(* terms (or divisibility of a linear term by an integer):         *)
(*                                                              *)
(*   aAtomEq[lt1, lt2]       — lt1 = lt2                          *)
(*   aAtomLeq[lt1, lt2]      — lt1 ≤ lt2                          *)
(*   aAtomLt[lt1, lt2]       — lt1 < lt2                          *)
(*   aAtomDivides[c, lt]     — c | lt, c a positive Integer       *)
(*                                                              *)
(* Formulas are the standard NNF tree extended with implication,  *)
(* iff, and the bool constants. nnfForm rewrites every            *)
(* aFormImp / aFormIff / double-negation / De-Morgan junction so   *)
(* that negation appears only at the atom layer.                  *)
(* ============================================================ *)

(* Binder names: we open ∀/∃ by replacing the bvar with a fresh    *)
(* free var. The fresh name is derived from the binder origin and  *)
(* the set of forbidden names (currently-bound + free in the body  *)
(* + the existing forbidden list).                                  *)

freshArithName[base_String, forbidden_List] :=
  Module[{i = 0, cand = base},
    While[MemberQ[forbidden, cand],
      i++; cand = base <> ToString[i]];
    cand
  ];

(* ===== parseAtom: HOL bool-atom → aAtom ===== *)

(* Recognize SUC chain as a numeric literal in literal-coef       *)
(* contexts for aAtomDivides. *)
parseAtom[t_] :=
  Which[
    MatchQ[t, comb[comb[const["=", _], _], _]] && (
      typeOf[t[[1, 2]]] === numTy),
      aAtomEq[parseLin[t[[1, 2]]], parseLin[t[[2]]]],

    MatchQ[t, comb[comb[const["≤", _], _], _]],
      aAtomLeq[parseLin[t[[1, 2]]], parseLin[t[[2]]]],

    MatchQ[t, comb[comb[const["<", _], _], _]],
      aAtomLt[parseLin[t[[1, 2]]], parseLin[t[[2]]]],

    MatchQ[t, comb[comb[const["divides", _], _], _]] &&
        litNumQ[t[[1, 2]]],
      aAtomDivides[parseLitNum[t[[1, 2]]], parseLin[t[[2]]]],

    True,
      HOL`Error`holError["arith-parse",
        "term not recognized as a Presburger atom",
        <|"got" -> t|>]
  ];

(* ===== parseForm: HOL bool formula → aForm ===== *)

(* `forbidden` carries the set of variable names already used by  *)
(* enclosing binders so a fresh peel name does not collide.        *)

parseForm[t_] := parseFormCtx[t, {}];

parseFormCtx[t_, forbidden_List] :=
  Which[
    MatchQ[t, const["T", _]], aFormTrue,
    MatchQ[t, const["F", _]], aFormFalse,

    MatchQ[t, comb[const["¬", _], _]],
      aFormNot[parseFormCtx[t[[2]], forbidden]],

    MatchQ[t, comb[comb[const["∧", _], _], _]],
      aFormAnd[parseFormCtx[t[[1, 2]], forbidden],
               parseFormCtx[t[[2]], forbidden]],

    MatchQ[t, comb[comb[const["∨", _], _], _]],
      aFormOr[parseFormCtx[t[[1, 2]], forbidden],
              parseFormCtx[t[[2]], forbidden]],

    MatchQ[t, comb[comb[const["⇒", _], _], _]],
      aFormImp[parseFormCtx[t[[1, 2]], forbidden],
               parseFormCtx[t[[2]], forbidden]],

    (* `=` on bool means iff. Distinguish by type of the LHS.      *)
    MatchQ[t, comb[comb[const["=", _], _], _]] &&
        typeOf[t[[1, 2]]] === boolTy,
      aFormIff[parseFormCtx[t[[1, 2]], forbidden],
               parseFormCtx[t[[2]], forbidden]],

    MatchQ[t, comb[const["∀", _],
        abs[bvar[0, ty_], _, _String]]] && t[[2, 1, 2]] === numTy,
      parseBinder["∀", t, forbidden],

    MatchQ[t, comb[const["∃", _],
        abs[bvar[0, ty_], _, _String]]] && t[[2, 1, 2]] === numTy,
      parseBinder["∃", t, forbidden],

    True,
      (* Fall through: treat as atom. *)
      aFormAtom[parseAtom[t]]
  ];

(* parseBinder: open the bvar, recurse into body, wrap as aForm-  *)
(* quantifier with the chosen variable name.                       *)
parseBinder[kind_String, comb[_, abs[bvar[0, _], body_, origin_]],
            forbidden_List] :=
  Module[{name, freeNames, opened, parsedBody, ctor},
    freeNames = Map[First, freesIn[body]];
    name = freshArithName[origin, Join[forbidden, freeNames]];
    opened = openBvar0[body, name];
    parsedBody = parseFormCtx[opened, Append[forbidden, name]];
    ctor = If[kind === "\[ForAll]", aFormForall, aFormExists];
    ctor[name, parsedBody]
  ];

(* openBvar0[body, varName]: replace every bvar[0, num] reference  *)
(* in `body` with `var[varName, num]`. Inner abs-bodies bump their *)
(* indices, so we have to walk depth-aware.                        *)
openBvar0[t_, name_String] := openBvarAt[t, 0, name];

openBvarAt[bvar[k_, ty_], k_, name_] /; ty === numTy :=
  var[name, numTy];
openBvarAt[t : bvar[_, _], _, _] := t;
openBvarAt[t : var[_, _], _, _] := t;
openBvarAt[t : const[_, _], _, _] := t;
openBvarAt[comb[f_, x_], k_, name_] :=
  comb[openBvarAt[f, k, name], openBvarAt[x, k, name]];
openBvarAt[abs[bv_, body_, origin_], k_, name_] :=
  abs[bv, openBvarAt[body, k + 1, name], origin];

(* ===== buildAtom: aAtom → HOL bool-atom ===== *)

buildAtom[aAtomEq[lt1_, lt2_]] :=
  mkEq[buildLin[lt1], buildLin[lt2]];

buildAtom[aAtomLeq[lt1_, lt2_]] :=
  mkComb[mkComb[HOL`Stdlib`Num`leqConst[], buildLin[lt1]],
         buildLin[lt2]];

buildAtom[aAtomLt[lt1_, lt2_]] :=
  mkComb[mkComb[HOL`Stdlib`Num`ltConst[], buildLin[lt1]],
         buildLin[lt2]];

buildAtom[aAtomDivides[c_Integer, lt_]] :=
  mkComb[mkComb[HOL`Stdlib`Num`dividesConst[], buildLitNum[c]],
         buildLin[lt]];

(* ===== buildForm: aForm → HOL bool formula ===== *)

trueTm[] := mkConst["T", boolTy];
falseTm[] := mkConst["F", boolTy];

andOp[]  := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
orOp[]   := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
impOp[]  := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notOp[]  := mkConst["¬", tyFun[boolTy, boolTy]];
forallOp[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
existsOp[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];

buildForm[aFormTrue]  := trueTm[];
buildForm[aFormFalse] := falseTm[];
buildForm[aFormAtom[atom_]] := buildAtom[atom];
buildForm[aFormNot[f_]] := mkComb[notOp[], buildForm[f]];
buildForm[aFormAnd[a_, b_]] :=
  mkComb[mkComb[andOp[], buildForm[a]], buildForm[b]];
buildForm[aFormOr[a_, b_]] :=
  mkComb[mkComb[orOp[], buildForm[a]], buildForm[b]];
buildForm[aFormImp[a_, b_]] :=
  mkComb[mkComb[impOp[], buildForm[a]], buildForm[b]];
buildForm[aFormIff[a_, b_]] :=
  mkEq[buildForm[a], buildForm[b]];
buildForm[aFormForall[name_String, body_]] :=
  mkComb[forallOp[numTy],
    mkAbs[mkVar[name, numTy], buildForm[body]]];
buildForm[aFormExists[name_String, body_]] :=
  mkComb[existsOp[numTy],
    mkAbs[mkVar[name, numTy], buildForm[body]]];

(* ============================================================ *)
(* nnfForm: push negation to the atom layer                      *)
(*                                                              *)
(* Algorithm only — no HOL theorem produced. The full QE engine  *)
(* will instead manufacture each rewrite as a HOL equivalence    *)
(* and chain them via TRANS.                                     *)
(* ============================================================ *)

nnfForm[aFormTrue]  := aFormTrue;
nnfForm[aFormFalse] := aFormFalse;
nnfForm[a : aFormAtom[_]] := a;

nnfForm[aFormAnd[a_, b_]] := aFormAnd[nnfForm[a], nnfForm[b]];
nnfForm[aFormOr[a_, b_]]  := aFormOr[nnfForm[a], nnfForm[b]];
nnfForm[aFormImp[a_, b_]] := aFormOr[nnfForm[aFormNot[a]], nnfForm[b]];
nnfForm[aFormIff[a_, b_]] :=
  aFormOr[
    aFormAnd[nnfForm[a], nnfForm[b]],
    aFormAnd[nnfForm[aFormNot[a]], nnfForm[aFormNot[b]]]];
nnfForm[aFormForall[n_, p_]] := aFormForall[n, nnfForm[p]];
nnfForm[aFormExists[n_, p_]] := aFormExists[n, nnfForm[p]];

(* Negation: push inwards. *)
nnfForm[aFormNot[aFormTrue]]  := aFormFalse;
nnfForm[aFormNot[aFormFalse]] := aFormTrue;
nnfForm[aFormNot[aFormAtom[atom_]]] := aFormNot[aFormAtom[atom]];
nnfForm[aFormNot[aFormNot[p_]]] := nnfForm[p];
nnfForm[aFormNot[aFormAnd[a_, b_]]] :=
  aFormOr[nnfForm[aFormNot[a]], nnfForm[aFormNot[b]]];
nnfForm[aFormNot[aFormOr[a_, b_]]] :=
  aFormAnd[nnfForm[aFormNot[a]], nnfForm[aFormNot[b]]];
nnfForm[aFormNot[aFormImp[a_, b_]]] :=
  aFormAnd[nnfForm[a], nnfForm[aFormNot[b]]];
nnfForm[aFormNot[aFormIff[a_, b_]]] :=
  aFormOr[
    aFormAnd[nnfForm[a], nnfForm[aFormNot[b]]],
    aFormAnd[nnfForm[aFormNot[a]], nnfForm[b]]];
nnfForm[aFormNot[aFormForall[n_, p_]]] :=
  aFormExists[n, nnfForm[aFormNot[p]]];
nnfForm[aFormNot[aFormExists[n_, p_]]] :=
  aFormForall[n, nnfForm[aFormNot[p]]];

(* Predicate: aForm is in NNF (negation appears only at the atom  *)
(* layer, no aFormImp / aFormIff anywhere). Useful as a test      *)
(* oracle for the round-trip nnfForm ∘ buildForm.                  *)

nnfFormQ[aFormTrue]  := True;
nnfFormQ[aFormFalse] := True;
nnfFormQ[aFormAtom[_]] := True;
nnfFormQ[aFormNot[aFormAtom[_]]] := True;
nnfFormQ[aFormAnd[a_, b_]] := nnfFormQ[a] && nnfFormQ[b];
nnfFormQ[aFormOr[a_, b_]]  := nnfFormQ[a] && nnfFormQ[b];
nnfFormQ[aFormForall[_, p_]] := nnfFormQ[p];
nnfFormQ[aFormExists[_, p_]] := nnfFormQ[p];
nnfFormQ[_] := False;

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
