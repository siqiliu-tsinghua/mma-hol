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
  "HOL`Tactics`",
  "HOL`Auto`PropTaut`",
  "HOL`Auto`Simp`",
  "HOL`Stdlib`Num`"
}];

nnfConv::usage =
  "nnfConv[holForm] — NNF conversion over Presburger ℕ: returns " <>
  "⊢ holForm = nnfForm[holForm] via REWRCONV/DEPTHCONV through the 9 " <>
  "schemata (¬¬, De Morgan over ∧/∨, ⇒-elim, ¬⇒, ⇔-DNF, ¬⇔, ¬∀-num, " <>
  "¬∃-num). Iterates to fixpoint. Distinct from " <>
  "HOL`Auto`PropTaut`nnfThm which transforms theorems (Γ ⊢ P ↦ Γ ⊢ NNF P) " <>
  "rather than producing the equation.";

notExistsNumThm::usage =
  "notExistsNumThm — ⊢ ∀P. ¬(∃x:num. P x) = (∀x:num. ¬P x). " <>
  "Quantifier deMorgan (constructive direction). Used as a " <>
  "rewrite schema for nnfConv via Miller HO matching.";

notForallNumThm::usage =
  "notForallNumThm — ⊢ ∀P. ¬(∀x:num. P x) = (∃x:num. ¬P x). " <>
  "Quantifier deMorgan (classical direction; forward uses CCONTR). " <>
  "Used as a rewrite schema for nnfConv via Miller HO matching.";

existsEqThm::usage =
  "existsEqThm — ⊢ ∀a:num. (∃x:num. x = a) = T. Trivial ∃-witness: x = a. " <>
  "First Cooper-instance theorem.";

existsLeqUbThm::usage =
  "existsLeqUbThm — ⊢ ∀a:num. (∃x:num. x ≤ a) = T. Witness via x = 0 + leqZero.";

existsLowerBoundThm::usage =
  "existsLowerBoundThm — ⊢ ∀a:num. (∃x:num. a ≤ x) = T. Witness via x = a + leqRefl.";

existsBoundedThm::usage =
  "existsBoundedThm — ⊢ ∀a b:num. (∃x:num. a ≤ x ∧ x ≤ b) = (a ≤ b). " <>
  "Cooper's interval-satisfiability theorem: an interval [a,b] is " <>
  "nonempty iff a ≤ b. Forward via CHOOSE+leqTrans, backward via " <>
  "EXISTS at a + leqRefl.";

arithProve::usage =
  "arithProve[goalTm] — linear ℕ arithmetic prover. ∃x:num. body " <>
  "goals close via witness search + ground verification; ∀x:num. " <>
  "H₁⇒…⇒Hₘ⇒C goals (C and each Hⱼ a ≤/< atom) close via a Farkas " <>
  "refutation (unit-subset certificate + kernel verifier) under " <>
  "CCONTR/DISCH/GEN. Linear only; non-unit multipliers and " <>
  "coefficient-merge are not yet supported (fall through to a " <>
  "tagged arith-farkas / arith-norm-merge error).";

linNormConv::usage =
  "linNormConv[t] — proof-producing linear normalizer over ℕ: " <>
  "returns ⊢ t = buildLin[parseLin[t]], the canonical constant-first, " <>
  "sorted-variable, right-associated form. Covers 0/SUC/+/vars and " <>
  "literal·literal products; throws arith-norm-merge on coefficient " <>
  "merge and arith-norm on unsupported shapes. The Farkas verifier's " <>
  "core building block.";

ARITH::usage =
  "ARITH[][goal] — tactic wrapper for arithProve: proves the goal's " <>
  "conclusion (a linear ℕ ∀/∃ statement) and closes the goal. Use " <>
  "via prove[goal, ARITH[]].";

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

parseLinAux[comb[const["SUC", _], u_] /; ! litNumQ[u]] :=
  linAdd[parseLinAux[u], linConst[1]];

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
(* Quantifier deMorgan theorems (at numTy)                       *)
(*                                                              *)
(*   notExistsNumThm : ⊢ ∀P. ¬(∃x:num. P x) = (∀x:num. ¬P x)     *)
(*   notForallNumThm : ⊢ ∀P. ¬(∀x:num. P x) = (∃x:num. ¬P x)     *)
(*                                                              *)
(* The ∃-version is constructive; the ∀-version needs CCONTR     *)
(* (intuitionistically not provable). Both are then used by      *)
(* nnfConv as Miller-pattern rewrites so that nnfForm-style       *)
(* normalization handles full Presburger formulas.                *)
(* ============================================================ *)

notTm[p_] := mkComb[notOp[], p];

notExistsNumThm =
  Module[{pV, xV, pAtX, existsPx, notExistsPx, forallNotPx,
          forwardDir, backwardDir, eqThm},
    pV = mkVar["P", tyFun[numTy, boolTy]];
    xV = mkVar["xQD", numTy];

    pAtX = mkComb[pV, xV];
    existsPx = mkComb[existsOp[numTy], mkAbs[xV, pAtX]];
    notExistsPx = notTm[existsPx];
    forallNotPx = mkComb[forallOp[numTy], mkAbs[xV, notTm[pAtX]]];

    (* Forward: (¬∃x. P x) ⊢ ∀x. ¬P x. *)
    forwardDir = Module[{notExHyp, pxHyp, existsFromX, contradInner,
                         notPxDerived, gen},
      notExHyp = ASSUME[notExistsPx];
      pxHyp = ASSUME[pAtX];
      existsFromX = HOL`Bool`EXISTS[existsPx, xV, pxHyp];
      (* (P x) ⊢ ∃x. P x *)
      contradInner = HOL`Bool`MP[
        HOL`Bool`NOTELIM[notExHyp], existsFromX];
      (* (¬∃x. P x, P x) ⊢ F *)
      notPxDerived = HOL`Bool`NOTINTRO[
        HOL`Bool`DISCH[pAtX, contradInner]];
      (* (¬∃x. P x) ⊢ ¬P x *)
      gen = HOL`Bool`GEN[xV, notPxDerived];
      (* (¬∃x. P x) ⊢ ∀x. ¬P x *)
      gen
    ];

    (* Backward: (∀x. ¬P x) ⊢ ¬(∃x. P x). *)
    backwardDir = Module[{allNotHyp, exHyp, pxChosen, notPxSpec,
                         contradInner, chosenContrad, notExFinal},
      allNotHyp = ASSUME[forallNotPx];
      exHyp = ASSUME[existsPx];
      pxChosen = ASSUME[pAtX];
      notPxSpec = HOL`Bool`SPEC[xV, allNotHyp];
      contradInner = HOL`Bool`MP[
        HOL`Bool`NOTELIM[notPxSpec], pxChosen];
      (* (∀x. ¬P x, P x) ⊢ F *)
      chosenContrad = HOL`Bool`CHOOSE[xV, exHyp, contradInner];
      (* (∀x. ¬P x, ∃x. P x) ⊢ F *)
      notExFinal = HOL`Bool`NOTINTRO[
        HOL`Bool`DISCH[existsPx, chosenContrad]];
      (* (∀x. ¬P x) ⊢ ¬(∃x. P x) *)
      notExFinal
    ];

    eqThm = HOL`Kernel`DEDUCTANTISYM[backwardDir, forwardDir];
    (* ⊢ ¬(∃x. P x) = ∀x. ¬P x *)
    HOL`Bool`GEN[pV, eqThm]
  ];

notForallNumThm =
  Module[{pV, xV, pAtX, forallPx, notForallPx, notPxTm, existsNotPx,
          forwardDir, backwardDir, eqThm},
    pV = mkVar["P", tyFun[numTy, boolTy]];
    xV = mkVar["xQD", numTy];

    pAtX = mkComb[pV, xV];
    forallPx = mkComb[forallOp[numTy], mkAbs[xV, pAtX]];
    notForallPx = notTm[forallPx];
    notPxTm = notTm[pAtX];
    existsNotPx = mkComb[existsOp[numTy], mkAbs[xV, notPxTm]];

    (* Forward: (¬∀x. P x) ⊢ ∃x. ¬P x. Classical reasoning. *)
    forwardDir = Module[{notForHyp, notExNotHyp, notPxHyp, existsFromX,
                         contradInner, pxFromCCONTR, forallPxDerived,
                         contradOuter, existsNotFromCCONTR},
      notForHyp = ASSUME[notForallPx];
      notExNotHyp = ASSUME[notTm[existsNotPx]];
      notPxHyp = ASSUME[notPxTm];
      (* Goal: derive F from notForHyp + notExNotHyp. *)
      existsFromX = HOL`Bool`EXISTS[existsNotPx, xV, notPxHyp];
      (* (¬P x) ⊢ ∃x. ¬P x *)
      contradInner = HOL`Bool`MP[
        HOL`Bool`NOTELIM[notExNotHyp], existsFromX];
      (* (¬∃x. ¬P x, ¬P x) ⊢ F *)
      pxFromCCONTR = HOL`Bool`CCONTR[pAtX, contradInner];
      (* (¬∃x. ¬P x) ⊢ P x  (CCONTR removes ¬P x from hyps) *)
      forallPxDerived = HOL`Bool`GEN[xV, pxFromCCONTR];
      (* (¬∃x. ¬P x) ⊢ ∀x. P x *)
      contradOuter = HOL`Bool`MP[
        HOL`Bool`NOTELIM[notForHyp], forallPxDerived];
      (* (¬∀x. P x, ¬∃x. ¬P x) ⊢ F *)
      existsNotFromCCONTR = HOL`Bool`CCONTR[existsNotPx, contradOuter];
      (* (¬∀x. P x) ⊢ ∃x. ¬P x *)
      existsNotFromCCONTR
    ];

    (* Backward: (∃x. ¬P x) ⊢ ¬(∀x. P x). *)
    backwardDir = Module[{exNotHyp, forallHyp, notPxChosen, pxSpec,
                         contradInner, chosenContrad, notForFinal},
      exNotHyp = ASSUME[existsNotPx];
      forallHyp = ASSUME[forallPx];
      notPxChosen = ASSUME[notPxTm];
      pxSpec = HOL`Bool`SPEC[xV, forallHyp];
      contradInner = HOL`Bool`MP[
        HOL`Bool`NOTELIM[notPxChosen], pxSpec];
      (* (∀x. P x, ¬P x) ⊢ F *)
      chosenContrad = HOL`Bool`CHOOSE[xV, exNotHyp, contradInner];
      (* (∃x. ¬P x, ∀x. P x) ⊢ F *)
      notForFinal = HOL`Bool`NOTINTRO[
        HOL`Bool`DISCH[forallPx, chosenContrad]];
      (* (∃x. ¬P x) ⊢ ¬(∀x. P x) *)
      notForFinal
    ];

    eqThm = HOL`Kernel`DEDUCTANTISYM[backwardDir, forwardDir];
    (* ⊢ ¬(∀x. P x) = ∃x. ¬P x *)
    HOL`Bool`GEN[pV, eqThm]
  ];

(* ============================================================ *)
(* Cooper-instance theorems — first stage of the Cooper main     *)
(* theorem. Each fixes a specific atom shape and proves the       *)
(* ∃-equivalence directly via kernel rules.                       *)
(* ============================================================ *)

existsEqThm =
  Module[{aV, xV, body, existsTm, witnessRefl, existsProved, eqTThm},
    aV = mkVar["a", numTy];
    xV = mkVar["xEx", numTy];
    body = mkEq[xV, aV];
    existsTm = mkComb[existsOp[numTy], mkAbs[xV, body]];
    witnessRefl = HOL`Kernel`REFL[aV];
    (* ⊢ a = a *)
    existsProved = HOL`Bool`EXISTS[existsTm, aV, witnessRefl];
    (* ⊢ ∃x. x = a *)
    eqTThm = HOL`Bool`EQTINTRO[existsProved];
    HOL`Bool`GEN[aV, eqTThm]
  ];

existsLeqUbThm =
  Module[{aV, xV, zeroN, body, existsTm, leqZeroA, existsProved, eqTThm},
    aV = mkVar["a", numTy];
    xV = mkVar["xEx", numTy];
    zeroN = HOL`Stdlib`Num`zeroConst[];
    body = mkComb[mkComb[HOL`Stdlib`Num`leqConst[], xV], aV];
    existsTm = mkComb[existsOp[numTy], mkAbs[xV, body]];
    leqZeroA = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`leqZeroThm];
    (* ⊢ 0 ≤ a *)
    existsProved = HOL`Bool`EXISTS[existsTm, zeroN, leqZeroA];
    (* ⊢ ∃x. x ≤ a *)
    eqTThm = HOL`Bool`EQTINTRO[existsProved];
    HOL`Bool`GEN[aV, eqTThm]
  ];

existsLowerBoundThm =
  Module[{aV, xV, body, existsTm, leqReflA, existsProved, eqTThm},
    aV = mkVar["a", numTy];
    xV = mkVar["xEx", numTy];
    body = mkComb[mkComb[HOL`Stdlib`Num`leqConst[], aV], xV];
    existsTm = mkComb[existsOp[numTy], mkAbs[xV, body]];
    leqReflA = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`leqReflThm];
    (* ⊢ a ≤ a; body[x↦a] = a ≤ a matches *)
    existsProved = HOL`Bool`EXISTS[existsTm, aV, leqReflA];
    eqTThm = HOL`Bool`EQTINTRO[existsProved];
    HOL`Bool`GEN[aV, eqTThm]
  ];

existsBoundedThm =
  Module[{aV, bV, xV, leqOp, leqAX, leqXB, leqAB, conjBody, existsTm,
          forwardDir, backwardDir, eqThm},
    aV = mkVar["a", numTy];
    bV = mkVar["b", numTy];
    xV = mkVar["xEx", numTy];
    leqOp = HOL`Stdlib`Num`leqConst[];
    leqAX = mkComb[mkComb[leqOp, aV], xV];
    leqXB = mkComb[mkComb[leqOp, xV], bV];
    leqAB = mkComb[mkComb[leqOp, aV], bV];
    conjBody = mkComb[mkComb[andOp[], leqAX], leqXB];
    existsTm = mkComb[existsOp[numTy], mkAbs[xV, conjBody]];

    forwardDir = Module[{exHyp, conjHyp, aLeqX, xLeqB, transSpec,
                         step1, step2, chosenAB},
      exHyp = ASSUME[existsTm];
      conjHyp = ASSUME[conjBody];
      aLeqX = HOL`Bool`CONJUNCT1[conjHyp];
      xLeqB = HOL`Bool`CONJUNCT2[conjHyp];
      transSpec = HOL`Bool`SPEC[bV,
        HOL`Bool`SPEC[xV,
          HOL`Bool`SPEC[aV, HOL`Stdlib`Num`leqTransThm]]];
      (* ⊢ a ≤ x ⇒ x ≤ b ⇒ a ≤ b *)
      step1 = HOL`Bool`MP[transSpec, aLeqX];
      step2 = HOL`Bool`MP[step1, xLeqB];
      (* {conjBody} ⊢ a ≤ b *)
      chosenAB = HOL`Bool`CHOOSE[xV, exHyp, step2];
      (* {existsTm} ⊢ a ≤ b *)
      chosenAB
    ];

    backwardDir = Module[{abHyp, leqReflA, conjAtA, existsProved},
      abHyp = ASSUME[leqAB];
      leqReflA = HOL`Bool`SPEC[aV, HOL`Stdlib`Num`leqReflThm];
      (* ⊢ a ≤ a *)
      conjAtA = HOL`Bool`CONJ[leqReflA, abHyp];
      (* {a ≤ b} ⊢ a ≤ a ∧ a ≤ b — matches body[x↦a] *)
      existsProved = HOL`Bool`EXISTS[existsTm, aV, conjAtA];
      (* {a ≤ b} ⊢ ∃x. a ≤ x ∧ x ≤ b *)
      existsProved
    ];

    eqThm = HOL`Kernel`DEDUCTANTISYM[backwardDir, forwardDir];
    (* ⊢ (∃x. a ≤ x ∧ x ≤ b) = (a ≤ b) *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, eqThm]]
  ];

(* ============================================================ *)
(* nnfConv — propositional + quantifier NNF certificate          *)
(*                                                              *)
(* Given a HOL bool-typed term `t`, return ⊢ t = NNF(t) by        *)
(* repeated kernel-checked rewrites with the 7 propositional +    *)
(* 2 quantifier deMorgan schemata.                                *)
(* ============================================================ *)

(* The 7 propositional schemata — built lazily on first use so we *)
(* don't run propTaut at module load time. *)

$arithNnfSchemata = Null;

ensureNnfSchemata[] :=
  If[$arithNnfSchemata === Null,
    $arithNnfSchemata = buildNnfSchemata[]];

(* Local bool-term builders to keep the schema definitions terse. *)
ptBoolVar[name_String] := mkVar[name, boolTy];
ptNotTm[a_] := mkComb[notOp[], a];
ptAndTm[a_, b_] := mkComb[mkComb[andOp[], a], b];
ptOrTm[a_, b_]  := mkComb[mkComb[orOp[], a], b];
ptImpTm[a_, b_] := mkComb[mkComb[impOp[], a], b];

buildNnfSchemata[] :=
  Module[{p, q, pPred},
    p = ptBoolVar["pNNF"];
    q = ptBoolVar["qNNF"];
    pPred = mkVar["P", tyFun[numTy, boolTy]];
    {
      (* ¬¬p = p *)
      propTaut[mkEq[ptNotTm[ptNotTm[p]], p]],
      (* ¬(p ∧ q) = ¬p ∨ ¬q *)
      propTaut[mkEq[ptNotTm[ptAndTm[p, q]],
        ptOrTm[ptNotTm[p], ptNotTm[q]]]],
      (* ¬(p ∨ q) = ¬p ∧ ¬q *)
      propTaut[mkEq[ptNotTm[ptOrTm[p, q]],
        ptAndTm[ptNotTm[p], ptNotTm[q]]]],
      (* p ⇒ q = ¬p ∨ q *)
      propTaut[mkEq[ptImpTm[p, q],
        ptOrTm[ptNotTm[p], q]]],
      (* ¬(p ⇒ q) = p ∧ ¬q *)
      propTaut[mkEq[ptNotTm[ptImpTm[p, q]],
        ptAndTm[p, ptNotTm[q]]]],
      (* (p ⇔ q) = (p ∧ q) ∨ (¬p ∧ ¬q) — = at bool *)
      propTaut[mkEq[mkEq[p, q],
        ptOrTm[ptAndTm[p, q], ptAndTm[ptNotTm[p], ptNotTm[q]]]]],
      (* ¬(p ⇔ q) = (p ∧ ¬q) ∨ (¬p ∧ q) *)
      propTaut[mkEq[ptNotTm[mkEq[p, q]],
        ptOrTm[ptAndTm[p, ptNotTm[q]], ptAndTm[ptNotTm[p], q]]]],
      (* ¬(∀x:num. P x) = ∃x:num. ¬P x  — SPEC away the outer ∀P *)
      HOL`Bool`SPEC[pPred, notForallNumThm],
      (* ¬(∃x:num. P x) = ∀x:num. ¬P x *)
      HOL`Bool`SPEC[pPred, notExistsNumThm]
    }
  ];

(* ===== combine + fixpoint helpers ===== *)

combineConvsLocal[{c_}] := c;
combineConvsLocal[{c_, rest__}] :=
  HOL`Drule`ORELSEC[c, combineConvsLocal[{rest}]];

(* Apply `conv` to `t` repeatedly via TRANS until the RHS is       *)
(* stable (under aconv) or repeats. TRYCONV makes failure return    *)
(* REFL, so the loop terminates cleanly on the first non-productive *)
(* step.                                                           *)

(* Extract the RHS of an equation theorem without going through the *)
(* kernel-private destEq. concl[eqTh] = comb[comb[=, lhs], rhs];     *)
(* its [[2]] slot is the rhs.                                         *)
eqRhsOf[eqTh_] := concl[eqTh][[2]];

fixpointConvLocal[conv_, t_] :=
  Module[{cur, nextEq, rhs, newRhs, seen},
    cur = HOL`Drule`TRYCONV[conv][t];
    rhs = eqRhsOf[cur];
    seen = <|rhs -> True|>;
    While[True,
      nextEq = HOL`Drule`TRYCONV[conv][rhs];
      newRhs = eqRhsOf[nextEq];
      If[HOL`Terms`aconv[rhs, newRhs], Break[]];
      If[KeyExistsQ[seen, newRhs], Break[]];
      seen[newRhs] = True;
      cur = TRANS[cur, nextEq];
      rhs = newRhs
    ];
    cur
  ];

HOL`Auto`Arith`nnfConv[holForm_] :=
  Module[{conv},
    ensureNnfSchemata[];
    conv = HOL`Drule`DEPTHCONV[
      combineConvsLocal[
        Map[HOL`Drule`REWRCONV, $arithNnfSchemata]]];
    fixpointConvLocal[conv, holForm]
  ];

(* ============================================================ *)
(* Cooper QE — AST-level building blocks                         *)
(*                                                              *)
(* These functions operate on aForm/aAtom (AST), not on HOL      *)
(* terms. They prepare the data structures that the eventual     *)
(* HOL-proof Cooper engine (session 6+) will consume:            *)
(*                                                              *)
(*   normalizeAtomsForm[f]   : rewrite every aAtomEq/Leq/Lt[a,b] *)
(*                             to […, b]→0 form via linSub.       *)
(*   linCoefOf[lt, x]        : coefficient of x in a linTerm.    *)
(*   atomCoefOnX[atom, x]    : coefficient of x in atom's lt.    *)
(*   formAtomsInvolvingX[f, x] : flat list of atoms whose        *)
(*                              x-coefficient is nonzero, with    *)
(*                              their negation flag.              *)
(*   deltaOnX[f, x]          : LCM of divisibility moduli where  *)
(*                             x appears (default 1).             *)
(*   phiMinusInfOnX[f, x]    : AST with atoms involving x        *)
(*                             replaced by their (x → -∞) limits  *)
(*                             (T / F / divisibility kept).      *)
(*                                                              *)
(* All assume the input formula is already in NNF (so ¬ appears   *)
(* only at the atom layer) and has been run through                *)
(* normalizeAtomsForm so each non-divisibility atom is `lt op 0`.  *)
(* B-set extraction, the big-disjunction assembly, and the HOL    *)
(* certificates are queued for session 6+.                         *)
(* ============================================================ *)

normalizeAtom[aAtomEq[a_, b_]]  := aAtomEq[linSub[a, b], linZero[]];
normalizeAtom[aAtomLeq[a_, b_]] := aAtomLeq[linSub[a, b], linZero[]];
normalizeAtom[aAtomLt[a_, b_]]  := aAtomLt[linSub[a, b], linZero[]];
normalizeAtom[a : aAtomDivides[_, _]] := a;

normalizeAtomsForm[aFormTrue]  := aFormTrue;
normalizeAtomsForm[aFormFalse] := aFormFalse;
normalizeAtomsForm[aFormAtom[atom_]] := aFormAtom[normalizeAtom[atom]];
normalizeAtomsForm[aFormNot[f_]] := aFormNot[normalizeAtomsForm[f]];
normalizeAtomsForm[aFormAnd[a_, b_]] :=
  aFormAnd[normalizeAtomsForm[a], normalizeAtomsForm[b]];
normalizeAtomsForm[aFormOr[a_, b_]] :=
  aFormOr[normalizeAtomsForm[a], normalizeAtomsForm[b]];
normalizeAtomsForm[aFormImp[a_, b_]] :=
  aFormImp[normalizeAtomsForm[a], normalizeAtomsForm[b]];
normalizeAtomsForm[aFormIff[a_, b_]] :=
  aFormIff[normalizeAtomsForm[a], normalizeAtomsForm[b]];
normalizeAtomsForm[aFormForall[v_, body_]] :=
  aFormForall[v, normalizeAtomsForm[body]];
normalizeAtomsForm[aFormExists[v_, body_]] :=
  aFormExists[v, normalizeAtomsForm[body]];

(* ===== Coefficient extraction ===== *)

linCoefOf[linTerm[_, vs_Association], x_String] := Lookup[vs, x, 0];

atomCoefOnX[aAtomEq[lt_, _], x_String]      := linCoefOf[lt, x];
atomCoefOnX[aAtomLeq[lt_, _], x_String]     := linCoefOf[lt, x];
atomCoefOnX[aAtomLt[lt_, _], x_String]      := linCoefOf[lt, x];
atomCoefOnX[aAtomDivides[_, lt_], x_String] := linCoefOf[lt, x];

(* ===== Collect atoms involving x ===== *)

(* Returns a flat list of pairs {negated?, atom} where atom is the *)
(* underlying aAtom*, and negated? is True iff the atom appeared    *)
(* inside aFormNot (after NNF, negation lives only at atoms).       *)

collectAtoms[aFormAtom[atom_], negated_:False] := {{negated, atom}};
collectAtoms[aFormNot[aFormAtom[atom_]], negated_:False] :=
  {{Not[negated], atom}};
collectAtoms[aFormAnd[a_, b_], negated_:False] :=
  Join[collectAtoms[a, negated], collectAtoms[b, negated]];
collectAtoms[aFormOr[a_, b_], negated_:False] :=
  Join[collectAtoms[a, negated], collectAtoms[b, negated]];
collectAtoms[aFormForall[_, body_], negated_:False] :=
  collectAtoms[body, negated];
collectAtoms[aFormExists[_, body_], negated_:False] :=
  collectAtoms[body, negated];
collectAtoms[_, _:False] := {};

formAtomsInvolvingX[f_, x_String] :=
  Select[collectAtoms[f, False],
    atomCoefOnX[#[[2]], x] =!= 0 &];

(* ===== δ : LCM of divisibility moduli touching x ===== *)

deltaOnX[f_, x_String] :=
  Module[{divPairs, moduli},
    divPairs = Select[collectAtoms[f, False],
      MatchQ[#[[2]], aAtomDivides[_, _]] &&
        atomCoefOnX[#[[2]], x] =!= 0 &];
    moduli = Map[#[[2, 1]] &, divPairs];
    If[moduli === {}, 1, LCM @@ moduli]
  ];

(* ===== φ_{-∞} on x — replace x-atoms with their limits ===== *)

phiMinusInfAtom[atom_, x_String, negated_] :=
  Module[{coef = atomCoefOnX[atom, x]},
    If[coef === 0,
      (* Atom doesn't involve x; keep as-is. *)
      If[negated, aFormNot[aFormAtom[atom]], aFormAtom[atom]],
      Switch[Head[atom],
        aAtomEq,
          (* c·x + t = 0 has at most one solution; as x → -∞, false. *)
          If[negated, aFormTrue, aFormFalse],
        aAtomLeq,
          If[coef > 0, If[negated, aFormFalse, aFormTrue],
                       If[negated, aFormTrue, aFormFalse]],
        aAtomLt,
          If[coef > 0, If[negated, aFormFalse, aFormTrue],
                       If[negated, aFormTrue, aFormFalse]],
        aAtomDivides,
          (* Periodic in x; keep as-is (will be evaluated at x := j). *)
          If[negated, aFormNot[aFormAtom[atom]], aFormAtom[atom]],
        _,
          If[negated, aFormNot[aFormAtom[atom]], aFormAtom[atom]]
      ]
    ]
  ];

phiMinusInfOnX[aFormTrue, _]  := aFormTrue;
phiMinusInfOnX[aFormFalse, _] := aFormFalse;
phiMinusInfOnX[aFormAtom[atom_], x_String] :=
  phiMinusInfAtom[atom, x, False];
phiMinusInfOnX[aFormNot[aFormAtom[atom_]], x_String] :=
  phiMinusInfAtom[atom, x, True];
phiMinusInfOnX[aFormAnd[a_, b_], x_String] :=
  aFormAnd[phiMinusInfOnX[a, x], phiMinusInfOnX[b, x]];
phiMinusInfOnX[aFormOr[a_, b_], x_String] :=
  aFormOr[phiMinusInfOnX[a, x], phiMinusInfOnX[b, x]];
(* Quantifiers shouldn't appear in a QF Cooper body, but keep      *)
(* pass-through semantics for robustness.                          *)
phiMinusInfOnX[aFormForall[v_, body_], x_String] :=
  aFormForall[v, phiMinusInfOnX[body, x]];
phiMinusInfOnX[aFormExists[v_, body_], x_String] :=
  aFormExists[v, phiMinusInfOnX[body, x]];
phiMinusInfOnX[other_, _] := other;

(* ============================================================ *)
(* Substitution: replace a variable in a linTerm / atom / form    *)
(* by another linTerm.                                            *)
(*                                                              *)
(* Used for the Cooper QE plug-in step: φ[x ↦ b + j] and          *)
(* φ_{-∞}[x ↦ j]. AST-level only; no HOL theorem.                 *)
(* ============================================================ *)

substVarInLin[linTerm[c_, vs_Association], x_String, rep_] :=
  If[KeyExistsQ[vs, x],
    Module[{coef = vs[x], restVars, scaled},
      restVars = KeyDrop[vs, x];
      scaled = linScale[coef, rep];
      linAdd[linTerm[c, restVars], scaled]
    ],
    linTerm[c, vs]
  ];

substVarInAtom[aAtomEq[a_, b_], x_, rep_] :=
  aAtomEq[substVarInLin[a, x, rep], substVarInLin[b, x, rep]];
substVarInAtom[aAtomLeq[a_, b_], x_, rep_] :=
  aAtomLeq[substVarInLin[a, x, rep], substVarInLin[b, x, rep]];
substVarInAtom[aAtomLt[a_, b_], x_, rep_] :=
  aAtomLt[substVarInLin[a, x, rep], substVarInLin[b, x, rep]];
substVarInAtom[aAtomDivides[c_, lt_], x_, rep_] :=
  aAtomDivides[c, substVarInLin[lt, x, rep]];

substVarInForm[aFormTrue, _, _]  := aFormTrue;
substVarInForm[aFormFalse, _, _] := aFormFalse;
substVarInForm[aFormAtom[atom_], x_, rep_] :=
  aFormAtom[substVarInAtom[atom, x, rep]];
substVarInForm[aFormNot[f_], x_, rep_] :=
  aFormNot[substVarInForm[f, x, rep]];
substVarInForm[aFormAnd[a_, b_], x_, rep_] :=
  aFormAnd[substVarInForm[a, x, rep], substVarInForm[b, x, rep]];
substVarInForm[aFormOr[a_, b_], x_, rep_] :=
  aFormOr[substVarInForm[a, x, rep], substVarInForm[b, x, rep]];
substVarInForm[aFormImp[a_, b_], x_, rep_] :=
  aFormImp[substVarInForm[a, x, rep], substVarInForm[b, x, rep]];
substVarInForm[aFormIff[a_, b_], x_, rep_] :=
  aFormIff[substVarInForm[a, x, rep], substVarInForm[b, x, rep]];
(* Don't substitute through a binder of the same name (shadowing). *)
substVarInForm[aFormForall[v_, body_], x_, rep_] :=
  If[v === x, aFormForall[v, body],
     aFormForall[v, substVarInForm[body, x, rep]]];
substVarInForm[aFormExists[v_, body_], x_, rep_] :=
  If[v === x, aFormExists[v, body],
     aFormExists[v, substVarInForm[body, x, rep]]];

(* ============================================================ *)
(* B-set: left-bound witnesses                                    *)
(*                                                              *)
(* For ∃x. φ in NNF + normalized form, each atom involving x      *)
(* contributes (at most) one witness term b such that             *)
(*   ⋃_{j=1..δ} φ[x ↦ b + j]                                      *)
(* covers the cases where x is "just above" a lower bound.        *)
(*                                                              *)
(* We restrict to |coef-x| = 1 for now (Cooper's general          *)
(* algorithm normalizes higher coefficients via the multiply-     *)
(* through trick; that handling is deferred to a later session).  *)
(* Inputs with |coef-x| > 1 throw `arith-cooper`.                  *)
(*                                                              *)
(* Cases by atom shape (lt = c·x + t, op 0):                       *)
(*   Eq, c = +1   :  x = -t.   Witness  -t - 1.                    *)
(*   Eq, c = -1   :  x =  t.   Witness   t - 1.                    *)
(*   Leq, c = +1  :  x ≤ -t.   Upper bound — no witness.            *)
(*   Leq, c = -1  :  x ≥  t.   Witness  t - 1.                     *)
(*   Lt,  c = +1  :  x < -t.   Upper bound — no witness.            *)
(*   Lt,  c = -1  :  x >  t.   Witness   t.                         *)
(*                                                              *)
(* Negated (= lt op 0 flipped):                                    *)
(*   ¬Eq          :  x ≠ -t (or t). Two-sided; skipped for now.    *)
(*   ¬Leq, c = +1 :  x > -t.   Witness  -t.                         *)
(*   ¬Leq, c = -1 :  x <  t.   Upper bound — no witness.            *)
(*   ¬Lt,  c = +1 :  x ≥ -t.   Witness  -t - 1.                     *)
(*   ¬Lt,  c = -1 :  x ≤  t.   Upper bound — no witness.            *)
(*                                                              *)
(* Divisibility atoms don't contribute to B (periodic; handled by *)
(* φ_{-∞}'s evaluation at j ∈ {1..δ}).                             *)
(* ============================================================ *)

(* atomConstPartOnX: lt with x's coefficient zeroed out. *)
atomConstPartOnX[linTerm[c_, vs_Association], x_String] :=
  linTerm[c, KeyDrop[vs, x]];

(* bWitnessOfAtom: returns Missing[] (no contribution) or a       *)
(* linTerm witness.                                                *)
bWitnessOfAtom[negated_, atom_, x_String] :=
  Module[{coef, t},
    coef = atomCoefOnX[atom, x];
    If[coef === 0, Return[Missing[]]];
    t = atomConstPartOnX[
      Switch[Head[atom],
        aAtomDivides, atom[[2]],
        _, atom[[1]]],
      x];
    Switch[Head[atom],
      aAtomEq,
        If[negated, Missing[],  (* ≠ skipped for session 6 *)
          Switch[coef,
             1, linSub[linNeg[t], linConst[1]],   (* x = -t,   b = -t - 1 *)
            -1, linSub[t, linConst[1]],            (* x =  t,   b =  t - 1 *)
            _, HOL`Error`holError["arith-cooper",
               "B-set: |coef-x| > 1 unsupported in session 6",
               <|"atom" -> atom, "coef" -> coef|>]]],
      aAtomLeq,
        If[negated,
          Switch[coef,
             1, linNeg[t],                         (* ¬(x ≤ -t) ⇒ x > -t, b = -t *)
            -1, Missing[],                         (* ¬(x ≥ t) ⇒ x < t, upper bound *)
            _, HOL`Error`holError["arith-cooper",
               "B-set: |coef-x| > 1 unsupported",
               <|"atom" -> atom, "coef" -> coef|>]],
          Switch[coef,
             1, Missing[],                         (* x ≤ -t, upper bound *)
            -1, linSub[t, linConst[1]],            (* x ≥ t,  b = t - 1 *)
            _, HOL`Error`holError["arith-cooper",
               "B-set: |coef-x| > 1 unsupported",
               <|"atom" -> atom, "coef" -> coef|>]]],
      aAtomLt,
        If[negated,
          Switch[coef,
             1, linSub[linNeg[t], linConst[1]],    (* ¬(x < -t) ⇒ x ≥ -t, b = -t-1 *)
            -1, Missing[],                         (* ¬(x > t)  ⇒ x ≤ t,  upper *)
            _, HOL`Error`holError["arith-cooper",
               "B-set: |coef-x| > 1 unsupported",
               <|"atom" -> atom, "coef" -> coef|>]],
          Switch[coef,
             1, Missing[],                         (* x < -t,  upper bound *)
            -1, t,                                 (* x > t,   b = t      *)
            _, HOL`Error`holError["arith-cooper",
               "B-set: |coef-x| > 1 unsupported",
               <|"atom" -> atom, "coef" -> coef|>]]],
      aAtomDivides,
        Missing[]   (* periodic; never a B-witness *)
    ]
  ];

bSetOnX[f_, x_String] :=
  Module[{pairs, witnesses},
    pairs = collectAtoms[f, False];
    witnesses = Map[bWitnessOfAtom[#[[1]], #[[2]], x] &, pairs];
    Select[witnesses, ! MissingQ[#] &]
  ];

(* ============================================================ *)
(* cooperExistsStep — assemble the final QE AST                  *)
(*                                                              *)
(*   ∃x. body  ⇔   (⋁_{j=1..δ} φ_{-∞}[x ↦ j])                    *)
(*            ∨   (⋁_{j=1..δ} ⋁_{b ∈ B} body[x ↦ b + j])           *)
(*                                                              *)
(* Inputs: variable name x and a QF NNF body. Returns an AST     *)
(* aForm. Empty B-set means the right disjunct is aFormFalse;    *)
(* δ = 1 with no divisibility is the typical "no modulus" case.   *)
(* Output may still contain ⊤ / ⊥ leaves and unsimplified atoms;  *)
(* propositional simplification is a separate later pass.         *)
(* ============================================================ *)

bigOr[{}] := aFormFalse;
bigOr[{f_}] := f;
bigOr[fs_List] := Fold[aFormOr[#1, #2] &, First[fs], Rest[fs]];

cooperExistsStep[xName_String, body_] :=
  Module[{normBody, delta, bSet, phiMinf, jRange,
          minfDisjunct, bDisjunct},
    normBody = normalizeAtomsForm[body];
    delta    = deltaOnX[normBody, xName];
    bSet     = bSetOnX[normBody, xName];
    phiMinf  = phiMinusInfOnX[normBody, xName];
    jRange   = Range[1, delta];

    minfDisjunct = bigOr[
      Map[Function[j,
        substVarInForm[phiMinf, xName, linConst[j]]],
        jRange]];

    bDisjunct = bigOr[Flatten[
      Map[Function[b,
        Map[Function[j,
          substVarInForm[normBody, xName,
            linAdd[b, linConst[j]]]],
          jRange]],
        bSet], 1]];

    aFormOr[minfDisjunct, bDisjunct]
  ];

(* ============================================================ *)
(* simpForm — AST-level propositional simplification              *)
(*                                                              *)
(*   - Evaluate ground atoms (linTerm with empty vars):           *)
(*       Eq[c1, c2]      → T iff c1 == c2                          *)
(*       Leq[c1, c2]     → T iff c1 ≤ c2                           *)
(*       Lt[c1, c2]      → T iff c1 < c2                           *)
(*       Divides[d, c]   → T iff d | c                              *)
(*     (linZero[] counts as ground with value 0.)                  *)
(*   - Fold ∧/∨/¬ when one operand is T or F:                      *)
(*       T ∧ x → x ; F ∧ x → F ; T ∨ x → T ; F ∨ x → x.           *)
(*       ¬T → F ; ¬F → T ; ¬¬p → p.                                *)
(*   - Recurse into ⇒/⇔/∀/∃ but don't simplify their inner form    *)
(*     beyond propagating bool constants (which mostly don't       *)
(*     happen for ⇒/⇔ in a NNF-then-Cooper pipeline).               *)
(*                                                              *)
(* Composed with cooperExistsStep, this turns a closed Presburger  *)
(* formula's QE output into a ground T/F.                          *)
(* ============================================================ *)

linIsGround[linTerm[_, vs_Association]] := Length[vs] === 0;

linConstValue1[linTerm[c_, vs_Association]] /; Length[vs] === 0 := c;

evalGroundAtom[aAtomEq[lt1_, lt2_]] /;
    linIsGround[lt1] && linIsGround[lt2] :=
  If[linConstValue1[lt1] === linConstValue1[lt2], aFormTrue, aFormFalse];

evalGroundAtom[aAtomLeq[lt1_, lt2_]] /;
    linIsGround[lt1] && linIsGround[lt2] :=
  If[linConstValue1[lt1] <= linConstValue1[lt2], aFormTrue, aFormFalse];

evalGroundAtom[aAtomLt[lt1_, lt2_]] /;
    linIsGround[lt1] && linIsGround[lt2] :=
  If[linConstValue1[lt1] < linConstValue1[lt2], aFormTrue, aFormFalse];

evalGroundAtom[aAtomDivides[d_Integer, lt_]] /; linIsGround[lt] :=
  If[Mod[linConstValue1[lt], d] === 0, aFormTrue, aFormFalse];

evalGroundAtom[other_] := aFormAtom[other];

simpNeg[aFormTrue]  := aFormFalse;
simpNeg[aFormFalse] := aFormTrue;
simpNeg[aFormNot[f_]] := f;
simpNeg[f_] := aFormNot[f];

simpAnd[aFormTrue, b_]  := b;
simpAnd[a_, aFormTrue]  := a;
simpAnd[aFormFalse, _]  := aFormFalse;
simpAnd[_, aFormFalse]  := aFormFalse;
simpAnd[a_, b_]         := aFormAnd[a, b];

simpOr[aFormTrue, _]   := aFormTrue;
simpOr[_, aFormTrue]   := aFormTrue;
simpOr[aFormFalse, b_] := b;
simpOr[a_, aFormFalse] := a;
simpOr[a_, b_]         := aFormOr[a, b];

simpImp[aFormFalse, _] := aFormTrue;
simpImp[_, aFormTrue]  := aFormTrue;
simpImp[aFormTrue, b_] := b;
simpImp[a_, aFormFalse] := simpNeg[a];
simpImp[a_, b_]        := aFormImp[a, b];

simpIff[aFormTrue, b_]  := b;
simpIff[a_, aFormTrue]  := a;
simpIff[aFormFalse, b_] := simpNeg[b];
simpIff[a_, aFormFalse] := simpNeg[a];
simpIff[a_, b_]         := aFormIff[a, b];

simpForm[aFormTrue]  := aFormTrue;
simpForm[aFormFalse] := aFormFalse;
simpForm[aFormAtom[atom_]] := evalGroundAtom[atom];
simpForm[aFormNot[f_]] := simpNeg[simpForm[f]];
simpForm[aFormAnd[a_, b_]] := simpAnd[simpForm[a], simpForm[b]];
simpForm[aFormOr[a_, b_]]  := simpOr[simpForm[a], simpForm[b]];
simpForm[aFormImp[a_, b_]] := simpImp[simpForm[a], simpForm[b]];
simpForm[aFormIff[a_, b_]] := simpIff[simpForm[a], simpForm[b]];
simpForm[aFormForall[v_, body_]] := aFormForall[v, simpForm[body]];
simpForm[aFormExists[v_, body_]] := aFormExists[v, simpForm[body]];
simpForm[other_] := other;

(* ============================================================ *)
(* Ground arithmetic provers (HOL theorems for concrete ℕ)        *)
(*                                                              *)
(* Each takes Wolfram Integers and returns a kernel-checked      *)
(* HOL theorem on the corresponding SUC-stacked literal terms.    *)
(* These are the building blocks for verifying Cooper witnesses  *)
(* in HOL: when the Cooper algorithm reports "yes" with witness   *)
(* w, we still need to PROVE in HOL that the body holds at w.     *)
(* That proof is composed of these concrete-arithmetic steps.    *)
(* ============================================================ *)

(* Local def-unfolders (parallel to the ones in stdlib/FTA.wl;    *)
(* private contexts don't cross files, so we inline here).         *)

unfoldLeq[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`leqDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

unfoldLt[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`ltDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

unfoldDivides[a_, b_] :=
  Module[{ap1, e1, ap2},
    ap1 = HOL`Equal`APTHM[HOL`Stdlib`Num`dividesDefThm, a];
    e1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[e1, b];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* proveGroundAddEq[m, n] for m, n ≥ 0:                           *)
(*   ⊢ buildLitNum[m] + buildLitNum[n] = buildLitNum[m + n]       *)
(* by recursion on m (left side):                                  *)
(*   m = 0:    addLeftZeroThm at n.                                *)
(*   m = SUC k: addLeftSucThm at (k, n); recurse on k; APTERM SUC. *)

proveGroundAddEq[0, n_Integer] :=
  HOL`Bool`SPEC[buildLitNum[n], HOL`Stdlib`Num`addLeftZeroThm];

proveGroundAddEq[m_Integer, n_Integer] /; m > 0 :=
  Module[{mPred, kLit, nLit, leftSucEq, recEq, apSucEq},
    mPred = m - 1;
    kLit  = buildLitNum[mPred];
    nLit  = buildLitNum[n];
    leftSucEq = HOL`Bool`SPEC[nLit, HOL`Bool`SPEC[kLit,
      HOL`Stdlib`Num`addLeftSucThm]];
    (* ⊢ SUC k + n = SUC (k + n) *)
    recEq = proveGroundAddEq[mPred, n];
    (* ⊢ k + n = (k + n) *)
    apSucEq = HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], recEq];
    (* ⊢ SUC (k + n) = SUC ((k + n)) *)
    TRANS[leftSucEq, apSucEq]
    (* ⊢ SUC k + n = SUC ((k + n)) = buildLitNum[m + n] *)
  ];

(* proveGroundMultEq[m, n] for m, n ≥ 0:                          *)
(*   ⊢ m * n = (m * n)                                            *)
(* by recursion on n (right side):                                 *)
(*   n = 0:   timesZeroEqThm at m.                                 *)
(*   n = SUC k: timesSucEqThm at (m, k) → m * SUC k = m * k + m;   *)
(*              recurse on k; APTERM(+ m); chain with groundAdd.   *)

proveGroundMultEq[m_Integer, 0] :=
  HOL`Bool`SPEC[buildLitNum[m], HOL`Stdlib`Num`timesZeroEqThm];

proveGroundMultEq[m_Integer, n_Integer] /; n > 0 :=
  Module[{nPred, mLit, kLit, sucEq, recEq, apPlusMEq, addEq, chain},
    nPred = n - 1;
    mLit  = buildLitNum[m];
    kLit  = buildLitNum[nPred];
    sucEq = HOL`Bool`SPEC[kLit, HOL`Bool`SPEC[mLit,
      HOL`Stdlib`Num`timesSucEqThm]];
    (* ⊢ m * SUC k = m * k + m *)
    recEq = proveGroundMultEq[m, nPred];
    (* ⊢ m * k = (m * k) *)
    apPlusMEq = HOL`Equal`APTHM[
      HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], recEq], mLit];
    (* ⊢ m * k + m = (m * k) + m *)
    addEq = proveGroundAddEq[m * nPred, m];
    (* ⊢ (m * k) + m = (m * k + m) *)
    chain = TRANS[sucEq, TRANS[apPlusMEq, addEq]];
    chain
  ];

(* proveGroundLeq[m, n] for m ≤ n, both ≥ 0:                       *)
(*   ⊢ buildLitNum[m] ≤ buildLitNum[n]                             *)
(* Witness in leqDefThm: k = n - m so m + k = n.                   *)

proveGroundLeq[m_Integer, n_Integer] /; m <= n :=
  Module[{mLit, nLit, k, kLit, addEq, existsBody, existsTm,
          existsThm, unfEq},
    mLit = buildLitNum[m]; nLit = buildLitNum[n];
    k = n - m;
    kLit = buildLitNum[k];
    addEq = proveGroundAddEq[m, k];
    (* ⊢ m + k = n *)
    existsBody = mkEq[mkComb[mkComb[HOL`Stdlib`Num`plusConst[], mLit],
      mkVar["kGL", numTy]], nLit];
    existsTm = mkComb[mkConst["\[Exists]",
      tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mkVar["kGL", numTy], existsBody]];
    existsThm = HOL`Bool`EXISTS[existsTm, kLit, addEq];
    (* ⊢ ∃k. m + k = n *)
    unfEq = unfoldLeq[mLit, nLit];
    (* ⊢ m ≤ n = ∃k. m + k = n *)
    EQMP[HOL`Equal`SYM[unfEq], existsThm]
    (* ⊢ m ≤ n *)
  ];

(* proveGroundLt[m, n] for m < n:                                 *)
(*   ⊢ buildLitNum[m] < buildLitNum[n]                            *)
(* Reduce via ltDefThm: m < n  ⇔  SUC m ≤ n.                       *)

proveGroundLt[m_Integer, n_Integer] /; m < n :=
  Module[{mLit, nLit, sucMLit, sucLeqN, unfEq},
    mLit = buildLitNum[m]; nLit = buildLitNum[n];
    sucMLit = buildLitNum[m + 1];
    sucLeqN = proveGroundLeq[m + 1, n];
    (* ⊢ SUC m ≤ n *)
    unfEq = unfoldLt[mLit, nLit];
    (* ⊢ m < n = SUC m ≤ n *)
    EQMP[HOL`Equal`SYM[unfEq], sucLeqN]
  ];

(* proveGroundDivides[d, n] for d > 0 and d | n:                  *)
(*   ⊢ divides buildLitNum[d] buildLitNum[n]                       *)
(* Witness in dividesDefThm: c = n / d so n = d * c.               *)

proveGroundDivides[d_Integer, n_Integer] :=
  Module[{dLit, nLit, c, cLit, multEq, nEqDC, existsBody,
          existsTm, existsThm, unfEq},
    If[! (d > 0 && Mod[n, d] === 0),
      HOL`Error`holError["arith-ground",
        "proveGroundDivides: need d > 0 and d | n",
        <|"d" -> d, "n" -> n|>]];
    dLit = buildLitNum[d]; nLit = buildLitNum[n];
    c = Quotient[n, d];
    cLit = buildLitNum[c];
    multEq = proveGroundMultEq[d, c];
    (* ⊢ d * c = n *)
    nEqDC = HOL`Equal`SYM[multEq];
    (* ⊢ n = d * c *)
    existsBody = mkEq[nLit, mkComb[mkComb[HOL`Stdlib`Num`timesConst[],
      dLit], mkVar["cGD", numTy]]];
    existsTm = mkComb[mkConst["\[Exists]",
      tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[mkVar["cGD", numTy], existsBody]];
    existsThm = HOL`Bool`EXISTS[existsTm, cLit, nEqDC];
    (* ⊢ ∃c. n = d * c *)
    unfEq = unfoldDivides[dLit, nLit];
    (* ⊢ divides d n = ∃c. n = d * c *)
    EQMP[HOL`Equal`SYM[unfEq], existsThm]
  ];

(* ============================================================ *)
(* proveGroundReduceTm — reduce a closed ℕ arithmetic term         *)
(* to its SUC-stacked literal form.                                *)
(*                                                              *)
(*   Input:  HOL term built from 0, SUC, +, * with all leaves    *)
(*           being literals (no free vars).                       *)
(*   Output: ⊢ t = (concreteValue)̄                                *)
(*                                                              *)
(* The output's RHS is `buildLitNum[concreteValue]`. This lets    *)
(* the atom prover handle compound arithmetic atoms like           *)
(* `2 * x + 1 ≤ 10` after substituting x with a literal: the LHS  *)
(* `2 * w + 1` reduces to the value, and the simplified atom       *)
(* matches the ground prover's literal-only contract.              *)
(* ============================================================ *)

proveGroundReduceTm[t_] :=
  Which[
    litNumQ[t], REFL[t],

    MatchQ[t, comb[const["SUC", _], _]],
      Module[{n, recTh},
        n = t[[2]];
        recTh = proveGroundReduceTm[n];
        (* ⊢ n = nLit ⇒ ⊢ SUC n = SUC nLit *)
        HOL`Equal`APTERM[HOL`Stdlib`Num`sucConst[], recTh]
      ],

    MatchQ[t, comb[comb[const["+", _], _], _]],
      Module[{a, b, aRed, bRed, aLit, bLit, congEq, addEq},
        a = t[[1, 2]]; b = t[[2]];
        aRed = proveGroundReduceTm[a];
        bRed = proveGroundReduceTm[b];
        aLit = concl[aRed][[2]];
        bLit = concl[bRed][[2]];
        (* ⊢ a + b = aLit + bLit (congruence on +) *)
        congEq = HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[HOL`Stdlib`Num`plusConst[], aRed], bRed];
        (* ⊢ aLit + bLit = (a+b)̄ *)
        addEq = proveGroundAddEq[parseLitNum[aLit], parseLitNum[bLit]];
        TRANS[congEq, addEq]
      ],

    MatchQ[t, comb[comb[const["*", _], _], _]],
      Module[{a, b, aRed, bRed, aLit, bLit, congEq, multEq},
        a = t[[1, 2]]; b = t[[2]];
        aRed = proveGroundReduceTm[a];
        bRed = proveGroundReduceTm[b];
        aLit = concl[aRed][[2]];
        bLit = concl[bRed][[2]];
        congEq = HOL`Kernel`MKCOMB[
          HOL`Equal`APTERM[HOL`Stdlib`Num`timesConst[], aRed], bRed];
        multEq = proveGroundMultEq[parseLitNum[aLit], parseLitNum[bLit]];
        TRANS[congEq, multEq]
      ],

    True,
      HOL`Error`holError["arith-reduce",
        "proveGroundReduceTm: term has non-literal leaf",
        <|"term" -> t|>]
  ];

(* ============================================================ *)
(* findSatWitness — concrete Integer witness for ∃x. body         *)
(*                                                              *)
(* For closed Presburger over ℕ, every satisfying x lies in       *)
(* {b + j : b ∈ B-set, j ∈ [1..δ]} ∪ {j : j ∈ [1..δ]} ∪ {0}.       *)
(* We search these candidates; the first w for which              *)
(*   simpForm[substVarInForm[normBody, xName, linConst[w]]]       *)
(* reduces to aFormTrue is returned as an Integer (or Missing[]).  *)
(* ============================================================ *)

candidateIntegers[xName_String, normBody_] :=
  Module[{delta, bSet, bConsts, baseCandidates, minfCandidates},
    delta = deltaOnX[normBody, xName];
    bSet  = bSetOnX[normBody, xName];
    bConsts = Select[bSet, linIsGround];
    baseCandidates = Flatten[Map[Function[b,
      Module[{bc = linConstValue1[b]},
        Map[bc + # &, Range[1, delta]]]], bConsts]];
    minfCandidates = Range[0, delta];
    DeleteDuplicates[Join[baseCandidates, minfCandidates]]
  ];

findSatWitness[xName_String, body_] :=
  Module[{normBody, candidates, hits},
    normBody = normalizeAtomsForm[body];
    candidates = candidateIntegers[xName, normBody];
    candidates = Select[candidates, # >= 0 &];   (* ℕ-only *)
    hits = Select[candidates, Function[w,
      simpForm[substVarInForm[normBody, xName,
        linConst[w]]] === aFormTrue]];
    If[hits === {}, Missing[], First[hits]]
  ];

(* ============================================================ *)
(* proveGroundFormulaTm — HOL proof of a closed propositional     *)
(* formula over ground arithmetic atoms                           *)
(*                                                              *)
(* Restricted to atoms of the form lit op lit (eq/leq/lt/divides) *)
(* and combinations via ∧, ∨, ¬, T, F. Other shapes throw         *)
(* `arith-ground-fmla`.                                            *)
(* ============================================================ *)

(* reduceAtomSides[t]: returns {aRed, bRed, aLit, bLit} for the    *)
(* atom's two ℕ-typed arguments. aRed / bRed are ⊢ a = aLit etc.   *)
(* Used by proveGroundAtomTm to handle compound arithmetic atoms.  *)
reduceAtomSides[t_] :=
  Module[{a, b, aRed, bRed},
    a = t[[1, 2]]; b = t[[2]];
    aRed = proveGroundReduceTm[a];
    bRed = proveGroundReduceTm[b];
    {aRed, bRed, concl[aRed][[2]], concl[bRed][[2]]}
  ];

(* Given a proof `⊢ aLit op bLit` and side-reductions               *)
(*   aRed : ⊢ a = aLit                                              *)
(*   bRed : ⊢ b = bLit                                              *)
(* recover `⊢ a op b` by MKCOMB-ing the symmetric equations to       *)
(* build `⊢ aLit op bLit = a op b`, then EQMP. Using SUBS here was   *)
(* unsafe because it rewrites every syntactic occurrence of aLit —   *)
(* including aLit-as-sub-pattern inside bLit (e.g. a literal 3       *)
(* inside SUC SUC SUC 0 = 5).                                        *)
liftReducedAtomProof[reducedThm_, opConst_, aRed_, bRed_] :=
  Module[{eqLifted},
    eqLifted = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[opConst, HOL`Equal`SYM[aRed]],
      HOL`Equal`SYM[bRed]];
    (* ⊢ opConst aLit bLit = opConst a b *)
    EQMP[eqLifted, reducedThm]
  ];

proveGroundAtomTm[t_] :=
  Which[
    (* a = b *)
    MatchQ[t, comb[comb[const["=", _], _], _]],
      Module[{opConst, aRed, bRed, aLit, bLit, am, bm, reducedThm},
        opConst = t[[1, 1]];
        {aRed, bRed, aLit, bLit} = reduceAtomSides[t];
        am = parseLitNum[aLit]; bm = parseLitNum[bLit];
        If[am =!= bm,
          HOL`Error`holError["arith-ground-fmla",
            "proveGroundAtomTm: eq atom is false",
            <|"term" -> t, "lhs" -> am, "rhs" -> bm|>]];
        reducedThm = REFL[aLit];   (* ⊢ aLit = aLit ≡ aLit = bLit *)
        liftReducedAtomProof[reducedThm, opConst, aRed, bRed]
      ],

    (* a ≤ b *)
    MatchQ[t, comb[comb[const["≤", _], _], _]],
      Module[{opConst, aRed, bRed, aLit, bLit, am, bm, reducedThm},
        opConst = t[[1, 1]];
        {aRed, bRed, aLit, bLit} = reduceAtomSides[t];
        am = parseLitNum[aLit]; bm = parseLitNum[bLit];
        If[am > bm,
          HOL`Error`holError["arith-ground-fmla",
            "proveGroundAtomTm: ≤ atom is false",
            <|"term" -> t, "lhs" -> am, "rhs" -> bm|>]];
        reducedThm = proveGroundLeq[am, bm];
        liftReducedAtomProof[reducedThm, opConst, aRed, bRed]
      ],

    (* a < b *)
    MatchQ[t, comb[comb[const["<", _], _], _]],
      Module[{opConst, aRed, bRed, aLit, bLit, am, bm, reducedThm},
        opConst = t[[1, 1]];
        {aRed, bRed, aLit, bLit} = reduceAtomSides[t];
        am = parseLitNum[aLit]; bm = parseLitNum[bLit];
        If[am >= bm,
          HOL`Error`holError["arith-ground-fmla",
            "proveGroundAtomTm: < atom is false",
            <|"term" -> t, "lhs" -> am, "rhs" -> bm|>]];
        reducedThm = proveGroundLt[am, bm];
        liftReducedAtomProof[reducedThm, opConst, aRed, bRed]
      ],

    (* divides d n *)
    MatchQ[t, comb[comb[const["divides", _], _], _]],
      Module[{opConst, dRed, nRed, dLit, nLit, dv, nv, reducedThm},
        opConst = t[[1, 1]];
        {dRed, nRed, dLit, nLit} = reduceAtomSides[t];
        dv = parseLitNum[dLit]; nv = parseLitNum[nLit];
        If[! (dv > 0 && Mod[nv, dv] === 0),
          HOL`Error`holError["arith-ground-fmla",
            "proveGroundAtomTm: divides atom is false",
            <|"term" -> t, "d" -> dv, "n" -> nv|>]];
        reducedThm = proveGroundDivides[dv, nv];
        liftReducedAtomProof[reducedThm, opConst, dRed, nRed]
      ],

    True,
      HOL`Error`holError["arith-ground-fmla",
        "proveGroundAtomTm: atom shape not recognized",
        <|"term" -> t|>]
  ];

proveGroundFormulaTm[t_] :=
  Which[
    t === mkConst["T", boolTy], HOL`Bool`TRUTH,

    MatchQ[t, comb[comb[const["∧", _], _], _]],
      Module[{a, b, aThm, bThm},
        a = t[[1, 2]]; b = t[[2]];
        aThm = proveGroundFormulaTm[a];
        bThm = proveGroundFormulaTm[b];
        HOL`Bool`CONJ[aThm, bThm]
      ],

    MatchQ[t, comb[comb[const["∨", _], _], _]],
      Module[{a, b, aThm},
        a = t[[1, 2]]; b = t[[2]];
        (* Try the left first; if it fails, try the right. *)
        aThm = Catch[proveGroundFormulaTm[a], HOL`Error`holErrorTag,
          Function[err, $Failed]];
        If[aThm =!= $Failed,
          HOL`Bool`DISJ1[aThm, b],
          HOL`Bool`DISJ2[proveGroundFormulaTm[b], a]]
      ],

    True,
      (* Treat as a leaf atom. *)
      proveGroundAtomTm[t]
  ];

(* ============================================================ *)
(* arithProveExists — orchestrate ∃-SAT proof                    *)
(*                                                              *)
(*   Goal:  ⊢ ∃x:num. body                                       *)
(*                                                              *)
(* 1. Parse the HOL goal; check shape ∃x:num. (…).                *)
(* 2. Use findSatWitness on the AST to extract w ∈ ℕ.              *)
(* 3. Compute body[x ↦ buildLitNum[w]] via BETACONV.               *)
(* 4. Prove the resulting closed ground formula via                *)
(*    proveGroundFormulaTm.                                        *)
(* 5. Apply HOL`Bool`EXISTS at w_lit.                              *)
(* ============================================================ *)

(* Candidate Integer witnesses for ∃x:num. body. Uses Cooper's     *)
(* B-set + 0..δ from the AST view of the body. Filters to ℕ. The   *)
(* result is a list of Integer w to try; we substitute and prove    *)
(* in order until one succeeds.                                     *)

inferCandidatesForGoal[xName_String, goalTm_] :=
  Module[{astExists, astBody, normBody, candidates},
    astExists = parseForm[goalTm];        (* aFormExists[name, body] *)
    astBody   = astExists[[2]];
    normBody  = normalizeAtomsForm[astBody];
    candidates = candidateIntegers[xName, normBody];
    Select[candidates, # >= 0 &]
  ];

(* arithProveExists handles one outer ∃x:num. body. If body itself  *)
(* is another ∃-quantifier (or has nested ∃ structure), we recurse  *)
(* via arithProve.                                                  *)

arithProveExists[goalTm_] :=
  Module[{absTm, xName, candidates, hit},
    If[! MatchQ[goalTm, comb[const["∃", _],
        abs[bvar[0, ty_], _, _String]]] ||
        goalTm[[2, 1, 2]] =!= numTy,
      HOL`Error`holError["arith-prove-exists",
        "expected ⊢ ∃x:num. body",
        <|"got" -> goalTm|>]];
    absTm = goalTm[[2]];
    xName = absTm[[3]];
    candidates = inferCandidatesForGoal[xName, goalTm];
    hit = Missing[];
    Scan[Function[w,
      If[MissingQ[hit],
        Module[{wLit, appTm, betaTh, substBody, bodyThm},
          wLit = buildLitNum[w];
          appTm = mkComb[absTm, wLit];
          betaTh = BETACONV[appTm];
          substBody = concl[betaTh][[2]];
          bodyThm = Catch[
            arithProveBody[substBody],
            HOL`Error`holErrorTag, Function[err, $Failed]];
          If[bodyThm =!= $Failed,
            hit = HOL`Bool`EXISTS[goalTm, wLit, bodyThm]]
        ]
      ]], candidates];
    If[MissingQ[hit],
      HOL`Error`holError["arith-prove-exists",
        "no witness found for ⊢ ∃x:num. body",
        <|"goal" -> goalTm|>]];
    hit
  ];

(* arithProveBody dispatches: if the term is another ∃-quantifier,  *)
(* recurse via arithProveExists; otherwise treat as a ground         *)
(* propositional formula.                                            *)

arithProveBody[t_] :=
  If[MatchQ[t, comb[const["∃", _], abs[bvar[0, ty_], _, _String]]] &&
       t[[2, 1, 2]] === numTy,
    arithProveExists[t],
    proveGroundFormulaTm[t]
  ];

(* ============================================================ *)
(* linNormConv — proof-producing linear normalizer               *)
(*                                                              *)
(*   linNormConv[t] → ⊢ t = buildLin[parseLin[t]]                *)
(*                                                              *)
(* Normalizes a ℕ linear term (built from 0, SUC, +, vars; and  *)
(* literal·literal products) to the canonical buildLin form:     *)
(* constant-first, then variable monomials in sorted order,      *)
(* right-associated. The hard work is in caAdd, which proves     *)
(* buildLin[L] + buildLin[M] = buildLin[L+M] by flattening the   *)
(* left summand tree (addAssoc) and folding each monomial of L   *)
(* into M's canonical form one at a time via caInsert.           *)
(*                                                              *)
(* This first cut covers sort + constant-folding + SUC. Two      *)
(* generalizations throw a tagged error until a goal forces      *)
(* them: coefficient-merge (same variable on both operands) and  *)
(* literal scaling of a non-constant term (k · expr).            *)
(* ============================================================ *)

nPlus[a_, b_] := mkComb[mkComb[plusConst[], a], b];
nTimes[a_, b_] := mkComb[mkComb[timesConst[], a], b];

(* canonical summand list of a linTerm, in buildLin order. *)
canonSummandList[linTerm[c_, vs_Association]] :=
  Module[{names, varParts},
    names = Sort[Keys[vs]];
    varParts = (With[{coef = vs[#]},
        If[coef === 1, var[#, numTy], nTimes[buildLitNum[coef], var[#, numTy]]]
      ] &) /@ names;
    Which[
      c =!= 0, Prepend[varParts, buildLitNum[c]],
      varParts === {}, {zeroConst[]},
      True, varParts]
  ];

(* right-associated `+` of a summand list (mirrors buildLin's Fold). *)
rightAssocPlus[{s_}] := s;
rightAssocPlus[ss_List] :=
  Fold[nPlus[#2, #1] &, Last[ss], Reverse[Most[ss]]];

summandIsConst[t_] := litNumQ[t];
summandVarName[var[nm_String, _]] := nm;
summandVarName[comb[comb[const["*", _], _], var[nm_String, _]]] := nm;

(* x sorts strictly before y in the canonical (Sort) order. *)
varOrderedBefore[x_String, y_String] := Order[x, y] === 1;

(* ===== algebraic lemma instances ===== *)

(* ⊢ (a + b) + c = a + (b + c) *)
addAssocInst[a_, b_, c_] :=
  HOL`Bool`SPEC[c, HOL`Bool`SPEC[b, HOL`Bool`SPEC[a,
    HOL`Stdlib`Num`addAssocThm]]];

(* ⊢ a + b = b + a *)
addCommInst[a_, b_] :=
  HOL`Bool`SPEC[b, HOL`Bool`SPEC[a, HOL`Stdlib`Num`addCommThm]];

(* ⊢ a + (b + c) = b + (a + c) *)
addLeftCommInst[a_, b_, c_] :=
  Module[{t1, t2, t3},
    t1 = HOL`Equal`SYM[addAssocInst[a, b, c]];
    (* ⊢ a + (b + c) = (a + b) + c *)
    t2 = HOL`Equal`APTHM[
      HOL`Equal`APTERM[plusConst[], addCommInst[a, b]], c];
    (* ⊢ (a + b) + c = (b + a) + c *)
    t3 = addAssocInst[b, a, c];
    (* ⊢ (b + a) + c = b + (a + c) *)
    TRANS[t1, TRANS[t2, t3]]
  ];

(* From ⊢ X = Y, build ⊢ X + rest = Y + rest. *)
plusLeftCong[xyThm_, rest_] :=
  HOL`Equal`APTHM[HOL`Equal`APTERM[plusConst[], xyThm], rest];

(* From ⊢ a = b, build ⊢ s + a = s + b. *)
plusRightCong[s_, abThm_] :=
  HOL`Equal`APTERM[mkComb[plusConst[], s], abThm];

(* ===== caInsertConst: fold a positive constant into canonical M ===== *)

caInsertConst[c_Integer, linTerm[cM_, vsM_Association]] :=
  Module[{cLit, ss, cMLit, restTerm, assoc, gAdd, reduced},
    cLit = buildLitNum[c];
    If[cM === 0,
      If[Length[vsM] === 0,
        (* M empty: c + 0 = c *)
        HOL`Bool`SPEC[cLit, HOL`Stdlib`Num`plusZeroEqThm],
        (* M has vars, no const: c + buildLin[M] is already canonical *)
        REFL[nPlus[cLit, buildLin[linTerm[cM, vsM]]]]
      ],
      ss = canonSummandList[linTerm[cM, vsM]];
      cMLit = First[ss];
      If[Length[ss] === 1,
        proveGroundAddEq[c, cM],
        restTerm = rightAssocPlus[Rest[ss]];
        assoc = HOL`Equal`SYM[addAssocInst[cLit, cMLit, restTerm]];
        gAdd = proveGroundAddEq[c, cM];
        reduced = plusLeftCong[gAdd, restTerm];
        TRANS[assoc, reduced]
      ]
    ]
  ];

(* ===== caInsertVar: insert a variable monomial into canonical M ===== *)

caInsertVar[x_String, k_Integer, linTerm[cM_, vsM_Association]] :=
  Module[{monoTerm},
    If[KeyExistsQ[vsM, x],
      HOL`Error`holError["arith-norm-merge",
        "linNormConv: coefficient merge not yet supported",
        <|"var" -> x|>]];
    monoTerm = If[k === 1, var[x, numTy],
      nTimes[buildLitNum[k], var[x, numTy]]];
    caInsertVarInto[monoTerm, x, buildLin[linTerm[cM, vsM]]]
  ];

(* ⊢ monoTerm + BM = (canonical insertion of monoTerm into BM) *)
caInsertVarInto[monoTerm_, x_String, BM_] :=
  Module[{head, rest, hasRest, hkName, lc, sub, cong},
    If[MatchQ[BM, comb[comb[const["+", _], _], _]],
      head = BM[[1, 2]]; rest = BM[[2]]; hasRest = True,
      head = BM; hasRest = False
    ];
    If[! hasRest,
      If[summandIsConst[head],
        addCommInst[monoTerm, head],
        hkName = summandVarName[head];
        Which[
          x === hkName,
            HOL`Error`holError["arith-norm-merge",
              "linNormConv: coefficient merge not yet supported",
              <|"var" -> x|>],
          varOrderedBefore[x, hkName], REFL[nPlus[monoTerm, head]],
          True, addCommInst[monoTerm, head]
        ]
      ],
      If[summandIsConst[head],
        lc = addLeftCommInst[monoTerm, head, rest];
        sub = caInsertVarInto[monoTerm, x, rest];
        cong = plusRightCong[head, sub];
        TRANS[lc, cong],
        hkName = summandVarName[head];
        Which[
          x === hkName,
            HOL`Error`holError["arith-norm-merge",
              "linNormConv: coefficient merge not yet supported",
              <|"var" -> x|>],
          varOrderedBefore[x, hkName], REFL[nPlus[monoTerm, BM]],
          True,
            lc = addLeftCommInst[monoTerm, head, rest];
            sub = caInsertVarInto[monoTerm, x, rest];
            cong = plusRightCong[head, sub];
            TRANS[lc, cong]
        ]
      ]
    ]
  ];

(* ===== caAdd: ⊢ buildLin[L] + buildLin[M] = buildLin[L+M] ===== *)

linTermIsZero[linTerm[c_, vs_Association]] := c === 0 && Length[vs] === 0;
monoCount[linTerm[c_, vs_Association]] := If[c =!= 0, 1, 0] + Length[vs];

(* {kind, data, restLin, summandTerm} for the first canonical mono of L. *)
firstMonoOf[linTerm[c_, vs_Association]] :=
  If[c =!= 0,
    {"const", c, linTerm[0, vs], buildLitNum[c]},
    Module[{nm, coef},
      nm = First[Sort[Keys[vs]]];
      coef = vs[nm];
      {"var", {nm, coef}, linTerm[0, KeyDrop[vs, nm]],
        If[coef === 1, var[nm, numTy],
          nTimes[buildLitNum[coef], var[nm, numTy]]]}
    ]
  ];

caAdd[L_, M_] :=
  Which[
    linTermIsZero[L],
      HOL`Bool`SPEC[buildLin[M], HOL`Stdlib`Num`addLeftZeroThm],
    linTermIsZero[M],
      HOL`Bool`SPEC[buildLin[L], HOL`Stdlib`Num`plusZeroEqThm],
    True, caAddNonzero[L, M]
  ];

caAddNonzero[L_, M_] :=
  Module[{kind, data, restLin, fs, doInsert, step1, step2, step3, step4},
    {kind, data, restLin, fs} = firstMonoOf[L];
    doInsert[targetM_] := If[kind === "const",
      caInsertConst[data, targetM],
      caInsertVar[data[[1]], data[[2]], targetM]];
    If[monoCount[L] === 1,
      doInsert[M],
      step1 = addAssocInst[fs, buildLin[restLin], buildLin[M]];
      step2 = caAdd[restLin, M];
      step3 = plusRightCong[fs, step2];
      step4 = doInsert[linAdd[restLin, M]];
      TRANS[step1, TRANS[step3, step4]]
    ]
  ];

(* ===== sucEqAddOne + normLin driver ===== *)

(* ⊢ SUC u = u + SUC 0 *)
sucEqAddOne[u_] :=
  Module[{e1, e2, e3, chain},
    e1 = HOL`Bool`SPEC[zeroConst[], HOL`Bool`SPEC[u,
      HOL`Stdlib`Num`plusSucEqThm]];
    (* ⊢ u + SUC 0 = SUC (u + 0) *)
    e2 = HOL`Bool`SPEC[u, HOL`Stdlib`Num`plusZeroEqThm];
    (* ⊢ u + 0 = u *)
    e3 = HOL`Equal`APTERM[sucConst[], e2];
    (* ⊢ SUC (u + 0) = SUC u *)
    chain = TRANS[e1, e3];
    HOL`Equal`SYM[chain]
  ];

normLinAux[t_const /; litNumQ[t]] := REFL[t];
normLinAux[t_comb /; litNumQ[t]] := REFL[t];
normLinAux[v : var[_String, ty_] /; ty === numTy] := REFL[v];

normLinAux[comb[const["SUC", _], u_] /; ! litNumQ[u]] :=
  Module[{thU, Lu, sucToAdd, cong, add, normRhs},
    thU = normLinAux[u];
    Lu = parseLin[u];
    sucToAdd = sucEqAddOne[u];
    cong = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[plusConst[], thU],
      REFL[mkComb[sucConst[], zeroConst[]]]];
    (* ⊢ u + SUC 0 = buildLin[Lu] + SUC 0 *)
    add = caAdd[Lu, linConst[1]];
    (* ⊢ buildLin[Lu] + SUC 0 = buildLin[Lu + 1] *)
    normRhs = TRANS[cong, add];
    TRANS[sucToAdd, normRhs]
  ];

normLinAux[comb[comb[const["+", _], a_], b_]] :=
  Module[{thA, thB, La, Lb, cong, add},
    thA = normLinAux[a];
    thB = normLinAux[b];
    La = parseLin[a];
    Lb = parseLin[b];
    cong = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[plusConst[], thA], thB];
    (* ⊢ a + b = buildLin[La] + buildLin[Lb] *)
    add = caAdd[La, Lb];
    TRANS[cong, add]
  ];

normLinAux[t_] :=
  HOL`Error`holError["arith-norm",
    "linNormConv: term not a supported linear ℕ expression",
    <|"got" -> t|>];

HOL`Auto`Arith`linNormConv[t_] := normLinAux[t];

(* ============================================================ *)
(* Farkas refutation: oracle + kernel verifier                   *)
(*                                                              *)
(* To refute a system of ℕ inequalities {Lᵢ ≤ Rᵢ}, an untrusted *)
(* oracle finds nonneg multipliers λᵢ with Σλᵢ(Lᵢ-Rᵢ) a         *)
(* positive constant (Farkas). The kernel verifier then scales,  *)
(* sums (leqAddMono), normalizes both sides (linNormConv), peels *)
(* the shared variable part (leqAddLeftCancel), and hits a       *)
(* ground-false c ≤ c' contradiction → ⊢ F. Oracle error only    *)
(* costs completeness ("can't prove"), never soundness.          *)
(*                                                              *)
(* This first cut implements the unit-subset certificate (all    *)
(* λ ∈ {0,1}) — which closes the capstone and the usual additive *)
(* monotonicity goals. General LinearProgramming multipliers and *)
(* the leqMultLeft scaling they require (which in turn needs      *)
(* linNormConv coefficient-merge) are the next generalization.    *)
(* ============================================================ *)

nLeqTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Num`leqConst[], a], b];

(* A ≤-fact's concl is `L ≤ R`; project the two sides. *)
leqSidesOf[th_] := Module[{c}, c = concl[th]; {c[[1, 2]], c[[2]]}];

(* Coerce a fact whose concl is `X < Y` into `SUC X ≤ Y`; pass
   through `≤` facts unchanged. *)
toLeqFact[th_] :=
  Module[{c, xT, yT},
    c = concl[th];
    Which[
      MatchQ[c, comb[comb[const["≤", _], _], _]], th,
      MatchQ[c, comb[comb[const["<", _], _], _]],
        xT = c[[1, 2]]; yT = c[[2]];
        EQMP[unfoldLt[xT, yT], th],
      True,
        HOL`Error`holError["arith-farkas",
          "toLeqFact: fact is neither ≤ nor <", <|"concl" -> c|>]
    ]
  ];

(* dᵢ = Lᵢ - Rᵢ as a ℤ-coefficient linTerm. *)
factDiff[th_] :=
  Module[{ls}, ls = leqSidesOf[th];
    linSub[parseLin[ls[[1]]], parseLin[ls[[2]]]]];

(* unit-subset Farkas oracle: smallest nonempty index set whose
   diff-sum has no variables and a positive constant, or $Failed. *)
unitCertWorks[diffs_, idxs_] :=
  Module[{s}, s = Fold[linAdd, linZero[], diffs[[idxs]]];
    Length[s[[2]]] === 0 && s[[1]] > 0];

farkasUnitCert[diffs_List] :=
  Module[{n, hit},
    n = Length[diffs];
    If[n > 8,
      HOL`Error`holError["arith-farkas",
        "farkasUnitCert: too many hypotheses for unit search",
        <|"n" -> n|>]];
    hit = SelectFirst[Subsets[Range[n], {1, n}],
      unitCertWorks[diffs, #] &];
    If[MissingQ[hit], $Failed, hit]
  ];

(* leqAddMono fold: from facts ⊢ Lᵢ ≤ Rᵢ produce ⊢ ΣLᵢ ≤ ΣRᵢ. *)
combineLeq[th1_, th2_] :=
  Module[{s1, s2, inst},
    s1 = leqSidesOf[th1]; s2 = leqSidesOf[th2];
    inst = HOL`Bool`SPEC[s2[[2]], HOL`Bool`SPEC[s2[[1]],
      HOL`Bool`SPEC[s1[[2]], HOL`Bool`SPEC[s1[[1]],
        HOL`Stdlib`Num`leqAddMonoThm]]]];
    HOL`Bool`MP[HOL`Bool`MP[inst, th1], th2]
  ];

sumLeqFacts[facts_List] := Fold[combineLeq, First[facts], Rest[facts]];

(* rewrite the LHS / RHS of a `≤` theorem using an equation. *)
rewriteLeqLhs[leqTh_, lhsEq_] :=
  Module[{sides, cong},
    sides = leqSidesOf[leqTh];
    cong = HOL`Equal`APTHM[
      HOL`Equal`APTERM[HOL`Stdlib`Num`leqConst[], lhsEq], sides[[2]]];
    EQMP[cong, leqTh]
  ];

rewriteLeqRhs[leqTh_, rhsEq_] :=
  Module[{sides, cong},
    sides = leqSidesOf[leqTh];
    cong = HOL`Kernel`MKCOMB[
      REFL[mkComb[HOL`Stdlib`Num`leqConst[], sides[[1]]]], rhsEq];
    EQMP[cong, leqTh]
  ];

(* ⊢ buildLin[linTerm[c, Vvars]] = Vterm + buildLitNum[c]. *)
commuteConstToRight[vLin : linTerm[_, vsV_], c_Integer] :=
  Module[{vTerm, cLit},
    vTerm = buildLin[vLin];
    cLit = buildLitNum[c];
    If[c === 0,
      HOL`Equal`SYM[HOL`Bool`SPEC[vTerm, HOL`Stdlib`Num`plusZeroEqThm]],
      addCommInst[cLit, vTerm]
    ]
  ];

(* From a list of ≤-facts, build ⊢ F (carrying the facts' hyps). *)
farkasRefute[leqFacts_List] :=
  Module[{diffs, cert, chosen, combined, sides, normL, normR, cl, cr,
          leqCanon, lcLin, rcLin, cL, cR, vLin, vTerm, groundLeq,
          commL, commR, step2, step3, cancel, glt, notLeqInst, notLeq},
    diffs = factDiff /@ leqFacts;
    cert = farkasUnitCert[diffs];
    If[cert === $Failed,
      HOL`Error`holError["arith-farkas",
        "no unit Farkas certificate", <|"diffs" -> diffs|>]];
    chosen = leqFacts[[cert]];
    combined = sumLeqFacts[chosen];
    sides = leqSidesOf[combined];
    normL = linNormConv[sides[[1]]];
    normR = linNormConv[sides[[2]]];
    cl = concl[normL][[2]]; cr = concl[normR][[2]];
    leqCanon = rewriteLeqRhs[rewriteLeqLhs[combined, normL], normR];
    lcLin = parseLin[cl]; rcLin = parseLin[cr];
    cL = lcLin[[1]]; cR = rcLin[[1]];
    If[lcLin[[2]] =!= rcLin[[2]] || ! (cL > cR),
      HOL`Error`holError["arith-farkas",
        "verifier: canonical sides not V+c with cL>cR (oracle bug)",
        <|"lhs" -> lcLin, "rhs" -> rcLin|>]];
    vLin = linTerm[0, lcLin[[2]]];
    If[Length[lcLin[[2]]] === 0,
      groundLeq = leqCanon,
      vTerm = buildLin[vLin];
      commL = commuteConstToRight[vLin, cL];
      commR = commuteConstToRight[vLin, cR];
      step2 = rewriteLeqLhs[leqCanon, commL];
      step3 = rewriteLeqRhs[step2, commR];
      cancel = HOL`Bool`SPEC[buildLitNum[cR], HOL`Bool`SPEC[buildLitNum[cL],
        HOL`Bool`SPEC[vTerm, HOL`Stdlib`Num`leqAddLeftCancelThm]]];
      groundLeq = HOL`Bool`MP[cancel, step3]
    ];
    glt = proveGroundLt[cR, cL];
    notLeqInst = HOL`Bool`SPEC[buildLitNum[cR], HOL`Bool`SPEC[buildLitNum[cL],
      HOL`Stdlib`Num`notLeqEqLtThm]];
    notLeq = EQMP[HOL`Equal`SYM[notLeqInst], glt];
    HOL`Bool`MP[HOL`Bool`NOTELIM[notLeq], groundLeq]
  ];

(* ============================================================ *)
(* arithProveForall — close a universally-quantified linear goal *)
(* ∀x₁…xₖ. H₁ ⇒ … ⇒ Hₘ ⇒ C (C and each Hⱼ an ℕ ≤/< atom) by     *)
(* assuming the Hⱼ and ¬C, Farkas-refuting to F, then            *)
(* CCONTR / DISCH / GEN to rebuild the universal.                *)
(* ============================================================ *)

peelForallNum[t_] :=
  If[MatchQ[t, comb[const["∀", _], abs[bvar[0, ty_], _, _String]]] &&
       t[[2, 1, 2]] === numTy,
    Module[{origin, opened, rec},
      origin = t[[2, 3]];
      opened = openBvar0[t[[2, 2]], origin];
      rec = peelForallNum[opened];
      {Prepend[rec[[1]], origin], rec[[2]]}
    ],
    {{}, t}
  ];

peelImp[t_] :=
  If[MatchQ[t, comb[comb[const["⇒", _], _], _]],
    Module[{rec}, rec = peelImp[t[[2]]];
      {Prepend[rec[[1]], t[[1, 2]]], rec[[2]]}],
    {{}, t}
  ];

(* ¬C ⊢ (the ≤-fact equivalent of ¬C). *)
negateConclFact[conclTm_] :=
  Module[{negC, assumed, sides, inst},
    negC = mkComb[notOp[], conclTm];
    assumed = HOL`Kernel`ASSUME[negC];
    sides = {conclTm[[1, 2]], conclTm[[2]]};
    Which[
      MatchQ[conclTm, comb[comb[const["≤", _], _], _]],
        inst = HOL`Bool`SPEC[sides[[2]], HOL`Bool`SPEC[sides[[1]],
          HOL`Stdlib`Num`notLeqEqLtThm]];
        toLeqFact[EQMP[inst, assumed]],
      MatchQ[conclTm, comb[comb[const["<", _], _], _]],
        inst = HOL`Bool`SPEC[sides[[2]], HOL`Bool`SPEC[sides[[1]],
          HOL`Stdlib`Num`notLtEqLeqThm]];
        toLeqFact[EQMP[inst, assumed]],
      True,
        HOL`Error`holError["arith-not-supported",
          "arithProveForall: conclusion not a ≤/< atom",
          <|"concl" -> conclTm|>]
    ]
  ];

arithProveForall[goalTm_] :=
  Module[{pf, varNames, body, pi, hypTms, conclTm, hypFacts, negFact,
          falseThm, cThm, dischd},
    pf = peelForallNum[goalTm];
    varNames = pf[[1]]; body = pf[[2]];
    pi = peelImp[body];
    hypTms = pi[[1]]; conclTm = pi[[2]];
    hypFacts = (toLeqFact[HOL`Kernel`ASSUME[#]] &) /@ hypTms;
    negFact = negateConclFact[conclTm];
    falseThm = farkasRefute[Append[hypFacts, negFact]];
    cThm = HOL`Bool`CCONTR[conclTm, falseThm];
    dischd = Fold[HOL`Bool`DISCH[#2, #1] &, cThm, Reverse[hypTms]];
    Fold[HOL`Bool`GEN[mkVar[#2, numTy], #1] &, dischd, Reverse[varNames]]
  ];

(* ============================================================ *)
(* Public entry points                                           *)
(*                                                              *)
(* arithProve[goalTm]   — closes ∃-SAT Presburger ℕ goals via    *)
(*                        Cooper QE + witness search + the       *)
(*                        ground-arithmetic provers. Other       *)
(*                        goal shapes (∀, mixed, non-Presburger) *)
(*                        throw `arith-not-supported` for now —  *)
(*                        ∀ requires the Cooper main theorem      *)
(*                        which is queued.                         *)
(*                                                              *)
(* ARITH[][goal]        — tactic wrapper. Calls arithProve on    *)
(*                        the goal's conclusion and closes the    *)
(*                        goal via tacResult.                     *)
(* ============================================================ *)

HOL`Auto`Arith`arithProve[goalTm_] :=
  Which[
    MatchQ[goalTm, comb[const["∀", _],
        abs[bvar[0, ty_], _, _String]]] &&
        goalTm[[2, 1, 2]] === numTy,
      arithProveForall[goalTm],
    MatchQ[goalTm, comb[const["∃", _],
        abs[bvar[0, ty_], _, _String]]] &&
        goalTm[[2, 1, 2]] === numTy,
      arithProveExists[goalTm],
    True,
      HOL`Error`holError["arith-not-supported",
        "arithProve: only ∀/∃ x:num. body goals are currently supported",
        <|"goal" -> goalTm|>]
  ];

HOL`Auto`Arith`ARITH[][g : HOL`Tactics`goal[asms_, conclTm_]] :=
  Module[{th},
    th = HOL`Auto`Arith`arithProve[conclTm];
    HOL`Tactics`tacResult[{}, Function[{thList}, th]]
  ];

End[];
EndPackage[];
