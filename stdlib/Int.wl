(* ::Package:: *)

(* M7-5 / stdlib/Int.wl — ℤ via canonical representatives.

   int is carved from num × num by the predicate
       INT_REP = λp. FST p = 0 ∨ SND p = 0,
   so a representative (a, b) stands for the integer a − b, and the
   canonical reps are exactly (n, 0) [= +n] and (0, n) [= −n].

   Stage a (this file, so far): the type itself — INT_REP, the
   newBasicTypeDefinition carve, ABS_int / REP_int and the round-trip
   theorems. Operations (canon, &ℤ, neg/succ/pred, +, *, order,
   embedding, bidirectional induction) build on top in later stages. *)

BeginPackage["HOL`Stdlib`Int`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Auto`Arith`"
}];

intRepConst::usage  = "intRepConst[] — INT_REP : num × num → bool, the carving predicate λp. FST p = 0 ∨ SND p = 0.";
intRepDefThm::usage = "intRepDefThm — ⊢ INT_REP = (λp. FST p = 0 ∨ SND p = 0).";
intRepZeroPairThm::usage = "intRepZeroPairThm — ⊢ INT_REP (0, 0). Witness for the type definition.";
intTy::usage        = "intTy — the int type (tyApp[\"int\", {}]).";
absIntConst::usage  = "absIntConst[] — ABS_int : num × num → int.";
repIntConst::usage  = "repIntConst[] — REP_int : int → num × num.";
absRepIntThm::usage = "absRepIntThm — ⊢ ABS_int (REP_int a) = a (round-trip on int).";
repAbsIntThm::usage = "repAbsIntThm — ⊢ INT_REP r = (REP_int (ABS_int r) = r).";

Begin["`Private`"];

numTy = mkType["num", {}];
zeroN[] := HOL`Stdlib`Num`zeroConst[];
numPairTy = HOL`Stdlib`Pair`prodTy[numTy, numTy];
intRepTy = tyFun[numPairTy, boolTy];

(* local ∨ builder (Num's orTm is in another file's Private) *)
orC[] := mkConst["∨", tyFun[boolTy, tyFun[boolTy, boolTy]]];
orTm[a_, b_] := mkComb[mkComb[orC[], a], b];

fstNum[] := mkConst["FST", tyFun[numPairTy, numTy]];
sndNum[] := mkConst["SND", tyFun[numPairTy, numTy]];

(* the `,` constructor at the concrete num × num type *)
numPairCons[a_, b_] :=
  mkComb[mkComb[mkConst[",", tyFun[numTy, tyFun[numTy, numPairTy]]], a], b];

(* INT_REP = λp. FST p = 0 ∨ SND p = 0 *)
intRepBody[] :=
  Module[{pV},
    pV = mkVar["p", numPairTy];
    mkAbs[pV, orTm[mkEq[mkComb[fstNum[], pV], zeroN[]],
                   mkEq[mkComb[sndNum[], pV], zeroN[]]]]
  ];

intRepDefThm = newDefinition[mkEq[mkVar["INT_REP", intRepTy], intRepBody[]]];

intRepConst[] := mkConst["INT_REP", intRepTy];

(* ⊢ INT_REP pTm = (FST pTm = 0 ∨ SND pTm = 0) *)
unfoldIntRep[pTm_] :=
  Module[{ap},
    ap = HOL`Equal`APTHM[intRepDefThm, pTm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]
  ];

(* ⊢ FST (0, 0) = 0 by instantiating fstPairEqThm to num × num. *)
fstZeroZeroThm =
  Module[{instTy, instAB},
    instTy = HOL`Kernel`INSTTYPE[
      {mkVarType["A"] -> numTy, mkVarType["B"] -> numTy},
      HOL`Stdlib`Pair`fstPairEqThm];
    HOL`Kernel`INST[
      {mkVar["a", numTy] -> zeroN[], mkVar["b", numTy] -> zeroN[]},
      instTy]
  ];

(* ⊢ INT_REP (0, 0) — the witness, via the FST-disjunct. *)
intRepZeroPairThm =
  Module[{zeroPair, sndEqTm, disjThm},
    zeroPair = numPairCons[zeroN[], zeroN[]];
    sndEqTm = mkEq[mkComb[sndNum[], zeroPair], zeroN[]];
    disjThm = HOL`Bool`DISJ1[fstZeroZeroThm, sndEqTm];
    (* ⊢ FST (0,0) = 0 ∨ SND (0,0) = 0 *)
    EQMP[HOL`Equal`SYM[unfoldIntRep[zeroPair]], disjThm]
  ];

(* ============================================================ *)
(* int type via newBasicTypeDefinition                          *)
(* ============================================================ *)

{absRepIntThm, repAbsIntThm} =
  newBasicTypeDefinition["int", "ABS_int", "REP_int", intRepZeroPairThm];

intTy = mkType["int", {}];
absIntConst[] := mkConst["ABS_int", tyFun[numPairTy, intTy]];
repIntConst[] := mkConst["REP_int", tyFun[intTy, numPairTy]];

End[];
EndPackage[];
