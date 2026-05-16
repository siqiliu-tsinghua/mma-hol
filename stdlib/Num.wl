(* ::Package:: *)

(* M7-3-a stdlib/Num — naturals from `ind` + INFINITY_AX (foundation slice).

   Steps in this file:
     1. IND_SUC : ind → ind, Hilbert-ε of (λf. ONE_ONE f ∧ ¬ ONTO f).
        Properties: ONE_ONE IND_SUC, ¬ ONTO IND_SUC.
     2. IND_0 : ind, Hilbert-ε of (λy. ¬ ∃x. y = IND_SUC x).
        Property: ¬ ∃x. IND_0 = IND_SUC x.

   NUM_REP, num type carving, 0/SUC, and induction defer to M7-3-b. *)

BeginPackage["HOL`Stdlib`Num`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`Simp`"
}];

indSuccConst::usage = "indSuccConst[] — IND_SUC : ind → ind, an injective non-onto function on ind picked from INFINITY_AX.";
ind0Const::usage    = "ind0Const[] — IND_0 : ind, an element not in the range of IND_SUC.";

indSuccDefThm::usage = "indSuccDefThm — ⊢ IND_SUC = (@ f:ind→ind. ONE_ONE f ∧ ¬ ONTO f).";
ind0DefThm::usage    = "ind0DefThm — ⊢ IND_0 = (@ y:ind. ¬ ∃x. y = IND_SUC x).";

indSuccPropThm::usage    = "indSuccPropThm — ⊢ ONE_ONE IND_SUC ∧ ¬ ONTO IND_SUC.";
indSuccOneOneThm::usage  = "indSuccOneOneThm — ⊢ ONE_ONE IND_SUC.";
indSuccNotOntoThm::usage = "indSuccNotOntoThm — ⊢ ¬ ONTO IND_SUC.";
ind0NotInRangeThm::usage = "ind0NotInRangeThm — ⊢ ¬ ∃x. IND_0 = IND_SUC x.";

numRepConst::usage = "numRepConst[] — NUM_REP : ind → bool, characterizes IND-encoded numerals.";
numRepDefThm::usage = "numRepDefThm — ⊢ NUM_REP = (λn. ∀P. P IND_0 ∧ (∀m. P m ⇒ P (IND_SUC m)) ⇒ P n).";
numRepIND0Witness::usage = "numRepIND0Witness — ⊢ (NUM_REP-body) IND_0; used as the witness for newBasicTypeDefinition.";
absRepNumThm::usage = "absRepNumThm — ⊢ ABS_num (REP_num a) = a (round-trip on num).";
repAbsNumThm::usage = "repAbsNumThm — ⊢ NUM_REP-body r = (REP_num (ABS_num r) = r).";

absNumConst::usage = "absNumConst[] — ABS_num : ind → num.";
repNumConst::usage = "repNumConst[] — REP_num : num → ind.";

zeroConst::usage = "zeroConst[] — 0 : num.";
zeroDefThm::usage = "zeroDefThm — ⊢ 0 = ABS_num IND_0.";

sucConst::usage = "sucConst[] — SUC : num → num.";
sucDefThm::usage = "sucDefThm — ⊢ SUC = (λn. ABS_num (IND_SUC (REP_num n))).";

selectOfExists::usage =
  "selectOfExists[predLambda, existsTh] — given a closed lambda " <>
  "predLambda = (λx. body) and a theorem existsTh : ⊢ ∃x. body, " <>
  "derive ⊢ body[(@predLambda)/x]. The standard `∃x.P x ⇒ P (@P)` " <>
  "chain — ISPEC selectAx at predLambda, SPEC at a fresh witness, " <>
  "beta-reduce, CHOOSE through MP.";

Begin["`Private`"];

indTy = mkType["ind", {}];
indFunTy = tyFun[indTy, indTy];
predTy[ty_] := tyFun[ty, boolTy];

andC[]       := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notC[]       := mkConst["¬", tyFun[boolTy, boolTy]];
forallC[ty_] := mkConst["∀", tyFun[predTy[ty], boolTy]];
existsC[ty_] := mkConst["∃", tyFun[predTy[ty], boolTy]];
selectC[ty_] := mkConst["@", tyFun[predTy[ty], ty]];

oneOneAt[a_, b_] := mkConst["ONE_ONE", tyFun[tyFun[a, b], boolTy]];
ontoAt[a_, b_]   := mkConst["ONTO", tyFun[tyFun[a, b], boolTy]];

destFunTypeLocal[tyApp["fun", {a_, b_}]] := {a, b};
destFunTypeLocal[other_] :=
  HOL`Error`holError["num", "destFunType: not a function type",
    <|"got" -> other|>];

(* ============================================================ *)
(* selectOfExists — `⊢ ∃x. P x  ⇒  ⊢ P (@P)`                     *)
(* ============================================================ *)

HOL`Stdlib`Num`selectOfExists[predLambda_, existsTh_] :=
  Module[{predDomTy, wV, specAxAtP, specAtW, specWBeta,
          hypTm, hypTh, mpStep},
    predDomTy = First[destFunTypeLocal[typeOf[predLambda]]];
    wV = mkVar["wChoose", predDomTy];
    specAxAtP = HOL`Bool`ISPEC[predLambda, HOL`Bootstrap`selectAx];
    specAtW = HOL`Bool`SPEC[wV, specAxAtP];
    specWBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]],
      specAtW];
    hypTm = concl[specWBeta][[1, 2]];
    hypTh = ASSUME[hypTm];
    mpStep = HOL`Bool`MP[specWBeta, hypTh];
    HOL`Bool`CHOOSE[wV, existsTh, mpStep]
  ];

(* ============================================================ *)
(* IND_SUC = ε f:ind→ind. ONE_ONE f ∧ ¬ ONTO f                   *)
(* ============================================================ *)

infinitePredBody[] :=
  Module[{fV, oneOneAppl, ontoAppl, body},
    fV = mkVar["f", indFunTy];
    oneOneAppl = mkComb[oneOneAt[indTy, indTy], fV];
    ontoAppl   = mkComb[ontoAt[indTy, indTy], fV];
    body = mkComb[mkComb[andC[], oneOneAppl],
                  mkComb[notC[], ontoAppl]];
    mkAbs[fV, body]
  ];

indSuccDefThm = newDefinition[mkEq[
  mkVar["IND_SUC", indFunTy],
  mkComb[selectC[indFunTy], infinitePredBody[]]
]];

indSuccConst[] := mkConst["IND_SUC", indFunTy];

(* atPredTh : ⊢ ONE_ONE (@P) ∧ ¬ ONTO (@P)  where P = infinitePredBody. *)
(* unfoldThm : ⊢ @P = IND_SUC. *)
(* Combine via APTERM/MKCOMB into the matching equation, then EQMP. *)

indSuccPropThm =
  Module[{predLam, atPredTh, unfoldThm,
          oneOneEq, ontoEq, notOntoEq, andLeftEq, fullEq,
          oneOneTm, ontoTm, notTm, andTm},
    predLam = infinitePredBody[];
    atPredTh = HOL`Stdlib`Num`selectOfExists[predLam, HOL`Bootstrap`infinityAx];
    unfoldThm = HOL`Equal`SYM[indSuccDefThm];

    oneOneTm = oneOneAt[indTy, indTy];
    ontoTm   = ontoAt[indTy, indTy];
    notTm    = notC[];
    andTm    = andC[];

    oneOneEq  = HOL`Equal`APTERM[oneOneTm, unfoldThm];
    ontoEq    = HOL`Equal`APTERM[ontoTm,   unfoldThm];
    notOntoEq = HOL`Equal`APTERM[notTm,    ontoEq];
    andLeftEq = HOL`Equal`APTERM[andTm,    oneOneEq];
    fullEq    = HOL`Kernel`MKCOMB[andLeftEq, notOntoEq];

    EQMP[fullEq, atPredTh]
  ];

indSuccOneOneThm  = HOL`Bool`CONJUNCT1[indSuccPropThm];
indSuccNotOntoThm = HOL`Bool`CONJUNCT2[indSuccPropThm];

(* ============================================================ *)
(* Unfold ¬ ONTO IND_SUC to ¬ (∀y. ∃x. y = IND_SUC x).            *)
(* ============================================================ *)

(* ontoDef is polymorphic — INSTTYPE to a := ind, b := ind first. *)
ontoDefAtInd =
  Module[{c, ontoTm, aTy, bTy},
    c = concl[HOL`Bootstrap`ontoDef];
    ontoTm = c[[1, 2]];
    {aTy, bTy} = destFunTypeLocal[First[destFunTypeLocal[typeOf[ontoTm]]]];
    HOL`Kernel`INSTTYPE[{aTy -> indTy, bTy -> indTy}, HOL`Bootstrap`ontoDef]
  ];

notOntoUnfoldedThm =
  Module[{indSucTm, afterEq, afterEqRhs, afterBeta, finalEq, finalTh},
    indSucTm = indSuccConst[];
    afterEq = HOL`Equal`APTHM[ontoDefAtInd, indSucTm];
    afterEqRhs = concl[afterEq][[2]];
    afterBeta = BETACONV[afterEqRhs];
    finalEq = TRANS[afterEq, afterBeta];
    finalTh = HOL`Equal`APTERM[notC[], finalEq];
    EQMP[finalTh, indSuccNotOntoThm]
  ];

(* ============================================================ *)
(* From ⊢ ¬ ∀y. pY y, derive ⊢ ∃y. ¬ pY y,                        *)
(*   where pY = λy. ∃x. y = IND_SUC x.                            *)
(* CCONTR-based one-off derivation specific to this predicate.    *)
(* ============================================================ *)

(* Work strictly with the β-normal predicate body `∃x. y = IND_SUC x`. *)
(* Building notPyAtY as `¬ (pY y)` would leave a β-redex inside        *)
(* `∃y. ¬ pY y`, which then breaks CHOOSE downstream.                   *)
Module[{yV, xV, pyBody, pY,
        forallPYTm, notForallPYTm, hypNotForall,
        notPyAtY, existsNotPYTm, notExistsNotPYTm, hypNotExistsNotPY,
        exNotPyFromY, contradWithExists, pyAtY,
        derivedForallPY, contradOuter, dischExt, notForallToExNot},

  yV = mkVar["y", indTy];
  xV = mkVar["x", indTy];

  pyBody = mkComb[existsC[indTy],
    mkAbs[xV, mkEq[yV, mkComb[indSuccConst[], xV]]]];
  pY = mkAbs[yV, pyBody];

  forallPYTm    = mkComb[forallC[indTy], pY];
  notForallPYTm = mkComb[notC[], forallPYTm];
  hypNotForall  = ASSUME[notForallPYTm];

  notPyAtY         = mkComb[notC[], pyBody];
  existsNotPYTm    = mkComb[existsC[indTy], mkAbs[yV, notPyAtY]];
  notExistsNotPYTm = mkComb[notC[], existsNotPYTm];
  hypNotExistsNotPY = ASSUME[notExistsNotPYTm];

  exNotPyFromY = HOL`Bool`EXISTS[existsNotPYTm, yV, ASSUME[notPyAtY]];
  contradWithExists = HOL`Bool`MP[
    HOL`Bool`NOTELIM[hypNotExistsNotPY], exNotPyFromY];
  pyAtY = HOL`Bool`CCONTR[pyBody, contradWithExists];

  derivedForallPY = HOL`Bool`GEN[yV, pyAtY];
  contradOuter = HOL`Bool`MP[
    HOL`Bool`NOTELIM[hypNotForall], derivedForallPY];
  dischExt = HOL`Bool`CCONTR[existsNotPYTm, contradOuter];

  notForallToExNot = HOL`Bool`DISCH[notForallPYTm, dischExt];

  notInRangeExistsThm = HOL`Bool`MP[notForallToExNot, notOntoUnfoldedThm];

  notInRangeBodyVal = mkAbs[yV, notPyAtY];
];

(* ============================================================ *)
(* IND_0 = ε y. ¬ ∃x. y = IND_SUC x                               *)
(* ============================================================ *)

ind0DefThm = newDefinition[mkEq[
  mkVar["IND_0", indTy],
  mkComb[selectC[indTy], notInRangeBodyVal]
]];

ind0Const[] := mkConst["IND_0", indTy];

(* atPredTh : ⊢ ¬ ∃x. (@notInRangeBodyVal) = IND_SUC x.                *)
(* unfoldThm : ⊢ @notInRangeBodyVal = IND_0.                            *)
(* Lift the substitution under the ∃-binder via ABS and EQMP it through.*)
ind0NotInRangeThm =
  Module[{atPredTh, unfoldThm, xV2, indSucxV2, eqOnEq, absEq,
          existsEq, notEq, eqConstAtInd},
    atPredTh = HOL`Stdlib`Num`selectOfExists[
      notInRangeBodyVal, notInRangeExistsThm];
    unfoldThm = HOL`Equal`SYM[ind0DefThm];
    xV2 = mkVar["x", indTy];
    indSucxV2 = mkComb[indSuccConst[], xV2];
    eqConstAtInd = mkConst["=", tyFun[indTy, tyFun[indTy, boolTy]]];
    eqOnEq = HOL`Kernel`MKCOMB[
      HOL`Equal`APTERM[eqConstAtInd, unfoldThm],
      REFL[indSucxV2]];
    absEq = HOL`Kernel`ABS[xV2, eqOnEq];
    existsEq = HOL`Equal`APTERM[existsC[indTy], absEq];
    notEq = HOL`Equal`APTERM[notC[], existsEq];
    EQMP[notEq, atPredTh]
  ];

(* ============================================================ *)
(* NUM_REP : ind → bool — smallest predicate containing IND_0   *)
(* and closed under IND_SUC.                                    *)
(*   NUM_REP n = ∀P. P IND_0 ∧ (∀m. P m ⇒ P (IND_SUC m)) ⇒ P n  *)
(* ============================================================ *)

andTm[a_, b_] := mkComb[mkComb[andC[], a], b];
impTm[a_, b_] :=
  mkComb[mkComb[mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]], a], b];

(* λn:ind. ∀P. P IND_0 ∧ (∀m. P m ⇒ P (IND_SUC m)) ⇒ P n *)
numRepPredicateBody[] :=
  Module[{nV, pV, mV, predTyInd, pIND0, pM, pSucM, stepImp,
          stepForall, conjBody, pN, impBody, outerForall},
    nV = mkVar["n", indTy];
    pV = mkVar["P", predTy[indTy]];
    mV = mkVar["m", indTy];
    pIND0  = mkComb[pV, ind0Const[]];
    pM     = mkComb[pV, mV];
    pSucM  = mkComb[pV, mkComb[indSuccConst[], mV]];
    stepImp    = impTm[pM, pSucM];
    stepForall = mkComb[forallC[indTy], mkAbs[mV, stepImp]];
    conjBody   = andTm[pIND0, stepForall];
    pN         = mkComb[pV, nV];
    impBody    = impTm[conjBody, pN];
    outerForall = mkComb[forallC[predTy[indTy]], mkAbs[pV, impBody]];
    mkAbs[nV, outerForall]
  ];

numRepDefThm = newDefinition[mkEq[
  mkVar["NUM_REP", predTy[indTy]],
  numRepPredicateBody[]
]];

numRepConst[] := mkConst["NUM_REP", predTy[indTy]];

(* Witness theorem for newBasicTypeDefinition:                 *)
(* ⊢ (numRepPredicateBody) IND_0                                *)
(* Proof: under the ∀P-body, ASSUME the antecedent, CONJUNCT1   *)
(* gives ⊢ P IND_0; DISCH, GEN P. Then un-beta the predicate    *)
(* application to fit newBasicTypeDefinition's `P x` shape.     *)
numRepIND0Witness =
  Module[{pV, mV, pIND0, pM, pSucM, stepImp, stepForall,
          conjBody, assumeConj, conj1, dischTh, genTh,
          predLam, predApplied, betaTh},
    pV = mkVar["P", predTy[indTy]];
    mV = mkVar["m", indTy];
    pIND0  = mkComb[pV, ind0Const[]];
    pM     = mkComb[pV, mV];
    pSucM  = mkComb[pV, mkComb[indSuccConst[], mV]];
    stepImp    = impTm[pM, pSucM];
    stepForall = mkComb[forallC[indTy], mkAbs[mV, stepImp]];
    conjBody   = andTm[pIND0, stepForall];
    assumeConj = ASSUME[conjBody];
    conj1      = HOL`Bool`CONJUNCT1[assumeConj];
    dischTh    = HOL`Bool`DISCH[conjBody, conj1];
    genTh      = HOL`Bool`GEN[pV, dischTh];
    (* genTh : ⊢ ∀P. P IND_0 ∧ … ⇒ P IND_0                       *)
    predLam = numRepPredicateBody[];
    predApplied = mkComb[predLam, ind0Const[]];
    betaTh = BETACONV[predApplied];
    (* betaTh : ⊢ predLam IND_0 = ∀P. … ⇒ P IND_0                *)
    EQMP[HOL`Equal`SYM[betaTh], genTh]
  ];

(* ============================================================ *)
(* num type via newBasicTypeDefinition                          *)
(* ============================================================ *)

{absRepNumThm, repAbsNumThm} =
  newBasicTypeDefinition["num", "ABS_num", "REP_num", numRepIND0Witness];

numTy = mkType["num", {}];
absNumConst[] := mkConst["ABS_num", tyFun[indTy, numTy]];
repNumConst[] := mkConst["REP_num", tyFun[numTy, indTy]];

(* ============================================================ *)
(* 0 : num  and  SUC : num → num                                *)
(* ============================================================ *)

zeroDefThm = newDefinition[mkEq[
  mkVar["0", numTy],
  mkComb[absNumConst[], ind0Const[]]
]];

zeroConst[] := mkConst["0", numTy];

sucDefThm =
  Module[{nV, sucBody},
    nV = mkVar["n", numTy];
    sucBody = mkAbs[nV,
      mkComb[absNumConst[],
        mkComb[indSuccConst[], mkComb[repNumConst[], nV]]]];
    newDefinition[mkEq[
      mkVar["SUC", tyFun[numTy, numTy]],
      sucBody]]
  ];

sucConst[] := mkConst["SUC", tyFun[numTy, numTy]];

End[];
EndPackage[];
