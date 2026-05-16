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

numRepInd0Thm::usage = "numRepInd0Thm — ⊢ NUM_REP IND_0.";
numRepSucThm::usage = "numRepSucThm — ⊢ ∀m. NUM_REP m ⇒ NUM_REP (IND_SUC m).";
numRepRepNumThm::usage = "numRepRepNumThm — ⊢ NUM_REP (REP_num n) (n : num free).";
repZeroThm::usage = "repZeroThm — ⊢ REP_num 0 = IND_0.";
repSucThm::usage = "repSucThm — ⊢ REP_num (SUC n) = IND_SUC (REP_num n) (n : num free).";
sucNotZeroThm::usage = "sucNotZeroThm — ⊢ ∀n. ¬ (SUC n = 0).";
sucInjThm::usage = "sucInjThm — ⊢ ∀m n. SUC m = SUC n ⇒ m = n.";
numInductionThm::usage = "numInductionThm — ⊢ ∀P. P 0 ∧ (∀n. P n ⇒ P (SUC n)) ⇒ ∀n. P n.";

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

(* ============================================================ *)
(* Helpers for unfolding / folding NUM_REP                      *)
(* ============================================================ *)

(* `⊢ NUM_REP t = ∀P. P IND_0 ∧ (∀m. P m ⇒ P (IND_SUC m)) ⇒ P t` *)
unfoldNumRep[t_] :=
  Module[{step1, step2},
    step1 = HOL`Equal`APTHM[numRepDefThm, t];
    step2 = BETACONV[concl[step1][[2]]];
    TRANS[step1, step2]
  ];

(* ============================================================ *)
(* numRepInd0Thm : ⊢ NUM_REP IND_0                              *)
(* ============================================================ *)

numRepInd0Thm =
  Module[{reducedWitness, unfoldEq},
    reducedWitness = HOL`Drule`CONVRULE[BETACONV, numRepIND0Witness];
    unfoldEq = unfoldNumRep[ind0Const[]];
    EQMP[HOL`Equal`SYM[unfoldEq], reducedWitness]
  ];

(* ============================================================ *)
(* numRepSucThm : ⊢ ∀m. NUM_REP m ⇒ NUM_REP (IND_SUC m)         *)
(* ============================================================ *)

numRepSucThm =
  Module[{mV, pV, indSucMTm, assumeNumRepM, unfoldedAtM,
          pIND0, pSucMV, pMV, stepImp, stepForall, conjBody,
          assumeConj, conj1, conj2, specPunfolded, mpFromUnfolded,
          specMV, mpStep, dischConj, genP, foldEq, foldedSuc,
          dischNumRepM, finalGen, mV2},
    mV = mkVar["m", indTy];
    pV = mkVar["P", predTy[indTy]];
    mV2 = mkVar["m", indTy];   (* same name; bound below in stepForall *)
    indSucMTm = mkComb[indSuccConst[], mV];

    assumeNumRepM = ASSUME[mkComb[numRepConst[], mV]];
    unfoldedAtM = EQMP[unfoldNumRep[mV], assumeNumRepM];
    (* unfoldedAtM : (NUM_REP m) ⊢ ∀P. P IND_0 ∧ (∀m'. P m' ⇒ P (IND_SUC m')) ⇒ P m *)

    pIND0   = mkComb[pV, ind0Const[]];
    pMV     = mkComb[pV, mV2];
    pSucMV  = mkComb[pV, mkComb[indSuccConst[], mV2]];
    stepImp    = impTm[pMV, pSucMV];
    stepForall = mkComb[forallC[indTy], mkAbs[mV2, stepImp]];
    conjBody   = andTm[pIND0, stepForall];

    assumeConj = ASSUME[conjBody];
    conj1 = HOL`Bool`CONJUNCT1[assumeConj];   (* (conj) ⊢ P IND_0 *)
    conj2 = HOL`Bool`CONJUNCT2[assumeConj];   (* (conj) ⊢ ∀m'. P m' ⇒ P (IND_SUC m') *)

    specPunfolded = HOL`Bool`SPEC[pV, unfoldedAtM];
    (* (NUM_REP m) ⊢ (P IND_0 ∧ ∀m'. P m' ⇒ P (IND_SUC m')) ⇒ P m *)
    mpFromUnfolded = HOL`Bool`MP[specPunfolded, assumeConj];
    (* (NUM_REP m, conj) ⊢ P m *)

    specMV = HOL`Bool`SPEC[mV, conj2];
    (* (conj) ⊢ P m ⇒ P (IND_SUC m) *)
    mpStep = HOL`Bool`MP[specMV, mpFromUnfolded];
    (* (NUM_REP m, conj) ⊢ P (IND_SUC m) *)

    dischConj = HOL`Bool`DISCH[conjBody, mpStep];
    (* (NUM_REP m) ⊢ conj ⇒ P (IND_SUC m) *)
    genP = HOL`Bool`GEN[pV, dischConj];
    (* (NUM_REP m) ⊢ ∀P. conj ⇒ P (IND_SUC m) *)

    foldEq = unfoldNumRep[indSucMTm];
    foldedSuc = EQMP[HOL`Equal`SYM[foldEq], genP];
    (* (NUM_REP m) ⊢ NUM_REP (IND_SUC m) *)

    dischNumRepM = HOL`Bool`DISCH[mkComb[numRepConst[], mV], foldedSuc];
    finalGen = HOL`Bool`GEN[mV, dischNumRepM]
  ];

(* ============================================================ *)
(* numRepRepNumThm : ⊢ NUM_REP (REP_num n) (n : num free)       *)
(* Strategy: absRepNumThm gives ABS_num (REP_num n) = n;        *)
(* APTERM REP_num on both sides gives REP_num (ABS_num x) = x   *)
(* with x = REP_num n. Use repAbsNumThm (INST r := REP_num n)   *)
(* in reverse to get (NUM_REP-body)(REP_num n); fold.           *)
(* ============================================================ *)

numRepRepNumThm =
  Module[{nV, repNV, absRepAtN, apThm1, repAbsAtRepN, body, reduced,
          unfoldEq},
    nV = mkVar["n", numTy];
    repNV = mkComb[repNumConst[], nV];
    absRepAtN = HOL`Kernel`INST[{mkVar["a", numTy] -> nV}, absRepNumThm];
    apThm1 = HOL`Equal`APTERM[repNumConst[], absRepAtN];
    (* ⊢ REP_num (ABS_num (REP_num n)) = REP_num n *)
    repAbsAtRepN = HOL`Kernel`INST[{mkVar["r", indTy] -> repNV}, repAbsNumThm];
    (* ⊢ (numRepBody) (REP_num n) = (REP_num (ABS_num (REP_num n)) = REP_num n) *)
    body = EQMP[HOL`Equal`SYM[repAbsAtRepN], apThm1];
    (* ⊢ (numRepBody) (REP_num n) (un-β) *)
    reduced = HOL`Drule`CONVRULE[BETACONV, body];
    unfoldEq = unfoldNumRep[repNV];
    EQMP[HOL`Equal`SYM[unfoldEq], reduced]
  ];

(* ============================================================ *)
(* repZeroThm : ⊢ REP_num 0 = IND_0                              *)
(* ============================================================ *)

repZeroThm =
  Module[{ap1, repAbsAtInd0, bodyAtInd0, reduced,
          numRepBodyAtInd0, eqRep, repEqRep},
    (* APTERM REP_num on zeroDefThm. *)
    ap1 = HOL`Equal`APTERM[repNumConst[], zeroDefThm];
    (* ⊢ REP_num 0 = REP_num (ABS_num IND_0) *)
    (* numRepInd0Thm : ⊢ NUM_REP IND_0; unfold to (numRepBody) IND_0 (un-β). *)
    numRepBodyAtInd0 = EQMP[unfoldNumRep[ind0Const[]], numRepInd0Thm];
    (* ⊢ ∀P. … ⇒ P IND_0 — but we want the un-β form for repAbsNumThm. *)
    (* repAbsNumThm INSTd r → IND_0 expects un-β LHS; re-unbeta:         *)
    bodyAtInd0 =
      Module[{predBody, predApplied, betaEq},
        predBody = numRepPredicateBody[];
        predApplied = mkComb[predBody, ind0Const[]];
        betaEq = BETACONV[predApplied];
        EQMP[HOL`Equal`SYM[betaEq], numRepBodyAtInd0]
      ];
    (* bodyAtInd0 : ⊢ (numRepBody) IND_0 *)
    repAbsAtInd0 = HOL`Kernel`INST[
      {mkVar["r", indTy] -> ind0Const[]}, repAbsNumThm];
    (* ⊢ (numRepBody) IND_0 = (REP_num (ABS_num IND_0) = IND_0) *)
    repEqRep = EQMP[repAbsAtInd0, bodyAtInd0];
    (* ⊢ REP_num (ABS_num IND_0) = IND_0 *)
    TRANS[ap1, repEqRep]
  ];

(* ============================================================ *)
(* repSucThm : ⊢ REP_num (SUC n) = IND_SUC (REP_num n)           *)
(* ============================================================ *)

repSucThm =
  Module[{nV, repNV, indSucRepN, sucAtN, sucAtNBeta, sucEq, ap1,
          numRepSucRepN, numRepInstSpecN, numRepImp,
          numRepIndSucRepN, bodyAtIndSucRepN, predBody, predApplied,
          betaEq, repAbsAtIndSucRepN, repEqIndSucRepN},
    nV = mkVar["n", numTy];
    repNV = mkComb[repNumConst[], nV];
    indSucRepN = mkComb[indSuccConst[], repNV];

    (* SUC n = ABS_num (IND_SUC (REP_num n)) *)
    sucAtN = HOL`Equal`APTHM[sucDefThm, nV];
    sucAtNBeta = BETACONV[concl[sucAtN][[2]]];
    sucEq = TRANS[sucAtN, sucAtNBeta];
    (* ⊢ SUC n = ABS_num (IND_SUC (REP_num n)) *)
    ap1 = HOL`Equal`APTERM[repNumConst[], sucEq];
    (* ⊢ REP_num (SUC n) = REP_num (ABS_num (IND_SUC (REP_num n))) *)

    (* NUM_REP (REP_num n) → NUM_REP (IND_SUC (REP_num n)) via numRepSucThm *)
    numRepInstSpecN = HOL`Bool`SPEC[repNV, numRepSucThm];
    (* ⊢ NUM_REP (REP_num n) ⇒ NUM_REP (IND_SUC (REP_num n)) *)
    numRepIndSucRepN = HOL`Bool`MP[numRepInstSpecN, numRepRepNumThm];
    (* ⊢ NUM_REP (IND_SUC (REP_num n)) *)

    (* Re-unbeta to (numRepBody) (IND_SUC (REP_num n)) for repAbsNumThm. *)
    predBody = numRepPredicateBody[];
    predApplied = mkComb[predBody, indSucRepN];
    betaEq = BETACONV[predApplied];
    bodyAtIndSucRepN = EQMP[HOL`Equal`SYM[betaEq],
      EQMP[unfoldNumRep[indSucRepN], numRepIndSucRepN]];
    repAbsAtIndSucRepN = HOL`Kernel`INST[
      {mkVar["r", indTy] -> indSucRepN}, repAbsNumThm];
    repEqIndSucRepN = EQMP[repAbsAtIndSucRepN, bodyAtIndSucRepN];
    (* ⊢ REP_num (ABS_num (IND_SUC (REP_num n))) = IND_SUC (REP_num n) *)
    TRANS[ap1, repEqIndSucRepN]
  ];

(* ============================================================ *)
(* sucNotZeroThm : ⊢ ∀n. ¬ (SUC n = 0)                           *)
(* ============================================================ *)

sucNotZeroThm =
  Module[{nV, repNV, sucEq0, ap1, chain1, chain2,
          existsIndSuc, repZeroAt, indNotInRangeInstSym,
          indNotInRange, mpContra, contradTh, dischImp,
          notTh, genN, eqInner, exTm, nNotInRangeInst},
    nV = mkVar["n", numTy];
    repNV = mkComb[repNumConst[], nV];
    sucEq0 = mkEq[mkComb[sucConst[], nV], zeroConst[]];

    (* Assume SUC n = 0; derive F. *)
    Module[{hyp, repEq, viaSuc, viaZero},
      hyp = ASSUME[sucEq0];
      repEq = HOL`Equal`APTERM[repNumConst[], hyp];
      (* (SUC n = 0) ⊢ REP_num (SUC n) = REP_num 0 *)
      viaSuc  = HOL`Equal`SYM[repSucThm];
      (* ⊢ IND_SUC (REP_num n) = REP_num (SUC n) *)
      viaZero = repZeroThm;
      (* ⊢ REP_num 0 = IND_0 *)
      chain1 = TRANS[viaSuc, repEq];
      (* (SUC n = 0) ⊢ IND_SUC (REP_num n) = REP_num 0 *)
      chain2 = TRANS[chain1, viaZero];
      (* (SUC n = 0) ⊢ IND_SUC (REP_num n) = IND_0 *)
      (* Convert to IND_0 = IND_SUC (REP_num n) for ind0NotInRangeThm. *)
      chain2 = HOL`Equal`SYM[chain2];

      eqInner = mkEq[ind0Const[], mkComb[indSuccConst[], mkVar["x", indTy]]];
      exTm = mkComb[existsC[indTy],
        mkAbs[mkVar["x", indTy], eqInner]];
      existsIndSuc = HOL`Bool`EXISTS[exTm, repNV, chain2];
      (* (SUC n = 0) ⊢ ∃x. IND_0 = IND_SUC x *)
      mpContra = HOL`Bool`MP[
        HOL`Bool`NOTELIM[ind0NotInRangeThm], existsIndSuc];
      (* (SUC n = 0) ⊢ F *)
      contradTh = mpContra;
    ];

    dischImp = HOL`Bool`DISCH[sucEq0, contradTh];
    (* ⊢ (SUC n = 0) ⇒ F *)
    notTh = HOL`Bool`NOTINTRO[dischImp];
    (* ⊢ ¬ (SUC n = 0) *)
    HOL`Bool`GEN[nV, notTh]
  ];

(* ============================================================ *)
(* sucInjThm : ⊢ ∀m n. SUC m = SUC n ⇒ m = n                     *)
(* ============================================================ *)

(* Helper: unfold ONE_ONE IND_SUC to ∀x y. IND_SUC x = IND_SUC y ⇒ x = y *)
oneOneDefAtInd =
  Module[{c, oneOneTm, aTy, bTy},
    c = concl[HOL`Bootstrap`oneOneDef];
    oneOneTm = c[[1, 2]];
    {aTy, bTy} = destFunTypeLocal[First[destFunTypeLocal[typeOf[oneOneTm]]]];
    HOL`Kernel`INSTTYPE[{aTy -> indTy, bTy -> indTy}, HOL`Bootstrap`oneOneDef]
  ];

indSuccOneOneUnfoldedThm =
  Module[{indSucTm, afterEq, afterBeta, finalEq},
    indSucTm = indSuccConst[];
    afterEq = HOL`Equal`APTHM[oneOneDefAtInd, indSucTm];
    afterBeta = BETACONV[concl[afterEq][[2]]];
    finalEq = TRANS[afterEq, afterBeta];
    (* ⊢ ONE_ONE IND_SUC = ∀x y. IND_SUC x = IND_SUC y ⇒ x = y *)
    EQMP[finalEq, indSuccOneOneThm]
  ];

sucInjThm =
  Module[{mV, nV, sucMEqSucN, repMV, repNV, hyp, repEq, chainLeft,
          chainRight, indEq, oneOneSpec1, oneOneSpec2, repMnEq,
          ap1, sym1, mEqAbsRepN, absRepAtN, mEqN, dischImp,
          genN, genM},
    mV = mkVar["m", numTy];
    nV = mkVar["n", numTy];
    repMV = mkComb[repNumConst[], mV];
    repNV = mkComb[repNumConst[], nV];
    sucMEqSucN = mkEq[mkComb[sucConst[], mV], mkComb[sucConst[], nV]];

    hyp = ASSUME[sucMEqSucN];
    repEq = HOL`Equal`APTERM[repNumConst[], hyp];
    (* (SUC m = SUC n) ⊢ REP_num (SUC m) = REP_num (SUC n) *)
    chainLeft = HOL`Equal`SYM[
      HOL`Kernel`INST[{mkVar["n", numTy] -> mV}, repSucThm]];
    (* ⊢ IND_SUC (REP_num m) = REP_num (SUC m) *)
    chainRight = HOL`Kernel`INST[{mkVar["n", numTy] -> nV}, repSucThm];
    (* ⊢ REP_num (SUC n) = IND_SUC (REP_num n) *)
    indEq = TRANS[TRANS[chainLeft, repEq], chainRight];
    (* (SUC m = SUC n) ⊢ IND_SUC (REP_num m) = IND_SUC (REP_num n) *)

    oneOneSpec1 = HOL`Bool`SPEC[repMV, indSuccOneOneUnfoldedThm];
    (* ⊢ ∀y. IND_SUC (REP_num m) = IND_SUC y ⇒ REP_num m = y *)
    oneOneSpec2 = HOL`Bool`SPEC[repNV, oneOneSpec1];
    (* ⊢ IND_SUC (REP_num m) = IND_SUC (REP_num n) ⇒ REP_num m = REP_num n *)
    repMnEq = HOL`Bool`MP[oneOneSpec2, indEq];
    (* (SUC m = SUC n) ⊢ REP_num m = REP_num n *)

    ap1 = HOL`Equal`APTERM[absNumConst[], repMnEq];
    (* (SUC m = SUC n) ⊢ ABS_num (REP_num m) = ABS_num (REP_num n) *)
    sym1 = HOL`Equal`SYM[
      HOL`Kernel`INST[{mkVar["a", numTy] -> mV}, absRepNumThm]];
    (* ⊢ m = ABS_num (REP_num m) *)
    mEqAbsRepN = TRANS[sym1, ap1];
    (* (SUC m = SUC n) ⊢ m = ABS_num (REP_num n) *)
    absRepAtN = HOL`Kernel`INST[{mkVar["a", numTy] -> nV}, absRepNumThm];
    (* ⊢ ABS_num (REP_num n) = n *)
    mEqN = TRANS[mEqAbsRepN, absRepAtN];
    (* (SUC m = SUC n) ⊢ m = n *)

    dischImp = HOL`Bool`DISCH[sucMEqSucN, mEqN];
    genN = HOL`Bool`GEN[nV, dischImp];
    genM = HOL`Bool`GEN[mV, genN]
  ];

(* ============================================================ *)
(* numInductionThm : ⊢ ∀P. P 0 ∧ (∀n. P n ⇒ P (SUC n)) ⇒ ∀n. P n *)
(*                                                              *)
(* Lift P : num → bool to Q : ind → bool defined as              *)
(*   Q i = NUM_REP i ∧ P (ABS_num i).                            *)
(* Then (1) Q IND_0 follows from numRepInd0Thm + P 0 + zeroDef;  *)
(* (2) Q m ⇒ Q (IND_SUC m) needs numRepSucThm + the induction   *)
(* step instantiated at ABS_num m + the equality                 *)
(*   ABS_num (IND_SUC m) = SUC (ABS_num m) (under NUM_REP m).    *)
(* So NUM_REP m ⊢ ∀P. … ⇒ Q m; specialise at Q to get Q m,       *)
(* take CONJUNCT2 → P (ABS_num m). At m := REP_num n, get P n    *)
(* via absRepNumThm.                                            *)
(* ============================================================ *)

numInductionThm =
  Module[{pV, nV, mV, iV, p0, pn, pSucN, stepImp, stepForall, conjBody,
          assumeInd, conjP0, conjStep,
          qBody, qLam, qIND0Tm, conj1Q,
          qIND0AndStep, finalInner},

    pV = mkVar["P", tyFun[numTy, boolTy]];
    nV = mkVar["n", numTy];
    mV = mkVar["m", indTy];
    iV = mkVar["i", indTy];

    p0     = mkComb[pV, zeroConst[]];
    pn     = mkComb[pV, nV];
    pSucN  = mkComb[pV, mkComb[sucConst[], nV]];
    stepImp    = impTm[pn, pSucN];
    stepForall = mkComb[
      mkConst["∀", tyFun[tyFun[numTy, boolTy], boolTy]],
      mkAbs[nV, stepImp]];
    conjBody = andTm[p0, stepForall];

    assumeInd = ASSUME[conjBody];
    conjP0 = HOL`Bool`CONJUNCT1[assumeInd];
    conjStep = HOL`Bool`CONJUNCT2[assumeInd];

    (* Q i = NUM_REP i ∧ P (ABS_num i) *)
    qBody = andTm[
      mkComb[numRepConst[], iV],
      mkComb[pV, mkComb[absNumConst[], iV]]];
    qLam = mkAbs[iV, qBody];

    (* ---- Q IND_0 ----                                                   *)
    (* P (ABS_num IND_0) ↔ P 0 via zeroDefThm; conjoin with numRepInd0Thm. *)
    Module[{absInd0Tm, sym1, pAbsInd0FromP0, qInd0Body},
      absInd0Tm = mkComb[absNumConst[], ind0Const[]];
      sym1 = HOL`Equal`SYM[zeroDefThm];   (* ⊢ ABS_num IND_0 = 0 *)
      (* APTERM pV: ⊢ P (ABS_num IND_0) = P 0. SYM flips to match conjP0. *)
      pAbsInd0FromP0 = EQMP[
        HOL`Equal`SYM[HOL`Equal`APTERM[pV, sym1]],
        conjP0];
      (* (conj) ⊢ P (ABS_num IND_0) *)
      conj1Q = HOL`Bool`CONJ[numRepInd0Thm, pAbsInd0FromP0];
      (* (conj) ⊢ NUM_REP IND_0 ∧ P (ABS_num IND_0) *)
    ];
    qIND0Tm = conj1Q;

    (* ---- ∀m. Q m ⇒ Q (IND_SUC m) ----                                  *)
    (* Assume Q m. Get NUM_REP m and P (ABS_num m). Derive NUM_REP (IND_SUC m) *)
    (* via numRepSucThm. For P side, need ABS_num (IND_SUC m) = SUC (ABS_num m) *)
    (* — this uses REP_num (ABS_num m) = m from repAbsNumThm INST'd at m, *)
    (* given NUM_REP m. Substituting into sucDefThm at ABS_num m closes it.*)
    Module[{qM, qSucM, qmHyp,
            qmCONJ1, qmCONJ2,
            numRepSucMV, sucEq, sucBetaEq, sucEqAt, ap2,
            repAbsAtM, repEqAbs, instRepAbs,
            absSubChain, predAtSuc, pSucForm, pAbsSucIndSucEq,
            qSucMConj, dischQMV, genMVQ},

      qM    = mkComb[qLam, mV];
      qSucM = mkComb[qLam, mkComb[indSuccConst[], mV]];

      (* β-normal forms of Q m and Q (IND_SUC m): *)
      Module[{qmNorm, qSucMNorm},
        qmNorm = andTm[
          mkComb[numRepConst[], mV],
          mkComb[pV, mkComb[absNumConst[], mV]]];
        qSucMNorm = andTm[
          mkComb[numRepConst[], mkComb[indSuccConst[], mV]],
          mkComb[pV, mkComb[absNumConst[], mkComb[indSuccConst[], mV]]]];
        qmHyp = ASSUME[qmNorm];
        qmCONJ1 = HOL`Bool`CONJUNCT1[qmHyp];  (* (Q m) ⊢ NUM_REP m *)
        qmCONJ2 = HOL`Bool`CONJUNCT2[qmHyp];  (* (Q m) ⊢ P (ABS_num m) *)

        (* NUM_REP (IND_SUC m) *)
        numRepSucMV = HOL`Bool`MP[HOL`Bool`SPEC[mV, numRepSucThm], qmCONJ1];
        (* (Q m) ⊢ NUM_REP (IND_SUC m) *)

        (* ABS_num (IND_SUC m) = SUC (ABS_num m) *)
        (* Strategy: sucDefThm @ ABS_num m unfolds RHS to                 *)
        (*   SUC (ABS_num m) = ABS_num (IND_SUC (REP_num (ABS_num m))).   *)
        (* Use repAbsNumThm to rewrite REP_num (ABS_num m) → m            *)
        (* (this uses NUM_REP m, providing the body un-β'd via repAbsNumThm).*)
        sucEqAt = HOL`Equal`APTHM[sucDefThm, mkComb[absNumConst[], mV]];
        sucBetaEq = BETACONV[concl[sucEqAt][[2]]];
        sucEq = TRANS[sucEqAt, sucBetaEq];
        (* ⊢ SUC (ABS_num m) = ABS_num (IND_SUC (REP_num (ABS_num m))) *)

        (* repAbsNumThm INSTd r → m: (body) m = (REP_num (ABS_num m) = m). *)
        instRepAbs = HOL`Kernel`INST[{mkVar["r", indTy] -> mV}, repAbsNumThm];
        Module[{predBody, predApplied, betaEq, bodyAtMnoBeta},
          predBody = numRepPredicateBody[];
          predApplied = mkComb[predBody, mV];
          betaEq = BETACONV[predApplied];
          bodyAtMnoBeta = EQMP[HOL`Equal`SYM[betaEq],
            EQMP[unfoldNumRep[mV], qmCONJ1]];
          repEqAbs = EQMP[instRepAbs, bodyAtMnoBeta];
          (* (Q m) ⊢ REP_num (ABS_num m) = m *)
        ];

        (* (Q m) ⊢ ABS_num (IND_SUC (REP_num (ABS_num m))) = ABS_num (IND_SUC m) *)
        absSubChain = HOL`Equal`APTERM[absNumConst[],
          HOL`Equal`APTERM[indSuccConst[], repEqAbs]];
        (* (Q m) ⊢ ABS_num (IND_SUC (REP_num (ABS_num m))) = ABS_num (IND_SUC m) *)
        (* sucEq SYM gives: ⊢ ABS_num (IND_SUC (REP_num (ABS_num m))) = SUC (ABS_num m). Wait, SYM[sucEq] does that. *)
        (* So: (Q m) ⊢ ABS_num (IND_SUC m) = SUC (ABS_num m). *)
        pSucForm = TRANS[HOL`Equal`SYM[absSubChain], HOL`Equal`SYM[sucEq]];
        (* pSucForm : (Q m) ⊢ ABS_num (IND_SUC m) = SUC (ABS_num m) *)

        (* P (SUC (ABS_num m)) from conjStep INST'd at ABS_num m + qmCONJ2. *)
        Module[{stepAtAbsM},
          stepAtAbsM = HOL`Bool`SPEC[mkComb[absNumConst[], mV], conjStep];
          (* (assumeInd) ⊢ P (ABS_num m) ⇒ P (SUC (ABS_num m)) *)
          predAtSuc = HOL`Bool`MP[stepAtAbsM, qmCONJ2];
          (* (assumeInd, Q m) ⊢ P (SUC (ABS_num m)) *)
        ];

        (* Need P (ABS_num (IND_SUC m)); use SYM[pSucForm] to rewrite SUC (ABS m) → ABS_num (IND_SUC m). *)
        pAbsSucIndSucEq = HOL`Equal`APTERM[pV, HOL`Equal`SYM[pSucForm]];
        (* (Q m) ⊢ P (SUC (ABS_num m)) = P (ABS_num (IND_SUC m)) *)
        Module[{pAbsIndSucM},
          pAbsIndSucM = EQMP[pAbsSucIndSucEq, predAtSuc];
          (* (assumeInd, Q m) ⊢ P (ABS_num (IND_SUC m)) *)
          qSucMConj = HOL`Bool`CONJ[numRepSucMV, pAbsIndSucM];
          (* (assumeInd, Q m) ⊢ NUM_REP (IND_SUC m) ∧ P (ABS_num (IND_SUC m)) *)
        ];

        dischQMV = HOL`Bool`DISCH[qmNorm, qSucMConj];
        (* (assumeInd) ⊢ Q m (β-norm) ⇒ NUM_REP (IND_SUC m) ∧ P (ABS_num (IND_SUC m)) *)
        genMVQ = HOL`Bool`GEN[mV, dischQMV];
        (* (assumeInd) ⊢ ∀m. (NUM_REP m ∧ P (ABS_num m)) ⇒ NUM_REP (IND_SUC m) ∧ P (ABS_num (IND_SUC m)) *)
        qIND0AndStep = HOL`Bool`CONJ[qIND0Tm, genMVQ];
      ];
    ];

    (* qIND0AndStep : (assumeInd) ⊢                                       *)
    (*   (NUM_REP IND_0 ∧ P (ABS_num IND_0))                              *)
    (*   ∧ ∀m. (NUM_REP m ∧ P (ABS_num m))                                *)
    (*          ⇒ (NUM_REP (IND_SUC m) ∧ P (ABS_num (IND_SUC m)))         *)

    (* Use numRepRepNumThm to instantiate the NUM_REP m'-style ∀P-body of *)
    (* (NUM_REP (REP_num n))-unfolded at Q (with Q the β-normal body),    *)
    (* MP through qIND0AndStep, take CONJUNCT2, rewrite ABS_num (REP_num n) → n, *)
    (* GEN over n.                                                        *)

    Module[{nVnew, repNew, numRepRepN, unfoldedRepN, qLamApplied,
            specAtQ, qLamApply0, qLamApplyStep, qIND0AndStepUnbeta,
            mpQRepN, qRepNBeta, conj2Q, absRepEq, pNEq, pNTh,
            dischIndConj, genPFinal},

      nVnew = mkVar["n", numTy];
      repNew = mkComb[repNumConst[], nVnew];
      numRepRepN = HOL`Kernel`INST[{mkVar["n", numTy] -> nVnew}, numRepRepNumThm];
      (* ⊢ NUM_REP (REP_num n) *)
      unfoldedRepN = EQMP[unfoldNumRep[repNew], numRepRepN];
      (* ⊢ ∀P'. P' IND_0 ∧ (∀m'. P' m' ⇒ P' (IND_SUC m')) ⇒ P' (REP_num n) *)

      (* SPEC at the abstraction `qLam`. *)
      specAtQ = HOL`Bool`SPEC[qLam, unfoldedRepN];
      (* ⊢ qLam IND_0 ∧ (∀m'. qLam m' ⇒ qLam (IND_SUC m')) ⇒ qLam (REP_num n) *)

      (* qIND0AndStep is in β-normal form (we built it that way).         *)
      (* specAtQ's antecedent has un-β'd `qLam IND_0` etc. We need to     *)
      (* match them by β-reducing specAtQ.                                *)
      specAtQ = HOL`Drule`CONVRULE[
        HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specAtQ];
      (* β-norm: ⊢ (NUM_REP IND_0 ∧ P (ABS_num IND_0))                    *)
      (*           ∧ (∀m'. (NUM_REP m' ∧ P (ABS_num m'))                  *)
      (*                    ⇒ NUM_REP (IND_SUC m') ∧ P (ABS_num (IND_SUC m'))) *)
      (*           ⇒ (NUM_REP (REP_num n) ∧ P (ABS_num (REP_num n)))      *)

      mpQRepN = HOL`Bool`MP[specAtQ, qIND0AndStep];
      (* (assumeInd) ⊢ NUM_REP (REP_num n) ∧ P (ABS_num (REP_num n)) *)
      conj2Q = HOL`Bool`CONJUNCT2[mpQRepN];
      (* (assumeInd) ⊢ P (ABS_num (REP_num n)) *)

      absRepEq = HOL`Kernel`INST[{mkVar["a", numTy] -> nVnew}, absRepNumThm];
      (* ⊢ ABS_num (REP_num n) = n *)
      pNEq = HOL`Equal`APTERM[pV, absRepEq];
      (* ⊢ P (ABS_num (REP_num n)) = P n *)
      pNTh = EQMP[pNEq, conj2Q];
      (* (assumeInd) ⊢ P n *)

      Module[{genN, dischInd},
        genN = HOL`Bool`GEN[nVnew, pNTh];
        dischInd = HOL`Bool`DISCH[conjBody, genN];
        genPFinal = HOL`Bool`GEN[pV, dischInd];
      ];
      finalInner = genPFinal;
    ];

    finalInner
  ];

End[];
EndPackage[];
