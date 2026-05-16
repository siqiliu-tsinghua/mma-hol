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

iterGraphConst::usage = "iterGraphConst[] — ITER_GRAPH : A → (A→A) → ind → A → bool. Smallest binary relation on (ind, A) containing (IND_0, e) and closed under (i, a) ↦ (IND_SUC i, f a).";
iterGraphDefThm::usage = "iterGraphDefThm — ⊢ ITER_GRAPH = (λe f i a. ∀S. S IND_0 e ∧ (∀i' a'. S i' a' ⇒ S (IND_SUC i') (f a')) ⇒ S i a).";

iterConst::usage  = "iterConst[] — ITER : A → (A→A) → num → A. Iteration on num. Defined as ITER e f n = ε a. ITER_GRAPH e f (REP_num n) a.";
iterDefThm::usage = "iterDefThm — ⊢ ITER = (λe f n. ε a. ITER_GRAPH e f (REP_num n) a).";
iterZeroEqThm::usage = "iterZeroEqThm — ⊢ ITER e f 0 = e.";
iterSucEqThm::usage  = "iterSucEqThm — ⊢ ∀n. ITER e f (SUC n) = f (ITER e f n).";
numIterationThm::usage = "numIterationThm — ⊢ ∀e:A. ∀f:A→A. ∃g:num→A. g 0 = e ∧ ∀n. g (SUC n) = f (g n).";

plusConst::usage = "plusConst[] — + : num → num → num. Addition, defined as +m n = ITER m SUC n.";
plusDefThm::usage = "plusDefThm — ⊢ + = (λm n. ITER m SUC n).";
plusZeroEqThm::usage = "plusZeroEqThm — ⊢ ∀m. m + 0 = m.";
plusSucEqThm::usage  = "plusSucEqThm — ⊢ ∀m n. m + (SUC n) = SUC (m + n).";
addLeftZeroThm::usage = "addLeftZeroThm — ⊢ ∀n. 0 + n = n.";

timesConst::usage = "timesConst[] — * : num → num → num. Multiplication, defined as *m n = ITER 0 (λa. a + m) n.";
timesDefThm::usage = "timesDefThm — ⊢ * = (λm n. ITER 0 (λa. a + m) n).";
timesZeroEqThm::usage = "timesZeroEqThm — ⊢ ∀m. m * 0 = 0.";
timesSucEqThm::usage  = "timesSucEqThm — ⊢ ∀m n. m * (SUC n) = m * n + m.";
timesLeftZeroThm::usage = "timesLeftZeroThm — ⊢ ∀n. 0 * n = 0.";

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

(* ============================================================ *)
(* M7-3-d: Iteration theorem                                    *)
(* ⊢ ∀e:A. ∀f:A→A. ∃g:num→A. g 0 = e ∧ ∀n. g (SUC n) = f (g n)  *)
(*                                                              *)
(* Proof skeleton:                                              *)
(*   1. Define ITER_GRAPH e f as the smallest binary relation   *)
(*      on (ind, A) containing (IND_0, e) and closed under      *)
(*      (i, a) ↦ (IND_SUC i, f a).                              *)
(*   2. graphInd0Lem  : ITER_GRAPH e f IND_0 e.                 *)
(*   3. graphSucLem   : ITER_GRAPH e f i a                      *)
(*                       ⇒ ITER_GRAPH e f (IND_SUC i) (f a).    *)
(*   4. graphUniqInd0 : ITER_GRAPH e f IND_0 a ⇒ a = e. Uses    *)
(*      ind0NotInRangeThm to vacuously satisfy the step-closure *)
(*      of S = λi'' a''. (i'' = IND_0 ⇒ a'' = e).               *)
(*   5. graphExtract  : ITER_GRAPH e f (IND_SUC i) a            *)
(*                       ⇒ ∃b. a = f b ∧ ITER_GRAPH e f i b.   *)
(*      Uses S = λi'' a''. ITER_GRAPH e f i'' a''                *)
(*                          ∧ (∀j. i'' = IND_SUC j              *)
(*                              ⇒ ∃b. a'' = f b ∧ … e f j b).    *)
(*   6. iterExists  : NUM_REP i ⇒ ∃a. ITER_GRAPH e f i a.       *)
(*      By NUM_REP induction with P = λi. ∃a. ITER_GRAPH e f i a.*)
(*   7. iterUnique  : NUM_REP i                                  *)
(*                     ⇒ ∀a b. ITER_GRAPH e f i a               *)
(*                              ∧ ITER_GRAPH e f i b ⇒ a = b.   *)
(*      By NUM_REP induction. Uses graphExtract + sucInj-at-ind *)
(*      (indSuccOneOneUnfoldedThm) at the step.                 *)
(*   8. The function g n = ε a. ITER_GRAPH e f (REP_num n) a    *)
(*      then satisfies the equations.                           *)
(*                                                              *)
(* This is heavy plumbing — proof is ~400 lines of derivations. *)
(* ============================================================ *)

aTy = tyVar["A"];
funATy = tyFun[aTy, aTy];
graphTy = tyFun[indTy, tyFun[aTy, boolTy]];
iterGraphTy = tyFun[aTy, tyFun[funATy, graphTy]];

iterGraphBodyTm[] :=
  Module[{eV, fV, iV, aV, sV, iVp, aVp,
          sInd0e, sStepInner, sStepInner2, sStep, premise, conclTm,
          forallSBody},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    iV = mkVar["i", indTy];
    aV = mkVar["a", aTy];
    sV = mkVar["S", graphTy];
    iVp = mkVar["i'", indTy];
    aVp = mkVar["a'", aTy];
    sInd0e = mkComb[mkComb[sV, ind0Const[]], eV];
    sStepInner = impTm[
      mkComb[mkComb[sV, iVp], aVp],
      mkComb[mkComb[sV, mkComb[indSuccConst[], iVp]],
                       mkComb[fV, aVp]]];
    sStepInner2 = mkComb[forallC[aTy], mkAbs[aVp, sStepInner]];
    sStep = mkComb[forallC[indTy], mkAbs[iVp, sStepInner2]];
    premise = andTm[sInd0e, sStep];
    conclTm = mkComb[mkComb[sV, iV], aV];
    forallSBody = mkComb[forallC[graphTy],
      mkAbs[sV, impTm[premise, conclTm]]];
    mkAbs[eV, mkAbs[fV, mkAbs[iV, mkAbs[aV, forallSBody]]]]
  ];

iterGraphDefThm = newDefinition[mkEq[
  mkVar["ITER_GRAPH", iterGraphTy],
  iterGraphBodyTm[]
]];

iterGraphConst[] := mkConst["ITER_GRAPH", iterGraphTy];

(* iterGraphAppTm[eTm, fTm, iTm, aTm] — the β-normal *unfolded* form of      *)
(*   `ITER_GRAPH e f i a`                                                   *)
(* = `∀S. (S IND_0 e ∧ (∀i' a'. S i' a' ⇒ S (IND_SUC i') (f a'))) ⇒ S i a`. *)
iterGraphAppTm[eTm_, fTm_, iTm_, aTm_] :=
  Module[{sV, iVp, aVp, sInd0e, sStepInner, sStep, premise, conclTm},
    sV = mkVar["S", graphTy];
    iVp = mkVar["i'", indTy];
    aVp = mkVar["a'", aTy];
    sInd0e = mkComb[mkComb[sV, ind0Const[]], eTm];
    sStepInner = impTm[
      mkComb[mkComb[sV, iVp], aVp],
      mkComb[mkComb[sV, mkComb[indSuccConst[], iVp]],
                       mkComb[fTm, aVp]]];
    sStep = mkComb[forallC[indTy],
      mkAbs[iVp, mkComb[forallC[aTy], mkAbs[aVp, sStepInner]]]];
    premise = andTm[sInd0e, sStep];
    conclTm = mkComb[mkComb[sV, iTm], aTm];
    mkComb[forallC[graphTy],
      mkAbs[sV, impTm[premise, conclTm]]]
  ];

(* iterGraphFoldTm[eTm, fTm, iTm, aTm] — the *folded* form                  *)
(*   `ITER_GRAPH e f i a` (using the constant).                              *)
iterGraphFoldTm[eTm_, fTm_, iTm_, aTm_] :=
  mkComb[mkComb[mkComb[mkComb[iterGraphConst[], eTm], fTm], iTm], aTm];

(* `⊢ ITER_GRAPH e f i a = (∀S. … ⇒ S i a)` (β-reduced RHS). *)
unfoldIterGraph[eTm_, fTm_, iTm_, aTm_] :=
  Module[{ap1, ap2, ap3, ap4, conv},
    ap1 = HOL`Equal`APTHM[iterGraphDefThm, eTm];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, fTm];
    ap2 = TRANS[ap2, BETACONV[concl[ap2][[2]]]];
    ap3 = HOL`Equal`APTHM[ap2, iTm];
    ap3 = TRANS[ap3, BETACONV[concl[ap3][[2]]]];
    ap4 = HOL`Equal`APTHM[ap3, aTm];
    TRANS[ap4, BETACONV[concl[ap4][[2]]]]
  ];

(* ============================================================ *)
(* graphInd0Lem :                                               *)
(*   ⊢ ITER_GRAPH e f IND_0 e                                   *)
(* For free e : A, f : A → A.                                   *)
(* ============================================================ *)

graphInd0Lem =
  Module[{eV, fV, sV, iVp, aVp, sInd0e, sStepInner, sStep,
          premise, assumeConj, conj1, dischConj, genS, foldEq},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    sV = mkVar["S", graphTy];
    iVp = mkVar["i'", indTy];
    aVp = mkVar["a'", aTy];
    sInd0e = mkComb[mkComb[sV, ind0Const[]], eV];
    sStepInner = impTm[
      mkComb[mkComb[sV, iVp], aVp],
      mkComb[mkComb[sV, mkComb[indSuccConst[], iVp]],
                       mkComb[fV, aVp]]];
    sStep = mkComb[forallC[indTy],
      mkAbs[iVp, mkComb[forallC[aTy], mkAbs[aVp, sStepInner]]]];
    premise = andTm[sInd0e, sStep];
    assumeConj = ASSUME[premise];
    conj1 = HOL`Bool`CONJUNCT1[assumeConj];   (* (premise) ⊢ S IND_0 e *)
    dischConj = HOL`Bool`DISCH[premise, conj1];
    genS = HOL`Bool`GEN[sV, dischConj];
    (* ⊢ ∀S. (premise) ⇒ S IND_0 e *)
    foldEq = unfoldIterGraph[eV, fV, ind0Const[], eV];
    EQMP[HOL`Equal`SYM[foldEq], genS]
  ];

(* ============================================================ *)
(* graphSucLem :                                                *)
(*   ⊢ ∀i a. ITER_GRAPH e f i a                                  *)
(*            ⇒ ITER_GRAPH e f (IND_SUC i) (f a)                *)
(* ============================================================ *)

graphSucLem =
  Module[{eV, fV, iV, aV, sV, iVp, aVp,
          sInd0e, sStepInner, sStep, premise,
          graphIAFold, assumeGraphIAFold, unfoldedAtIA,
          assumeConj, conj2, conj2SpecI, conj2SpecIa,
          unfoldedSpecS, mpStep, dischConj, genS,
          foldEq, foldedThm, dischGraphIA, genA, genI},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    iV = mkVar["i", indTy];
    aV = mkVar["a", aTy];
    sV = mkVar["S", graphTy];
    iVp = mkVar["i'", indTy];
    aVp = mkVar["a'", aTy];

    sInd0e = mkComb[mkComb[sV, ind0Const[]], eV];
    sStepInner = impTm[
      mkComb[mkComb[sV, iVp], aVp],
      mkComb[mkComb[sV, mkComb[indSuccConst[], iVp]],
                       mkComb[fV, aVp]]];
    sStep = mkComb[forallC[indTy],
      mkAbs[iVp, mkComb[forallC[aTy], mkAbs[aVp, sStepInner]]]];
    premise = andTm[sInd0e, sStep];

    (* Assume the FOLDED form (ITER_GRAPH e f i a) so the hypothesis  *)
    (* matches what users hand us; unfold it internally.              *)
    graphIAFold = iterGraphFoldTm[eV, fV, iV, aV];
    assumeGraphIAFold = ASSUME[graphIAFold];
    unfoldedAtIA = EQMP[unfoldIterGraph[eV, fV, iV, aV], assumeGraphIAFold];
    (* (ITER_GRAPH e f i a) ⊢ ∀S. premise ⇒ S i a *)

    assumeConj = ASSUME[premise];
    conj2 = HOL`Bool`CONJUNCT2[assumeConj];
    conj2SpecI = HOL`Bool`SPEC[iV, conj2];
    conj2SpecIa = HOL`Bool`SPEC[aV, conj2SpecI];

    unfoldedSpecS = HOL`Bool`SPEC[sV, unfoldedAtIA];
    mpStep = HOL`Bool`MP[unfoldedSpecS, assumeConj];
    mpStep = HOL`Bool`MP[conj2SpecIa, mpStep];

    dischConj = HOL`Bool`DISCH[premise, mpStep];
    genS = HOL`Bool`GEN[sV, dischConj];

    foldEq = unfoldIterGraph[eV, fV,
      mkComb[indSuccConst[], iV], mkComb[fV, aV]];
    foldedThm = EQMP[HOL`Equal`SYM[foldEq], genS];

    dischGraphIA = HOL`Bool`DISCH[graphIAFold, foldedThm];
    genA = HOL`Bool`GEN[aV, dischGraphIA];
    genI = HOL`Bool`GEN[iV, genA]
  ];

(* ============================================================ *)
(* indSucNotInd0Lem : ⊢ ∀i. ¬ (IND_SUC i = IND_0)                *)
(* ============================================================ *)

indSucNotInd0Lem =
  Module[{iV, sucIEqInd0, hyp, symHyp, exTm, existsTh, mpStep,
          dischTh, notTh},
    iV = mkVar["i", indTy];
    sucIEqInd0 = mkEq[mkComb[indSuccConst[], iV], ind0Const[]];
    hyp = ASSUME[sucIEqInd0];
    symHyp = HOL`Equal`SYM[hyp];
    exTm = mkComb[existsC[indTy],
      mkAbs[mkVar["x", indTy],
        mkEq[ind0Const[], mkComb[indSuccConst[], mkVar["x", indTy]]]]];
    existsTh = HOL`Bool`EXISTS[exTm, iV, symHyp];
    mpStep = HOL`Bool`MP[HOL`Bool`NOTELIM[ind0NotInRangeThm], existsTh];
    dischTh = HOL`Bool`DISCH[sucIEqInd0, mpStep];
    notTh = HOL`Bool`NOTINTRO[dischTh];
    HOL`Bool`GEN[iV, notTh]
  ];

(* ============================================================ *)
(* graphUniqInd0Lem : ⊢ ∀a. ITER_GRAPH e f IND_0 a ⇒ a = e       *)
(*                                                              *)
(* Pick S = λi''. λa''. i'' = IND_0 ⇒ a'' = e. Verify the       *)
(* base+step premise:                                            *)
(*   - Base S IND_0 e: (IND_0 = IND_0 ⇒ e = e). Trivial.        *)
(*   - Step: (i' = IND_0 ⇒ a' = e) ⇒                            *)
(*           (IND_SUC i' = IND_0 ⇒ f a' = e). The latter        *)
(*     antecedent is impossible via indSucNotInd0Lem; close      *)
(*     vacuously via propTaut.                                  *)
(* Then unfold ITER_GRAPH e f IND_0 a, SPEC at this S, MP, β,    *)
(* and MP with REFL[IND_0] to extract a = e.                    *)
(* ============================================================ *)

graphUniqInd0Lem =
  Module[{eV, fV, aV, iVpp, aVpp, iVp, aVp,
          graphIAFold, assumeGraphIAFold, assumeGraphIA, sUniqLam,
          conj1Proof, conj2Proof, conjProof,
          specS, mpThroughPremise, finalImp, mpReflInd0,
          dischGraphIA, genA,
          ind0EqInd0Tm, iEqInd0Tm, sucIEqInd0Tm, aEqETm, faEqETm,
          vacuousImp, ipImp, ipConcl, propTautTh, specINotIndPostNot,
          notIndPostI, contradImp, vacuousAtAprime, vacuousAtIprime},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    aV = mkVar["a", aTy];
    iVpp = mkVar["iPP", indTy];
    aVpp = mkVar["aPP", aTy];
    iVp = mkVar["i'", indTy];
    aVp = mkVar["a'", aTy];

    (* Take folded ITER_GRAPH e f IND_0 a as antecedent; unfold internally. *)
    graphIAFold = iterGraphFoldTm[eV, fV, ind0Const[], aV];
    assumeGraphIAFold = ASSUME[graphIAFold];
    assumeGraphIA = EQMP[unfoldIterGraph[eV, fV, ind0Const[], aV],
      assumeGraphIAFold];

    (* sUniqLam = λi''. λa''. (i'' = IND_0) ⇒ (a'' = e) *)
    sUniqLam = mkAbs[iVpp,
      mkAbs[aVpp,
        impTm[mkEq[iVpp, ind0Const[]], mkEq[aVpp, eV]]]];

    (* Part 1: ⊢ IND_0 = IND_0 ⇒ e = e *)
    ind0EqInd0Tm = mkEq[ind0Const[], ind0Const[]];
    conj1Proof = HOL`Bool`DISCH[ind0EqInd0Tm, REFL[eV]];

    (* Part 2: ⊢ ∀i'. ∀a'. (i' = IND_0 ⇒ a' = e)                  *)
    (*                     ⇒ (IND_SUC i' = IND_0 ⇒ f a' = e)      *)
    iEqInd0Tm     = mkEq[iVp, ind0Const[]];
    aEqETm        = mkEq[aVp, eV];
    sucIEqInd0Tm  = mkEq[mkComb[indSuccConst[], iVp], ind0Const[]];
    faEqETm       = mkEq[mkComb[fV, aVp], eV];

    (* propTaut: ⊢ ¬ p ⇒ (p ⇒ q)   then INST p, q.                *)
    propTautTh = HOL`Auto`PropTaut`propTaut[
      impTm[mkComb[notC[], mkVar["p", boolTy]],
        impTm[mkVar["p", boolTy], mkVar["q", boolTy]]]];
    (* ⊢ ¬p ⇒ (p ⇒ q) *)
    notIndPostI = HOL`Bool`SPEC[iVp, indSucNotInd0Lem];
    (* ⊢ ¬ (IND_SUC i' = IND_0) *)
    vacuousAtAprime = HOL`Bool`MP[
      HOL`Kernel`INST[
        {mkVar["p", boolTy] -> sucIEqInd0Tm,
         mkVar["q", boolTy] -> faEqETm},
        propTautTh],
      notIndPostI];
    (* ⊢ IND_SUC i' = IND_0 ⇒ f a' = e *)

    (* Step rule: (i' = IND_0 ⇒ a' = e) ⇒ (IND_SUC i' = IND_0 ⇒ f a' = e). *)
    (* The conclusion is already proven independent of the assumption — *)
    (* DISCH the hypothesis vacuously.                                    *)
    ipImp = HOL`Bool`DISCH[impTm[iEqInd0Tm, aEqETm], vacuousAtAprime];
    (* ⊢ (i' = IND_0 ⇒ a' = e) ⇒ (IND_SUC i' = IND_0 ⇒ f a' = e) *)
    conj2Proof = HOL`Bool`GEN[iVp, HOL`Bool`GEN[aVp, ipImp]];

    (* Combine into the premise (un-β'd via the SPEC of sUniqLam shortly). *)
    conjProof = HOL`Bool`CONJ[conj1Proof, conj2Proof];

    (* SPEC at sUniqLam, β-reduce, MP through the premise. *)
    specS = HOL`Bool`SPEC[sUniqLam, assumeGraphIA];
    specS = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specS];
    (* (graphIA) ⊢ [(IND_0 = IND_0 ⇒ e = e) ∧                            *)
    (*               (∀i' a'. (i' = IND_0 ⇒ a' = e)                     *)
    (*                        ⇒ (IND_SUC i' = IND_0 ⇒ f a' = e))]       *)
    (*              ⇒ (IND_0 = IND_0 ⇒ a = e)                            *)
    mpThroughPremise = HOL`Bool`MP[specS, conjProof];
    (* (graphIA) ⊢ IND_0 = IND_0 ⇒ a = e *)
    mpReflInd0 = HOL`Bool`MP[mpThroughPremise, REFL[ind0Const[]]];
    (* (graphIAFold) ⊢ a = e *)

    dischGraphIA = HOL`Bool`DISCH[graphIAFold, mpReflInd0];
    genA = HOL`Bool`GEN[aV, dischGraphIA]
  ];

(* ============================================================ *)
(* ind0NotSucLem : ⊢ ∀j. ¬ (IND_0 = IND_SUC j)                    *)
(* ============================================================ *)

ind0NotSucLem =
  Module[{jV, eqTm, hyp, exTm, existsTh, mpStep, dischTh, notTh},
    jV = mkVar["j", indTy];
    eqTm = mkEq[ind0Const[], mkComb[indSuccConst[], jV]];
    hyp = ASSUME[eqTm];
    exTm = mkComb[existsC[indTy], mkAbs[jV, eqTm]];
    existsTh = HOL`Bool`EXISTS[exTm, jV, hyp];
    mpStep = HOL`Bool`MP[HOL`Bool`NOTELIM[ind0NotInRangeThm], existsTh];
    dischTh = HOL`Bool`DISCH[eqTm, mpStep];
    notTh = HOL`Bool`NOTINTRO[dischTh];
    HOL`Bool`GEN[jV, notTh]
  ];

(* ============================================================ *)
(* graphExtractLem :                                            *)
(*   ⊢ ∀i a. ITER_GRAPH e f (IND_SUC i) a                       *)
(*           ⇒ ∃b. a = f b ∧ ITER_GRAPH e f i b                 *)
(*                                                              *)
(* S = λi''. λa''. ITER_GRAPH e f i'' a''                       *)
(*                  ∧ (∀j. i'' = IND_SUC j                       *)
(*                       ⇒ ∃b. a'' = f b ∧ ITER_GRAPH e f j b). *)
(* ============================================================ *)

graphExtractLem =
  Module[{eV, fV, iV, aV, iVpp, aVpp, jV, bV,
          sExtractLam, sExtractApp,
          graphAtIndSuc, assumeGraphIndSuc, unfoldedAtIndSuc,
          propTautVac, vacuousImpForJ,
          ind0NotSucAtJ, sBase, sBaseExistsPart, sBaseConj,
          sBaseUnbeta, sStep, sStepUnbeta, premiseProof,
          specSExtract, specSExtractBeta, mpThroughPremise,
          conj2OfS, specJAtI, mpReflSucI, existsResult,
          dischGraphAtIndSuc, genA, genI,
          (* helpers for step *)
          iVp, aVp, sIa, hypSIa, sIaConj1, sIaConj2,
          indSucIpEqIndSucJTm, hypInjAss, applyInj, injAtIp,
          witnessB, graphIpAp, conjForB, exB, dischInjAss,
          genJStep, graphSucAtIpAp, conjStepResult,
          stepRule, dischSIp, genApStep, genIpStep,
          (* unbeta for S at specific positions *)
          sLamAppInd0e, sLamAppIndSuci, sLamAppIpAp,
          sLamAppSucIpFap, betaPair, betaSucPair, betaStepPair},

    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    iV = mkVar["i", indTy];
    aV = mkVar["a", aTy];
    iVpp = mkVar["iPP", indTy];
    aVpp = mkVar["aPP", aTy];
    jV = mkVar["j", indTy];
    bV = mkVar["b", aTy];

    (* Build sExtractLam = λi''. λa''. body, using the FOLDED                 *)
    (* `ITER_GRAPH e f …` form so that downstream β leaves the constant       *)
    (* in place (matches graphInd0Lem / graphSucLem outputs).                  *)
    sExtractLam = mkAbs[iVpp,
      mkAbs[aVpp,
        andTm[
          iterGraphFoldTm[eV, fV, iVpp, aVpp],
          mkComb[forallC[indTy],
            mkAbs[jV,
              impTm[
                mkEq[iVpp, mkComb[indSuccConst[], jV]],
                mkComb[existsC[aTy],
                  mkAbs[bV,
                    andTm[
                      mkEq[aVpp, mkComb[fV, bV]],
                      iterGraphFoldTm[eV, fV, jV, bV]]]]]]]]]];

    (* propTaut: ⊢ ¬ p ⇒ (p ⇒ q). *)
    propTautVac = HOL`Auto`PropTaut`propTaut[
      impTm[mkComb[notC[], mkVar["p", boolTy]],
        impTm[mkVar["p", boolTy], mkVar["q", boolTy]]]];

    (* ---------------- S IND_0 e (β-normal form) ---------------- *)
    (* Goal: ITER_GRAPH e f IND_0 e                                 *)
    (*       ∧ (∀j. IND_0 = IND_SUC j                              *)
    (*              ⇒ ∃b. e = f b ∧ ITER_GRAPH e f j b)             *)
    Module[{ind0EqIndSucJTm, existsRhsAtJ, vacuousImpAtJ, genJ},
      ind0EqIndSucJTm = mkEq[ind0Const[], mkComb[indSuccConst[], jV]];
      existsRhsAtJ = mkComb[existsC[aTy],
        mkAbs[bV,
          andTm[
            mkEq[eV, mkComb[fV, bV]],
            iterGraphFoldTm[eV, fV, jV, bV]]]];
      ind0NotSucAtJ = HOL`Bool`SPEC[jV, ind0NotSucLem];
      vacuousImpAtJ = HOL`Bool`MP[
        HOL`Kernel`INST[
          {mkVar["p", boolTy] -> ind0EqIndSucJTm,
           mkVar["q", boolTy] -> existsRhsAtJ},
          propTautVac],
        ind0NotSucAtJ];
      (* ⊢ (IND_0 = IND_SUC j) ⇒ ∃b. e = f b ∧ ITER_GRAPH e f j b *)
      genJ = HOL`Bool`GEN[jV, vacuousImpAtJ];
      sBaseConj = HOL`Bool`CONJ[graphInd0Lem, genJ];
    ];
    (* sBaseConj is the β-form of S IND_0 e. Now un-β. *)
    sLamAppInd0e = mkComb[mkComb[sExtractLam, ind0Const[]], eV];
    betaPair = HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]][sLamAppInd0e];
    (* betaPair : ⊢ sLam IND_0 e = (β-form) *)
    sBaseUnbeta = EQMP[HOL`Equal`SYM[betaPair], sBaseConj];
    (* ⊢ sExtractLam IND_0 e *)

    (* ---------------- S step (un-β form) ---------------- *)
    iVp = mkVar["i'", indTy];
    aVp = mkVar["a'", aTy];

    sLamAppIpAp = mkComb[mkComb[sExtractLam, iVp], aVp];
    sLamAppSucIpFap = mkComb[
      mkComb[sExtractLam, mkComb[indSuccConst[], iVp]],
      mkComb[fV, aVp]];

    betaStepPair = HOL`Drule`DEPTHCONV[
      HOL`Drule`TRYCONV[BETACONV]][sLamAppIpAp];
    betaSucPair = HOL`Drule`DEPTHCONV[
      HOL`Drule`TRYCONV[BETACONV]][sLamAppSucIpFap];
    (* betaStepPair : ⊢ S i' a' = body[i'/i'', a'/a''] *)
    (* betaSucPair  : ⊢ S (IND_SUC i') (f a') = body[IND_SUC i'/i'', f a'/a''] *)

    (* Assume S i' a' (un-β); convert to β-form. *)
    hypSIa = ASSUME[sLamAppIpAp];
    Module[{betaForm},
      betaForm = EQMP[betaStepPair, hypSIa];
      sIaConj1 = HOL`Bool`CONJUNCT1[betaForm];
      sIaConj2 = HOL`Bool`CONJUNCT2[betaForm];
    ];

    (* Step result LHS: ITER_GRAPH e f (IND_SUC i') (f a'). *)
    graphSucAtIpAp = HOL`Bool`MP[
      HOL`Bool`SPEC[aVp, HOL`Bool`SPEC[iVp, graphSucLem]],
      sIaConj1];

    (* Step result RHS: ∀j. IND_SUC i' = IND_SUC j                 *)
    (*                       ⇒ ∃b. f a' = f b ∧ ITER_GRAPH e f j b. *)
    indSucIpEqIndSucJTm = mkEq[
      mkComb[indSuccConst[], iVp],
      mkComb[indSuccConst[], jV]];
    hypInjAss = ASSUME[indSucIpEqIndSucJTm];
    (* From hypInjAss + indSuccOneOneUnfoldedThm: i' = j. *)
    Module[{spec1, spec2, ipEqJ, witnessFaEqFaSubst, graphIpApSubst,
            graphCallAtJa, faEqFb, conjForJ, exAtA},
      spec1 = HOL`Bool`SPEC[iVp, indSuccOneOneUnfoldedThm];
      spec2 = HOL`Bool`SPEC[jV, spec1];
      (* ⊢ IND_SUC i' = IND_SUC j ⇒ i' = j *)
      ipEqJ = HOL`Bool`MP[spec2, hypInjAss];
      (* (IND_SUC i' = IND_SUC j) ⊢ i' = j *)
      (* Substitute i' → j in sIaConj1 to get ITER_GRAPH e f j a'.   *)
      (* APTERM ITER_GRAPH-e-f on ipEqJ → ITER_GRAPH e f i' = … e f j; *)
      (* APTHM at a' lifts to applied form.                            *)
      graphCallAtJa = EQMP[
        HOL`Equal`APTHM[
          HOL`Equal`APTERM[
            mkComb[mkComb[iterGraphConst[], eV], fV],
            ipEqJ],
          aVp],
        sIaConj1];
      (* ⊢ (S i' a', IND_SUC i' = IND_SUC j) ⊢ ITER_GRAPH e f j a' *)
      faEqFb = REFL[mkComb[fV, aVp]];
      (* ⊢ f a' = f a' *)
      conjForJ = HOL`Bool`CONJ[faEqFb, graphCallAtJa];
      (* (S i' a', IND_SUC i' = IND_SUC j) ⊢ f a' = f a' ∧ ITER_GRAPH e f j a' *)
      exAtA = HOL`Bool`EXISTS[
        mkComb[existsC[aTy],
          mkAbs[bV,
            andTm[
              mkEq[mkComb[fV, aVp], mkComb[fV, bV]],
              iterGraphFoldTm[eV, fV, jV, bV]]]],
        aVp,
        conjForJ];
      (* (S i' a', IND_SUC i' = IND_SUC j) ⊢ ∃b. f a' = f b ∧ ITER_GRAPH e f j b *)
      dischInjAss = HOL`Bool`DISCH[indSucIpEqIndSucJTm, exAtA];
      genJStep = HOL`Bool`GEN[jV, dischInjAss];
      (* (S i' a') ⊢ ∀j. IND_SUC i' = IND_SUC j ⇒ ∃b. f a' = f b ∧ ITER_GRAPH e f j b *)
    ];

    conjStepResult = HOL`Bool`CONJ[graphSucAtIpAp, genJStep];
    (* (S i' a') ⊢ ITER_GRAPH e f (IND_SUC i') (f a')              *)
    (*             ∧ (∀j. IND_SUC i' = IND_SUC j                    *)
    (*                   ⇒ ∃b. f a' = f b ∧ ITER_GRAPH e f j b)    *)
    (* Now un-β to S (IND_SUC i') (f a'). *)
    stepRule = EQMP[HOL`Equal`SYM[betaSucPair], conjStepResult];
    (* (S i' a') ⊢ S (IND_SUC i') (f a') *)
    dischSIp = HOL`Bool`DISCH[sLamAppIpAp, stepRule];
    (* ⊢ S i' a' ⇒ S (IND_SUC i') (f a') *)
    genApStep = HOL`Bool`GEN[aVp, dischSIp];
    genIpStep = HOL`Bool`GEN[iVp, genApStep];
    (* ⊢ ∀i'. ∀a'. S i' a' ⇒ S (IND_SUC i') (f a') *)

    premiseProof = HOL`Bool`CONJ[sBaseUnbeta, genIpStep];
    (* ⊢ (S IND_0 e) ∧ (∀i' a'. S i' a' ⇒ S (IND_SUC i') (f a')) *)

    (* ---------------- ASSUME folded ITER_GRAPH e f (IND_SUC i) a; *)
    (*                  unfold internally to access ∀S. body.       *)
    graphAtIndSuc = iterGraphFoldTm[eV, fV, mkComb[indSuccConst[], iV], aV];
    assumeGraphIndSuc = ASSUME[graphAtIndSuc];
    Module[{unfolded},
      unfolded = EQMP[
        unfoldIterGraph[eV, fV, mkComb[indSuccConst[], iV], aV],
        assumeGraphIndSuc];
      (* (folded) ⊢ ∀S. premise ⇒ S (IND_SUC i) a *)
      specSExtract = HOL`Bool`SPEC[sExtractLam, unfolded];
    ];
    (* (graphIA) ⊢ premise[sExtractLam/S] ⇒ sExtractLam (IND_SUC i) a *)
    mpThroughPremise = HOL`Bool`MP[specSExtract, premiseProof];
    (* (graphIA) ⊢ sExtractLam (IND_SUC i) a (un-β) *)

    Module[{sLamAppIa, betaIa, betaForm},
      sLamAppIa = mkComb[mkComb[sExtractLam, mkComb[indSuccConst[], iV]], aV];
      betaIa = HOL`Drule`DEPTHCONV[
        HOL`Drule`TRYCONV[BETACONV]][sLamAppIa];
      betaForm = EQMP[betaIa, mpThroughPremise];
      (* (graphIA) ⊢ ITER_GRAPH e f (IND_SUC i) a                  *)
      (*              ∧ (∀j. IND_SUC i = IND_SUC j                  *)
      (*                     ⇒ ∃b. a = f b ∧ ITER_GRAPH e f j b)    *)
      conj2OfS = HOL`Bool`CONJUNCT2[betaForm];
      specJAtI = HOL`Bool`SPEC[iV, conj2OfS];
      (* (graphIA) ⊢ IND_SUC i = IND_SUC i ⇒ ∃b. a = f b ∧ ITER_GRAPH e f i b *)
      mpReflSucI = HOL`Bool`MP[specJAtI,
        REFL[mkComb[indSuccConst[], iV]]];
      existsResult = mpReflSucI;
      (* (graphIA) ⊢ ∃b. a = f b ∧ ITER_GRAPH e f i b *)
    ];

    dischGraphAtIndSuc = HOL`Bool`DISCH[graphAtIndSuc, existsResult];
    genA = HOL`Bool`GEN[aV, dischGraphAtIndSuc];
    genI = HOL`Bool`GEN[iV, genA]
  ];

(* ============================================================ *)
(* iterExistsLem :                                              *)
(*   ⊢ ∀i. NUM_REP i ⇒ ∃a. ITER_GRAPH e f i a                   *)
(* By NUM_REP-induction with P = λi. ∃a. ITER_GRAPH e f i a.    *)
(* ============================================================ *)

iterExistsLem =
  Module[{eV, fV, iV, aV, mV, pLam, pmTm, pSucMTm,
          ind0Exists, ind0ExistsTm,
          hypPm, hypGraphMa, sucSpec, sucMP, exSuc, choosed,
          dischPm, genM, premiseConj,
          assumeNumRepI, unfoldedNumRepI, specAtP, betaReduce,
          mpPremise, dischNumRepI, finalGen},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    iV = mkVar["i", indTy];
    aV = mkVar["a", aTy];
    mV = mkVar["m", indTy];

    (* P = λi'. ∃a. ITER_GRAPH e f i' a *)
    pLam = mkAbs[iV,
      mkComb[existsC[aTy],
        mkAbs[aV, iterGraphFoldTm[eV, fV, iV, aV]]]];

    (* ⊢ ∃a. ITER_GRAPH e f IND_0 a *)
    ind0ExistsTm = mkComb[existsC[aTy],
      mkAbs[aV, iterGraphFoldTm[eV, fV, ind0Const[], aV]]];
    ind0Exists = HOL`Bool`EXISTS[ind0ExistsTm, eV, graphInd0Lem];

    (* ⊢ ∀m. (∃a. ITER_GRAPH e f m a) ⇒ (∃a. ITER_GRAPH e f (IND_SUC m) a) *)
    pmTm    = mkComb[existsC[aTy],
      mkAbs[aV, iterGraphFoldTm[eV, fV, mV, aV]]];
    pSucMTm = mkComb[existsC[aTy],
      mkAbs[aV, iterGraphFoldTm[eV, fV, mkComb[indSuccConst[], mV], aV]]];
    hypPm        = ASSUME[pmTm];
    hypGraphMa   = ASSUME[iterGraphFoldTm[eV, fV, mV, aV]];
    sucSpec = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[mV, graphSucLem]];
    sucMP = HOL`Bool`MP[sucSpec, hypGraphMa];
    exSuc = HOL`Bool`EXISTS[pSucMTm, mkComb[fV, aV], sucMP];
    choosed = HOL`Bool`CHOOSE[aV, hypPm, exSuc];
    dischPm = HOL`Bool`DISCH[pmTm, choosed];
    genM = HOL`Bool`GEN[mV, dischPm];

    premiseConj = HOL`Bool`CONJ[ind0Exists, genM];

    assumeNumRepI = ASSUME[mkComb[numRepConst[], iV]];
    unfoldedNumRepI = EQMP[unfoldNumRep[iV], assumeNumRepI];
    specAtP = HOL`Bool`SPEC[pLam, unfoldedNumRepI];
    betaReduce = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specAtP];
    mpPremise = HOL`Bool`MP[betaReduce, premiseConj];
    dischNumRepI = HOL`Bool`DISCH[mkComb[numRepConst[], iV], mpPremise];
    finalGen = HOL`Bool`GEN[iV, dischNumRepI]
  ];

(* ============================================================ *)
(* iterUniqueLem :                                              *)
(*   ⊢ ∀i. NUM_REP i ⇒                                          *)
(*           ∀a b. ITER_GRAPH e f i a ∧ ITER_GRAPH e f i b      *)
(*                  ⇒ a = b                                      *)
(* By NUM_REP-induction.                                        *)
(*   Base: graphUniqInd0Lem twice + TRANS.                       *)
(*   Step: graphExtractLem on each of the two assumptions →     *)
(*     CHOOSE the extracted witnesses → IH gives the witnesses  *)
(*     are equal → APTERM f + TRANS gives a = b.                *)
(* ============================================================ *)

iterUniqueLem =
  Module[{eV, fV, iV, aV, bV, mV, a1V, b1V,
          pLam, pmBody,
          (* base *)
          baseAndTm, baseHyp, baseC1, baseC2, baseAEqE, baseBEqE,
          baseAEqB, baseDischAnd, baseGenB, baseGenA, baseProof,
          (* step *)
          hypPmTm, hypPm, stepAndTm, stepHyp, stepC1, stepC2,
          ex1, ex2, body1Tm, body2Tm, hyp1, hyp2,
          c1Eq, c1Gr, c2Eq, c2Gr,
          hpmInstAB, conjGraphs, a1Eqb1, sameF, aEqFb1, aEqB,
          chooseB1, chooseA1, stepDischAnd, stepGenB, stepGenA,
          stepDischPm, stepProof,
          (* induction *)
          premiseConj, assumeNumRepI, unfoldedNumRepI, specAtP,
          betaReduce, mpPremise, dischNumRepI, finalGen},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    iV = mkVar["i", indTy];
    aV = mkVar["a", aTy];
    bV = mkVar["b", aTy];
    mV = mkVar["m", indTy];
    a1V = mkVar["a1", aTy];
    b1V = mkVar["b1", aTy];

    (* P = λi'. ∀a b. ITER_GRAPH e f i' a ∧ ITER_GRAPH e f i' b ⇒ a = b *)
    pLam = mkAbs[iV,
      mkComb[forallC[aTy], mkAbs[aV,
        mkComb[forallC[aTy], mkAbs[bV,
          impTm[
            andTm[iterGraphFoldTm[eV, fV, iV, aV],
                  iterGraphFoldTm[eV, fV, iV, bV]],
            mkEq[aV, bV]]]]]]];

    (* --------- Base: ⊢ P IND_0 (β-norm) --------- *)
    baseAndTm = andTm[
      iterGraphFoldTm[eV, fV, ind0Const[], aV],
      iterGraphFoldTm[eV, fV, ind0Const[], bV]];
    baseHyp = ASSUME[baseAndTm];
    baseC1 = HOL`Bool`CONJUNCT1[baseHyp];
    baseC2 = HOL`Bool`CONJUNCT2[baseHyp];
    baseAEqE = HOL`Bool`MP[HOL`Bool`SPEC[aV, graphUniqInd0Lem], baseC1];
    baseBEqE = HOL`Bool`MP[HOL`Bool`SPEC[bV, graphUniqInd0Lem], baseC2];
    baseAEqB = TRANS[baseAEqE, HOL`Equal`SYM[baseBEqE]];
    baseDischAnd = HOL`Bool`DISCH[baseAndTm, baseAEqB];
    baseGenB = HOL`Bool`GEN[bV, baseDischAnd];
    baseProof = HOL`Bool`GEN[aV, baseGenB];

    (* --------- Step: ⊢ ∀m. P m ⇒ P (IND_SUC m) --------- *)
    (* P m (β-norm). *)
    pmBody = mkComb[forallC[aTy], mkAbs[aV,
      mkComb[forallC[aTy], mkAbs[bV,
        impTm[
          andTm[iterGraphFoldTm[eV, fV, mV, aV],
                iterGraphFoldTm[eV, fV, mV, bV]],
          mkEq[aV, bV]]]]]];
    hypPm = ASSUME[pmBody];

    stepAndTm = andTm[
      iterGraphFoldTm[eV, fV, mkComb[indSuccConst[], mV], aV],
      iterGraphFoldTm[eV, fV, mkComb[indSuccConst[], mV], bV]];
    stepHyp = ASSUME[stepAndTm];
    stepC1 = HOL`Bool`CONJUNCT1[stepHyp];
    stepC2 = HOL`Bool`CONJUNCT2[stepHyp];

    (* Extract witnesses via graphExtractLem. *)
    ex1 = HOL`Bool`MP[
      HOL`Bool`SPEC[aV, HOL`Bool`SPEC[mV, graphExtractLem]], stepC1];
    ex2 = HOL`Bool`MP[
      HOL`Bool`SPEC[bV, HOL`Bool`SPEC[mV, graphExtractLem]], stepC2];

    body1Tm = andTm[
      mkEq[aV, mkComb[fV, a1V]],
      iterGraphFoldTm[eV, fV, mV, a1V]];
    body2Tm = andTm[
      mkEq[bV, mkComb[fV, b1V]],
      iterGraphFoldTm[eV, fV, mV, b1V]];
    hyp1 = ASSUME[body1Tm];
    hyp2 = ASSUME[body2Tm];

    c1Eq = HOL`Bool`CONJUNCT1[hyp1];   (* a = f a1 *)
    c1Gr = HOL`Bool`CONJUNCT2[hyp1];   (* ITER_GRAPH e f m a1 *)
    c2Eq = HOL`Bool`CONJUNCT1[hyp2];   (* b = f b1 *)
    c2Gr = HOL`Bool`CONJUNCT2[hyp2];   (* ITER_GRAPH e f m b1 *)

    hpmInstAB = HOL`Bool`SPEC[b1V, HOL`Bool`SPEC[a1V, hypPm]];
    (* ⊢ ITER_GRAPH e f m a1 ∧ ITER_GRAPH e f m b1 ⇒ a1 = b1 *)
    conjGraphs = HOL`Bool`CONJ[c1Gr, c2Gr];
    a1Eqb1 = HOL`Bool`MP[hpmInstAB, conjGraphs];
    sameF = HOL`Equal`APTERM[fV, a1Eqb1];
    aEqFb1 = TRANS[c1Eq, sameF];
    aEqB = TRANS[aEqFb1, HOL`Equal`SYM[c2Eq]];
    (* Hyps: {hypPm, body1Tm, body2Tm, stepAndTm} *)

    (* CHOOSE b1V from ex2. b1V must not be free in conclusion (aEqB has a, b, *)
    (* not b1) nor in ex2.hyps (hypAnd has eV, fV, mV, aV, bV — no b1V). *)
    chooseB1 = HOL`Bool`CHOOSE[b1V, ex2, aEqB];
    (* hyps now: {hypPm, body1Tm, stepAndTm} *)
    chooseA1 = HOL`Bool`CHOOSE[a1V, ex1, chooseB1];
    (* hyps: {hypPm, stepAndTm} *)

    stepDischAnd = HOL`Bool`DISCH[stepAndTm, chooseA1];
    stepGenB = HOL`Bool`GEN[bV, stepDischAnd];
    stepGenA = HOL`Bool`GEN[aV, stepGenB];
    stepDischPm = HOL`Bool`DISCH[pmBody, stepGenA];
    stepProof = HOL`Bool`GEN[mV, stepDischPm];

    (* --------- NUM_REP induction --------- *)
    premiseConj = HOL`Bool`CONJ[baseProof, stepProof];
    assumeNumRepI = ASSUME[mkComb[numRepConst[], iV]];
    unfoldedNumRepI = EQMP[unfoldNumRep[iV], assumeNumRepI];
    specAtP = HOL`Bool`SPEC[pLam, unfoldedNumRepI];
    betaReduce = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], specAtP];
    mpPremise = HOL`Bool`MP[betaReduce, premiseConj];
    dischNumRepI = HOL`Bool`DISCH[mkComb[numRepConst[], iV], mpPremise];
    finalGen = HOL`Bool`GEN[iV, dischNumRepI]
  ];

(* ============================================================ *)
(* ITER : A → (A→A) → num → A                                    *)
(*   ITER e f n = ε a. ITER_GRAPH e f (REP_num n) a              *)
(* ============================================================ *)

iterTy = tyFun[aTy, tyFun[funATy, tyFun[numTy, aTy]]];

iterDefBody[] :=
  Module[{eV, fV, nV, aV},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    nV = mkVar["n", numTy];
    aV = mkVar["a", aTy];
    mkAbs[eV, mkAbs[fV, mkAbs[nV,
      mkComb[selectC[aTy],
        mkAbs[aV,
          iterGraphFoldTm[eV, fV,
            mkComb[repNumConst[], nV], aV]]]]]]
  ];

iterDefThm = newDefinition[mkEq[
  mkVar["ITER", iterTy],
  iterDefBody[]
]];

iterConst[] := mkConst["ITER", iterTy];

(* ============================================================ *)
(* iterZeroEqThm : ⊢ ITER e f 0 = e                              *)
(*                                                              *)
(*   1. Unfold ITER at (e, f, 0) via three APTHM + BETACONV     *)
(*      to get `⊢ ITER e f 0 = ε a. ITER_GRAPH e f (REP_num 0) a`.*)
(*   2. Replace `REP_num 0` by `IND_0` under the ε via           *)
(*      APTERM/APTHM + ABS + APTERM[@] using repZeroThm.         *)
(*   3. Use selectOfExists at predLam = λa. ITER_GRAPH e f IND_0 a*)
(*      with existsTh = `⊢ ∃a. ITER_GRAPH e f IND_0 a` (via       *)
(*      EXISTS on graphInd0Lem) to get                          *)
(*      `⊢ ITER_GRAPH e f IND_0 (@ predLam)`. Note @ predLam IS  *)
(*      the right-hand-side term after step 2 (same construction).*)
(*   4. SPEC `@ predLam` in graphUniqInd0Lem, MP step 3,         *)
(*      yielding `⊢ (@ predLam) = e`.                            *)
(*   5. TRANS step 1, step 2, step 4 gives `⊢ ITER e f 0 = e`.   *)
(* ============================================================ *)

(* Apply iterDefThm at (eTm, fTm, nTm), β-reducing each step.   *)
unfoldIterAt[eTm_, fTm_, nTm_] :=
  Module[{ap1, ap2, ap3},
    ap1 = HOL`Equal`APTHM[iterDefThm, eTm];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, fTm];
    ap2 = TRANS[ap2, BETACONV[concl[ap2][[2]]]];
    ap3 = HOL`Equal`APTHM[ap2, nTm];
    TRANS[ap3, BETACONV[concl[ap3][[2]]]]
  ];

iterZeroEqThm =
  Module[{eV, fV, aV, iterEfAt0, predLamInd0, epsTmInd0,
          ind0ExistsTm, ind0Exists, epsSatisfies,
          uniqAtEps, epsEqE,
          repZeroLift, repZeroLiftStep, predLamRepZero, epsTmRepZero,
          finalChain},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    aV = mkVar["a", aTy];

    (* Step 1: ⊢ ITER e f 0 = ε a. ITER_GRAPH e f (REP_num 0) a *)
    iterEfAt0 = unfoldIterAt[eV, fV, zeroConst[]];

    (* Build the predicates / ε-terms for IND_0 and REP_num 0. *)
    predLamInd0 = mkAbs[aV, iterGraphFoldTm[eV, fV, ind0Const[], aV]];
    epsTmInd0 = mkComb[selectC[aTy], predLamInd0];
    predLamRepZero = mkAbs[aV,
      iterGraphFoldTm[eV, fV, mkComb[repNumConst[], zeroConst[]], aV]];
    epsTmRepZero = mkComb[selectC[aTy], predLamRepZero];

    (* Step 2: ⊢ ε a. ITER_GRAPH e f (REP_num 0) a                  *)
    (*           = ε a. ITER_GRAPH e f IND_0 a.                     *)
    (* For free aV, ⊢ ITER_GRAPH e f (REP_num 0) aV                 *)
    (*                = ITER_GRAPH e f IND_0 aV by APTHM repZeroThm. *)
    Module[{ap1, absStep, selStep},
      ap1 = HOL`Equal`APTHM[
        HOL`Equal`APTERM[
          mkComb[mkComb[iterGraphConst[], eV], fV],
          repZeroThm],
        aV];
      (* ⊢ ITER_GRAPH e f (REP_num 0) aV = ITER_GRAPH e f IND_0 aV *)
      absStep = HOL`Kernel`ABS[aV, ap1];
      (* ⊢ (λa. ITER_GRAPH e f (REP_num 0) a) = (λa. ITER_GRAPH e f IND_0 a) *)
      selStep = HOL`Equal`APTERM[selectC[aTy], absStep];
      (* ⊢ (ε a. ITER_GRAPH e f (REP_num 0) a)                       *)
      (*    = (ε a. ITER_GRAPH e f IND_0 a)                          *)
      repZeroLift = selStep;
    ];

    (* Step 3: ⊢ ITER_GRAPH e f IND_0 (ε a. ITER_GRAPH e f IND_0 a). *)
    ind0ExistsTm = mkComb[existsC[aTy], predLamInd0];
    ind0Exists = HOL`Bool`EXISTS[ind0ExistsTm, eV, graphInd0Lem];
    epsSatisfies = HOL`Stdlib`Num`selectOfExists[predLamInd0, ind0Exists];
    (* selectOfExists already β-reduces internally; epsSatisfies is        *)
    (* ⊢ ITER_GRAPH e f IND_0 (@predLamInd0) in β-normal form.              *)

    (* Step 4: ⊢ (@ predLamInd0) = e. *)
    uniqAtEps = HOL`Bool`SPEC[epsTmInd0, graphUniqInd0Lem];
    (* ⊢ ITER_GRAPH e f IND_0 (epsTmInd0) ⇒ epsTmInd0 = e *)
    epsEqE = HOL`Bool`MP[uniqAtEps, epsSatisfies];

    (* Step 5: TRANS iterEfAt0 + repZeroLift + epsEqE. *)
    finalChain = TRANS[TRANS[iterEfAt0, repZeroLift], epsEqE]
  ];

(* ============================================================ *)
(* iterSucEqThm : ⊢ ∀n. ITER e f (SUC n) = f (ITER e f n)        *)
(* ============================================================ *)

iterSucEqThm =
  Module[{eV, fV, nV, aV,
          repN, repSucN, iterEfSucN, iterEfN,
          itnSatisfies, atSucGraphAtSuc,
          finalChain,
          atIterEfSucNTm, atIterEfNTm,
          predLamAtRepN, epsTmAtRepN,
          predLamAtRepSucN, epsTmAtRepSucN,
          predLamAtIndSucRepN, epsTmAtIndSucRepN,
          graphSucInst, graphSucMp, repSucEqAtN},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    nV = mkVar["n", numTy];
    aV = mkVar["a", aTy];

    repN    = mkComb[repNumConst[], nV];
    repSucN = mkComb[repNumConst[], mkComb[sucConst[], nV]];

    (* iter equations as terms. *)
    iterEfN     = mkComb[mkComb[mkComb[iterConst[], eV], fV], nV];
    iterEfSucN  = mkComb[mkComb[mkComb[iterConst[], eV], fV],
                          mkComb[sucConst[], nV]];

    (* Unfold ITER e f n and ITER e f (SUC n). *)
    atIterEfNTm = unfoldIterAt[eV, fV, nV];
    (* ⊢ ITER e f n = ε a. ITER_GRAPH e f (REP_num n) a *)
    atIterEfSucNTm = unfoldIterAt[eV, fV, mkComb[sucConst[], nV]];
    (* ⊢ ITER e f (SUC n) = ε a. ITER_GRAPH e f (REP_num (SUC n)) a *)

    (* Define ε-terms and predicate lambdas. *)
    predLamAtRepN = mkAbs[aV, iterGraphFoldTm[eV, fV, repN, aV]];
    epsTmAtRepN = mkComb[selectC[aTy], predLamAtRepN];

    predLamAtRepSucN = mkAbs[aV, iterGraphFoldTm[eV, fV, repSucN, aV]];
    epsTmAtRepSucN = mkComb[selectC[aTy], predLamAtRepSucN];

    predLamAtIndSucRepN = mkAbs[aV,
      iterGraphFoldTm[eV, fV, mkComb[indSuccConst[], repN], aV]];
    epsTmAtIndSucRepN = mkComb[selectC[aTy], predLamAtIndSucRepN];

    (* iter exists at REP_num n (we have NUM_REP (REP_num n)). *)
    Module[{numRepRepN, ipsExistsThm},
      numRepRepN = HOL`Kernel`INST[
        {mkVar["n", numTy] -> nV}, numRepRepNumThm];
      ipsExistsThm = HOL`Bool`MP[
        HOL`Bool`SPEC[repN, iterExistsLem], numRepRepN];
      itnSatisfies = HOL`Stdlib`Num`selectOfExists[
        predLamAtRepN, ipsExistsThm];
    ];

    (* Apply graphSucLem at (REP_num n, epsTmAtRepN) to get:           *)
    (* ⊢ ITER_GRAPH e f (IND_SUC (REP_num n)) (f epsTmAtRepN).         *)
    graphSucInst = HOL`Bool`SPEC[epsTmAtRepN,
      HOL`Bool`SPEC[repN, graphSucLem]];
    graphSucMp = HOL`Bool`MP[graphSucInst, itnSatisfies];
    (* graphSucMp : ⊢ ITER_GRAPH e f (IND_SUC (REP_num n)) (f epsTmAtRepN) *)

    (* Lift via repSucThm: IND_SUC (REP_num n) = REP_num (SUC n).      *)
    repSucEqAtN = HOL`Kernel`INST[
      {mkVar["n", numTy] -> nV}, repSucThm];
    (* repSucEqAtN : ⊢ REP_num (SUC n) = IND_SUC (REP_num n)            *)
    Module[{ap1},
      ap1 = HOL`Equal`APTHM[
        HOL`Equal`APTERM[
          mkComb[mkComb[iterGraphConst[], eV], fV],
          HOL`Equal`SYM[repSucEqAtN]],
        mkComb[fV, epsTmAtRepN]];
      (* ap1 : ⊢ ITER_GRAPH e f (IND_SUC (REP_num n)) (f epsTmAtRepN) *)
      (*       = ITER_GRAPH e f (REP_num (SUC n)) (f epsTmAtRepN)     *)
      atSucGraphAtSuc = EQMP[ap1, graphSucMp];
    ];

    (* ITER e f (SUC n) = εTmAtRepSucN (from atIterEfSucNTm).         *)
    (* Want: ⊢ εTmAtRepSucN = f epsTmAtRepN.                            *)
    (* Use uniqueness: numRepRepNumThm at (SUC n) ⇒ NUM_REP (REP_num (SUC n)). *)
    (* Hence iterUniqueLem SPEC'd at REP_num (SUC n), MP with NUM_REP,  *)
    (* SPEC'd at εTmAtRepSucN and (f epsTmAtRepN), MP with the          *)
    (* CONJ of `ITER_GRAPH e f (REP_num (SUC n)) εTmAtRepSucN` (from   *)
    (* selectOfExists at predLamAtRepSucN + iterExistsLem at REP_num (SUC n)) *)
    (* and atSucGraphAtSuc.                                             *)
    Module[{numRepRepSucN, ipsExistsAtSucThm, satisfiesAtSuc,
            eitherSat, uniqAtSucN, uniqInstEps, mpForUniq, eqIt},
      numRepRepSucN = HOL`Kernel`INST[
        {mkVar["n", numTy] -> mkComb[sucConst[], nV]}, numRepRepNumThm];
      ipsExistsAtSucThm = HOL`Bool`MP[
        HOL`Bool`SPEC[repSucN, iterExistsLem], numRepRepSucN];
      satisfiesAtSuc = HOL`Stdlib`Num`selectOfExists[
        predLamAtRepSucN, ipsExistsAtSucThm];
      (* satisfiesAtSuc : ⊢ ITER_GRAPH e f (REP_num (SUC n)) (epsTmAtRepSucN) *)

      uniqAtSucN = HOL`Bool`MP[
        HOL`Bool`SPEC[repSucN, iterUniqueLem], numRepRepSucN];
      (* uniqAtSucN : ⊢ ∀a b. ITER_GRAPH e f (REP_num (SUC n)) a       *)
      (*                       ∧ ITER_GRAPH e f (REP_num (SUC n)) b   *)
      (*                       ⇒ a = b                                  *)
      uniqInstEps = HOL`Bool`SPEC[mkComb[fV, epsTmAtRepN],
        HOL`Bool`SPEC[epsTmAtRepSucN, uniqAtSucN]];
      (* ⊢ ITER_GRAPH e f (REP_num (SUC n)) epsTmAtRepSucN              *)
      (*    ∧ ITER_GRAPH e f (REP_num (SUC n)) (f epsTmAtRepN)          *)
      (*    ⇒ epsTmAtRepSucN = f epsTmAtRepN                            *)
      mpForUniq = HOL`Bool`MP[uniqInstEps,
        HOL`Bool`CONJ[satisfiesAtSuc, atSucGraphAtSuc]];
      (* mpForUniq : ⊢ epsTmAtRepSucN = f epsTmAtRepN *)

      (* Combine with atIterEfSucNTm and SYM[atIterEfNTm]:              *)
      (* ITER e f (SUC n) = epsTmAtRepSucN = f epsTmAtRepN = f (ITER e f n) *)
      Module[{atIterEfNSym, fAtIterN, transFinal},
        atIterEfNSym = HOL`Equal`SYM[atIterEfNTm];
        (* ⊢ epsTmAtRepN = ITER e f n *)
        fAtIterN = HOL`Equal`APTERM[fV, atIterEfNSym];
        (* ⊢ f epsTmAtRepN = f (ITER e f n) *)
        eqIt = TRANS[TRANS[atIterEfSucNTm, mpForUniq], fAtIterN];
        (* eqIt : ⊢ ITER e f (SUC n) = f (ITER e f n) *)
        finalChain = eqIt;
      ];
    ];

    HOL`Bool`GEN[nV, finalChain]
  ];

(* ============================================================ *)
(* numIterationThm :                                            *)
(*   ⊢ ∀e:A. ∀f:A→A. ∃g:num→A. g 0 = e ∧ ∀n. g (SUC n) = f (g n)*)
(*                                                              *)
(* Witness: g = ITER e f. CONJ the two equations and EXISTS.    *)
(* ============================================================ *)

numIterationThm =
  Module[{eV, fV, nV, witness, conjBody, exTm, existsTh, genF, genE},
    eV = mkVar["e", aTy];
    fV = mkVar["f", funATy];
    nV = mkVar["n", numTy];
    witness = mkComb[mkComb[iterConst[], eV], fV];
    (* The desired body in terms of `g`. *)
    (* ∃g. g 0 = e ∧ ∀n. g (SUC n) = f (g n)                            *)
    Module[{gV, gBody, gAt0Eq, gSucNeq, conjForG, exFormula, witnessConj},
      gV = mkVar["g", tyFun[numTy, aTy]];
      gAt0Eq = mkEq[mkComb[gV, zeroConst[]], eV];
      gSucNeq = mkComb[forallC[numTy], mkAbs[nV,
        mkEq[
          mkComb[gV, mkComb[sucConst[], nV]],
          mkComb[fV, mkComb[gV, nV]]]]];
      conjForG = andTm[gAt0Eq, gSucNeq];
      exFormula = mkComb[existsC[tyFun[numTy, aTy]],
        mkAbs[gV, conjForG]];

      (* Build the conj of equations at g = witness. *)
      witnessConj = HOL`Bool`CONJ[iterZeroEqThm, iterSucEqThm];
      existsTh = HOL`Bool`EXISTS[exFormula, witness, witnessConj];
    ];
    genF = HOL`Bool`GEN[fV, existsTh];
    genE = HOL`Bool`GEN[eV, genF]
  ];

(* ============================================================ *)
(* + : num → num → num                                          *)
(*   m + n = ITER m SUC n                                        *)
(* ============================================================ *)

plusTy = tyFun[numTy, tyFun[numTy, numTy]];

(* ITER instantiated at A := num. *)
iterAtNumConst[] :=
  mkConst["ITER", tyFun[numTy,
    tyFun[tyFun[numTy, numTy], tyFun[numTy, numTy]]]];

plusDefBody[] :=
  Module[{mV, nV},
    mV = mkVar["m", numTy];
    nV = mkVar["n", numTy];
    mkAbs[mV, mkAbs[nV,
      mkComb[mkComb[mkComb[iterAtNumConst[], mV], sucConst[]], nV]]]
  ];

plusDefThm = newDefinition[mkEq[
  mkVar["+", plusTy],
  plusDefBody[]
]];

plusConst[] := mkConst["+", plusTy];

plusTm[mTm_, nTm_] := mkComb[mkComb[plusConst[], mTm], nTm];

(* Unfold m + n via plusDefThm. ⊢ m + n = ITER m SUC n. *)
unfoldPlus[mTm_, nTm_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[plusDefThm, mTm];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, nTm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ ∀m. m + 0 = m  via iterZeroEqThm at e=m, f=SUC. *)
plusZeroEqThm =
  Module[{mV, unfoldedTo0, iterAt0AtNum, instE, trans, genM},
    mV = mkVar["m", numTy];
    unfoldedTo0 = unfoldPlus[mV, zeroConst[]];
    (* ⊢ m + 0 = ITER m SUC 0 *)
    iterAt0AtNum = HOL`Kernel`INSTTYPE[
      {tyVar["A"] -> numTy}, iterZeroEqThm];
    (* ⊢ ITER e f 0 = e (at concrete num types) *)
    instE = HOL`Kernel`INST[
      {mkVar["e", numTy] -> mV,
       mkVar["f", tyFun[numTy, numTy]] -> sucConst[]},
      iterAt0AtNum];
    (* ⊢ ITER m SUC 0 = m *)
    trans = TRANS[unfoldedTo0, instE];
    genM = HOL`Bool`GEN[mV, trans]
  ];

(* ⊢ ∀m n. m + (SUC n) = SUC (m + n)  via iterSucEqThm. *)
plusSucEqThm =
  Module[{mV, nV, unfoldedToSucN, unfoldedToN,
          iterSucAtNum, instE, specN, trans1, symUnfoldedToN,
          sucApply, finalTh, genN, genM},
    mV = mkVar["m", numTy];
    nV = mkVar["n", numTy];
    unfoldedToSucN = unfoldPlus[mV, mkComb[sucConst[], nV]];
    (* ⊢ m + (SUC n) = ITER m SUC (SUC n) *)
    iterSucAtNum = HOL`Kernel`INSTTYPE[
      {tyVar["A"] -> numTy}, iterSucEqThm];
    (* ⊢ ∀n. ITER e f (SUC n) = f (ITER e f n) (at num) *)
    instE = HOL`Kernel`INST[
      {mkVar["e", numTy] -> mV,
       mkVar["f", tyFun[numTy, numTy]] -> sucConst[]},
      iterSucAtNum];
    specN = HOL`Bool`SPEC[nV, instE];
    (* ⊢ ITER m SUC (SUC n) = SUC (ITER m SUC n) *)
    trans1 = TRANS[unfoldedToSucN, specN];
    (* ⊢ m + (SUC n) = SUC (ITER m SUC n) *)
    unfoldedToN = unfoldPlus[mV, nV];
    (* ⊢ m + n = ITER m SUC n *)
    symUnfoldedToN = HOL`Equal`SYM[unfoldedToN];
    (* ⊢ ITER m SUC n = m + n *)
    sucApply = HOL`Equal`APTERM[sucConst[], symUnfoldedToN];
    (* ⊢ SUC (ITER m SUC n) = SUC (m + n) *)
    finalTh = TRANS[trans1, sucApply];
    (* ⊢ m + (SUC n) = SUC (m + n) *)
    genN = HOL`Bool`GEN[nV, finalTh];
    genM = HOL`Bool`GEN[mV, genN]
  ];

(* ============================================================ *)
(* addLeftZeroThm : ⊢ ∀n. 0 + n = n   (by induction)              *)
(* ============================================================ *)

addLeftZeroThm =
  Module[{nV, pLam, baseTh, hypIh, plusSucAt0n, sucIh,
          stepTh, dischIh, genN, premise, indSpec, indBeta, mpInd},
    nV = mkVar["n", numTy];

    (* P = λn. 0 + n = n. *)
    pLam = mkAbs[nV, mkEq[plusTm[zeroConst[], nV], nV]];

    (* Base: ⊢ 0 + 0 = 0. *)
    baseTh = HOL`Bool`SPEC[zeroConst[], plusZeroEqThm];

    (* Step: ASSUME 0 + n = n. Show 0 + SUC n = SUC n. *)
    hypIh = ASSUME[mkEq[plusTm[zeroConst[], nV], nV]];
    plusSucAt0n = HOL`Bool`SPEC[nV,
      HOL`Bool`SPEC[zeroConst[], plusSucEqThm]];
    (* ⊢ 0 + SUC n = SUC (0 + n) *)
    sucIh = HOL`Equal`APTERM[sucConst[], hypIh];
    (* (IH) ⊢ SUC (0 + n) = SUC n *)
    stepTh = TRANS[plusSucAt0n, sucIh];
    (* (IH) ⊢ 0 + SUC n = SUC n *)
    dischIh = HOL`Bool`DISCH[concl[hypIh], stepTh];
    genN = HOL`Bool`GEN[nV, dischIh];

    premise = HOL`Bool`CONJ[baseTh, genN];
    indSpec = HOL`Bool`SPEC[pLam, numInductionThm];
    indBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], indSpec];
    HOL`Bool`MP[indBeta, premise]
  ];

(* ============================================================ *)
(* * : num → num → num                                          *)
(*   m * n = ITER 0 (λa. a + m) n                                *)
(* ============================================================ *)

timesTy = tyFun[numTy, tyFun[numTy, numTy]];

(* λa:num. a + mV  — the step function for multiplication.       *)
timesStepLam[mTm_] :=
  Module[{aV},
    aV = mkVar["a", numTy];
    mkAbs[aV, plusTm[aV, mTm]]
  ];

timesDefBody[] :=
  Module[{mV, nV},
    mV = mkVar["m", numTy];
    nV = mkVar["n", numTy];
    mkAbs[mV, mkAbs[nV,
      mkComb[
        mkComb[mkComb[iterAtNumConst[], zeroConst[]], timesStepLam[mV]],
        nV]]]
  ];

timesDefThm = newDefinition[mkEq[
  mkVar["*", timesTy],
  timesDefBody[]
]];

timesConst[] := mkConst["*", timesTy];

timesTm[mTm_, nTm_] := mkComb[mkComb[timesConst[], mTm], nTm];

unfoldTimes[mTm_, nTm_] :=
  Module[{ap1, ap2},
    ap1 = HOL`Equal`APTHM[timesDefThm, mTm];
    ap1 = TRANS[ap1, BETACONV[concl[ap1][[2]]]];
    ap2 = HOL`Equal`APTHM[ap1, nTm];
    TRANS[ap2, BETACONV[concl[ap2][[2]]]]
  ];

(* ⊢ ∀m. m * 0 = 0.  Via iterZeroEqThm at e=0, f=λa. a + m. *)
timesZeroEqThm =
  Module[{mV, unfoldedTo0, iterAt0AtNum, instE, trans, genM},
    mV = mkVar["m", numTy];
    unfoldedTo0 = unfoldTimes[mV, zeroConst[]];
    (* ⊢ m * 0 = ITER 0 (λa. a + m) 0 *)
    iterAt0AtNum = HOL`Kernel`INSTTYPE[
      {tyVar["A"] -> numTy}, iterZeroEqThm];
    instE = HOL`Kernel`INST[
      {mkVar["e", numTy] -> zeroConst[],
       mkVar["f", tyFun[numTy, numTy]] -> timesStepLam[mV]},
      iterAt0AtNum];
    (* ⊢ ITER 0 (λa. a + m) 0 = 0 *)
    trans = TRANS[unfoldedTo0, instE];
    genM = HOL`Bool`GEN[mV, trans]
  ];

(* ⊢ ∀m n. m * (SUC n) = m * n + m.                              *)
(* Via iterSucEqThm: ITER 0 (λa. a + m) (SUC n)                  *)
(*                    = (λa. a + m) (ITER 0 (λa. a + m) n).       *)
(* β-reduce the RHS application: = (ITER 0 (λa. a + m) n) + m.    *)
(* And ITER 0 (λa. a + m) n = m * n by SYM of unfoldTimes.        *)
timesSucEqThm =
  Module[{mV, nV, unfoldedToSucN, unfoldedToN,
          iterSucAtNum, instE, specN, trans1,
          itnPlusMTm, betaStep, symUnfoldedToN,
          plusApply, finalTh, genN, genM},
    mV = mkVar["m", numTy];
    nV = mkVar["n", numTy];
    unfoldedToSucN = unfoldTimes[mV, mkComb[sucConst[], nV]];
    (* ⊢ m * (SUC n) = ITER 0 (λa. a + m) (SUC n) *)
    iterSucAtNum = HOL`Kernel`INSTTYPE[
      {tyVar["A"] -> numTy}, iterSucEqThm];
    instE = HOL`Kernel`INST[
      {mkVar["e", numTy] -> zeroConst[],
       mkVar["f", tyFun[numTy, numTy]] -> timesStepLam[mV]},
      iterSucAtNum];
    specN = HOL`Bool`SPEC[nV, instE];
    (* ⊢ ITER 0 (λa. a + m) (SUC n)                                  *)
    (*    = (λa. a + m) (ITER 0 (λa. a + m) n)                       *)
    (* β-reduce RHS: = (ITER 0 (λa. a + m) n) + m. *)
    betaStep = BETACONV[concl[specN][[2]]];
    (* ⊢ (λa. a + m) (ITER 0 (λa. a + m) n) = ITER 0 (λa. a + m) n + m *)
    trans1 = TRANS[TRANS[unfoldedToSucN, specN], betaStep];
    (* ⊢ m * (SUC n) = ITER 0 (λa. a + m) n + m *)
    unfoldedToN = unfoldTimes[mV, nV];
    symUnfoldedToN = HOL`Equal`SYM[unfoldedToN];
    (* ⊢ ITER 0 (λa. a + m) n = m * n *)
    plusApply = HOL`Equal`APTHM[
      HOL`Equal`APTERM[plusConst[], symUnfoldedToN],
      mV];
    (* ⊢ (ITER 0 (λa. a + m) n) + m = (m * n) + m *)
    finalTh = TRANS[trans1, plusApply];
    genN = HOL`Bool`GEN[nV, finalTh];
    genM = HOL`Bool`GEN[mV, genN]
  ];

(* ============================================================ *)
(* timesLeftZeroThm : ⊢ ∀n. 0 * n = 0 (by induction)             *)
(* ============================================================ *)

timesLeftZeroThm =
  Module[{nV, pLam, baseTh, hypIh, timesSucAt0n, plusZeroAt0,
          stepIhPlusEq, stepTh, dischIh, genN, premise,
          indSpec, indBeta, sym1},
    nV = mkVar["n", numTy];

    pLam = mkAbs[nV, mkEq[timesTm[zeroConst[], nV], zeroConst[]]];

    baseTh = HOL`Bool`SPEC[zeroConst[], timesZeroEqThm];

    hypIh = ASSUME[mkEq[timesTm[zeroConst[], nV], zeroConst[]]];
    (* (IH) ⊢ 0 * n = 0 *)
    timesSucAt0n = HOL`Bool`SPEC[nV,
      HOL`Bool`SPEC[zeroConst[], timesSucEqThm]];
    (* ⊢ 0 * SUC n = 0 * n + 0 *)
    (* Rewrite 0 * n → 0 via IH on the LHS of the +. *)
    stepIhPlusEq = HOL`Equal`APTHM[
      HOL`Equal`APTERM[plusConst[], hypIh], zeroConst[]];
    (* (IH) ⊢ (0 * n) + 0 = 0 + 0 *)
    plusZeroAt0 = HOL`Bool`SPEC[zeroConst[], plusZeroEqThm];
    (* ⊢ 0 + 0 = 0 *)
    stepTh = TRANS[TRANS[timesSucAt0n, stepIhPlusEq], plusZeroAt0];
    (* (IH) ⊢ 0 * SUC n = 0 *)
    dischIh = HOL`Bool`DISCH[concl[hypIh], stepTh];
    genN = HOL`Bool`GEN[nV, dischIh];

    premise = HOL`Bool`CONJ[baseTh, genN];
    indSpec = HOL`Bool`SPEC[pLam, numInductionThm];
    indBeta = HOL`Drule`CONVRULE[
      HOL`Drule`DEPTHCONV[HOL`Drule`TRYCONV[BETACONV]], indSpec];
    HOL`Bool`MP[indBeta, premise]
  ];

End[];
EndPackage[];
