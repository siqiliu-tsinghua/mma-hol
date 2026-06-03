(* M7-7 / stdlib/Real/Cut.wl — ℝ via Dedekind cuts (single lower set).

   A real number is a *lower set* L : rat → bool satisfying the Dedekind
   cut predicate

       IS_CUT L  =  (∃q. L q)                         (* nonempty       *)
                  ∧ (∃q. ¬ L q)                        (* proper / bdd above *)
                  ∧ (∀q r. L q ⇒ ratLt r q ⇒ L r)     (* downward closed *)
                  ∧ (∀q. L q ⇒ ∃r. L r ∧ ratLt q r),  (* no greatest elt *)

   i.e. L corresponds to { q : q < x } for the real x. The fourth ("open",
   no-greatest-element) clause is the canonicalizer: it forces a unique
   lower set per real, so kernel `=` on real IS real equality — NO setoid
   (continuing the Int/Rat canonical-representative tower one level up).

   real is carved from rat → bool by IS_CUT via newBasicTypeDefinition,
   with witness the principal cut of 0, { q : q < 0 }. The reusable
   principal-cut lemma `principalCutIsCutThm : ⊢ ∀q. IS_CUT (λp. p < q)`
   is exactly what `&ℝ : rat → real` will consume in Field.wl.

   This is the first stdlib milestone to follow PLAN §8.1: stdlib/Real/ is
   a FOLDER whose files share the package context HOL`Stdlib`Real` so that
   private term-builder / unfold vocabulary crosses files for free. The
   small reusable Rat/Int order lemmas built here (ratLtIrreflThm,
   ratLtTransThm, ratOfIntLtThm, intOfNumLtThm) logically belong to
   Rat/Int; kept in the Real shared vocab during construction to avoid
   churning the lower snapshots, migrate when stabilizing. *)

BeginPackage["HOL`Stdlib`Real`", {
  "HOL`Error`", "HOL`Types`", "HOL`Terms`", "HOL`Kernel`",
  "HOL`Bootstrap`", "HOL`Equal`", "HOL`Bool`", "HOL`Drule`",
  "HOL`Auto`PropTaut`",
  "HOL`Stdlib`Pair`", "HOL`Stdlib`Num`", "HOL`Stdlib`List`",
  "HOL`Stdlib`Int`", "HOL`Stdlib`Rat`"
}];

(* ===== reusable Rat/Int strict-order vocabulary (Real-internal) ===== *)
intOfNumLtThm::usage = "intOfNumLtThm — ⊢ ∀m n. intLt (&ℤ m) (&ℤ n) = (m < n). &ℤ is a strict-order embedding.";
ratOfIntLtThm::usage = "ratOfIntLtThm — ⊢ ∀a b. ratLt (&ℚ a) (&ℚ b) = intLt a b. &ℚ is a strict-order embedding.";
ratLtIrreflThm::usage = "ratLtIrreflThm — ⊢ ∀x. ¬ (ratLt x x). Strict order is irreflexive.";
ratLtTransThm::usage = "ratLtTransThm — ⊢ ∀a b c. ratLt a b ⇒ ratLt b c ⇒ ratLt a c. Strict order is transitive.";
ratZeroLtOneThm::usage = "ratZeroLtOneThm — ⊢ ratLt (&ℚ (&ℤ 0)) (&ℚ (&ℤ (SUC 0))). 0 < 1 in ℚ.";
ratNegOneLtZeroThm::usage = "ratNegOneLtZeroThm — ⊢ ratLt (ratNeg (&ℚ (&ℤ (SUC 0)))) (&ℚ (&ℤ 0)). −1 < 0 in ℚ.";
ratPredLtThm::usage = "ratPredLtThm — ⊢ ∀q. ratLt (ratAdd q (ratNeg (&ℚ (&ℤ (SUC 0))))) q. q−1 < q (a rational strictly below any q).";

(* ===== the cut predicate + carve ===== *)
isCutConst::usage = "isCutConst[] — IS_CUT : (rat → bool) → bool, the Dedekind cut predicate.";
isCutDefThm::usage = "isCutDefThm — ⊢ IS_CUT = (λL. (∃q. L q) ∧ (∃q. ¬ L q) ∧ (∀q r. L q ⇒ ratLt r q ⇒ L r) ∧ (∀q. L q ⇒ ∃r. L r ∧ ratLt q r)).";
principalCutIsCutThm::usage = "principalCutIsCutThm — ⊢ ∀q. IS_CUT (λp. ratLt p q). Every principal cut { p : p < q } is a Dedekind cut (consumed by &ℝ later).";
isCutZeroWitnessThm::usage = "isCutZeroWitnessThm — ⊢ IS_CUT (λp. ratLt p (&ℚ (&ℤ 0))). The cut of 0, witness for the type definition.";

absRealConst::usage = "absRealConst[] — ABS_real : (rat → bool) → real.";
repRealConst::usage = "repRealConst[] — REP_real : real → (rat → bool).";
absRepRealThm::usage = "absRepRealThm — ⊢ ABS_real (REP_real x) = x (round-trip on real).";
repAbsRealThm::usage = "repAbsRealThm — ⊢ IS_CUT L = (REP_real (ABS_real L) = L).";
repRealIsCutThm::usage = "repRealIsCutThm — ⊢ IS_CUT (REP_real x) (x free): REP_real lands in the carve.";

(* ===== cut accessors (the 4 IS_CUT conditions for REP_real x) ===== *)
realNonemptyThm::usage = "realNonemptyThm — ⊢ ∀x. ∃q. REP_real x q. Every real's cut is nonempty.";
realProperThm::usage = "realProperThm — ⊢ ∀x. ∃q. ¬ (REP_real x q). Every real's cut is bounded above (proper).";
realDownClosedThm::usage = "realDownClosedThm — ⊢ ∀x q r. REP_real x q ⇒ ratLt r q ⇒ REP_real x r. Every real's cut is downward closed.";
realOpenThm::usage = "realOpenThm — ⊢ ∀x q. REP_real x q ⇒ ∃r. REP_real x r ∧ ratLt q r. Every real's cut has no greatest element.";

(* ===== the order ===== *)
realLeConst::usage = "realLeConst[] — realLe : real → real → bool, the order, defined by lower-set inclusion: realLe x y ⟺ ∀q. REP_real x q ⇒ REP_real y q.";
realLeDefThm::usage = "realLeDefThm — ⊢ realLe = (λx y. ∀q. REP_real x q ⇒ REP_real y q).";
realLeReflThm::usage = "realLeReflThm — ⊢ ∀x. realLe x x.";
realLeTransThm::usage = "realLeTransThm — ⊢ ∀x y z. realLe x y ⇒ realLe y z ⇒ realLe x z.";
realLeAntisymThm::usage = "realLeAntisymThm — ⊢ ∀x y. realLe x y ⇒ realLe y x ⇒ x = y. Mutual inclusion ⟹ equal lower sets ⟹ equal reals (the canonical-representative payoff: kernel = is real equality).";
realLeTotalThm::usage = "realLeTotalThm — ⊢ ∀x y. realLe x y ∨ realLe y x. The cut order is total (uses rat trichotomy + downward closure).";

ratLeCasesThm::usage = "ratLeCasesThm — ⊢ ∀a b. ratLe a b ⇒ ratLt a b ∨ (a = b). Non-strict splits into strict-or-equal (rat trichotomy).";

realLtConst::usage = "realLtConst[] — realLt : real → real → bool, strict order, realLt x y = ¬ (realLe y x).";
realLtDefThm::usage = "realLtDefThm — ⊢ realLt = (λx y. ¬ (realLe y x)).";
realLtNotLeThm::usage = "realLtNotLeThm — ⊢ ∀x y. realLt x y = ¬ (realLe y x).";

Begin["`Private`"];

(* ============================================================ *)
(* Shared Real vocabulary: types + term builders.                *)
(* ============================================================ *)

numTy = mkType["num", {}];
intTy = mkType["int", {}];
ratTy = mkType["rat", {}];
cutTy = tyFun[ratTy, boolTy];          (* lower set L : rat → bool *)
isCutTy = tyFun[cutTy, boolTy];

(* connectives (the surrounding files' builders are in foreign Private) *)
andC[] := mkConst["∧", tyFun[boolTy, tyFun[boolTy, boolTy]]];
impC[] := mkConst["⇒", tyFun[boolTy, tyFun[boolTy, boolTy]]];
notC[] := mkConst["¬", tyFun[boolTy, boolTy]];
conjTm[a_, b_] := mkComb[mkComb[andC[], a], b];
impTm[a_, b_]  := mkComb[mkComb[impC[], a], b];
notTm[a_]      := mkComb[notC[], a];

forallC[ty_] := mkConst["∀", tyFun[tyFun[ty, boolTy], boolTy]];
existsC[ty_] := mkConst["∃", tyFun[tyFun[ty, boolTy], boolTy]];
forallTm[xV_, body_] := mkComb[forallC[typeOf[xV]], mkAbs[xV, body]];
existsTm[xV_, body_] := mkComb[existsC[typeOf[xV]], mkAbs[xV, body]];

(* numerals *)
zeroN[] := HOL`Stdlib`Num`zeroConst[];
sucT[x_] := mkComb[HOL`Stdlib`Num`sucConst[], x];

(* int / rat constructors *)
intOfNumTm[n_] := mkComb[HOL`Stdlib`Int`intOfNumConst[], n];
ratOfIntTm[z_] := mkComb[HOL`Stdlib`Rat`ratOfIntConst[], z];
ratLtC[]  := HOL`Stdlib`Rat`ratLtConst[];
ratLeC[]  := HOL`Stdlib`Rat`ratLeConst[];
ratLtTm[a_, b_] := mkComb[mkComb[ratLtC[], a], b];
ratLeTm[a_, b_] := mkComb[mkComb[ratLeC[], a], b];
ratAddTm[a_, b_] := mkComb[mkComb[HOL`Stdlib`Rat`ratAddConst[], a], b];
ratNegTm[a_] := mkComb[HOL`Stdlib`Rat`ratNegConst[], a];

(* shorthand integer / rational constants used below *)
zeroInt[] := intOfNumTm[zeroN[]];               (* &ℤ 0 *)
oneInt[]  := intOfNumTm[sucT[zeroN[]]];          (* &ℤ (SUC 0) *)
zeroQ[]   := ratOfIntTm[zeroInt[]];              (* &ℚ (&ℤ 0) *)
oneQ[]    := ratOfIntTm[oneInt[]];               (* &ℚ (&ℤ (SUC 0)) *)
negOne[]  := ratNegTm[oneQ[]];                   (* ratNeg 1 *)

(* ============================================================ *)
(* intOfNumLtThm — ⊢ ∀m n. intLt (&ℤ m)(&ℤ n) = (m < n).         *)
(*   intLt(&ℤm)(&ℤn) = ¬(intLe(&ℤn)(&ℤm)) = ¬(n≤m) = (m<n).       *)
(* ============================================================ *)

intOfNumLtThm =
  Module[{mV, nV, intM, intN, ltNotLe, leNM, apNotLe, notLtMN, ltMN,
          ddneg, apNotNotLt, notLeEqLt, chain},
    mV = mkVar["m", numTy]; nV = mkVar["n", numTy];
    intM = intOfNumTm[mV]; intN = intOfNumTm[nV];
    (* intLt (&ℤ m)(&ℤ n) = ¬ (intLe (&ℤ n)(&ℤ m)) *)
    ltNotLe = HOL`Bool`SPEC[intN, HOL`Bool`SPEC[intM, HOL`Stdlib`Int`intLtNotLeThm]];
    (* intLe (&ℤ n)(&ℤ m) = (n ≤ m) *)
    leNM = HOL`Bool`SPEC[mV, HOL`Bool`SPEC[nV, HOL`Stdlib`Int`intOfNumLeThm]];
    apNotLe = HOL`Equal`APTERM[notC[], leNM];     (* ¬(intLe(&ℤn)(&ℤm)) = ¬(n≤m) *)
    (* ¬ (m < n) = (n ≤ m) *)
    notLtMN = HOL`Bool`SPEC[nV, HOL`Bool`SPEC[mV, HOL`Stdlib`Num`notLtEqLeqThm]];
    ltMN = concl[notLtMN][[1, 2, 2]];             (* the term m < n *)
    ddneg = HOL`Auto`PropTaut`propTaut[mkEq[notTm[notTm[ltMN]], ltMN]];   (* ¬¬(m<n) = (m<n) *)
    apNotNotLt = HOL`Equal`APTERM[notC[], notLtMN];   (* ¬¬(m<n) = ¬(n≤m) *)
    notLeEqLt = TRANS[HOL`Equal`SYM[apNotNotLt], ddneg];   (* ¬(n≤m) = (m<n) *)
    chain = TRANS[TRANS[ltNotLe, apNotLe], notLeEqLt];     (* intLt(&ℤm)(&ℤn) = (m<n) *)
    HOL`Bool`GEN[mV, HOL`Bool`GEN[nV, chain]]
  ];

(* ============================================================ *)
(* ratOfIntLtThm — ⊢ ∀a b. ratLt (&ℚ a)(&ℚ b) = intLt a b.       *)
(* ============================================================ *)

ratOfIntLtThm =
  Module[{aV, bV, ratA, ratB, ltNotLe, leBA, apNotLe, intLtNL, chain},
    aV = mkVar["a", intTy]; bV = mkVar["b", intTy];
    ratA = ratOfIntTm[aV]; ratB = ratOfIntTm[bV];
    (* ratLt(&ℚa)(&ℚb) = ¬(ratLe(&ℚb)(&ℚa)) *)
    ltNotLe = HOL`Bool`SPEC[ratB, HOL`Bool`SPEC[ratA, HOL`Stdlib`Rat`ratLtNotLeThm]];
    (* ratLe(&ℚb)(&ℚa) = intLe b a *)
    leBA = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratOfIntLeThm]];
    apNotLe = HOL`Equal`APTERM[notC[], leBA];      (* ¬(ratLe(&ℚb)(&ℚa)) = ¬(intLe b a) *)
    (* intLt a b = ¬(intLe b a) *)
    intLtNL = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Int`intLtNotLeThm]];
    chain = TRANS[TRANS[ltNotLe, apNotLe], HOL`Equal`SYM[intLtNL]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, chain]]
  ];

(* ============================================================ *)
(* ratLtIrreflThm — ⊢ ∀x. ¬ (ratLt x x).                         *)
(* ============================================================ *)

ratLtIrreflThm =
  Module[{xV, ltDef, leRefl, hAssume, notLe, falseThm, irr},
    xV = mkVar["x", ratTy];
    ltDef = HOL`Bool`SPEC[xV, HOL`Bool`SPEC[xV, HOL`Stdlib`Rat`ratLtNotLeThm]];  (* ratLt x x = ¬(ratLe x x) *)
    leRefl = HOL`Bool`SPEC[xV, HOL`Stdlib`Rat`ratLeReflThm];                     (* ratLe x x *)
    hAssume = ASSUME[ratLtTm[xV, xV]];
    notLe = EQMP[ltDef, hAssume];                  (* ⊢ ¬(ratLe x x)  [ratLt x x] *)
    falseThm = HOL`Bool`MP[HOL`Bool`NOTELIM[notLe], leRefl];   (* ⊢ F  [ratLt x x] *)
    irr = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[ratLtTm[xV, xV], falseThm]];
    HOL`Bool`GEN[xV, irr]
  ];

(* ============================================================ *)
(* ratLtTransThm — ⊢ ∀a b c. ratLt a b ⇒ ratLt b c ⇒ ratLt a c.  *)
(* ============================================================ *)

ratLtTransThm =
  Module[{aV, bV, cV, hab, hbc, abDef, notLeBA, totAB, leAB,
          bcDef, notLeCB, hca, leCB, falseT, acDef, notLeCA, ltAC, disch},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy]; cV = mkVar["c", ratTy];
    hab = ASSUME[ratLtTm[aV, bV]];
    hbc = ASSUME[ratLtTm[bV, cV]];
    (* ratLt a b = ¬(ratLe b a) ⇒ derive ratLe a b via totality *)
    abDef = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLtNotLeThm]];
    notLeBA = EQMP[abDef, hab];                    (* ¬(ratLe b a)  [ratLt a b] *)
    totAB = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLeTotalThm]];  (* ratLe a b ∨ ratLe b a *)
    leAB = HOL`Bool`DISJCASES[totAB,
             ASSUME[ratLeTm[aV, bV]],
             HOL`Bool`CONTR[ratLeTm[aV, bV],
               HOL`Bool`MP[HOL`Bool`NOTELIM[notLeBA], ASSUME[ratLeTm[bV, aV]]]]];  (* ratLe a b *)
    (* ratLt b c = ¬(ratLe c b) *)
    bcDef = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratLtNotLeThm]];
    notLeCB = EQMP[bcDef, hbc];                    (* ¬(ratLe c b)  [ratLt b c] *)
    hca = ASSUME[ratLeTm[cV, aV]];
    (* ratLe c a ⇒ ratLe a b ⇒ ratLe c b *)
    leCB = HOL`Bool`MP[HOL`Bool`MP[
             HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[cV, HOL`Stdlib`Rat`ratLeTransThm]]],
             hca], leAB];                          (* ratLe c b *)
    falseT = HOL`Bool`MP[HOL`Bool`NOTELIM[notLeCB], leCB];   (* F  [ratLt a b, ratLt b c, ratLe c a] *)
    acDef = HOL`Bool`SPEC[cV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLtNotLeThm]];   (* ratLt a c = ¬(ratLe c a) *)
    notLeCA = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[ratLeTm[cV, aV], falseT]];          (* ¬(ratLe c a) *)
    ltAC = EQMP[HOL`Equal`SYM[acDef], notLeCA];     (* ratLt a c *)
    disch = HOL`Bool`DISCH[ratLtTm[aV, bV], HOL`Bool`DISCH[ratLtTm[bV, cV], ltAC]];
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`GEN[cV, disch]]]
  ];

(* ============================================================ *)
(* ratZeroLtOneThm — ⊢ ratLt (&ℚ(&ℤ 0)) (&ℚ(&ℤ(SUC 0))).        *)
(* ============================================================ *)

ratZeroLtOneThm =
  Module[{intLt01Eq, lt01, intLt01, ratLt01Eq},
    (* intLt(&ℤ 0)(&ℤ(SUC 0)) = (0 < SUC 0) *)
    intLt01Eq = HOL`Bool`SPEC[sucT[zeroN[]], HOL`Bool`SPEC[zeroN[], intOfNumLtThm]];
    lt01 = HOL`Bool`SPEC[zeroN[], HOL`Stdlib`Num`ltSucThm];   (* 0 < SUC 0 *)
    intLt01 = EQMP[HOL`Equal`SYM[intLt01Eq], lt01];           (* intLt(&ℤ0)(&ℤ(SUC0)) *)
    (* ratLt(&ℚ(&ℤ0))(&ℚ(&ℤ(SUC0))) = intLt(&ℤ0)(&ℤ(SUC0)) *)
    ratLt01Eq = HOL`Bool`SPEC[oneInt[], HOL`Bool`SPEC[zeroInt[], ratOfIntLtThm]];
    EQMP[HOL`Equal`SYM[ratLt01Eq], intLt01]
  ];

(* ============================================================ *)
(* ratNegOneLtZeroThm — ⊢ ratLt (ratNeg 1) (&ℚ(&ℤ 0)).           *)
(*   ratLtAddMono on 0<1 by u := −1, then simplify 0+(−1)=−1,     *)
(*   1+(−1)=0.                                                    *)
(* ============================================================ *)

ratNegOneLtZeroThm =
  Module[{mono, addCommZN, addZeroN, leftEq, rightEq, congThm},
    mono = HOL`Bool`MP[
      HOL`Bool`SPEC[negOne[], HOL`Bool`SPEC[oneQ[], HOL`Bool`SPEC[zeroQ[],
        HOL`Stdlib`Rat`ratLtAddMonoThm]]],
      ratZeroLtOneThm];                            (* ratLt (0+(−1)) (1+(−1)) *)
    (* 0 + (−1) = −1 *)
    addCommZN = HOL`Bool`SPEC[negOne[], HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]];
    addZeroN = HOL`Bool`SPEC[negOne[], HOL`Stdlib`Rat`ratAddZeroThm];
    leftEq = TRANS[addCommZN, addZeroN];           (* ratAdd 0 (−1) = −1 *)
    (* 1 + (−1) = 0 *)
    rightEq = HOL`Bool`SPEC[oneQ[], HOL`Stdlib`Rat`ratAddNegThm];   (* ratAdd 1 (ratNeg 1) = &ℚ(&ℤ0) *)
    congThm = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], leftEq], rightEq];
    EQMP[congThm, mono]                            (* ratLt (−1) (&ℚ(&ℤ0)) *)
  ];

(* ============================================================ *)
(* ratPredLtThm — ⊢ ∀q. ratLt (ratAdd q (ratNeg 1)) q.           *)
(*   ratLtAddMono on −1<0 by u := q, then simplify.              *)
(* ============================================================ *)

ratPredLtThm =
  Module[{qV, mono2, leftEq2, zCommq, qAddZero, rightEq2, congThm2, predLt},
    qV = mkVar["q", ratTy];
    mono2 = HOL`Bool`MP[
      HOL`Bool`SPEC[qV, HOL`Bool`SPEC[zeroQ[], HOL`Bool`SPEC[negOne[],
        HOL`Stdlib`Rat`ratLtAddMonoThm]]],
      ratNegOneLtZeroThm];                         (* ratLt ((−1)+q) (0+q) *)
    leftEq2 = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[negOne[], HOL`Stdlib`Rat`ratAddCommThm]];  (* (−1)+q = q+(−1) *)
    zCommq = HOL`Bool`SPEC[qV, HOL`Bool`SPEC[zeroQ[], HOL`Stdlib`Rat`ratAddCommThm]];    (* 0+q = q+0 *)
    qAddZero = HOL`Bool`SPEC[qV, HOL`Stdlib`Rat`ratAddZeroThm];                          (* q+0 = q *)
    rightEq2 = TRANS[zCommq, qAddZero];            (* 0+q = q *)
    congThm2 = HOL`Kernel`MKCOMB[HOL`Equal`APTERM[ratLtC[], leftEq2], rightEq2];
    predLt = EQMP[congThm2, mono2];                (* ratLt (q+(−1)) q *)
    HOL`Bool`GEN[qV, predLt]
  ];

(* ============================================================ *)
(* IS_CUT predicate + definition.                                *)
(* ============================================================ *)

isCutDefThm =
  Module[{Lv, qv, rv, lAppQ, lAppR, c1, c2, c3, c4, body},
    Lv = mkVar["L", cutTy];
    qv = mkVar["q", ratTy]; rv = mkVar["r", ratTy];
    lAppQ = mkComb[Lv, qv]; lAppR = mkComb[Lv, rv];
    c1 = existsTm[qv, lAppQ];                                          (* ∃q. L q *)
    c2 = existsTm[qv, notTm[lAppQ]];                                   (* ∃q. ¬ L q *)
    c3 = forallTm[qv, forallTm[rv, impTm[lAppQ, impTm[ratLtTm[rv, qv], lAppR]]]];   (* ∀q r. L q ⇒ r<q ⇒ L r *)
    c4 = forallTm[qv, impTm[lAppQ, existsTm[rv, conjTm[lAppR, ratLtTm[qv, rv]]]]];  (* ∀q. L q ⇒ ∃r. L r ∧ q<r *)
    body = mkAbs[Lv, conjTm[c1, conjTm[c2, conjTm[c3, c4]]]];
    newDefinition[mkEq[mkVar["IS_CUT", isCutTy], body]]
  ];

isCutConst[] := mkConst["IS_CUT", isCutTy];

(* ⊢ IS_CUT Ltm = (the 4-way conjunction with L := Ltm). The inner Ltm
   applications are NOT β-reduced (only the outer (λL. …) redex is). *)
unfoldIsCut[Ltm_] :=
  Module[{ap}, ap = HOL`Equal`APTHM[isCutDefThm, Ltm];
    TRANS[ap, BETACONV[concl[ap][[2]]]]];

(* ============================================================ *)
(* principalCutIsCutThm — ⊢ ∀q. IS_CUT (λp. ratLt p q).          *)
(* ============================================================ *)

principalCutIsCutThm =
  Module[{qV, pv, cutQ, betaAt, cutUnfold, rhsConj, c1Tm, rest1, c2Tm,
          rest2, c3Tm, c4Tm, aV, bV,
          wBelow, predLtAtQ, memW, c1Thm,
          notMemQ, c2Thm,
          hCutA, ltAQ, hLtBA, ltBQ, memB, c3Disch, c3Thm,
          hCutA4, ltAQ4, denseAQ, midTm, ltAmid, ltMidQ, memMid, bodyThm,
          existsBody, c4Disch, c4Thm,
          conjAll, isCutCutQ},
    qV = mkVar["q", ratTy];
    pv = mkVar["p", ratTy];
    cutQ = mkAbs[pv, ratLtTm[pv, qV]];                  (* λp. ratLt p q *)
    betaAt[t_] := BETACONV[mkComb[cutQ, t]];            (* ⊢ cutQ t = ratLt t q *)
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];

    cutUnfold = unfoldIsCut[cutQ];
    rhsConj = concl[cutUnfold][[2]];                    (* conj c1 (conj c2 (conj c3 c4)) *)
    c1Tm = rhsConj[[1, 2]];
    rest1 = rhsConj[[2]];
    c2Tm = rest1[[1, 2]];
    rest2 = rest1[[2]];
    c3Tm = rest2[[1, 2]];
    c4Tm = rest2[[2]];

    (* --- c1: ∃q. cutQ q.  witness q + (−1) --- *)
    wBelow = ratAddTm[qV, negOne[]];
    predLtAtQ = HOL`Bool`SPEC[qV, ratPredLtThm];        (* ratLt (q+(−1)) q *)
    memW = EQMP[HOL`Equal`SYM[betaAt[wBelow]], predLtAtQ];   (* cutQ (q+(−1)) *)
    c1Thm = HOL`Bool`EXISTS[c1Tm, wBelow, memW];

    (* --- c2: ∃q. ¬ cutQ q.  witness q --- *)
    notMemQ = EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[notC[], betaAt[qV]]],
                   HOL`Bool`SPEC[qV, ratLtIrreflThm]];  (* ¬ cutQ q *)
    c2Thm = HOL`Bool`EXISTS[c2Tm, qV, notMemQ];

    (* --- c3: ∀a b. cutQ a ⇒ ratLt b a ⇒ cutQ b --- *)
    hCutA = ASSUME[mkComb[cutQ, aV]];
    ltAQ = EQMP[betaAt[aV], hCutA];                     (* ratLt a q *)
    hLtBA = ASSUME[ratLtTm[bV, aV]];
    ltBQ = HOL`Bool`MP[HOL`Bool`MP[
             HOL`Bool`SPEC[qV, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, ratLtTransThm]]],
             hLtBA], ltAQ];                             (* ratLt b q *)
    memB = EQMP[HOL`Equal`SYM[betaAt[bV]], ltBQ];       (* cutQ b *)
    c3Disch = HOL`Bool`DISCH[mkComb[cutQ, aV], HOL`Bool`DISCH[ratLtTm[bV, aV], memB]];
    c3Thm = HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, c3Disch]];

    (* --- c4: ∀a. cutQ a ⇒ ∃b. cutQ b ∧ ratLt a b --- *)
    hCutA4 = ASSUME[mkComb[cutQ, aV]];
    ltAQ4 = EQMP[betaAt[aV], hCutA4];                   (* ratLt a q *)
    denseAQ = HOL`Bool`MP[HOL`Bool`SPEC[qV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratDenseThm]], ltAQ4];
    (* ⊢ ratLt a mid ∧ ratLt mid q *)
    midTm = concl[denseAQ][[1, 2]][[2]];
    ltAmid = HOL`Bool`CONJUNCT1[denseAQ];               (* ratLt a mid *)
    ltMidQ = HOL`Bool`CONJUNCT2[denseAQ];               (* ratLt mid q *)
    memMid = EQMP[HOL`Equal`SYM[betaAt[midTm]], ltMidQ];   (* cutQ mid *)
    bodyThm = HOL`Bool`CONJ[memMid, ltAmid];            (* cutQ mid ∧ ratLt a mid *)
    existsBody = HOL`Bool`EXISTS[
      existsTm[bV, conjTm[mkComb[cutQ, bV], ratLtTm[aV, bV]]], midTm, bodyThm];
    c4Disch = HOL`Bool`DISCH[mkComb[cutQ, aV], existsBody];
    c4Thm = HOL`Bool`GEN[aV, c4Disch];

    (* --- assemble --- *)
    conjAll = HOL`Bool`CONJ[c1Thm, HOL`Bool`CONJ[c2Thm, HOL`Bool`CONJ[c3Thm, c4Thm]]];
    isCutCutQ = EQMP[HOL`Equal`SYM[cutUnfold], conjAll];   (* IS_CUT cutQ *)
    HOL`Bool`GEN[qV, isCutCutQ]
  ];

isCutZeroWitnessThm = HOL`Bool`SPEC[zeroQ[], principalCutIsCutThm];

(* ============================================================ *)
(* real type via newBasicTypeDefinition.                         *)
(* ============================================================ *)

{absRepRealThm, repAbsRealThm} =
  newBasicTypeDefinition["real", "ABS_real", "REP_real", isCutZeroWitnessThm];

realTy = mkType["real", {}];
absRealConst[] := mkConst["ABS_real", tyFun[cutTy, realTy]];
repRealConst[] := mkConst["REP_real", tyFun[realTy, cutTy]];

(* ⊢ IS_CUT (REP_real x)  (x free): REP_real lands in the carve. *)
repRealIsCutThm =
  Module[{xV, repX, rVar, repAbsInst, aVar, absRepX, rhsThm},
    xV = mkVar["x", realTy];
    repX = mkComb[repRealConst[], xV];
    rVar = concl[repAbsRealThm][[1, 2, 2]];
    repAbsInst = HOL`Kernel`INST[{rVar -> repX}, repAbsRealThm];
    aVar = concl[absRepRealThm][[2]];
    absRepX = HOL`Kernel`INST[{aVar -> xV}, absRepRealThm];
    rhsThm = HOL`Equal`APTERM[repRealConst[], absRepX];
    EQMP[HOL`Equal`SYM[repAbsInst], rhsThm]
  ];

(* ============================================================ *)
(* Order vocabulary.                                             *)
(* ============================================================ *)

repRealTm[x_] := mkComb[repRealConst[], x];        (* REP_real x : rat → bool *)
repApp[x_, q_] := mkComb[repRealTm[x], q];          (* REP_real x q : bool *)

realLeTy = tyFun[realTy, tyFun[realTy, boolTy]];
realLeConst[] := mkConst["realLe", realLeTy];
realLeTm[a_, b_] := mkComb[mkComb[realLeConst[], a], b];

(* ============================================================ *)
(* Cut accessors: project the 4 IS_CUT conditions onto REP_real x. *)
(* ============================================================ *)

xVcut = mkVar["x", realTy];
condsCut = EQMP[unfoldIsCut[repRealTm[xVcut]], repRealIsCutThm];   (* conj of 4 conds [x free] *)

realNonemptyThm   = HOL`Bool`GEN[xVcut, HOL`Bool`CONJUNCT1[condsCut]];
realProperThm     = HOL`Bool`GEN[xVcut, HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[condsCut]]];
realDownClosedThm = HOL`Bool`GEN[xVcut, HOL`Bool`CONJUNCT1[HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[condsCut]]]];
realOpenThm       = HOL`Bool`GEN[xVcut, HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[HOL`Bool`CONJUNCT2[condsCut]]]];

(* ============================================================ *)
(* realLe — lower-set inclusion.                                 *)
(* ============================================================ *)

realLeDefThm =
  Module[{xV, yV, qv, inner, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; qv = mkVar["q", ratTy];
    inner = forallTm[qv, impTm[repApp[xV, qv], repApp[yV, qv]]];   (* ∀q. REP x q ⇒ REP y q *)
    body = mkAbs[xV, mkAbs[yV, inner]];
    newDefinition[mkEq[mkVar["realLe", realLeTy], body]]
  ];

(* ⊢ realLe a b = (∀q. REP_real a q ⇒ REP_real b q) *)
unfoldRealLe[a_, b_] :=
  Module[{step1, step1b, step2},
    step1 = HOL`Equal`APTHM[realLeDefThm, a];
    step1b = TRANS[step1, BETACONV[concl[step1][[2]]]];   (* realLe a = (λy. …) *)
    step2 = HOL`Equal`APTHM[step1b, b];
    TRANS[step2, BETACONV[concl[step2][[2]]]]             (* realLe a b = ∀q. … *)
  ];

realLeReflThm =
  Module[{xV, qv, repXq, unf, impRefl, allRefl, leXX},
    xV = mkVar["x", realTy]; qv = mkVar["q", ratTy];
    repXq = repApp[xV, qv];
    unf = unfoldRealLe[xV, xV];
    impRefl = HOL`Bool`DISCH[repXq, ASSUME[repXq]];      (* REP x q ⇒ REP x q *)
    allRefl = HOL`Bool`GEN[qv, impRefl];
    leXX = EQMP[HOL`Equal`SYM[unf], allRefl];
    HOL`Bool`GEN[xV, leXX]
  ];

realLeTransThm =
  Module[{xV, yV, zV, qv, hxy, hyz, leXYu, leYZu, repXq, assumeXq,
          toYq, toZq, impXZ, allXZ, leXZ, disch},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; zV = mkVar["z", realTy];
    qv = mkVar["q", ratTy];
    hxy = ASSUME[realLeTm[xV, yV]]; hyz = ASSUME[realLeTm[yV, zV]];
    leXYu = EQMP[unfoldRealLe[xV, yV], hxy];   (* ∀q. REP x q ⇒ REP y q *)
    leYZu = EQMP[unfoldRealLe[yV, zV], hyz];   (* ∀q. REP y q ⇒ REP z q *)
    repXq = repApp[xV, qv];
    assumeXq = ASSUME[repXq];
    toYq = HOL`Bool`MP[HOL`Bool`SPEC[qv, leXYu], assumeXq];   (* REP y q *)
    toZq = HOL`Bool`MP[HOL`Bool`SPEC[qv, leYZu], toYq];       (* REP z q *)
    impXZ = HOL`Bool`DISCH[repXq, toZq];
    allXZ = HOL`Bool`GEN[qv, impXZ];
    leXZ = EQMP[HOL`Equal`SYM[unfoldRealLe[xV, zV]], allXZ];
    disch = HOL`Bool`DISCH[realLeTm[xV, yV], HOL`Bool`DISCH[realLeTm[yV, zV], leXZ]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`GEN[zV, disch]]]
  ];

realLeAntisymThm =
  Module[{xV, yV, qv, hxy, hyx, leXYu, leYXu, repXq, repYq, fwd, bwd,
          entail1, entail2, eqQ, perGen, funcEq, apAbs, aVarAbs, absX, absY,
          xEqY, disch},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy]; qv = mkVar["q", ratTy];
    hxy = ASSUME[realLeTm[xV, yV]]; hyx = ASSUME[realLeTm[yV, xV]];
    leXYu = EQMP[unfoldRealLe[xV, yV], hxy];
    leYXu = EQMP[unfoldRealLe[yV, xV], hyx];
    repXq = repApp[xV, qv]; repYq = repApp[yV, qv];
    fwd = HOL`Bool`SPEC[qv, leXYu];   (* REP x q ⇒ REP y q *)
    bwd = HOL`Bool`SPEC[qv, leYXu];   (* REP y q ⇒ REP x q *)
    entail1 = HOL`Bool`MP[fwd, ASSUME[repXq]];   (* {…, REP x q} ⊢ REP y q *)
    entail2 = HOL`Bool`MP[bwd, ASSUME[repYq]];   (* {…, REP y q} ⊢ REP x q *)
    eqQ = HOL`Kernel`DEDUCTANTISYM[entail1, entail2];   (* ⊢ REP y q = REP x q *)
    perGen = HOL`Bool`GEN[qv, HOL`Equal`SYM[eqQ]];       (* ∀q. REP x q = REP y q *)
    funcEq = HOL`Stdlib`List`funcExtThm[repRealTm[xV], repRealTm[yV], perGen];   (* REP_real x = REP_real y *)
    apAbs = HOL`Equal`APTERM[absRealConst[], funcEq];   (* ABS(REP x) = ABS(REP y) *)
    aVarAbs = concl[absRepRealThm][[2]];
    absX = HOL`Kernel`INST[{aVarAbs -> xV}, absRepRealThm];   (* ABS(REP x) = x *)
    absY = HOL`Kernel`INST[{aVarAbs -> yV}, absRepRealThm];   (* ABS(REP y) = y *)
    xEqY = TRANS[TRANS[HOL`Equal`SYM[absX], apAbs], absY];    (* x = y *)
    disch = HOL`Bool`DISCH[realLeTm[xV, yV], HOL`Bool`DISCH[realLeTm[yV, xV], xEqY]];
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, disch]]
  ];

(* ============================================================ *)
(* ratLeCasesThm — ⊢ ∀a b. ratLe a b ⇒ ratLt a b ∨ (a = b).      *)
(* ============================================================ *)

ratLeCasesThm =
  Module[{aV, bV, hLe, em, eqBranch, hNeq, hLeBA, antis, falseFromBA,
          notLeBA, ltDef, ltAB, neqBranch, disj},
    aV = mkVar["a", ratTy]; bV = mkVar["b", ratTy];
    hLe = ASSUME[ratLeTm[aV, bV]];
    em = HOL`Bool`EXCLUDEDMIDDLE[mkEq[aV, bV]];
    eqBranch = HOL`Bool`DISJ2[ASSUME[mkEq[aV, bV]], ratLtTm[aV, bV]];   (* ratLt a b ∨ a=b *)
    hNeq = ASSUME[notTm[mkEq[aV, bV]]];
    hLeBA = ASSUME[ratLeTm[bV, aV]];
    antis = HOL`Bool`MP[HOL`Bool`MP[
              HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLeAntisymThm]],
              hLe], hLeBA];                       (* a = b  [ratLe a b, ratLe b a] *)
    falseFromBA = HOL`Bool`MP[HOL`Bool`NOTELIM[hNeq], antis];   (* F *)
    notLeBA = HOL`Bool`NOTINTRO[HOL`Bool`DISCH[ratLeTm[bV, aV], falseFromBA]];   (* ¬(ratLe b a) *)
    ltDef = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Stdlib`Rat`ratLtNotLeThm]];   (* ratLt a b = ¬(ratLe b a) *)
    ltAB = EQMP[HOL`Equal`SYM[ltDef], notLeBA];   (* ratLt a b *)
    neqBranch = HOL`Bool`DISJ1[ltAB, mkEq[aV, bV]];   (* ratLt a b ∨ a=b *)
    disj = HOL`Bool`DISJCASES[em, eqBranch, neqBranch];   (* ratLt a b ∨ a=b  [ratLe a b] *)
    HOL`Bool`GEN[aV, HOL`Bool`GEN[bV, HOL`Bool`DISCH[ratLeTm[aV, bV], disj]]]
  ];

(* ============================================================ *)
(* realLeTotalThm — ⊢ ∀x y. realLe x y ∨ realLe y x.            *)
(*   EM on (realLe x y). If not, extract a ∈ L_x \ L_y, show     *)
(*   every b ∈ L_y satisfies b < a (rat trichotomy + downward    *)
(*   closure of L_y), then L_x downward-closed at a gives b∈L_x. *)
(* ============================================================ *)

realLeTotalThm =
  Module[{xV, yV, em, dj1, notLeBranch},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    em = HOL`Bool`EXCLUDEDMIDDLE[realLeTm[xV, yV]];
    dj1 = HOL`Bool`DISJ1[ASSUME[realLeTm[xV, yV]], realLeTm[yV, xV]];

    notLeBranch =
      Module[{qv, Bq, allForm, existsNotForm, hNotLe, apNeg, notAll,
              hNotEx, hNotBq, exFromNotBq, contr1, BqThm, allBq, contr2, existsNot,
              aV, repXa, repYa, notBa, hChosen, extractP, extractNotQ,
              repXaThm, notRepYaThm,
              bV, repYb, repXb, hRepYb,
              hNotLtBA, ratLtNL, apNegLt, ddElim, notNotLeAB, leAB, cases,
              dcInstY, ltABcase, eqABcase, falseFromCases, ltBA,
              dcInstX, repXbThm, impYbXb, allYX, leYX, chosenLeYX},
        qv = mkVar["q", ratTy];
        Bq = impTm[repApp[xV, qv], repApp[yV, qv]];        (* REP x q ⇒ REP y q *)
        allForm = forallTm[qv, Bq];                         (* ∀q. … *)
        existsNotForm = existsTm[qv, notTm[Bq]];            (* ∃q. ¬(…) *)

        hNotLe = ASSUME[notTm[realLeTm[xV, yV]]];
        apNeg = HOL`Equal`APTERM[notC[], unfoldRealLe[xV, yV]];   (* ¬(realLe x y) = ¬allForm *)
        notAll = EQMP[apNeg, hNotLe];                       (* ¬allForm  [¬(realLe x y)] *)

        (* inline ¬∀ ⟹ ∃¬ via CCONTR *)
        hNotEx = ASSUME[notTm[existsNotForm]];
        hNotBq = ASSUME[notTm[Bq]];
        exFromNotBq = HOL`Bool`EXISTS[existsNotForm, qv, hNotBq];
        contr1 = HOL`Bool`MP[HOL`Bool`NOTELIM[hNotEx], exFromNotBq];
        BqThm = HOL`Bool`CCONTR[Bq, contr1];                (* Bq  [¬∃] *)
        allBq = HOL`Bool`GEN[qv, BqThm];                    (* allForm  [¬∃] *)
        contr2 = HOL`Bool`MP[HOL`Bool`NOTELIM[notAll], allBq];
        existsNot = HOL`Bool`CCONTR[existsNotForm, contr2]; (* existsNotForm  [¬(realLe x y)] *)

        (* choose witness a *)
        aV = mkVar["a", ratTy];
        repXa = repApp[xV, aV]; repYa = repApp[yV, aV];
        notBa = notTm[impTm[repXa, repYa]];
        hChosen = ASSUME[notBa];
        extractP = HOL`Auto`PropTaut`propTaut[impTm[notBa, repXa]];        (* ¬(P⇒Q) ⇒ P *)
        extractNotQ = HOL`Auto`PropTaut`propTaut[impTm[notBa, notTm[repYa]]];   (* ¬(P⇒Q) ⇒ ¬Q *)
        repXaThm = HOL`Bool`MP[extractP, hChosen];          (* REP x a  [¬Ba] *)
        notRepYaThm = HOL`Bool`MP[extractNotQ, hChosen];    (* ¬(REP y a)  [¬Ba] *)

        (* prove ∀b. REP y b ⇒ REP x b *)
        bV = mkVar["b", ratTy];
        repYb = repApp[yV, bV]; repXb = repApp[xV, bV];
        hRepYb = ASSUME[repYb];

        (* show ratLt b a by CCONTR *)
        hNotLtBA = ASSUME[notTm[ratLtTm[bV, aV]]];
        ratLtNL = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Stdlib`Rat`ratLtNotLeThm]];   (* ratLt b a = ¬(ratLe a b) *)
        apNegLt = HOL`Equal`APTERM[notC[], ratLtNL];        (* ¬(ratLt b a) = ¬¬(ratLe a b) *)
        ddElim = HOL`Auto`PropTaut`propTaut[
          impTm[notTm[notTm[ratLeTm[aV, bV]]], ratLeTm[aV, bV]]];   (* ¬¬(ratLe a b) ⇒ ratLe a b *)
        notNotLeAB = EQMP[apNegLt, hNotLtBA];               (* ¬¬(ratLe a b)  [¬(ratLt b a)] *)
        leAB = HOL`Bool`MP[ddElim, notNotLeAB];             (* ratLe a b  [¬(ratLt b a)] *)
        cases = HOL`Bool`MP[HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, ratLeCasesThm]], leAB];   (* ratLt a b ∨ a=b *)
        dcInstY = HOL`Bool`SPEC[aV, HOL`Bool`SPEC[bV, HOL`Bool`SPEC[yV, realDownClosedThm]]];   (* REP y b ⇒ ratLt a b ⇒ REP y a *)
        ltABcase = HOL`Bool`MP[HOL`Bool`NOTELIM[notRepYaThm],
                     HOL`Bool`MP[HOL`Bool`MP[dcInstY, hRepYb], ASSUME[ratLtTm[aV, bV]]]];   (* F  [¬Ba, REP y b, ratLt a b] *)
        eqABcase = HOL`Bool`MP[HOL`Bool`NOTELIM[notRepYaThm],
                     EQMP[HOL`Equal`SYM[HOL`Equal`APTERM[repRealTm[yV], ASSUME[mkEq[aV, bV]]]], hRepYb]];   (* F  [¬Ba, REP y b, a=b] *)
        falseFromCases = HOL`Bool`DISJCASES[cases, ltABcase, eqABcase];   (* F  [¬(ratLt b a), ¬Ba, REP y b] *)
        ltBA = HOL`Bool`CCONTR[ratLtTm[bV, aV], falseFromCases];   (* ratLt b a  [¬Ba, REP y b] *)
        dcInstX = HOL`Bool`SPEC[bV, HOL`Bool`SPEC[aV, HOL`Bool`SPEC[xV, realDownClosedThm]]];   (* REP x a ⇒ ratLt b a ⇒ REP x b *)
        repXbThm = HOL`Bool`MP[HOL`Bool`MP[dcInstX, repXaThm], ltBA];   (* REP x b  [¬Ba, REP y b] *)
        impYbXb = HOL`Bool`DISCH[repYb, repXbThm];          (* REP y b ⇒ REP x b  [¬Ba] *)
        allYX = HOL`Bool`GEN[bV, impYbXb];                  (* ∀b. REP y b ⇒ REP x b  [¬Ba] *)
        leYX = EQMP[HOL`Equal`SYM[unfoldRealLe[yV, xV]], allYX];   (* realLe y x  [¬Ba] *)
        chosenLeYX = HOL`Bool`CHOOSE[aV, existsNot, leYX];  (* realLe y x  [¬(realLe x y)] *)
        HOL`Bool`DISJ2[chosenLeYX, realLeTm[xV, yV]]        (* realLe x y ∨ realLe y x  [¬(realLe x y)] *)
      ];

    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, HOL`Bool`DISJCASES[em, dj1, notLeBranch]]]
  ];

(* ============================================================ *)
(* realLt — strict order, ¬(realLe y x).                         *)
(* ============================================================ *)

realLtDefThm =
  Module[{xV, yV, body},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    body = mkAbs[xV, mkAbs[yV, notTm[realLeTm[yV, xV]]]];
    newDefinition[mkEq[mkVar["realLt", realLeTy], body]]
  ];

realLtConst[] := mkConst["realLt", realLeTy];

realLtNotLeThm =
  Module[{xV, yV, step1, step1b, step2, unf},
    xV = mkVar["x", realTy]; yV = mkVar["y", realTy];
    step1 = HOL`Equal`APTHM[realLtDefThm, xV];
    step1b = TRANS[step1, BETACONV[concl[step1][[2]]]];
    step2 = HOL`Equal`APTHM[step1b, yV];
    unf = TRANS[step2, BETACONV[concl[step2][[2]]]];   (* realLt x y = ¬(realLe y x) *)
    HOL`Bool`GEN[xV, HOL`Bool`GEN[yV, unf]]
  ];

End[];
EndPackage[];
