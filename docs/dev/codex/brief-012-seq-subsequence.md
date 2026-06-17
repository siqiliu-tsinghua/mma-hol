# Brief 012 — stdlib/Real/Seq.wl Stage 4a: subsequences + every sequence has a monotone subsequence

## Goal

Extend `stdlib/Real/Seq.wl` (Stages 1–3, briefs 008–011 — read the whole file
first) with the **subsequence infrastructure** and the combinatorial heart of
Bolzano–Weierstrass: **every sequence has a monotone subsequence** (the Peak
lemma). This is the hardest, most debug-prone stage — it needs two `num→num`
recursions built via the iteration principle + Hilbert-ε. Bolzano–Weierstrass
itself (bounded ⇒ convergent subsequence) is the NEXT brief; do NOT do it here.
Append tests.

## Blueprint (in-repo, gitignored, on disk — READ and mirror closely)

`tautology-ref/Tautology/RealSequence/Subsequence.lean` — the COMPLETE 0-sorry
reference for EXACTLY this deliverable. Mirror its structure 1:1:
`SubsequenceIndex`, `subsequence`, `subsequenceIndex_mono`,
`subsequenceIndex_ge_self`, `Peak`, `not_peak_exists_later_above`,
`eventually_not_peak_of_not_infinite`, `peakIndex` (recursion),
`peakIndex_peak`/`_step`/`_subsequence`/`_decreasing`, `risingIndex`
(recursion), `risingIndex_step`/`_step_le`/`_subsequence`/`_increasing`,
`exists_monotone_subsequence`. Surface translation: `F.le/lt`, `F.le_total`,
`F.le_refl/le_trans`, `MonotoneIncreasing/Decreasing` → our `realLe`/(num)`<`,
`realLeTotalThm`, `realLeReflThm`/`realLeTransThm`, `monoInc`/`monoDec` (brief-011
defs). Lean's `Classical.choose`/dependent-subtype recursion → our iteration
principle + `selectOfExists` (mechanics below).

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- In context `HOL`Stdlib`Real`` — all Real-folder + Seq.wl privates reachable
  (brief-011's `monoInc`/`monoDec` defs + `monoIncConst[]`/`monoIncTm` etc.).
- **The num→num recursion mechanics (STUDY the existing patterns):**
  - `HOL`Stdlib`Num`numIterationThm` ⊢ ∀e:A. ∀f:A→A. ∃g:num→A. g 0 = e ∧
    ∀n. g (SUC n) = f (g n). To DEFINE a recursive `num→num` function:
    ISPEC e and f at A:=num, then CHOOSE g (the function) — you get
    `g 0 = e` and `∀n. g(SUC n) = f(g n)` as the two recursion equations.
    Read `stdlib/Num.wl` (the `+`/`*` definitions via ITER) and `stdlib/List.wl`
    (LIST_ITER) for worked examples of pulling g out and using its equations.
  - `HOL`Stdlib`Num`selectOfExists[predLam, existsTh]` — given ⊢ ∃x. P x
    (existsTh) and the predicate lambda P (predLam = `λx. body`), returns
    ⊢ P (@ P), i.e. the chosen witness satisfies the body (β-reduced
    internally). This is how you extract BOTH conjuncts of a chosen witness's
    spec. `selectAx` ⊢ ∀P x. P x ⇒ P (@P) is the underlying axiom. MANY
    examples in `stdlib/List.wl` (search `selectOfExists`).
- **Available lemmas (verify ::usage before use):**
  - Num: `numInductionThm`, `leqReflThm`, `leqTransThm`,
    `ltSucThm`/`leqSucThm`, `ltDefThm` (m<n ⇔ SUC m ≤ n — VERIFY),
    `ltLeqThm`/`ltImpliesLeq` (m<n ⇒ m≤n — find the exact name),
    `zeroLeqThm`/`leqZeroThm`, `addCommThm`, `plusSucEqThm`/`plusZeroEqThm`,
    `sucConst[]`/`zeroConst[]`/`leqConst[]`/`ltConst[]`. The `≤`/`<` here are
    Num's (the index arithmetic is ALL ℕ, no reals).
    **ARITH is available** (`HOL`Auto`Arith`arithProve` / `ARITH[]`) for the
    purely-ℕ index inequalities (the `omega` steps in the blueprint) — use it
    for `n ≤ phi n` style and the `s.val < m ⇒ N ≤ m` steps, instead of hand
    chaining leqTrans (but ARITH rejects ¬(=) hyps; keep goals as ≤/< chains).
  - Mul.wl: `realLeTotalThm` ⊢ ∀x y. realLe x y ∨ realLe y x (VERIFY — may be
    in Cut.wl); `realLeReflThm`, `realLeTransThm`.
  - Bool: `EXCLUDEDMIDDLE`, `DISJCASES`, `CHOOSE`, `CCONTR`, `CONTR`,
    `NOTINTRO`, `EXISTS`, `CONJ`, `CONJUNCT1/2`, `propTaut` (public).
- The reals only enter via `realLe (u m) (u n)` (Peak) and the monotone
  conclusions; everything else (phi, indices) is pure ℕ.

## Scope

- MODIFY: `stdlib/Real/Seq.wl` (append Stage 4a), `tests/real_seq_tests.wl`.
- Do NOT touch other files / runner lists. MUST NOT touch Kernel/Types/Terms/
  Bootstrap/bootstrap.mx/docs/codex(except report). No newAxiom. No new files.

## Definitions (pin; new constants in Seq.wl + unfold helpers)

```
subseqIndexDefThm:  ⊢ subseqIndex = (λphi. ∀n. phi n < phi (SUC n))   (phi : num→num; < is Num)
subsequenceDefThm:  ⊢ subsequence = (λu phi. λn. u (phi n))           (u : num→real)
peakDefThm:         ⊢ peak = (λu n. ∀m. n ≤ m ⇒ realLe (u m) (u n))
```
Export `subseqIndexConst[]`/`subseqIndexTm`, `subsequenceConst[]`/
`subsequenceTm[uT,phiT]`, `peakConst[]`/`peakTm[uT,nT]` + unfold helpers.

## Deliverable theorems (mirror the blueprint names)

1. `subseqIndexMonoThm` ⊢ ∀phi. subseqIndex phi ⇒ ∀n m. n ≤ m ⇒ phi n ≤ phi m.
   (numInduction on m≥n, or ARITH-assisted; uses phi n < phi(SUC n) ⇒ ≤.)
2. `subseqIndexGeSelfThm` ⊢ ∀phi. subseqIndex phi ⇒ ∀n. n ≤ phi n.
   (numInduction; base 0≤phi 0; step n≤phi n < phi(SUC n).)
3. `notPeakExistsLaterThm` ⊢ ∀u n. ¬(peak u n) ⇒ ∃m. n < m ∧ realLe (u n) (u m).
   Mirror `not_peak_exists_later_above`: CCONTR/by_cases — if no such m, show
   peak u n (for m≥n: realLeTotal (u n)(u m); the `u m ≤ u n` branch direct,
   the `u n ≤ u m` branch forces m=n hence u m = u n ≤ u n, OR n<m contradicts
   the no-witness assumption). Distinctive binders (mW).
4. `eventuallyNotPeakThm` ⊢ ∀u.
   ¬(∀N. ∃n. N ≤ n ∧ peak u n) ⇒ ∃N. ∀n. N ≤ n ⇒ ¬(peak u n).
   Mirror `eventually_not_peak_of_not_infinite` (double CCONTR; the
   contrapositive packaging). propTaut for the propositional shuffles.

### peakIndex recursion (the infinitely-many-peaks branch)

Under hypothesis `hinf : ∀N. ∃n. N ≤ n ∧ peak u n`:
- f := λj. (@ n. SUC j ≤ n ∧ peak u n). e := (@ n. 0 ≤ n ∧ peak u n). Build
  `peakIndex` = the g from numIterationThm ISPEC[num] e f (CHOOSE g). Its
  spec at each index: `selectOfExists` at predLam = `λn. (m̂ ≤ n ∧ peak u n)`
  with existsTh = hinf m̂ gives `(m̂ ≤ peakIndex… ∧ peak u peakIndex…)` — extract
  via CONJUNCT.
5. `peakIndexPeakThm` ⊢ peak u (peakIndex k) (∀k; cases 0 / SUC via the two
   recursion equations + selectOfExists spec, CONJUNCT2).
6. `peakIndexStepThm` ⊢ peakIndex k < peakIndex (SUC k) (from the SUC equation:
   peakIndex(SUC k) = @n.(SUC(peakIndex k) ≤ n ∧ …), spec CONJUNCT1 gives
   SUC(peakIndex k) ≤ peakIndex(SUC k), i.e. peakIndex k < peakIndex(SUC k) via
   ltDef/ARITH).
7. `peakIndexSubseqThm` ⊢ subseqIndex (peakIndex) (= step, folded to the def).
8. `peakIndexDecreasingThm` ⊢ monoDec (subsequence u peakIndex) (subseqIndexMono
   gives peakIndex n ≤ peakIndex m; peakIndexPeak at n applied at peakIndex m).

### risingIndex recursion (the eventually-no-peaks branch)

Under `N` and `hno : ∀n. N ≤ n ⇒ ¬(peak u n)`:
- f := λj. (@ m. j < m ∧ realLe (u j) (u m)). e := N. Build `risingIndex` via
  numIterationThm ISPEC[num] N f (CHOOSE g). Equations: risingIndex 0 = N,
  risingIndex(SUC k) = @m.(risingIndex k < m ∧ realLe (u(risingIndex k))(u m)).
- **Invariant FIRST** `risingIndexGeThm` ⊢ ∀k. N ≤ risingIndex k (numInduction;
  base risingIndex 0 = N ⇒ refl; step: IH N≤risingIndex k ⇒ ¬peak(risingIndex k)
  by hno ⇒ ∃m. risingIndex k<m ∧ … by notPeakExistsLater ⇒ selectOfExists gives
  the SUC-equation witness satisfies risingIndex k < risingIndex(SUC k) ⇒
  N ≤ risingIndex k < risingIndex(SUC k), ARITH). The existence at each k is
  ONLY valid because of this invariant — derive the per-step spec inside.
9. `risingIndexStepThm` ⊢ risingIndex k < risingIndex (SUC k) (per-k: invariant
   ⇒ ¬peak ⇒ notPeakExistsLater ⇒ selectOfExists CONJUNCT1).
10. `risingIndexStepLeThm` ⊢ realLe (u(risingIndex k)) (u(risingIndex (SUC k)))
    (same spec, CONJUNCT2).
11. `risingIndexSubseqThm` ⊢ subseqIndex (risingIndex).
12. `risingIndexIncreasingThm` ⊢ monoInc (subsequence u risingIndex)
    (numInduction on n≤m using risingIndexStepLe + realLeTrans; mirror the Lean
    `induction hnm`).

### The capstone

13. `existsMonoSubseqThm` ⊢ ∀u. ∃phi.
    subseqIndex phi ∧ (monoInc (subsequence u phi) ∨ monoDec (subsequence u phi)).
    EXCLUDEDMIDDLE on `∀N. ∃n. N ≤ n ∧ peak u n`:
    - true (hinf): EXISTS phi := peakIndex; CONJ subseqIndex + DISJ2 decreasing.
    - false: `eventuallyNotPeakThm` ⇒ ∃N. hno; CHOOSE N; EXISTS phi := risingIndex;
      CONJ subseqIndex + DISJ1 increasing.

If the recursion mechanics stall, deliver the loadable subset (defs +
1–4 + notPeakExistsLater + whichever recursion landed) and STOP per stop-loss
with a precise report on where the iteration/ε extraction broke.

## Tests (append ~12 asserts)

- Defs unfold at fresh vars; shape checks.
- `notPeakExistsLaterThm`, `existsMonoSubseqThm` concl-shape checks (SPEC at a
  var u; the existentials make full instantiation heavy — assert the
  conclusion shape via aconv on a built expected term, hyp empty).
- A constant sequence `λn. c`: every n is a peak (peak (λn.c) n via realLeRefl);
  `existsMonoSubseqThm` applies; OR check `subsequence (λn.c) phi = λn. c` shape.
- `subseqIndexGeSelfThm` / `subseqIndexMonoThm` exercised on a concrete
  `phi := λn. n` (identity is a... no — identity has phi n = n, NOT n<SUC n
  strict? n < SUC n IS true, so identity IS a subseqIndex) — instantiate and
  check.
- aconv against folder-builder expected terms; no deep MatchQ.

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder
privates reachable; Num/Bool publics only (`numIterationThm`, `selectOfExists`,
`numInductionThm`, `arithProve` are public). 4. HOL var identity=(name,type):
the recursion's internal binders (g, f's bound j, the ε predicate's n/m, CHOOSE
witnesses) ALL distinctive (gRec, jStep, nPk, mRise, nW) — NEVER bare n/m/k
that the statement's canonical binders carry. 5. holError HoldRest.
6. `wolframscript -file` only. 7. aconv tests, no deep MatchQ. 8. mkVar/mkConst/
mkComb/mkAbs only — the recursion f/e terms built with these. 9. Narrow probes.
10. No Return in Do/For/While. 11. **SPEC does not β-reduce** — the iteration
equations `g(SUC n) = f(g n)` and selectOfExists outputs may carry redexes;
clean with CONVRULE[DEPTHCONV[TRYCONV[BETACONV]]]. selectOfExists β-reduces its
predicate application internally (per its doc) — but the f-application f(g n)
may still need a BETACONV. 12. The index arithmetic is ALL ℕ — use Num's `≤`/`<`
and ARITH/numInduction; reals appear ONLY inside `realLe (u …) (u …)`.
13. **Defining a function via numIterationThm**: the ∃g is discharged by CHOOSE
(g becomes a fresh var bound in the proof) — but to EXPORT peakIndex/risingIndex
as reusable terms you must either (a) keep the whole development inside one
Module that CHOOSEs g and proves everything about it, or (b) Hilbert-ε the g out
(`@ g. g 0 = e ∧ …`) so peakIndex is a closed term. Option (b) (selectOfExists
on numIterationThm) matches how Num.wl/List.wl expose ITER-defined functions —
prefer it for clean per-theorem reuse.

## Verification

Sandbox can't run wolframscript: deliver statically-checked code; report
file:line where each borrowed lemma/builder name was verified. Reviewer runs
`tests/dev.wls stdlib/Real/Seq.wl real_seq` then cold Strict run_all.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. How you exposed peakIndex/risingIndex (CHOOSE-in-module vs ε-out) + the
   exact recursion-equation theorems you got from numIterationThm.
4. Which theorems fully proven vs stopped.
5. Open questions (empty if none).
