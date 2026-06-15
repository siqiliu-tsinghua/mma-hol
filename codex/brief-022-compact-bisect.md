# Brief 022 — M8.2 Branch B: the bisection recursion (lower/upper, nested, bad) — append to Real/Compact.wl

## Goal

Append the bisection-recursion core of the Heine–Borel proof: `bisectInterval`
(a `num → (real × real)` recursion that repeatedly keeps a BAD half-interval),
the endpoint sequences `lower`/`upper`, their recursion equations, monotonicity,
`nestedIntervals` membership, and `badIntervals` (every bisected interval has no
finite subcover). This is the hardest M8.2 brief (pair-valued recursion + a COND
half-choice). Append to `tests/real_compact_tests.wl`. Self-verify, iterate to
green; graded delivery (see Stop-loss).

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealCompactness/ClosedInterval/FromNestedFinite.lean`:
`stepInterval` (69), `bisectInterval` (82), `lower`/`upper` (88/93),
`lower_zero`/`upper_zero` (98/103), `lower_succ_right`/`upper_succ_right`/
`lower_succ_left`/`upper_succ_left` (108/127/145/165), `lower_step_le`/
`upper_step_le` (206/220), `lower_mono`/`upper_antitone` (234/244),
`interval_order` (186), `nested_intervals` (254), `BadInterval` (def),
`bad_intervals` (267). Read those.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- Compact.wl + SeqAux.wl both frontier (committed, not snapshot); dev.wls names both.
- **The recursion is `num → (real × real)`.** Use Pair.wl + numIterationThm:
  - Pair: `fstConst[]`/`sndConst[]`, the pair constructor (grep Pair.wl for the
    `,`/`mkPair` builder), `fstPairEqThm` ⊢ FST (a,b) = a, `sndPairEqThm` ⊢
    SND (a,b) = b (VERIFY name). Pair type `α×β` builder (grep `pairTy`/the type
    constructor in Pair.wl).
  - `numIterationThm` ISPEC'd at A := `real × real`, e := the pair (left, right),
    f := `stepInterval U` (a `(real×real)→(real×real)` term). ε-out `g` via
    `selectOfExists` (like Stage 4a peakIndex / brief-018 dyadic) → recursion
    equations `bisect 0 = (left,right)`, `bisect (SUC n) = stepInterval (bisect n)`.
    **Deep-β unfold (`seqBetaClean`) — [[wl-unfold-deep-beta-select]].**
  - `lower U left right = λn. FST (bisect … n)`, `upper … = λn. SND (bisect … n)`.
- **`stepInterval U` = `λp. COND (finiteSubcover U (closedInterval (FST p)
  (midpoint (FST p) (SND p)))) (pair (midpoint (FST p)(SND p)) (SND p))
  (pair (FST p) (midpoint (FST p)(SND p)))`** — a COND-valued pair function.
  Bool.wl: `condConst[ty]`, `condTThm` ⊢ ∀a b. COND T a b = a, `condFThm` ⊢
  ∀a b. COND F a b = b. The succ equations split on the COND condition.
- **Available (brief-020/021, same file):** `closedInterval`/`finiteSubcover`/
  `noFiniteSubcover`(+unfolds), `midpoint`(+`leftLeMidpoint`/`midpointLeRight`/
  `leftLtMidpoint`/`midpointLtRight`), `rightHalfBadThm`, the iota tyvar idiom.
  Seq.wl (snapshot): `nestedIntervals`/`nestedIntervalsTm`/`unfoldNestedIntervals`
  (the Stage-6 def: `(∀n. a n ≤ b n) ∧ (∀n m. n≤m ⇒ a n ≤ a m) ∧
  (∀n m. n≤m ⇒ b m ≤ b n)`). Num: `numInductionThm`, leq lemmas, ARITH.
  Bool: `EXCLUDEDMIDDLE`, `DISJCASES`, `condReduce`-style (rewrite COND cond to
  T/F via EQTINTRO/eqfIntro — grep Mul.wl `condReduceT`/`realMulCase*` for the
  idiom). `realLeTransThm`, `realLeReflThm`.

## Scope

- MODIFY: `stdlib/Real/Compact.wl` (append), `tests/real_compact_tests.wl`.
  No other files / runner lists. MUST NOT touch Kernel/Types/Terms/Bootstrap/
  bootstrap.mx/docs/codex(except report). No newAxiom. No new files.

## Definitions (pin)

```
badIntervalDefThm:   ⊢ badInterval = (λU a b. realLe a b ∧ noFiniteSubcover U a b)
stepIntervalDefThm:  ⊢ stepInterval = (λU p. COND
    (finiteSubcover U (closedInterval (FST p) (midpoint (FST p) (SND p))))
    (<pair> (midpoint (FST p) (SND p)) (SND p))
    (<pair> (FST p) (midpoint (FST p) (SND p))))
bisectIntervalDefThm: ⊢ bisectInterval = (ε-out of numIterationThm at A:=real×real,
    e := <pair> left right, f := stepInterval U)   [polymorphic in U / iota]
lowerDefThm:  ⊢ lower = (λU left right n. FST (bisectInterval U left right n))
upperDefThm:  ⊢ upper = (λU left right n. SND (bisectInterval U left right n))
```
Export `*Const[]`/`*Tm`/unfold helpers + `bisectRecSpecThm` (the 0/SUC equations).

## Deliverable theorems (mirror the blueprint)

1. `lowerZeroThm` ⊢ ∀U left right. lower U left right 0 = left;
   `upperZeroThm` ⊢ … = right. (bisect 0 = (left,right) + fst/sndPairEq.)
2. `lowerSuccRightThm` ⊢ (under finiteSubcover U (closedInterval (lower n)
   (midpoint (lower n)(upper n)))) lower (SUC n) = midpoint (lower n)(upper n);
   `upperSuccRightThm` ⊢ … upper (SUC n) = upper n. (bisectSucc + stepInterval
   COND with condition TRUE → condTThm → the (midpoint, upper) pair → fst/snd.)
3. `lowerSuccLeftThm` ⊢ (under ¬finiteSubcover …) lower (SUC n) = lower n;
   `upperSuccLeftThm` ⊢ … upper (SUC n) = midpoint (lower n)(upper n). (condFThm.)
   (For the COND condition→T/F: from the finiteSubcover hyp / its negation, build
   `cond = T` / `cond = F` via EQTINTRO / the eqfIntro idiom, rewrite the COND,
   apply condTThm/condFThm.)
4. `badIntervalsThm` ⊢ ∀U left right. realLe left right ⇒
   noFiniteSubcover U left right ⇒ ∀n. badInterval U (lower U left right n)
   (upper U left right n). numInduction on n: base (lowerZero/upperZero) gives
   left≤right + noFiniteSubcover left right. Step: EXCLUDEDMIDDLE on
   `finiteSubcover U (closedInterval (lower n) (midpoint (lower n)(upper n)))`:
   TRUE → `rightHalfBadThm` gives noFiniteSubcover (midpoint)(upper n);
   lowerSuccRight/upperSuccRight rewrite; badInterval = midpointLeRight (using
   ih's lower n ≤ upper n) + the right-bad. FALSE → lowerSuccLeft/upperSuccLeft;
   badInterval = leftLeMidpoint (ih) + the ¬finiteSubcover IS the noFiniteSubcover.
5. `intervalOrderThm` ⊢ ∀U left right. realLe left right ⇒
   noFiniteSubcover U left right ⇒ ∀n. realLe (lower … n) (upper … n)
   (= CONJUNCT1 of badIntervals n).
6. `lowerStepLeThm` ⊢ (hyps) ∀n. realLe (lower n) (lower (SUC n));
   `upperStepLeThm` ⊢ (hyps) ∀n. realLe (upper (SUC n)) (upper n). EXCLUDEDMIDDLE
   on the same cond: TRUE → lower(SUC n)=midpoint ≥ lower n (leftLeMidpoint, since
   lower n ≤ upper n) and upper(SUC n)=upper n (refl); FALSE → lower(SUC n)=lower n
   (refl) and upper(SUC n)=midpoint ≤ upper n (midpointLeRight).
7. `lowerMonoThm` ⊢ (hyps) ∀n m. n ≤ m ⇒ realLe (lower n) (lower m);
   `upperAntitoneThm` ⊢ (hyps) ∀n m. n ≤ m ⇒ realLe (upper m) (upper n).
   (Induction on m≥n using step-le + realLeTrans — mirror Seq.wl's
   subseqIndexMono structure.)
8. `nestedIntervalsThm` ⊢ ∀U left right. realLe left right ⇒
   noFiniteSubcover U left right ⇒ nestedIntervals (lower U left right)
   (upper U left right). CONJ of intervalOrder (∀n) + lowerMono + upperAntitone,
   folded into the Stage-6 `nestedIntervals` def (SYM unfold).

## Stop-loss / graded delivery (this is the hard brief)

Tier 1 (must): defs + bisectRecSpec + lowerZero/upperZero + the four succ
equations (2,3). Tier 2: intervalOrder/badIntervals (4,5) + step-le (6). Tier 3:
mono/antitone/nested (7,8). If a tier stalls (same failure twice), deliver the
lower tiers that ARE green and STOP with a precise report (which theorem, the
exact thrown payload). A loadable subset is fully acceptable — do NOT thrash.

## Tests (append ~10 asserts)

- `bisectRecSpec` 0/SUC equation shapes; lowerZero/upperZero concrete;
  the succ-equation conclusion shapes (conditional); badIntervals/nestedIntervals
  concl shapes at fresh U,left,right (aconv). aconv against folder builders; no
  deep MatchQ. **NO `testExit[]`.**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. in-folder + Pair/Bool/Num
publics reachable. 4. **iota tyvar** consistent (brief-020); `U : iota→real→bool`.
5. holError HoldRest. 6. dev.wls verifier. 7. aconv tests, no deep MatchQ, **no
testExit**. 8. mkVar/mkConst/mkComb/mkAbs only. 9. **Narrow probes** — this is a
load-heavy file; localize a load throw by catch-load + per-theorem isThm (Stage
4a method), do NOT dump terms. 10. No Return in Do/For/While. 11. **deep-β unfold
for the ε-out bisect** ([[wl-unfold-deep-beta-select]]); the recursion `f`-app
`stepInterval(bisect n)` leaves a redex selectOfExists already reduced — match it
with `seqBetaClean`. 12. SPEC/COND: `condTThm`/`condFThm` need the COND condition
to be literally `T`/`F`; rewrite the `finiteSubcover …` condition to T (when it
holds, via EQTINTRO) or F (when negated, via the eqfIntro idiom — grep Mul.wl
`condReduceT`/`condReduceF`/`realMulCasePPThm` for the exact pattern) before
applying condT/F. 13. Pair: `FST (a,b)`/`SND (a,b)` reduce via fst/sndPairEqThm;
the pair constructor's type carries both component types (real,real here).
14. realArithProve is LINEAR (midpoint facts already proven in brief-021 — REUSE
`leftLeMidpoint`/`midpointLeRight`, don't re-derive).

## Verification (MANDATORY — you run wolframscript)

Full machine access. Both frontier files named:

```
wolframscript -file tests/dev.wls stdlib/Real/SeqAux.wl stdlib/Real/Compact.wl real_compact
```

Loop edit → run → read failure → fix until `failed: 0`; paste the final
`passed: N  failed: 0` into your report. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other
command, nothing outside the repo, no network. If the same failure recurs twice,
deliver the loadable subset (per the tiers) and report exactly where it broke.
If dev.wls reports a stale snapshot for some OTHER file, STOP and report.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls
  verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. How you exposed `bisectInterval` + the recursion equations from numIterationThm
   at the pair type, and how you reduced the COND condition to T/F.
4. The exact final `passed: N  failed: 0` from your dev.wls run.
5. Which theorems (by tier) fully proven vs stopped.
6. Open questions (empty if none).
