# Brief 017 — M8.2 Branch A.2: accumulation-point principle (BW set version), in Real/Compact.wl

## Goal

Extend `stdlib/Real/Compact.wl` (Branch A.1, brief-016 — read it first) with the
**Bolzano–Weierstrass accumulation-point principle**: a bounded INFINITE subset
of ℝ has an accumulation point —
`⊢ ∀S. setBounded S ⇒ listInfinite S ⇒ ∃x. accumulationPoint S x`. The proof
builds a sequence of pairwise-distinct points of S (each chosen fresh w.r.t. the
list of earlier ones), applies Branch A.1's `bwSequentialThm` to get a
convergent subsequence, and shows its limit is an accumulation point. Append to
`tests/real_compact_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint (in-repo — READ and mirror 1:1)

`tautology-ref/Tautology/RealCompactness/ClosedInterval/SeqToAccum.lean` — the
COMPLETE 0-sorry reference. Mirror its structure: `freshFromList`/`_mem`/
`_not_mem`, `freshList` (the num→list recursion), `freshSeq`, `freshList_succ`,
`freshSeq_mem`/`_not_mem_freshList`/`_mem_freshList_of_lt`/`_ne_of_lt`,
`freshSeq_bounded`, `limit_of_fresh_subsequence_is_accumulation`,
`accumulationPrinciple`. Defs `AccumulationPoint`, `SeqBounded`/`SetBounded`,
`dist` are in `RealCompactness/Compact.lean`; `ListInfinite` is
`Foundation/Cardinal/Finite.lean:26`. Surface: `F.lt/le`, `dist F y x` =
`|y − x|`, `Classical.choose`-`freshList` recursion + `Nat.le_succ`/`omega` →
our concrete `realLt/realLe`, `realAbs (realAdd y (realNeg x))`, the
`numIterationThm` + `selectOfExists` recursion (below), and `arithProve`/Num
lemmas for the ℕ index steps.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **The `freshList` recursion is `num → (real list)`, built EXACTLY like Stage
  4a's `peakIndex`/`risingIndex` in Seq.wl** — re-read those: `numIterationThm`
  ISPEC'd at A := the `real list` type, e := NIL, f := λl. CONS (the fresh
  choice for l) l; ε-out the `g` (via `selectOfExists` on `numIterationThm`),
  giving the two recursion equations `freshList 0 = NIL`,
  `freshList (SUC n) = f (freshList n)`. **The unfold helper for the ε-out
  constant MUST deep-β-reduce (`seqBetaClean`), not a single BETACONV — see
  [[wl-unfold-deep-beta-select]]; this exact bug cost three fixes in Stage 4a.**
  The per-step fresh choice = `selectOfExists` on the `listInfinite` existential
  at the current list `freshList n` (the predicate `λx. S x ∧ ¬(MEM x xs)`).
- **Available, verified (grep ::usage):**
  - Compact.wl (brief-016): `seqBounded`/`seqBoundedTm`, `hasConvergentSubseq`,
    `bwSequentialThm` ⊢ ∀u. seqBounded u ⇒ ∃l. hasConvergentSubseq u l; the
    seq-bounded def shape (`∃lo hi. ∀n. lo ≤ u n ∧ u n ≤ hi`).
  - Seq.wl: `subseqIndex`/`subsequence`(`subsequenceTm[uT,phiT]`)/`tendsto`;
    `subseqIndexGeSelfThm` (n ≤ phi n) + `subseqIndexThm`-family; the
    `peakIndex`/`risingIndex` recursion code as the model.
  - List.wl: `nilConst[]` (NIL), `consConst[]` (CONS), `memConst[]` (MEM),
    `memNilThm` ⊢ ∀x. MEM x NIL = F, `memConsThm` ⊢ ∀x y l. MEM x (CONS y l) =
    (x = y ∨ MEM x l), `consInjThm`, `nilNotEqConsThm`. The list element type
    is `real` (`MEM : real → real list → bool`).
  - Num: `numIterationThm` ⊢ ∀e f. ∃g. g 0 = e ∧ ∀n. g(SUC n) = f (g n);
    `HOL`Stdlib`Num`selectOfExists[predLam, existsTh]`; `numInductionThm`;
    `arithProve`/`ARITH[]` for ℕ index inequalities (m<n ⇒ m<SUC n etc.);
    `leqReflThm`, `ltSucThm`/`leqSucThm`, `ltDefThm`.
  - Abs.wl/Cut.wl: `realAbsPosThm`, `realLeTransThm`, `realLeReflThm`,
    `realLtNotLeThm`. RealArith: `realArithProve`, `realLtIrreflThm`.

## Scope

- MODIFY: `stdlib/Real/Compact.wl` (append Branch A.2),
  `tests/real_compact_tests.wl` (append). Do NOT touch runner lists (Compact.wl
  already wired). MUST NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/docs/
  codex(except report). No newAxiom. No new files.

## Definitions (pin; new constants + unfold helpers in Compact.wl)

```
listInfiniteDefThm:  ⊢ listInfinite = (λS. ∀xs. ∃x. S x ∧ ¬(MEM x xs))
setBoundedDefThm:    ⊢ setBounded = (λS. ∃lo. ∃hi. ∀x. S x ⇒ realLe lo x ∧ realLe x hi)
distDefThm:          ⊢ dist = (λy x. realAbs (realAdd y (realNeg x)))
accumulationPointDefThm: ⊢ accumulationPoint = (λS x. ∀eps. realLt 0 eps ⇒
    ∃y. S y ∧ ¬(y = x) ∧ realLt (dist y x) eps)
```
- S : real→bool; xs : real list; x,y,lo,hi,eps : real. `0` = zeroRealTm[].
  Export the `*Const[]`/`*Tm`/unfold helpers.

## Deliverable theorems (mirror SeqToAccum.lean)

Recursion + fresh points (the hard part):
1. `freshList` (ε-out `num→real list` via numIterationThm) + `freshListRecSpecThm`
   (`freshList S 0 = NIL`, `freshList S (SUC n) = CONS (freshSeq S n)
   (freshList S n)` — mirror Stage 4a's `peakIndexRecSpecThm`, with the deep-β
   unfold). `freshSeq S n = ` the `selectOfExists` fresh choice at
   `freshList S n`.
2. `freshSeqMemThm` (S (freshSeq S n)) and `freshSeqNotMemThm`
   (¬(MEM (freshSeq S n) (freshList S n))) — both CONJUNCT of the selectOfExists
   spec (listInfinite at the current list).
3. `freshSeqMemFreshListOfLtThm` ⊢ ∀m n. m < n ⇒ MEM (freshSeq S m) (freshList S n).
   numInduction on n (generalize m): base vacuous (m<0); step uses freshList(SUC
   n)=CONS… + `memConsThm`: m=n → head (x=y); m<n → IH + tail. (ℕ case split via
   ARITH / leq lemmas.)
4. `freshSeqNeOfLtThm` ⊢ ∀m n. m < n ⇒ ¬(freshSeq S n = freshSeq S m).
   Assume equal; then freshSeq S m ∈ freshList S n (by 3) rewrites to
   freshSeq S n ∈ freshList S n, contradicting `freshSeqNotMemThm`.
5. `freshSeqBoundedThm` ⊢ setBounded S ⇒ seqBounded (freshSeq S). CHOOSE lo,hi;
   same lo,hi; each freshSeq S n ∈ S (by 2) so lo ≤ it ≤ hi.

Accumulation (mirror `limit_of_fresh_subsequence_is_accumulation` +
`accumulationPrinciple`):
6. `freshLimitIsAccumThm` ⊢ ∀phi l. subseqIndex phi ⇒
   tendsto (subsequence (freshSeq S) phi) l ⇒ accumulationPoint S l.
   GEN eps, DISCH 0<eps; from tendsto get N with the subseq within eps of l for
   indices ≥ N; y0 := freshSeq S (phi N), y1 := freshSeq S (phi (SUC N)); both
   ∈ S (by 2); both within eps of l (dist < eps, from the tendsto witness +
   `distDefThm`); y1 ≠ y0 (by 4, since phi N < phi (SUC N) — subseqIndex);
   EXCLUDEDMIDDLE on `y0 = l`: if y0=l, use y1 (y1≠l since y1≠y0=l), else use y0.
   Each gives ∃y. S y ∧ ¬(y=l) ∧ dist y l < eps.
7. `accumulationPrincipleThm` ⊢ ∀S. setBounded S ⇒ listInfinite S ⇒
   ∃x. accumulationPoint S x. From `freshSeqBoundedThm`, `bwSequentialThm`
   (Branch A.1) gives ∃l. hasConvergentSubseq (freshSeq S) l; CHOOSE l, then
   CHOOSE phi from hasConvergentSubseq (subseqIndex phi ∧ tendsto …);
   `freshLimitIsAccumThm` ⇒ accumulationPoint S l; EXISTS l.

**Stop-loss / graded delivery:** the `freshList` recursion (1) + distinctness
(2–4) are the risky part. If the accumulation argument (6–7) stalls, deliver
through (5) `freshSeqBoundedThm` and STOP with a precise report — a loadable
subset is acceptable. If the recursion itself won't go (deep-β / selectOfExists
shape), deliver the defs + report exactly where it broke.

## Tests (append ~10 asserts)

- Defs unfold at fresh vars; shape checks.
- `freshListRecSpec` NIL/CONS equations at a fresh S; `freshSeqMem`/`NeOfLt`
  concl shapes.
- `accumulationPrincipleThm` concl-shape at a fresh S (aconv on a built expected
  term; the ∃/∀ make full instantiation heavy — shape check + empty hyps).
- aconv against folder builders; no deep MatchQ. **Do NOT add `testExit[]` —
  end with the last `runTests[...]` (a per-file testExit truncates cold
  run_all).**

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder +
Seq/Compact/List publics reachable; Num/Bool publics only. 4. HOL var
identity=(name,type): recursion binders (the iteration `g`, the fresh-choice
`x`, list `xs`, CHOOSE witnesses `loW`/`hiW`/`lW`/`phiW`) distinctive — never
bare S/x/y/n/m the statement carries. 5. holError HoldRest. 6. dev.wls is your
verifier (Verification). 7. aconv tests, no deep MatchQ, **no testExit in test
files**. 8. mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes. 10. No Return in
Do/For/While. 11. **deep-β unfold for the ε-out recursion constant** — single
BETACONV ≠ selectOfExists's DEPTHCONV form, the @-terms won't aconv-match and
the RecSpec fold silently fails (Stage 4a, [[wl-unfold-deep-beta-select]]); use
`seqBetaClean`. 12. SPEC doesn't β-reduce; clean redexes. 13. **realArithProve
is LINEAR** — dist/realAbs/freshSeq are opaque atoms; the index arithmetic is
pure ℕ (ARITH/numInduction). 14. MEM/list facts via `memNilThm`/`memConsThm`
(rewrite, EQMP) — MEM is bool-valued, `MEM x (CONS y l) = (x=y ∨ MEM x l)` is an
equation, use it with EQMP/SUBS not as a Prop.

## Verification (MANDATORY — you run wolframscript)

Full machine access. Verify and iterate to green before delivering. The ONLY
command you run:

```
wolframscript -file tests/dev.wls stdlib/Real/Compact.wl real_compact
```

Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste
that final `passed: N  failed: 0` into your report. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other
command, nothing outside the repo, no network. If the same failure recurs twice,
deliver the loadable subset and report. Reading failures: `Throw::nocatch` at
load = proof/term bug (localize via which theorem stopped binding — catch-load +
per-theorem isThm probe, as in Stage 4a); `Syntax::sntx`+line = bracket typo;
`failed:K`+`FAIL` = assertion/aconv mismatch. If dev.wls says the snapshot is
STALE, STOP and report — do not rebuild.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one
  dev.wls verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. How you exposed `freshList` (ε-out vs CHOOSE-in-module) + the exact
   recursion-equation theorems from numIterationThm.
4. The exact final `passed: N  failed: 0` from your dev.wls run.
5. Which theorems fully proven vs stopped.
6. Open questions (empty if none).
