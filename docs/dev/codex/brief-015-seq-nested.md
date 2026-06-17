# Brief 015 — stdlib/Real/Seq.wl Stage 6: nested-interval principle from the sup (确界 → 区间套)

## Goal

Extend `stdlib/Real/Seq.wl` (Stages 1–5, briefs 008–014 — read the whole file
first; in particular `monoIncTendstoSupThm` from Stage 3 is the structural twin
of this proof) with the **nested-interval principle** proved from the sup: a
nest of closed intervals has a common point, unique when the lengths tend to 0.
This is a SEQUENCE-layer result (lives in Seq.wl, before graduation). Append
tests. Self-verify with dev.wls and iterate to green (see Verification).

## Blueprint (in-repo, gitignored — READ and mirror 1:1)

`tautology-ref/Tautology/RealSequence/Principles/FromSupNested.lean` — the
COMPLETE 0-sorry reference for EXACTLY this. The defs are in
`RealSequence/Principles/Statements.lean` (`NestedClosedIntervals`,
`IntervalLengthsToZero`). Mirror the proof structure: `Range a` (= `λx. ∃n. x =
a n`, the SAME realSup-set idiom as our Stage 3 `monoIncTendstoSupThm`),
`upper_endpoint_upperBound`, `supLowerEndpoints` (= sup of Range a),
`supLowerEndpoints_in_interval`, `exists_point`, `common_point_le`,
`common_points_equal`, `unique_point_of_lengths_zero`. Surface translation:
`F.lt/le/sub/abs`, `SeqTendsto`, `Classical.choose`-`supLowerEndpoints` → our
`realLt/realLe/(realAdd x (realNeg y))/realAbs/tendsto/realSup`; `le_lub_of_mem`
→ `realSupUpperThm` (member ≤ sup), `lub_le_of_upper` → `realSupLeastThm`
(sup ≤ upper bound). Linear ε / sub-algebra → `realArithProve`.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **`monoIncTendstoSupThm` (Stage 3) is your closest model** — it already does
  `realSup (λx. ∃n. x = u n)` + nonempty + bounded + `realSupUpperThm`/
  `realSupLeastThm`. Re-read its proof in Seq.wl and copy the realSup-set
  plumbing (the nonempty witness, the bounded-above ∃w, the SPEC of the sup
  lemmas on the raw `λx. ∃n. x = a n` predicate).
- **Available, verified (grep ::usage before use):**
  - Complete.wl: `realSupUpperThm` ⊢ ∀S. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u)
    ⇒ ∀a. S a ⇒ realLe a (realSup S); `realSupLeastThm` ⊢ ∀S v. (∃a. S a) ⇒
    (∃u. ∀a. S a ⇒ realLe a u) ⇒ (∀a. S a ⇒ realLe a v) ⇒ realLe (realSup S) v.
  - Cut.wl: `realLeReflThm`, `realLeTransThm`, `realLeAntisymThm`
    (⊢ ∀x y. realLe x y ⇒ realLe y x ⇒ x = y — VERIFY arg order),
    `realLeTotalThm` ⊢ ∀x y. realLe x y ∨ realLe y x, `realLtNotLeThm`.
  - Abs.wl: `realAbsPosThm` ⊢ ∀x. realLe 0 x ⇒ realAbs x = x.
  - Complete.wl strict: `realLtImpLeThm`, `realLeLtTransThm`, `realLtLeTransThm`.
  - RealArith.wl: `realArithProve[goalTm]` (LINEAR — for the sub/length/ε
    rearrangements over opaque atoms a n, b n, x, y, realSup …);
    `realLtIrreflThm`.
  - Seq.wl Stage 1: `tendsto`/`tendstoTm`/`unfoldTendsto` (for
    IntervalLengthsToZero = tendsto of the length seq to 0; to extract the ∃N
    in the uniqueness proof, unfold tendsto + MP at the chosen eps + CHOOSE N,
    mirroring how Stage 5's Cauchy proof CHOSE its N).
  - Num: `leqReflThm`, `leqTotalThm` (the m≤n / n≤m case split in
    `upper_endpoint_upperBound`).

## Scope

- MODIFY: `stdlib/Real/Seq.wl` (append Stage 6), `tests/real_seq_tests.wl`.
- Do NOT touch other files or runner lists. MUST NOT touch Kernel/Types/Terms/
  Bootstrap/bootstrap.mx/docs/codex(except report). No newAxiom. No new files.

## Definitions (pin; new constants + unfold helpers)

```
nestedIntervalsDefThm:   ⊢ nestedIntervals = (λa b.
    (∀n. realLe (a n) (b n))
  ∧ (∀n m. n ≤ m ⇒ realLe (a n) (a m))
  ∧ (∀n m. n ≤ m ⇒ realLe (b m) (b n)))
intervalLengthsToZeroDefThm: ⊢ intervalLengthsToZero = (λa b.
    tendsto (λn. realAdd (b n) (realNeg (a n))) 0)
```
- a, b : num→real; `0` = zeroRealTm[]; `≤` on n,m is Num leq; the length seq's
  limit `0` is the real zero. Export `nestedIntervalsConst[]`/
  `nestedIntervalsTm[aT,bT]`, `intervalLengthsToZeroConst[]`/`…Tm[aT,bT]` +
  unfold helpers (deep-beta `seqBetaClean` if a redex remains —
  [[wl-unfold-deep-beta-select]]).

## Deliverable theorems (mirror the blueprint)

Helpers (private, names yours; suggested):
- `nestedRangeNonempty`, `nestedRangeBddAbove` (Range a nonempty by a 0,
  bounded above by b 0 via `upperEndpointUB`).
- `upperEndpointUBThm`: ∀n. b n is an upper bound of `λx. ∃m. x = a m`. Case
  `leqTotalThm` on m,n: m≤n ⇒ a m ≤ a n ≤ b n; n≤m ⇒ a m ≤ b m ≤ b n (two
  realLeTrans, using the nest's monotonicity + a n ≤ b n).
- `supInIntervalThm`: ∀n. realLe (a n) s ∧ realLe s (b n) where s = realSup
  (Range a) — `realSupUpperThm` (a n ≤ s, a n is a member) + `realSupLeastThm`
  (s ≤ b n, b n is an upper bound), under nonempty+bounded.

Public:
1. `nestedExistsPointThm` ⊢ ∀a b. nestedIntervals a b ⇒
   ∃x. ∀n. realLe (a n) x ∧ realLe x (b n). EXISTS x := realSup (Range a) +
   `supInIntervalThm`.
2. `nestedUniquePointThm` ⊢ ∀a b. nestedIntervals a b ⇒
   intervalLengthsToZero a b ⇒
   ∃x. (∀n. realLe (a n) x ∧ realLe x (b n)) ∧
       (∀y. (∀n. realLe (a n) y ∧ realLe y (b n)) ⇒ y = x).
   x := realSup (Range a); first conjunct = `supInIntervalThm`; second:
   `commonPointsEqualThm` (below). **This "lengths→0 ⇒ unique common point"
   theorem is the one downstream M8.2 cares about** — make sure it lands.
   Helpers for it:
   - `commonGapLeLengthThm`: x,y both common points ⇒ ∀n. realLe (realAdd x
     (realNeg y)) (realAdd (b n) (realNeg (a n))) (i.e. x−y ≤ b n − a n) —
     from a n ≤ y and x ≤ b n via realArithProve (linear over a n,b n,x,y).
   - `commonPointLeThm`: x,y common + lengths→0 ⇒ realLe x y. Contradiction:
     CCONTR ¬(x≤y) ⇒ y<x (realLeTotal + realLtNotLe) ⇒ eps := x−y > 0
     (realArithProve); intervalLengthsToZero at eps (unfold tendsto, MP, CHOOSE
     N) gives |（b N−a N)−0| < eps, and since b N−a N ≥ 0 (`realAbsPosThm` after
     a N ≤ b N), b N − a N < eps; but commonGapLeLength gives eps = x−y ≤
     b N−a N, so eps < eps — `realLtIrreflThm` ⇒ F.
   - `commonPointsEqualThm`: x,y common + lengths→0 ⇒ y = x (`commonPointLe`
     both ways + `realLeAntisymThm`).

If a step stalls, deliver the loadable subset (defs + nestedExistsPoint +
helpers) and STOP per stop-loss with a precise report.

## Tests (append ~8 asserts)

- Defs unfold at fresh a,b vars; shape checks.
- `nestedExistsPointThm`/`nestedUniquePointThm` concl-shape at fresh a,b (aconv
  on built expected terms).
- Constant nest `a := λn. c`, `b := λn. c` (c ≤ c, trivially nested, length
  seq ≡ 0 → tendsto 0 via `tendstoConstThm`-style): `nestedExistsPoint` MP'd ⇒
  ∃x. ∀n. c ≤ x ∧ x ≤ c; assert theorem, empty hyps. (Length-zero via
  realArithProve `c + (−c) = 0` under the λ + tendstoConst at 0, or reuse a
  Stage-1 helper.)
- aconv against folder builders; no deep MatchQ.

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder
privates reachable; Complete/Abs/Cut/Num/Bool publics only. 4. HOL var
identity=(name,type): the Range set's bound vars and CHOOSE witnesses
(`mUB`, `nIv`, `Nw`, `yW`) distinctive — never bare a/b/n/m/x/y the caller
carries. 5. holError HoldRest. 6. dev.wls is your verifier (Verification).
7. aconv tests, no deep MatchQ. 8. mkVar/mkConst/mkComb/mkAbs only. 9. Narrow
probes. 10. No Return in Do/For/While. 11. **SPEC does not β-reduce** — the
Range predicate / length λ applied to an index leaves redexes; clean with
BETACONV / seqBetaClean. 12. **realArithProve is LINEAR** — realSup/realAbs/
a-n/b-n opaque atoms; sup ORDER facts from realSupUpper/Least, only the
sub/length/ε rearrangements are realArithProve's (it knows a n,b n,x,y as
atoms; `x−y ≤ b n−a n` from `a n ≤ y`,`x ≤ b n` IS linear → realArithProve).
13. realSup set = raw `λx. ∃n. x = a n`; nonempty `∃a. S a`, bound `∃w. ∀a. S a
⇒ realLe a w` — match the lemma shapes (same as Stage 3 monoIncTendstoSup).

## Verification (MANDATORY — you run wolframscript)

Full machine access. Verify and iterate to green before delivering. The ONLY
command you run:

```
wolframscript -file tests/dev.wls stdlib/Real/Seq.wl real_seq
```

Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste
that final `passed: N  failed: 0` line into your report. Do NOT run
build_snapshot/extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all,
no other command, nothing outside the repo, no network. If the same failure
recurs twice, deliver the loadable subset and report where you stopped — never
fake a green count. Reading failures: `Throw::nocatch` at load = proof/term bug
(localize by which theorem stopped binding); `Syntax::sntx`+line = bracket typo;
`failed:K` + `FAIL` = assertion/aconv mismatch.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one
  dev.wls verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. The exact final `passed: N  failed: 0` from your dev.wls run.
4. Which theorems fully proven vs stopped.
5. Open questions (empty if none).
