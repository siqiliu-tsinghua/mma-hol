# Brief 011 — stdlib/Real/Seq.wl Stage 3: monotone convergence from the sup principle

## Goal

Extend `stdlib/Real/Seq.wl` (Stages 1+2, briefs 008–010 — read the whole file
first) with the **monotone convergence theorem**: a monotone-increasing
bounded-above sequence converges to the sup of its range; the decreasing case
by negation. Plus the two prerequisites it needs (an "abs from two-sided
bounds" lemma and a "below-sup ⇒ a member exceeds it" LUB lemma) and the
monotone/bounded predicate definitions. This is M7-8 Stage 3. Append tests.

## Blueprint (in-repo, gitignored, on disk — READ and mirror)

`tautology-ref/Tautology/RealSequence/`:
- `Principles/Statements.lean` — the defs `MonotoneIncreasing`,
  `MonotoneDecreasing`, `SeqBoundedAbove`, `SeqBoundedBelow` (mirror exactly).
- `Principles/FromSupMonotone.lean` — **THE proof structure**:
  `range_nonempty`, `range_bounded_above`, `supRange` (= sup of the range
  set), `supRange_is_lub`, `monotone_increasing_tendsto_sup`,
  `neg_monotone_increasing_of_decreasing`,
  `neg_bounded_above_of_bounded_below`, `monotone_decreasing_converges`.
- `Order.lean:27` `abs_sub_lt_of_bounds` — the abs-from-bounds lemma.

Surface translation as before: `F.lt/le/add/sub/neg/zero`, `abs F`,
`SeqTendsto` → our `realLt/realLe/realAdd/(realAdd x (realNeg y))/realNeg/
zeroRealTm[]/realAbsTm/tendsto`. Their `exists_lt_of_lt_lub`,
`le_lub_of_mem`, `abs_sub_lt_of_bounds` → our new prerequisite lemmas below.
Their `Classical.choose`-based `supRange` → our concrete `realSup` (Complete.wl)
applied to the range PREDICATE. Their linear ε-steps → `realArithProve`.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- In context `HOL`Stdlib`Real`` — all Real-folder + Seq.wl privates reachable
  by bare name (e.g. brief-010's private `realAbsNonposThm` ⊢ ∀x. realLe x 0 ⇒
  realAbs x = realNeg x — reuse it, do NOT redefine).
- **Verified available (grep ::usage before use):**
  - Complete.wl: `realSupConst[]`/`realSupDefThm`; `realSupUpperThm` ⊢ ∀S.
    (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ ∀a. S a ⇒ realLe a (realSup S);
    `realSupLeastThm` ⊢ ∀S v. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒
    (∀a. S a ⇒ realLe a v) ⇒ realLe (realSup S) v;
    `dedekindCompleteThm` (packaged). **NOTE the set S is a RAW `real→bool`
    predicate applied directly (`S a`), NOT a Set.wl IN-wrapper.**
  - Abs.wl: `realAbsPosThm` ⊢ ∀x. realLe 0 x ⇒ realAbs x = x;
    `realAbsNonnegThm`. (For x≤0 use the in-file `realAbsNonposThm`.)
  - Mul.wl: `realLeNegThm` ⊢ ∀x y. realLe x y ⇒ realLe (realNeg y)(realNeg x);
    `realNegNegThm` ⊢ ∀x. realNeg(realNeg x)=x.
  - Cut.wl: `realLtNotLeThm` ⊢ ∀x y. realLt x y = ¬(realLe y x);
    `realLeReflThm`, `realLeTransThm`.
  - Complete.wl strict-order: `realLtLeTransThm`, `realLeLtTransThm`,
    `realLtImpLeThm`, `realLtTransThm`.
  - RealArith.wl: `realNotLeLtThm` ⊢ ∀x y. ¬(realLe x y) = realLt y x;
    `realLtIrreflThm`; `realArithProve[goalTm]`.
  - Seq.wl Stage 1: `tendstoConst[]`/`tendstoTm`/`unfoldTendsto`,
    `tendstoNegThm` ⊢ ∀a A. tendsto a A ⇒ tendsto (λn. realNeg(a n))(realNeg A);
    the `eventually` combinator (brief-009) — optional here.
  - Num: `leqReflThm`, `leqTransThm`, `leqConst[]`, the seq type `seqTy`
    (num→real) and its builders (grep Seq.wl for `seqTy`, `mkComb[uV, nV]`).
- `realArithProve` is LINEAR over opaque atoms — use it for every linear real
  step (`s + (−eps) < x ⟺ −eps < x + (−s)`, `x < s + eps ⟺ x + (−s) < eps`,
  `s + (−eps) < s` from `0 < eps`, the `t < t ⇒ F` close, etc.). It abstracts
  `realAbs …`, `u n`, `realSup …` as opaque variables, so anything mentioning
  those as indivisible atoms in a LINEAR relation is fine.

## Scope

- MODIFY: `stdlib/Real/Seq.wl` (append Stage 3), `tests/real_seq_tests.wl`.
- Do NOT touch other Real files or runner lists. MUST NOT touch Kernel/Types/
  Terms/Bootstrap/bootstrap.mx/docs/codex(except report). No newAxiom. No new
  files.

## Definitions (pin exactly; new constants in Seq.wl, newDefinition + unfold helpers)

```
monoIncDefThm:        ⊢ monoInc = (λu. ∀n m. n ≤ m ⇒ realLe (u n) (u m))
monoDecDefThm:        ⊢ monoDec = (λu. ∀n m. n ≤ m ⇒ realLe (u m) (u n))
seqBddAboveDefThm:    ⊢ seqBddAbove = (λu. ∃B. ∀n. realLe (u n) B)
seqBddBelowDefThm:    ⊢ seqBddBelow = (λu. ∃B. ∀n. realLe B (u n))
```
- u : num→real (the seq type). `≤` on n,m is Num leq. Export
  `monoIncConst[]`/`monoIncTm[uT]` etc. + `unfold*` helpers (APTHM+BETACONV).

## Deliverable theorems

### Prerequisites

1. `realAbsSubLtThm` ⊢ ∀x a e.
   realLt (realAdd a (realNeg e)) x ⇒ realLt x (realAdd a e) ⇒
   realLt (realAbs (realAdd x (realNeg a))) e.
   Mirror Order.lean `abs_sub_lt_of_bounds`. EXCLUDEDMIDDLE on
   `realLe 0 (realAdd x (realNeg a))`:
   - 0 ≤ x−a: `realAbsPosThm` ⇒ |x−a| = x−a; goal becomes x−a < e, which is
     `realArithProve`-equivalent to the hyp `x < a+e`. EQMP the abs equation.
   - ¬(0 ≤ x−a): `realAbsNonposThm` needs x−a ≤ 0 — get it from
     `realNotLeLtThm` (¬(0≤x−a) ⇒ x−a < 0) + `realLtImpLeThm`. Then
     |x−a| = −(x−a); goal becomes −(x−a) < e, i.e. `realArithProve`-equivalent
     to the hyp `a−e < x` (i.e. `a + (−e) < x`). EQMP.
   (Each branch: one realArithProve for the linear equivalence + EQMP through
   the abs equation. Build the `realLt (realAbs …) e` from the rewritten side.)

2. `realSupLtMemThm` ⊢ ∀S t.
   (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ realLt t (realSup S) ⇒
   ∃a. S a ∧ realLt t a.
   CCONTR on the goal. ASSUME `¬(∃a. S a ∧ realLt t a)`. Show t is an upper
   bound: GEN aB (distinctive), DISCH (S aB); from the ¬∃ derive
   ¬(S aB ∧ realLt t aB) (a `∃`-intro contrapositive / NOT_EXISTS step — if
   building NOT_EXISTS is awkward, do: ASSUME (realLt t aB), then EXISTS to
   contradict ¬∃, discharge to ¬(realLt t aB)), then ¬(realLt t aB) ⇒
   realLe aB t via `realLtNotLeThm` (realLt t aB = ¬(realLe aB t)) + double-neg
   (propTaut or CCONTR). So `∀a. S a ⇒ realLe a t`. `realSupLeastThm` (with the
   nonempty+bounded hyps) ⇒ realLe (realSup S) t. With `realLt t (realSup S)`,
   realArithProve closes `t < realSup S ≤ t ⇒ F` (treat realSup S as an opaque
   atom: `∀t s. realLt t s ⇒ realLe s t ⇒ <False-ish>` — actually feed it as
   `realLt t s ∧ realLe s t` and close via realLtIrrefl after realLeLtTrans, or
   one realArithProve proving the contradiction atom then NOTELIM). Distinctive
   binders (aB, the witness).

### Main theorems

3. `monoIncTendstoSupThm` ⊢ ∀u. monoInc u ⇒ seqBddAbove u ⇒
   tendsto u (realSup (λx. ∃n. x = u n)).
   Mirror `monotone_increasing_tendsto_sup`. Let `rangeTm[uT] = λx. ∃n. x = u n`
   (real→bool; distinctive bound names xR, nR). Nonempty: EXISTS x:=u 0, n:=0,
   REFL (⊢ ∃a. range a). Bounded: from `seqBddAbove u` CHOOSE B; ⊢ ∃w. ∀a.
   range a ⇒ realLe a w with w:=B (GEN a, DISCH (range a), CHOOSE n with a=u n,
   rewrite, apply the bound at n). s := realSup range. `realSupUpperThm` (with
   the two hyps) ⇒ ∀a. range a ⇒ realLe a s, so realLe (u n) s for any n
   (EXISTS the range-membership). Unfold tendsto: GEN eps, DISCH (0<eps).
   `realSupLtMemThm` at t := s + (−eps) (note s+(−eps) < s by realArithProve
   from 0<eps) ⇒ ∃a. range a ∧ s+(−eps) < a; CHOOSE a, then CHOOSE N with
   a = u N; so s+(−eps) < u N. EXISTS N. GEN n, DISCH (N ≤ n):
   - hleft: s+(−eps) < u N ≤ u n (monoInc N n, needs N≤n) ⇒ s+(−eps) < u n
     (realLtLeTrans).
   - hright: u n ≤ s (realSupUpper at n) and s < s+eps (realArithProve from
     0<eps) ⇒ u n < s+eps (realLeLtTrans).
   - `realAbsSubLtThm` x:=u n, a:=s, e:=eps ⇒ realLt (realAbs (u n + (−s))) eps
     = the tendsto body. Build the ∃N.∀n… witness.
4. `monoConvergesIncThm` ⊢ ∀u. monoInc u ⇒ seqBddAbove u ⇒ ∃L. tendsto u L.
   EXISTS L := realSup (range u), from theorem 3. (The ∃ form Stage 4/5 consume.)
5. `monoConvergesDecThm` ⊢ ∀u. monoDec u ⇒ seqBddBelow u ⇒ ∃L. tendsto u L.
   Mirror `monotone_decreasing_converges`: let v := λn. realNeg (u n). Show
   `monoInc v` (from monoDec u + `realLeNegThm`) and `seqBddAbove v` (from
   seqBddBelow u + realLeNegThm, bound −B). monoConvergesIncThm ⇒ ∃L'. tendsto
   v L'; CHOOSE L'. `tendstoNegThm` ⇒ tendsto (λn. realNeg (v n)) (realNeg L').
   The sequence `λn. realNeg (realNeg (u n))` reduces to u via `realNegNegThm`
   under the λ (APTERM/funcExt or eventuallyMono on the body — follow the Lean
   `simpa [neg_neg]`); EXISTS (realNeg L'). Mind β-redexes (pitfall 11).

If a step stalls, deliver the loadable subset (defs + prerequisites + the
increasing theorems at minimum) and STOP per stop-loss with a report.

## Tests (append ~15 asserts)

- Defs: unfold each at a fresh seq var; shape check.
- `realAbsSubLtThm` SPEC'd at rnum literals + MP two bound facts (from
  `realArithProve`/`rnumLt`) ⇒ a concrete |·|<e.
- `realSupLtMemThm`: hard to instantiate cleanly; a shape/concl check after
  SPEC + the three MPs against a simple finite range is enough, OR skip and
  rely on the monotone theorems exercising it.
- A constant sequence `λn. c` is monoInc (and monoDec) and bddAbove (and
  below): build `monoInc (λn.c)` via the defs + `realLeReflThm`, feed
  `monoConvergesIncThm` ⇒ ∃L. tendsto (λn.c) L; cross-check with
  `tendstoConstThm` shape.
- `monoConvergesDecThm` on a constant sequence.
- Build expected terms with folder builders; aconv; no deep MatchQ.

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder
privates reachable; RealArith/Bool/PropTaut privates NOT (publics:
realArithProve, realNotLeLtThm, realLtIrreflThm; propTaut IS public).
4. HOL var identity=(name,type); the range set's bound vars (xR,nR), the sup
upper-bound binder, CHOOSE witnesses (aW,nW,bW,lW) all distinctive — NEVER
bare x/n/a that the caller's `u`/terms carry. 5. holError HoldRest.
6. `wolframscript -file` only. 7. aconv tests, no deep MatchQ. 8. mkVar/
mkConst/mkComb/mkAbs only. 9. Narrow probes. 10. No Return in Do/For/While.
11. **SPEC does not β-reduce** — clean λ-application redexes (the range
predicate applied to a witness, the `λn. −−u n` body) with
CONVRULE[DEPTHCONV[TRYCONV[BETACONV]]]. 12. **realArithProve is LINEAR** —
realSup/realAbs/u-n are opaque atoms to it; the sup ORDER facts come from
realSupUpper/Least, only the ε-rearrangements are realArithProve's.
13. The sup set is a RAW predicate `λx. ∃n. x = u n` fed to realSup/the sup
lemmas as `S`; the nonempty hyp is `∃a. S a`, the bound hyp `∃w. ∀a. S a ⇒
realLe a w` — match these shapes exactly (the lemmas SPEC on S).

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
3. Which theorems fully proven vs stopped.
4. Open questions (empty if none).
