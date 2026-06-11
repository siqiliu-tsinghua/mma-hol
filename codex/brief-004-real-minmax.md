# Brief 004 — stdlib/Real/MinMax.wl: binary max/min on ℝ (M8 prerequisite)

## Goal

Create `stdlib/Real/MinMax.wl` — binary `realMax`/`realMin` with their
order-theoretic characterizations — plus `tests/real_minmax_tests.wl`.
NEW FRONTIER file: do NOT wire any runner list; acceptance runs outside via
`tests/dev.wls stdlib/Real/MinMax.wl real_minmax`.

This brief follows brief-003 (`stdlib/Real/Abs.wl`, now part of the
snapshot): reuse its structure — same package header, same COND-definition
pattern, same condReduce case-reduction style, same test-file conventions
(`tests/real_abs_tests.wl` is the closest model).

## Context pointers

- Read `CLAUDE.md` Conventions + the stdlib/Real folder notes.
- Structural template: `stdlib/Real/Abs.wl` (brief-003's output — read it
  first; it is the most recent and closest precedent, including how it
  builds COND terms, unfolds the definition, and reduces under a
  hypothesis).
- Available theorems (besides everything listed in brief-003):
  `realLeReflThm`, `realLeTransThm`, `realLeAntisymThm`, `realLeTotalThm`,
  and now ALL of Abs.wl's exports (`realAbsPosThm`, `realAbsNegCaseThm`,
  `realLeAbsSelfThm`, `realNegLeAbsThm`, …).
- Case-split idiom: `EXCLUDEDMIDDLE` + `DISJCASES`; from `¬(x≤y)` get
  `y≤x` via `realLeTotalThm` + DISJCASES + CONTR (Abs.wl does exactly this).

## Scope

- Files you MAY create: `stdlib/Real/MinMax.wl`, `tests/real_minmax_tests.wl`.
- Files you MUST NOT touch: everything else (runners, bootstrap.mx, all
  existing sources, docs, codex/).
- Do NOT add new axioms.

## Deliverable — definitions + theorems, in this order

1. `realMaxDefThm` — `⊢ realMax = (λx y. COND (realLe x y) y x)` via
   `newDefinition`; `realMaxConst[]`; unfold helper. Type
   `real → real → real`. Likewise `realMinDefThm` —
   `⊢ realMin = (λx y. COND (realLe x y) x y)`.
2. Case-reduction lemmas (condReduce style):
   `realMaxLeCaseThm` — `⊢ ∀x y. realLe x y ⇒ realMax x y = y`;
   `realMaxGtCaseThm` — `⊢ ∀x y. ¬(realLe x y) ⇒ realMax x y = x`;
   `realMinLeCaseThm` — `⊢ ∀x y. realLe x y ⇒ realMin x y = x`;
   `realMinGtCaseThm` — `⊢ ∀x y. ¬(realLe x y) ⇒ realMin x y = y`.
3. Upper-bound laws:
   `realLeMaxLeftThm` — `⊢ ∀x y. realLe x (realMax x y)`;
   `realLeMaxRightThm` — `⊢ ∀x y. realLe y (realMax x y)`.
   Sketch: EM on `x≤y`; in each branch rewrite max by the case lemma; the
   nontrivial side uses `¬(x≤y) ⇒ y≤x` (totality + CONTR) or `realLeReflThm`.
4. Lower-bound laws (mirror): `realMinLeLeftThm` (`min x y ≤ x`),
   `realMinLeRightThm` (`min x y ≤ y`).
5. Least-upper-bound / greatest-lower-bound:
   `realMaxLubThm` — `⊢ ∀x y z. realLe x z ⇒ realLe y z ⇒ realLe (realMax x y) z`;
   `realMinGlbThm` — `⊢ ∀x y z. realLe z x ⇒ realLe z y ⇒ realLe z (realMin x y)`.
   Sketch: EM on `x≤y`, rewrite, the hypothesis for the surviving arm closes it.
6. Commutativity:
   `realMaxCommThm` — `⊢ ∀x y. realMax x y = realMax y x`;
   `realMinCommThm`.
   Sketch: EM on `x≤y` and on `y≤x` (nested). Mixed corners are direct case
   rewrites; the both-≤ corner gives `x = y` by `realLeAntisymThm` — after
   substituting the equation the two sides become syntactically equal terms
   (finish with REFL/EQMP chains, or rewrite one side's argument via an
   APTERM/MKCOMB congruence with the equation). The both-¬ corner is
   impossible: totality + CONTR.
   Alternative (often FEWER steps): prove both sides equal by
   `realLeAntisymThm` applied to two `realMaxLubThm`/`realLeMax*` instances
   — `max x y ≤ max y x` (Lub with `x ≤ max y x` = LeMaxRight at (y,x), and
   `y ≤ max y x` = LeMaxLeft at (y,x)) and symmetrically. Pick whichever you
   find cleaner; the antisym route avoids the corner analysis entirely.
7. BONUS (optional, attempt only after 1–6 are done):
   `realAbsMaxThm` — `⊢ ∀x. realAbs x = realMax x (realNeg x)`.
   Sketch: antisym route — `|x| ≤ max x (−x)`: EM on `0≤x` rewrites |x| to
   x or −x, each is ≤ max by 3; `max x (−x) ≤ |x|`: Lub with
   `realLeAbsSelfThm` + `realNegLeAbsThm`.

Tests (`tests/real_minmax_tests.wl`): copy `tests/real_abs_tests.wl`'s
header/style; one runTests block per exported theorem (hyp === {} +
isThm). If you skip the bonus, no test for it.

**Graded delivery**: 1–6 REQUIRED; 7 optional. Stop-loss per the template;
deliver a loadable subset (remove, don't comment out, unfinished items).

## WL / project pitfalls

All ten from `codex/TEMPLATE.md` (note rule 10 — no `Return` inside
`Do`/`For`/`While`; it exits only the loop, not the Module). Task-specific:

- Final-statement binders: `x`, `y`, `z` only, outermost GENs. No internal
  variable may reuse those names.
- Extract, don't rebuild: take COND-unfold RHS terms from `concl[...]`.
- Two `newDefinition` calls in one file is fine (Abs.wl has one; Pair/Num
  have many) — each needs a CLOSED λ-body.
- The ¬-branch helper "¬(a≤b) ⇒ b≤a" appears in Abs.wl as an inline
  pattern; you may factor a local private helper `notLeFlip` for it (used
  many times here).

## Verification

Sandbox cannot run wolframscript (known). Deliver statically self-checked;
acceptance outside via `tests/dev.wls stdlib/Real/MinMax.wl real_minmax`.

## Hard rules

No git operations; stop-loss; minimal diff (exactly two new files).

## Report format

As TEMPLATE.md: per-item delivery status, case structures actually used
(esp. whether you took the antisym route for 6/7), unsure points.
