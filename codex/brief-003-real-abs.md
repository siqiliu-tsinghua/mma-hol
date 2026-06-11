# Brief 003 — stdlib/Real/Abs.wl: absolute value on ℝ (M8 prerequisite)

## Goal

Create `stdlib/Real/Abs.wl` — the absolute-value layer on the completed
ordered field ℝ — with definition, sign/case lemmas, and the triangle
inequality, plus a test file `tests/real_abs_tests.wl`. This is a NEW
FRONTIER file: do NOT wire it into any runner list; verification is done
outside your sandbox with `tests/dev.wls`.

## Context pointers

- Read `CLAUDE.md` (Conventions; the variable-capture hygiene block; the
  stdlib/Real folder description) first.
- The Real folder shares one package context `HOL`Stdlib`Real``: every file
  begins with the same `BeginPackage["HOL`Stdlib`Real`", {…}]` header (copy
  the import list from `stdlib/Real/Complete.wl`) and all `` `Private` ``
  helpers of Cut/Field/Mul/Inv/Complete are directly usable by bare name.
- **Structural template: `stdlib/Real/Inv.wl`.** Its `realInv` is defined as
  a `COND` over a sign test and unfolded/case-reduced exactly the way
  `realAbs` needs. Read how `realInvDefThm` builds the COND term, how the
  unfold helper works, and how `realInvPosThm`/`realInvNegThm` reduce the
  COND under a hypothesis (grep `condReduce` in `stdlib/Real/*.wl` for the
  reusable helpers; they live in the shared Private context).
- Useful existing builders (shared Private): `realTy`, `realLeTm`,
  `realLtTm`, `realAddTm`, `realNegTm`, `realOfRatTm`, `zeroQ[]`, `rZ[]`
  (= the term `&ℝ (&ℚ (&ℤ 0))`), `forallTm`, `conjTm`, `impTm`, `notTm`.
  Grep before assuming a name; if one is missing, define it locally.
- Useful existing theorems (all exported from the Real folder):
  `realLeReflThm`, `realLeTransThm`, `realLeAntisymThm`, `realLeTotalThm`
  (Cut); `realAddCommThm`, `realAddZeroThm`, `realAddNegThm`,
  `realAddAssocThm` (Field); `realNegZeroThm`, `realNegNegThm`,
  `realNegAddThm` (−(x+y) = −x + −y), `realLeNegThm` (x≤y ⇒ −y≤−x),
  `realLeAddMonoThm` (a≤b ⇒ a+c≤b+c), and the
  `realNegNonneg`/`realNegNonpos`/`notNonnegNeg` group (Mul — read their
  ::usage strings to pick the right one); `realLtImpLeThm` etc. (Complete).
- Proof style: pure forward style (ASSUME/SPEC/MP/EQMP/TRANS/DISCH/GEN +
  EXCLUDEDMIDDLE/DISJCASES for case splits), one `Module` per theorem, like
  every file in the folder. No tactics needed.

## Scope

- Files you MAY create: `stdlib/Real/Abs.wl`, `tests/real_abs_tests.wl`.
- Files you MUST NOT touch: everything else. In particular do NOT edit the
  runner lists (`tests/run_all.wls`, `tests/run_all_stable.wls`,
  `tests/build_snapshot.wls`), `bootstrap.mx`, any existing Real file,
  `CLAUDE.md`/`PLAN.md`/`PROGRESS.md`/`TODO.md`, `codex/`.
- Do NOT add new axioms.

## Deliverable — definition + theorems, in this order

Let `0ᵣ` abbreviate the term `rZ[]` = `&ℝ (&ℚ (&ℤ 0))` below.

1. `realAbsDefThm` — `⊢ realAbs = (λx. COND (realLe 0ᵣ x) x (realNeg x))`
   via `newDefinition`; `realAbsConst[]`; an unfold/`realAbsTm` helper in
   the style of Inv.wl. Type: `real → real`.
2. `realAbsPosThm` — `⊢ ∀x. realLe 0ᵣ x ⇒ realAbs x = x` (condReduce-T).
3. `realAbsNegCaseThm` — `⊢ ∀x. ¬(realLe 0ᵣ x) ⇒ realAbs x = realNeg x`
   (condReduce-F).
4. `realAbsZeroThm` — `⊢ realAbs 0ᵣ = 0ᵣ` (MP of 2 with `realLeReflThm`).
5. `realAbsNonnegThm` — `⊢ ∀x. realLe 0ᵣ (realAbs x)`.
   Sketch: EXCLUDEDMIDDLE on `realLe 0ᵣ x`; positive branch rewrites by 2
   and is the hypothesis itself; negative branch rewrites by 3 and needs
   `¬(0≤x) ⇒ 0 ≤ −x`: from `realLeTotalThm[0ᵣ, x]` the negative hypothesis
   forces `x ≤ 0ᵣ` (DISJCASES, CONTR on the impossible side), then
   `realLeNegThm` gives `−0 ≤ −x`, then rewrite `−0` to `0` with
   `realNegZeroThm` (one of the `realNeg*`/`notNonneg*` lemmas in Mul may
   already package this step — check usages first).
6. `realLeAbsSelfThm` — `⊢ ∀x. realLe x (realAbs x)`.
   Sketch: EM on `0≤x`; positive: rewrite |x|=x, `realLeReflThm`; negative:
   rewrite |x|=−x, then x ≤ 0 ≤ −x by the two facts from step 5's negative
   branch + `realLeTransThm`.
7. `realNegLeAbsThm` — `⊢ ∀x. realLe (realNeg x) (realAbs x)`.
   Sketch: mirror of 6 — positive branch: −x ≤ 0 ≤ x = |x| (from 0≤x via
   `realLeNegThm` + `realNegZeroThm`); negative branch: |x| = −x, refl.
8. `realAbsNegThm` — `⊢ ∀x. realAbs (realNeg x) = realAbs x`.
   Sketch: EM on `0≤x`.
   - Negative branch is the EASY one (no sub-split): `¬(0≤x)` gives
     `0 ≤ −x` (as in 5), so |−x| = −x (by 2 at −x) and |x| = −x (by 3);
     chain the equations.
   - Positive branch needs a SUB-split (EM on `0 ≤ −x`):
     (a) `0≤x ∧ ¬(0≤−x)`: |−x| = −(−x) (by 3 at −x) = x (`realNegNegThm`)
         = |x| (by 2, SYM).
     (b) `0≤x ∧ 0≤−x`: then `x ≤ 0` (negate the second via
         `realLeNegThm`/`realNegZeroThm` reasoning in reverse — from
         `0 ≤ −x` derive `x = −(−x) ≤ −0 = 0` or use antisymmetry directly)
         so `x = 0ᵣ` by `realLeAntisymThm`; rewrite both sides through
         `realNegZeroThm`/`realAbsZeroThm`. This is the fiddly corner —
         take the equation-chaining slowly and keep every rewrite an
         explicit EQMP/TRANS.
9. Private helper `leAddMono2` — from `⊢ a≤b` and `⊢ c≤d` derive
   `⊢ a+c ≤ b+d`: `realLeAddMonoThm` (right-add c) gives a+c≤b+c; the same
   lemma (right-add b) gives c+b≤d+b; commute both sides with
   `realAddCommThm` (EQMP through a `MKCOMB`/`APTERM` congruence or rewrite
   each side separately) to get b+c≤b+d; `realLeTransThm` chains.
10. `realAbsTriangleThm` —
    `⊢ ∀x y. realLe (realAbs (realAdd x y)) (realAdd (realAbs x) (realAbs y))`.
    Sketch: EM on `0 ≤ x+y`.
    - Positive: |x+y| = x+y (by 2); x ≤ |x| (6), y ≤ |y| (6); `leAddMono2`;
      rewrite the left side back through the |x+y| equation (SYM + EQMP via
      an `APTERM`/`MKCOMB` congruence on the ≤ term).
    - Negative: |x+y| = −(x+y) (by 3) = −x + −y (`realNegAddThm`);
      −x ≤ |x| (7), −y ≤ |y| (7); `leAddMono2`; rewrite.

Tests (`tests/real_abs_tests.wl`): copy the header + style of
`tests/real_complete_tests.wl` exactly (Needs list, `HOLTest`runTests`
blocks asserting `hyp[...] === {}` and `isThm[...]`), one block per exported
theorem (items 1–8 and 10; the private helper needs no test).

**Graded delivery**: items 1–7 are REQUIRED. If 8 or 10 hits the stop-loss
(same failure twice), deliver the completed subset — but the file MUST stay
loadable: remove (do not comment out) any unfinished theorem and its test,
and say exactly where you stopped and why in the report.

## WL / project pitfalls

All nine from `codex/TEMPLATE.md`, plus the ones that dominate THIS task:

- **Variable hygiene (CLAUDE.md block — read it)**: HOL var identity is
  (name, type). Final-statement binders use canonical names (`x`, `y`);
  any proof-internal witness or case variable must get a distinctive name.
  For this task you mostly bind over `x`,`y` directly (safe: they are the
  outermost GEN binders), but never introduce a SECOND internal variable
  named `x`/`y`.
- **Extract, don't rebuild**: when a kernel/derived rule hands you a term
  (a COND unfold RHS, an instantiated body), reuse it via `concl[...]`
  positions instead of re-typing the term by hand — α-mismatches in
  hand-rebuilt terms are the classic failure here.
- Wrong-context symbols return UNEVALUATED and only explode later as
  "concl: not a theorem" — if a rule application stays unevaluated, check
  the symbol's context (`Context[sym]`) before anything else. Rat-layer
  lemma names like `ratNegNegThm` live in `HOL`Stdlib`Real`` (RatAux), NOT
  `HOL`Stdlib`Rat`` — for this task you should not need Rat internals at
  all; stay on the real-layer surface listed above.
- `newDefinition` takes `mkEq[mkVar["realAbs", absTy], bodyAbs]` with a
  CLOSED body — copy Inv.wl's `realInvDefThm` shape.

## Verification

Your sandbox cannot run wolframscript (no WolframKernel) — known limitation.
Therefore: deliver code statically self-checked (balanced brackets, no `_`
identifiers, no `*)` inside comments, every theorem's Module returns the
final GEN/DISCH chain). State clearly in the report that the WL suite was
not run. Acceptance will be run outside via
`tests/dev.wls stdlib/Real/Abs.wl real_abs`.

## Hard rules

- No git commit/branch/push; leave changes in the working tree.
- Stop-loss: same failure twice → stop, trim to the loadable subset, report.
- Minimal diff: exactly two new files, nothing else.

## Report format

1. What you delivered (which items; file line counts).
2. For items 8/10: the case structure you actually used (it may differ from
   the sketch — that is fine if the logic is sound).
3. Anything you are unsure about (α-matching spots, helper-name guesses).
