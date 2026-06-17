# Brief 018 — M8.2 Branch B prereq: dyadic-Archimedean principle (new file Real/SeqAux.wl)

## Goal

Start a NEW frontier file `stdlib/Real/SeqAux.wl` (shares `HOL`Stdlib`Real``
context) holding the sequence-layer prerequisites that M8.2 Branch B
(Heine–Borel via nested intervals) needs. This brief delivers the **dyadic
sequence** `dyadic n = 2^n` and the **dyadic-Archimedean principle**:
`⊢ ∀L eps. realLe 0 L ⇒ realLt 0 eps ⇒ ∃n. realLt (realMul L (realInv (dyadic n))) eps`
— i.e. `L / 2^n` can be made arbitrarily small (the tool that makes bisected
interval lengths shrink to 0). New test file `tests/real_seqaux_tests.wl`.
Self-verify with dev.wls, iterate to green.

## Blueprint (in-repo — READ and mirror 1:1)

`tautology-ref/Tautology/RealSequence/Principles/Dyadic.lean` — the COMPLETE
0-sorry reference. Mirror: `dyadic` (num→real recursion), `dyadic_zero`/`_succ`/
`_succ_eq_add`/`_pos`/`_ne_zero`/`one_le_dyadic`/`nat_le_dyadic`,
`exists_dyadic_gt`, `small_mul_inv`, `dyadicArchimedean`. Surface: `F.mul/lt/le/
add/inv/one/zero`, `two F`, `nat F n` → our `realMul/realLt/realLe/realAdd/
realInv/(the 1 literal)/zeroRealTm[]`, the real `2` literal, and `&ℝ(&ℚ(&ℤn̂))`
(= our `realArchThm`'s embedded nat). Their `exists_nat_gt` = our `realArchThm`.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **`dyadic` is a `num→real` recursion via `numIterationThm`** (e := the 1
  literal, f := λx. realMul x two) — SIMPLER than Stage 4a's peakIndex (NO
  Hilbert ε, plain iteration). ε-out the `g` (selectOfExists on numIterationThm
  at A := real) and prove the two recursion equations `dyadic 0 = 1`,
  `dyadic (SUC n) = realMul (dyadic n) two`. **The unfold helper must deep-β
  (`seqBetaClean`), not single BETACONV** ([[wl-unfold-deep-beta-select]]).
  Model it on Seq.wl's `peakIndexRecSpecThm` (but no selectOfExists in f).
- **Available, verified (grep ::usage):**
  - Complete.wl: `realArchThm` ⊢ ∀x. ∃n. realLt x (&ℝ (&ℚ (&ℤ n))) — THE
    Archimedean `exists_nat_gt`. The `&ℝ(&ℚ(&ℤ n))` term is the embedded nat;
    build it with the public `realOfRatConst[]`/`ratOfIntConst[]`/`intOfNumConst[]`
    + a num var (grep how Complete.wl / RealArith builds it).
  - Mul.wl: `realMulOneThm` ⊢ ∀x. realMul x (&ℝ(&ℚ(&ℤ(SUC 0)))) = x (the 1
    literal is `&ℝ(&ℚ(&ℤ(SUC 0)))`); `realMulAssocThm`, `realMulCommThm`,
    `realMulDistribThm`, `realLtMulPosThm`/`realLtMulMonoThm` (mul_lt_mul_pos),
    `realLeMulMonoThm`; sign/order from Mul/Cut.
  - Inv.wl: `realMulInvThm` ⊢ ∀x. ¬(x = &ℝ 0) ⇒ realMul x (realInv x) =
    &ℝ(&ℚ(&ℤ(SUC 0))); `realInvPosThm` ⊢ ∀x. realLt 0 x ⇒ realLt 0 (realInv x)
    (VERIFY exact name); `invPos…`.
  - Cut/Complete: `realLeTransThm`, `realLtLeTransThm`, `realLtTransThm`,
    `realLtImpLeThm`, `realLeReflThm`, `realLtNotLeThm`.
  - RealArith.wl: `realArithProve` (LINEAR — for the `0<1`, `0<2`, `0≤x⇒x≤x+x`,
    additive steps; products of variables are opaque, use the mul lemmas);
    `realLtIrreflThm`. The real `2` literal = `&ℝ(&ℚ(&ℤ(SUC(SUC 0))))`; build it
    with the folder builders (grep `zeroRealTm` in Mul.wl for the pattern, or
    `realOfRatTm`/`ratOfIntTm`).
  - Num: `numIterationThm`, `selectOfExists`, `numInductionThm`, `plusSucEqThm`/
    `addCommThm` (the `n+1` vs `SUC n` — use `SUC n` consistently).
- `two = realAdd 1 1 = realMul 1 2`? In the blueprint `two F = F.add F.one F.one`
  and `dyadic_succ_eq_add` rewrites `x·2 = x + x` (via `mul_add`+`mul_one`). Use
  whichever 2-form is cleanest; `realArithProve` can prove `x·2 = x + x` if 2 is
  the literal `&ℝ(&ℚ(&ℤ(SUC(SUC 0))))` (it knows numerals) — lean on it.

## Scope

- Files you may CREATE: `stdlib/Real/SeqAux.wl`, `tests/real_seqaux_tests.wl`.
- Do NOT touch runner load lists (reviewer wires SeqAux into run_all after Seq.wl
  / before Compact.wl at acceptance). MUST NOT touch Kernel/Types/Terms/Bootstrap/
  bootstrap.mx/docs/codex(except report). No newAxiom. No other new files.
- `SeqAux.wl` package: copy `Compact.wl`'s `BeginPackage["HOL`Stdlib`Real`", {…}]`
  import list + `Begin["`Private`"]`/`End[]`/`EndPackage[]` exactly.

## Definitions (pin; new constants + unfold helpers)

```
dyadicDefThm:  ⊢ dyadic = (ε-out of numIterationThm at e:=<1 literal>, f:=λx. realMul x <2 literal>)
   so that:  dyadicRecSpecThm ⊢ dyadic 0 = <1> ∧ ∀n. dyadic (SUC n) = realMul (dyadic n) <2>
```
Export `dyadicConst[]`/`dyadicTm[nT]` + `dyadicRecSpecThm` (the two equations,
via the deep-β fold — mirror peakIndexRecSpecThm).

## Deliverable theorems (mirror Dyadic.lean)

1. `dyadicZeroThm` ⊢ dyadic 0 = <1 literal>; `dyadicSuccThm` ⊢ ∀n.
   dyadic (SUC n) = realMul (dyadic n) <2>; `dyadicSuccAddThm` ⊢ ∀n.
   dyadic (SUC n) = realAdd (dyadic n) (dyadic n) (from succ + `x·2 = x+x` via
   realArithProve or realMulDistrib+realMulOne).
2. `dyadicPosThm` ⊢ ∀n. realLt 0 (dyadic n) (numInduction: base 0<1; step
   0<dyadic n ∧ 0<2 ⇒ 0<dyadic n · 2 via realLtMulPos).
3. `dyadicNeZeroThm` ⊢ ∀n. ¬(dyadic n = 0) (from pos).
4. `oneLeDyadicThm` ⊢ ∀n. realLe 1 (dyadic n) (numInduction; step: dyadic n ≤
   dyadic n + dyadic n = dyadic(SUC n), using 0 ≤ dyadic n).
5. `natLeDyadicThm` ⊢ ∀n. realLe (&ℝ(&ℚ(&ℤ n))) (dyadic n) (numInduction; base
   0 ≤ 1; step (n's embed)+1 ≤ dyadic n + 1 ≤ dyadic n + dyadic n = dyadic(SUC n);
   the `&ℝ(&ℚ(&ℤ(SUC n))) = &ℝ(&ℚ(&ℤ n)) + 1` step via the embedding homs /
   realArithProve over the embedded-nat atom).
6. `existsDyadicGtThm` ⊢ ∀x. ∃n. realLt x (dyadic n) (from `realArchThm` at x
   giving x < &ℝ(&ℚ(&ℤ n)), then `natLeDyadicThm` + realLtLeTrans).
7. `dyadicArchThm` ⊢ ∀L eps. realLe 0 L ⇒ realLt 0 eps ⇒
   ∃n. realLt (realMul L (realInv (dyadic n))) eps. Mirror `small_mul_inv`:
   `existsDyadicGtThm` at `realMul L (realInv eps)` gives n with
   L·(1/eps) < dyadic n; then L < dyadic n · eps (mul_lt_mul_pos by eps,
   cancel inv via realMulInvThm); then L·(1/dyadic n) < eps (mul_lt_mul_pos by
   1/dyadic n > 0, cancel). The cancellations are `realMulInvThm` +
   realMulAssoc/Comm/One (NOT realArithProve — products of variables).

If a step stalls, deliver through whatever lands (defs + 1–6 at least) and STOP
per stop-loss with a precise report.

## Tests (`tests/real_seqaux_tests.wl`, ~10 asserts)

- Import harness + folder; structure like real_compact_tests.wl. **NO
  `testExit[]` — end with the last `runTests[...]`.**
- `dyadicRecSpec` 0/SUC equations; `dyadicPos`/`oneLeDyadic`/`natLeDyadic`/
  `dyadicArch` concl shapes at fresh vars (aconv).
- `dyadicZeroThm` concrete; `dyadicSuccThm` at a numeral.
- aconv against folder builders; no deep MatchQ.

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder +
Seq/Compact/Num publics reachable. 4. HOL var identity=(name,type): recursion/
CHOOSE binders distinctive (`gIt`, `nW`, `LW`, `epsW`). 5. holError HoldRest.
6. dev.wls is your verifier. 7. aconv tests, no deep MatchQ, **no testExit**.
8. mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes (catch-load + per-theorem
isThm to localize a load throw). 10. No Return in Do/For/While. 11. **deep-β
unfold for the ε-out `dyadic`** ([[wl-unfold-deep-beta-select]]); `seqBetaClean`.
12. SPEC doesn't β-reduce. 13. **realArithProve is LINEAR** — `dyadic n`,
`realInv …`, `&ℝ(&ℚ(&ℤn))` are opaque atoms; `x·2 = x+x`, `0<1`, `0<2`,
additive/embedded-nat steps are realArithProve; the inv-cancellation products
are the mul lemmas. 14. New file: BeginPackage import list + Begin/End/EndPackage
exactly (copy Compact.wl).

## Verification (MANDATORY — you run wolframscript)

Full machine access. The ONLY command you run:

```
wolframscript -file tests/dev.wls stdlib/Real/SeqAux.wl real_seqaux
```

Loop edit → run → read failure → fix until `failed: 0`; paste the final
`passed: N  failed: 0` into your report. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other
command, nothing outside the repo, no network. Same failure twice → deliver the
loadable subset + report. If dev.wls says the snapshot is STALE, STOP and report.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls
  verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. How you exposed `dyadic` + the recursion equations.
4. The exact final `passed: N  failed: 0` from your dev.wls run.
5. Which theorems fully proven vs stopped.
6. Open questions (empty if none).
