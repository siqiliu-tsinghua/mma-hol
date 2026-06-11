# Brief 007 — auto/RealArith.wl Stage 3: Farkas oracle + verifier + REAL_ARITH tactic

## Goal

Final stage of M7-ε REAL_ARITH. Extend `auto/RealArith.wl` (Stages 1+2 —
read the whole file first; nearly every primitive you need already exists)
with the decision procedure: `realArithProve[goalTm]` proving universally
quantified linear-arithmetic implications over ℝ via a Fourier–Motzkin
oracle (untrusted, exact rationals, certificate-producing) + a kernel
verifier that replays the Farkas certificate through the Stage 1/2 lemmas;
plus the `REAL_ARITH[]` tactic wrapper. Capstone test (MUST pass):
`∀a b:real. a < b ⇒ a < (a+b)·realInv(rnum 2)`. Tests appended to
`tests/real_arith_tests.wl`.

## Context pointers

- `CLAUDE.md` (**Conventions**, hygiene rules) first.
- `auto/RealArith.wl` — your base. Directly reusable (same Private context):
  - Stage 1 publics: `rnumAdd/Mul/Le/Lt/NotLe/Pos/Nonneg/Ne`, the
    add-mono family `realLe/Lt…AddMono…Thm`, `realLtIrreflThm`,
    `realNotLeLtThm`, `realLe/LtMulCancelThm`, `realEqIffLeLeThm`,
    `realLe/LtAddCancelThm`.
  - Stage 1/2 privates: `rnumTm`, `natTm`, `rAdd/rMul/rNeg/rLe/rLt`
    appliers, `specAll`, `leCong/ltCong`, rule lifters `leAddMono`,
    `ltAddMono`, `leAddMonoR`, `ltAddMonoR`, `leTrans`, `ltLeTrans`,
    `leLtTrans`, `ltTrans`, `ltImpLe`, `leMulMono`, `ltMulMono`,
    `notLeLtAt`, `realLeSides/realLtSides`; AST `parseLinR` →
    `rLin[const, vars, env]`, `buildLinR`/`buildLinRAny`, `rnumLitQ`/
    `rnumLitValue`; convs `realLinNormConv`, `realAtomNormConv`.
    Check each signature in the source before use.
- `auto/Arith.wl` — the ℕ precedent. READ: `farkasFM` (≈ line 1951–2065,
  FM elimination with certificate tracking), `farkasRefute`, the
  `arithProve` intake (CCONTR/DISCH/GEN management), and the `ARITH[]`
  tactic wrapper at the end of the file. Your Stage 3 mirrors all four —
  over ℝ it is SIMPLER: no implicit `0 ≤ var` retry (ℝ vars are unsigned),
  no integrality concerns; but you must track STRICTNESS through the
  elimination.
- `Tactics.wl` — `goal[asms, concl]`, `tacResult`, `prove` (for the
  tactic wrapper; copy ARITH[]'s pattern).
- Bool toolkit: `GEN SPEC CONJUNCT1/2 MP DISCH UNDISCH NOTINTRO NOTELIM
  CONTR CCONTR EXCLUDEDMIDDLE DISJCASES ASSUME EQMP`. `freshName` is
  Bool-PRIVATE — not available; binder names you SPEC with come from the
  goal itself (see intake below), no fresh names needed.

## Scope

- Files you may MODIFY: `auto/RealArith.wl` (append Stage 3),
  `tests/real_arith_tests.wl` (append). Nothing else; no new files; runners
  already wired. Trust-boundary no-touch list as in briefs 005/006.
  No `newAxiom`.

## Accepted goal language (pin; reject everything else with a throw)

```
goal ::= ∀x:real. goal | imp
imp  ::= hyp ⇒ imp | concl
hyp  ::= atom | ¬atom | hyp ∧ hyp
concl::= atom | ¬atom
atom ::= realLe s t | realLt s t | (s = t)        s,t real-typed linear
```
Linear = whatever `parseLinR`/`realAtomNormConv` accept (opaque-atom
abstraction included — `realAbs u`, `x·y`, … become Farkas variables).
Unsupported shapes throw `holError["realarith-unsupported", <literal
String>, <literal Association>]` — REMEMBER holError is HoldRest: literal
msg/assoc at every call site.

## Deliverable

### Intake — `realArithProve[goalTm]`

1. Strip leading ∀-binders: SPEC each binder's own `var` (name+type taken
   from the goal term — destructure the `∀` like Arith.wl's intake does;
   collect the var list for the final GENs).
2. Split the implication spine into hyps H₁…Hₘ and conclusion C.
3. Build the FACT list (each fact a thm with its own ASSUME hypothesis):
   - from each Hⱼ: ASSUME, then recursively: conjunction → CONJUNCT1/2;
     `realLe`/`realLt` atom → keep; `s = t` (real) → EQMP through
     `realEqIffLeLeThm` instance, CONJUNCT both directions (two facts);
     `¬(realLe s t)` → EQMP through `realNotLeLtThm` instance → `t < s`;
     `¬(realLt s t)` → derive `t ≤ s` by CCONTR: ASSUME `¬(t ≤ s)`,
     `notLeLtAt` → `s < t`, NOTELIM the Hⱼ-fact + MP → F, CCONTR;
     `¬(s = t)` → throw "realarith-unsupported" (disequalities deferred);
     anything else → throw.
   - from the conclusion C, the REFUTATION facts:
     - C = `realLe s t`: fact `t < s` from ASSUME `¬C` via notLeLtAt;
       close at the end with CCONTR[C, F-thm].
     - C = `realLt s t`: fact `t ≤ s` from ASSUME `¬C` by the CCONTR route
       above; close with CCONTR.
     - C = `¬A` (A an atom): add A's facts directly (ASSUME A, expand as a
       hyp would be); close with NOTINTRO[DISCH[A, F-thm]].
     - C = `s = t`: do NOT negate. Run the refutation TWICE: once with the
       facts ∪ {refutation facts for `realLe s t`}, once for `realLe t s`;
       close each with CCONTR, combine with `realLeAntisymThm` (verify its
       exact name/statement in stdlib/Real/Cut.wl) + MP.
4. Normalize every fact: `EQMP[realAtomNormConv[concl[fact]], fact]` →
   canonical atoms `Lᵢ RELᵢ Rᵢ` (nonneg ℕ-coefficient sides).

### Oracle — `farkasFMReal[rows]` (untrusted; mirror Arith.wl `farkasFM`)

Input rows: for each canonical atom, the record
`dᵢ = lin(Rᵢ) − lin(Lᵢ)` (Rational/Integer entries via the rLin records)
plus `strictᵢ` (True for <). The system {dᵢ ≥ 0, strict rows > 0} is
claimed infeasible; find nonneg rational multipliers λᵢ with
`Σ λᵢ·dᵢ = constant record c` where `c < 0`, OR `c ≤ 0` with `λᵢ > 0`
for at least one strict row. FM elimination: pick a variable, combine
each (positive-coefficient row, negative-coefficient row) pair into a new
row (strict = strictA ∨ strictB), carrying the multiplier vector
(start: unit vectors); rows with the variable absent pass through;
repeat until variable-free; scan for a contradictory row. Exact
arithmetic only. Return the multiplier vector over the ORIGINAL rows, or
$Failed → caller throws `holError["realarith-farkas", <literal>, <literal>]`.
Scale the returned λ vector by the LCM of denominators → nat multipliers.

### Verifier — replay the certificate in the kernel

1. For each fact with nat multiplier λᵢ: λᵢ = 0 → drop; λᵢ = 1 → keep;
   λᵢ ≥ 2 → scale: `leMulMono`/`ltMulMono` with `rnumPos[λᵢ]` (check the
   lifter signatures — they take the positivity thm + the atom thm) →
   ⊢ λᵢ·Lᵢ REL λᵢ·Rᵢ.
2. Fold the scaled atoms into one combined inequality with the two-sided
   add-mono family: ≤+≤ → `realLeAddMono2Thm`, <+≤ → `realLtLeAddMonoThm`,
   ≤+< → `realLeLtAddMonoThm`, <+< → `realLtAddMono2Thm` (specAll + MP MP;
   the combined REL is < iff any used row was <).
3. Renormalize: `EQMP[realAtomNormConv[concl[combined]], combined]`. The
   oracle guarantees all variables cancel: the result must be GROUND
   `rnumTm a REL rnumTm b`. If a variable survives, that is an internal
   bug: throw `holError["realarith-internal", <literal>, <literal>]`.
4. Contradiction → F:
   - REL is ≤ and a > b: `rnumNotLe[a, b]`, NOTELIM, MP with the combined
     thm → F.
   - REL is < and a ≥ b: if a == b, `realLtIrreflThm` SPEC'd at rnum a,
     NOTELIM, MP → F; if a > b… cannot happen with a correct certificate,
     but handle uniformly: from combined `rnum a < rnum b` and
     `rnumLe[b, a]` (b ≤ a), `ltLeTrans` → `rnum a < rnum a`, then as
     before.
   (Either polarity of certificate may arrive depending on row signs —
   derive which ground case you actually have from a and b, don't assume.)
5. Close per the conclusion case (CCONTR / NOTINTRO / antisym combine),
   DISCH the original H₁…Hₘ in reverse order, GEN the ∀-vars in reverse.

### Tactic — `REAL_ARITH[]`

Mirror `ARITH[]` at the end of Arith.wl exactly (same goal/tacResult
plumbing, same shape of justification function), calling `realArithProve`
on the goal's conclusion.

### Tests (append to `tests/real_arith_tests.wl`, ~20 asserts)

Each positive case: thm with empty hyps, concl aconv the goal term (build
goal terms with the local builders; `forallTm`/`impTm`/`conjTm`/`notTm`
already exist in the file).
- CAPSTONE: `∀a b. a < b ⇒ a < (a+b)·realInv(rnum 2)`.
- `∀x. x ≤ x`; `∀x y z. x≤y ⇒ y≤z ⇒ x≤z`; `∀x y. x<y ⇒ x≤y`.
- Equality conclusion: `∀x y. x≤y ⇒ y≤x ⇒ x = y`.
- Equality hypothesis: `∀x y. x = y ⇒ x ≤ y`.
- Negated conclusion: `∀x. ¬(x < x)`; `∀x y. x<y ⇒ ¬(y<x)`.
- Negated hypothesis: `∀x y. ¬(x≤y) ⇒ y<x`.
- Conjunction hypothesis: `∀x y. (x≤y ∧ y≤x) ⇒ x = y`.
- Scaling: `∀x. rnum 2·x ≤ rnum 6 ⇒ x ≤ rnum 3`.
- Constants: `rnum 2 < rnum 3` (closed, no binders); `∀x. x + rnum 1 ≤ x + rnum 2`.
- Opaque atoms: `∀x. realAbs x ≤ rnum 1 ⇒ rnum 2·realAbs x ≤ rnum 2`.
- Throws: `∀x y. x ≤ y` → "realarith-farkas" (unprovable);
  `∀x y. ¬(x = y) ⇒ x < y` → "realarith-unsupported";
  a num-typed quantifier → "realarith-unsupported" (or the parser's
  "realarith-norm"; assert whichever tag your code throws, but make it one
  of the realarith-* family).
- Tactic: `prove[capstoneGoal, REAL_ARITH[]]` returns the theorem.

## WL / project pitfalls (read twice)

1. No `_` in identifiers (incl. Module locals); camelCase.
2. WL comments close at the first `*)`.
3. Cross-file Private symbols unreachable (in-file Stage 1/2 privates ARE
   reachable); `freshName` is Bool-private — do not call it.
4. HOL var identity = (name, type); scaffolding binders distinctive.
5. holError is HoldRest — literal String/Association at call sites.
6. `wolframscript -file` (sandbox can't run it anyway).
7. Harness asserts + aconv; no deep MatchQ.
8. mkVar/mkConst/mkComb/mkAbs only.
9. Narrow probes, no term dumps.
10. No `Return` inside Do/For/While.
11. Exact Rational/Integer arithmetic only; `LCM`/`Numerator`/`Denominator`.
12. FM blowup is fine at this scale (≤ ~6 atoms in tests); no optimization.

## Verification

Sandbox cannot run wolframscript: deliver statically-checked code; report
which file:line you verified each reused helper's signature at. Reviewer
runs `tests/dev.wls auto/RealArith.wl real_arith` + cold Strict run_all.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck on scope, STOP and report.
- Stop-loss: same failure twice → STOP and report.
- Minimal diff.

## Report format

1. Per-file changes with line ranges + one-line why.
2. Helper-signature verification table (name → file:line).
3. Any deviation from the pinned pipeline and why.
4. Open questions (empty if none).
