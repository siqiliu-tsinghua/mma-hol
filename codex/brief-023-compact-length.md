# Brief 023 — M8.2 Branch B: interval length + length→0 (append to Real/Compact.wl)

## Goal

Append the *length bookkeeping* of the Heine–Borel proof to
`stdlib/Real/Compact.wl`: define `length U left right n = upper n − lower n`,
prove its recursion (`length 0 = right − left`, `length (SUC n) =
length n · ½`), the closed form `length n = (right − left) · inv(dyadic n)`
(via the multiplicative invariant `dyadic n · length n = right − left`), the
sign/monotonicity facts, and the capstone **`lengthsToZeroThm`**: under
`left ≤ right` and `noFiniteSubcover U left right`, the bisection endpoint
sequences satisfy `intervalLengthsToZero (lower U left right)
(upper U left right)` — i.e. the nested intervals shrink to a point. This is the
input `nestedUniquePointThm` (Seq.wl) consumes in the next brief (Heine–Borel
finish). Append ~8 asserts to `tests/real_compact_tests.wl`. Self-verify with
dev.wls, iterate to green; graded delivery (see Stop-loss).

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealCompactness/ClosedInterval/FromNestedFinite.lean`:
`length` (def, line 298), `length_zero` (303), `length_succ` (309),
`length_formula` (327), `length_tendsto_zero` (354–386). Read those five.
Two deviations from the blueprint, both because our inverse algebra is thinner:

- We do NOT have `inv_one` / `inv_mul` (inv(xy)=inv x·inv y). So prove
  `length_formula` NOT by the blueprint's direct induction, but from the
  **multiplicative invariant** `dyadic n · length n = right − left` (a clean
  induction needing only `realMulInvThm`, `realMulOneThm`, assoc/comm), then
  divide once by `dyadic n` (≠0) to land the closed form.
- Our `intervalOrder`/`lowerMono`/`upperAntitone` (brief-022, this file) all
  carry BOTH hyps `realLe left right` AND `noFiniteSubcover U left right`. So
  our `length_tendsto_zero` analog carries both too (the blueprint needs only
  `h0` — irrelevant for us; in brief-024 both are in scope by contradiction).

## Context pointers

- `CLAUDE.md` (Conventions + **capture hygiene**) first.
- Compact.wl AND SeqAux.wl are BOTH frontier (committed, not in `bootstrap.mx`);
  dev.wls names BOTH. You are appending to the **end of Compact.wl** (before
  `End[]; EndPackage[];`) and adding `::usage` lines in its usage block.
- **In-file (Compact.wl `` `Private` ``, reachable by bare name — VERIFIED):**
  - Endpoint terms: `compactLowerAt[u,left,right,n]` / `compactUpperAt[…]` →
    `lower/upper U left right n`; `lowerTm[u,left,right]`/`upperTm[…]` (the
    `num→real` functions); `lowerConst[]`/`upperConst[]`.
  - Recursion equations (brief-022): `compactLowerZeroEq[u,left,right]`
    (⊢ lower…0 = left), `compactUpperZeroEq[…]` (⊢ upper…0 = right);
    `compactLowerSuccRightEq[u,left,right,n,hTh]` /
    `compactUpperSuccRightEq[…]` (under `hTh : finiteSubcover …`),
    `compactLowerSuccLeftEq[…,hNotTh]` / `compactUpperSuccLeftEq[…]` (under the
    negation). `compactStepCondition[u,left,right,n]` = the COND condition term
    `finiteSubcover U (closedInterval (lower n) (midpoint (lower n)(upper n)))`;
    `compactNotTm[t]` = `¬t`.
  - Order/mono (brief-022): `intervalOrderThm`, `compactIntervalOrderAt[u,left,
    right,hLeTh,hBadTh,n]` (⊢ realLe (lower…n)(upper…n)); `lowerMonoThm`
    (⊢ ∀U l r. l≤r ⇒ noFin ⇒ ∀n m. n≤m ⇒ realLe (lower n)(lower m)),
    `upperAntitoneThm` (… ∀n m. n≤m ⇒ realLe (upper m)(upper n)). (No `…At`
    accessor for mono — build via `SPEC[m, MP[MP[compactSpecAll[lowerMonoThm,
    {u,left,right}], hLe], hBad]]` then `SPEC[n,…]` then `MP` the `N≤n` hyp;
    for "upper n ≤ upper N at N≤n" SPEC the pair (N,n).)
  - Midpoint length facts (brief-021, UNCONDITIONAL): `midpointSubLeftThm`
    ⊢ ∀a b. midpoint a b − a = (b−a)·inv 2; `rightSubMidpointThm`
    ⊢ ∀a b. b − midpoint a b = (b−a)·inv 2. `compactMidpointCong[eqA,eqB]`.
  - Scalars/builders: `compactTwoReal[]` (real 2), `compactHalfScalar[]`
    (= `realInv 2`), `compactRealInv[x]` (= `realInv x`), `realInvConst[]`;
    `realMulTm[x,y]`/`realAddTm[x,y]`/`realNegTm[x]` (folder builders),
    `zeroRealTm[]` (real 0), `compactNatLe[a,b]` (= `a ≤ b` on num).
  - Combinators: `compactSpecAll[th,{…}]` (fold SPEC), `compactTransList[{…}]`
    (fold TRANS), `compactRealLeCong[eqL,eqR]`, `compactRealLtCong[eqL,eqR]`,
    `compactBetaClean[th]`; `compactCoverTy` (U's type `iota→real→bool`),
    `compactRealPairTy`. numInduction idiom: `compactBetaClean[SPEC[pLam,
    HOL\`Stdlib\`Num\`numInductionThm]]` (see lowerMonoThm line ~2168).
  - `HOL\`Auto\`RealArith\`realArithProve[goalTm]` — **LINEAR over opaque
    atoms** (`length…n`, `lower…n`, `upper…n`, `dyadic n` are all opaque).
- **Snapshot-available (Seq.wl/SeqAux.wl/Inv/Mul/Abs/Complete — VERIFIED):**
  - SeqAux: `dyadicTm[n]`, `dyadicZeroThm` (⊢ dyadic 0 = 1), `dyadicSuccThm`
    (⊢ ∀n. dyadic(SUC n) = realMul (dyadic n) 2), `dyadicNeZeroThm`
    (⊢ ∀n. ¬(dyadic n = 0)), **`dyadicArchThm`** (⊢ ∀L eps. realLe 0 L ⇒
    realLt 0 eps ⇒ ∃n. realLt (realMul L (realInv (dyadic n))) eps).
  - Inv: `realMulInvThm` ⊢ ∀x. ¬(x = 0) ⇒ realMul x (realInv x) = 1
    (the `1` is `&ℝ(&ℚ(&ℤ(SUC 0)))`). Mul: `realMulOneThm` ⊢ ∀x. realMul x 1 = x
    (same `1`), `realMulCommThm`, `realMulAssocThm`
    (⊢ realMul (realMul x y) z = realMul x (realMul y z)). Abs:
    `realAbsPosThm` ⊢ ∀x. realLe 0 x ⇒ realAbs x = x, `realAbsConst[]`.
    Complete: `realLeLtTransThm` ⊢ ∀x y z. x≤y ⇒ y<z ⇒ x<z.
    Seq: `seqArithPosNeZeroThm` ⊢ ∀x. realLt 0 x ⇒ ¬(x = 0) (PUBLIC — use it
    with `realArithProve[realLt 0 2]` to get `¬(2 = 0)` for `realMulInvThm`).
  - Seq: `tendstoTm[a,L]`, `unfoldTendsto[a,L]` (⊢ tendsto a L = ∀e. 0<e ⇒
    ∃N. ∀n. N≤n ⇒ realAbs (a n + realNeg L) < e); `intervalLengthsToZeroTm[a,b]`,
    `unfoldIntervalLengthsToZero[a,b]` (⊢ intervalLengthsToZero a b =
    tendsto (λn. realAdd (b n) (realNeg (a n))) 0). `realLeReflThm`.
    `HOL\`Stdlib\`Num\`numInductionThm`.

## Scope

- MODIFY: `stdlib/Real/Compact.wl` (append theorems + `::usage` lines),
  `tests/real_compact_tests.wl` (append asserts). No other files, no runner
  lists. MUST NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/docs/SeqAux.wl/
  Seq.wl/codex(except your report). No newAxiom. No new files.

## Definitions (pin)

```
lengthDefThm: ⊢ length = (λU left right n.
    realAdd (upper U left right n) (realNeg (lower U left right n)))
  -- length type: compactCoverTy → real → real → num → real.
```
Export `lengthConst[]`/`lengthTm[u,left,right]`/`unfoldLength[u,left,right,n]`
(the deep-β-reduced def at all four args — APTHM the def 4× then β; use
`compactBetaClean`) + `compactLengthAt[u,left,right,n]` (= `mkComb[lengthTm[…],
n]`). **Pick the body order `upper − lower` (= `realAdd upper (realNeg lower)`)
so that `length U left right` is α-identical to the lambda in
`unfoldIntervalLengthsToZero[lower…, upper…]` (b−a with a:=lower, b:=upper).**

## Deliverable theorems (mirror the blueprint)

1. `lengthZeroThm` ⊢ ∀U left right.
   length U left right 0 = realAdd right (realNeg left).
   (unfoldLength at 0 → `realAdd (upper…0)(realNeg(lower…0))`; rewrite with
   `compactUpperZeroEq`/`compactLowerZeroEq` via `compactRealAddCong`-style
   congruence — build `MKCOMB[APTERM[realAddConst[], upperEq], APTERM[realNegConst[],
   lowerEq]]` if no add-cong helper exists, or two TRANS steps.)

2. `lengthSuccThm` ⊢ ∀U left right n.
   length U left right (SUC n) = realMul (length U left right n) (realInv 2).
   **UNCONDITIONAL** (no left≤right / noFin needed). Mirror `lowerStepLeThm`'s
   EXCLUDEDMIDDLE on `compactStepCondition`:
   - unfoldLength at SUC n → `realAdd (upper…(SUC n))(realNeg(lower…(SUC n)))`.
   - TRUE branch (`hTh = ASSUME condTm`): `compactUpperSuccRightEq` (upper(SUC)=
     upper n) + `compactLowerSuccRightEq` (lower(SUC)=midpoint(lower n,upper n));
     so length(SUC) = `upper n − midpoint(lower n)(upper n)` = `rightSubMidpointThm`
     SPEC (lower n, upper n) = `(upper n − lower n)·inv 2` = `realMul (length n)
     (realInv 2)` (the last `=` is unfoldLength at n, SYM, under `compactRealMulCongLeft`).
   - FALSE branch (`hNot = ASSUME ¬condTm`): `compactLowerSuccLeftEq`/
     `compactUpperSuccLeftEq`; length(SUC) = `midpoint(lower n)(upper n) − lower n`
     = `midpointSubLeftThm` SPEC = same `(upper n − lower n)·inv 2`.
   - DISJCASES (both branches conclude the same RHS).

3. `lengthInvariantThm` ⊢ ∀U left right n.
   realMul (dyadic n) (length U left right n) = realAdd right (realNeg left).
   numInduction on n (`pLam` idiom):
   - base (n:=0): LHS = `realMul (dyadic 0)(length…0)` = `realMul 1 (right−left)`
     (dyadicZeroThm + lengthZeroThm) = `right − left` (need `1·x = x`: comm then
     `realMulOneThm`).
   - succ: LHS = `realMul (dyadic(SUC n))(length(SUC n))` = `realMul (realMul
     (dyadic n) 2)(realMul (length n)(inv 2))` (dyadicSuccThm + lengthSuccThm,
     congruence). Rearrange `(a·2)·(c·inv2) → (a·c)·(2·inv2)` (a:=dyadic n,
     c:=length n) by assoc/comm; `2·inv 2 = 1` (realMulInvThm SPEC `compactTwoReal[]`,
     MP `¬(2=0)` from `MP[SPEC[compactTwoReal[], seqArithPosNeZeroThm],
     realArithProve[realLt 0 2-term]]`); `X·1 = X` (realMulOneThm); = `right−left`
     by IH. **The 4-factor rearrange is the one fiddly step** — recommended: prove
     a local `∀a b c d. realMul (realMul a b)(realMul c d) = realMul (realMul a c)
     (realMul b d)` once (TRANS chain of realMulAssocThm/realMulCommThm congruences)
     and SPEC it; OR do the explicit assoc/comm chain inline. realArithProve CANNOT
     do this (nonlinear).

4. `lengthFormulaThm` ⊢ ∀U left right n.
   length U left right n = realMul (realAdd right (realNeg left)) (realInv (dyadic n)).
   From `lengthInvariantThm` (call it `inv-eq`: `dyadic n · length n = L`,
   L := right−left) and `dyadicNeZeroThm` (dyadic n ≠ 0):
   - left-multiply inv-eq by `realInv (dyadic n)`:
     `inv(dyadic n)·(dyadic n·length n) = inv(dyadic n)·L`.
   - LHS = `(inv(dyadic n)·dyadic n)·length n` (assoc, SYM) = `1·length n`
     (`realMulInvThm` SPEC `dyadic n` MP `dyadicNeZeroThm` gives
     `dyadic n·inv(dyadic n)=1`; comm → `inv·dyadic = 1`) = `length n`
     (comm + realMulOneThm).
   - RHS = `inv(dyadic n)·L` = `L·inv(dyadic n)` (comm). So length n = L·inv(dyadic n).

5. `lengthNonnegThm` ⊢ ∀U left right. realLe left right ⇒
   noFiniteSubcover U left right ⇒ ∀n. realLe (zeroRealTm[]) (length U left right n).
   `compactIntervalOrderAt` gives `realLe (lower…n)(upper…n)`; `realArithProve`
   on the goal `realLe 0 (realAdd (upper…n)(realNeg(lower…n)))` from that hyp
   (linear, lower/upper opaque); rewrite the abstracted sum to `length…n` via
   `unfoldLength` SYM under `compactRealLeCong`.

6. `lengthDecreaseThm` ⊢ ∀U left right. realLe left right ⇒
   noFiniteSubcover U left right ⇒ ∀N n. compactNatLe N n ⇒
   realLe (length U left right n) (length U left right N).
   From `upperAntitoneThm` SPEC (N,n) MP (N≤n): `realLe (upper…n)(upper…N)`; from
   `lowerMonoThm` SPEC (N,n) MP (N≤n): `realLe (lower…N)(lower…n)`. `realArithProve`:
   those two ⇒ `realLe (upper…n − lower…n)(upper…N − lower…N)` (linear). Rewrite
   both subtractions to `length` via `unfoldLength` SYM (under `compactRealLeCong`).

7. `lengthsToZeroThm` ⊢ ∀U left right. realLe left right ⇒
   noFiniteSubcover U left right ⇒
   intervalLengthsToZero (lower U left right) (upper U left right).
   Internal lemma first — prove `tendsto (lengthTm[u,left,right]) (zeroRealTm[])`
   under the two hyps, then bridge. Structure (unfoldTendsto skeleton):
   - SYM `unfoldTendsto[lengthTm[…], 0]`; build its body
     `∀e. 0<e ⇒ ∃N. ∀n. N≤n ⇒ realAbs ((length…) n + realNeg 0) < e`.
   - GEN e, DISCH `realLt 0 e`. `L := realAdd right (realNeg left)`. `0 ≤ L` from
     `left≤right` via `realArithProve`. `dyadicArchThm` SPEC (L, e), MP `0≤L`, MP
     `0<e` → `∃N. realMul L (realInv (dyadic N)) < e`. CHOOSE N (fresh witness
     name, e.g. `bigN`), hyp `hN : realMul L (realInv (dyadic N)) < e`.
   - EXISTS N; GEN n, DISCH `N ≤ n` (`compactNatLe[bigN, nV]`). Then:
     - `lengthFormulaThm` SPEC (…,N): `length N = L·inv(dyadic N)`; EQMP into hN
       (via `compactRealLtCong[SYM that, REFL e]`) → `lenNlt : length N < e`.
     - `lengthDecreaseThm` MP'd at (N,n) with the `N≤n` hyp → `length n ≤ length N`.
     - `realLeLtTransThm` → `lenNlt'` : `length n < e`.
     - `lengthNonnegThm` MP'd at n → `0 ≤ length n`. `realAbsPosThm` SPEC
       `length…n` MP that → `realAbs (length…n) = length…n`.
     - `realArithProve`: `realAdd (length…n)(realNeg 0) = length…n` (linear).
       TRANS with the abs-eq (under `APTERM[realAbsConst[], …]`) →
       `realAbs (length…n + realNeg 0) = length…n`. EQMP[compactRealLtCong[SYM
       that, REFL e], lenNlt'] → `realAbs (length…n + realNeg 0) < e`.
   - Package: GEN n / DISCH / GEN e / DISCH → tendsto body; EQMP SYM unfoldTendsto
     → `tendsto (length…) 0`.
   - **Bridge to intervalLengthsToZero:** `unfoldLength`-partial gives
     `lenFunEq : length U left right = (λn. realAdd (upper…n)(realNeg(lower…n)))`
     (APTHM lengthDefThm 3× at U,left,right + β — NOT applied to n). EQMP
     `[MKCOMB[APTERM[tendstoConst[], lenFunEq], REFL[0]] , tendsto (length…) 0]`
     → `tendsto (λn…) 0`. Then `EQMP[SYM unfoldIntervalLengthsToZero[lowerTm[…],
     upperTm[…]], that]` → `intervalLengthsToZero (lower…)(upper…)`. (The λ in
     unfoldIntervalLengthsToZero is `λn. realAdd ((upper…) n)(realNeg((lower…) n))`,
     α-identical to lenFunEq's RHS by the body-order choice in the def — VERIFY
     with `aconv` if EQMP rejects.) GEN U/left/right + DISCH both hyps.

## Stop-loss / graded delivery

Tier 1 (must): `length` def/const/tm/unfold + accessor; (1) lengthZero; (2)
lengthSucc. Tier 2: (3) invariant; (4) formula; (5) nonneg; (6) decrease. Tier 3:
(7) lengthsToZero capstone. If a tier stalls (same failure twice), deliver the
green lower tiers and STOP with a precise report (which theorem, the exact thrown
payload). A loadable subset is fully acceptable — do NOT thrash. The most likely
sticking points: the 4-factor mul rearrange in (3), and the tendsto/length
α-bridge in (7) — if (7)'s bridge fights `aconv`, deliver through (6) + the
internal `tendsto (length…) 0` lemma and report the bridge mismatch.

## Tests (append ~8 asserts to tests/real_compact_tests.wl)

- `lengthZeroThm`/`lengthSuccThm` concl shape at fresh U,left,right(,n) (aconv
  against built expected terms; SPEC then compare).
- `lengthInvariantThm`/`lengthFormulaThm` concl shape (aconv).
- `lengthNonnegThm`/`lengthDecreaseThm` concl shape (after the two DISCHes; check
  the ∀-body or just `isThm` + a shallow head/slot probe).
- `lengthsToZeroThm` concl shape: `intervalLengthsToZero (lower U left right)
  (upper U left right)` under the two hyps (after GEN/DISCH, hyps empty; aconv
  the conclusion against `intervalLengthsToZeroTm[lowerTm[…], upperTm[…]]`).
- aconv against folder builders; no deep `MatchQ`. **NO `testExit[]`** — end the
  file with the last `runTests[...]`, nothing after.

## WL / project pitfalls (read twice)

1. No `_` in idents (Module locals too). 2. WL comments close at first `*)`. 3.
In-file Compact privates + snapshot publics reachable; a wrong-context symbol
stays UNEVALUATED → fails far below. 4. **HOL var identity = (name,type)** —
GEN binders canonical (U/left/right/n); CHOOSE the dyadicArch witness with a
DISTINCTIVE name (`bigN`, not `n`/`N`) so it can't collide with the GEN'd `n`.
5. holError HoldRest. 6. dev.wls verifier (below). 7. aconv tests, no deep
MatchQ, **no testExit**. 8. mkVar/mkConst/mkComb/mkAbs only. 9. **Narrow probes**
— Compact.wl is load-heavy; localize a load throw by per-theorem `isThm`, do NOT
dump terms. 10. No Return in Do/For/While. 11. **realArithProve is LINEAR** —
use it ONLY for: `0≤L`, the sub-monotonicity in (6), `0≤length n`, the
`x+(−0)=x` identity, and `realLt 0 2`. The nonlinear mul rearranges (3)(4) are
hand assoc/comm; the abs step is realAbsPosThm. 12. **`1` is one term** —
`realMulInvThm`/`realMulOneThm` both use `&ℝ(&ℚ(&ℤ(SUC 0)))`; they compose
directly, no renormalize. 13. **Pin body order** `upper − lower` in the def so
(7)'s bridge α-matches `unfoldIntervalLengthsToZero` (b−a, a:=lower, b:=upper).
14. The succ equations need the COND hyp `hTh`/`hNot`; EXCLUDEDMIDDLE on
`compactStepCondition` supplies both (mirror `lowerStepLeThm` exactly).

## Verification (MANDATORY — you run wolframscript)

Full machine access. Both frontier files named (dependency order) or dev.wls
hits its staleness guard:

```
wolframscript -file tests/dev.wls stdlib/Real/SeqAux.wl stdlib/Real/Compact.wl real_compact
```

Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste
the final `passed: N  failed: 0` line into your report verbatim. Do NOT run
build_snapshot/extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all,
no other command, nothing outside the repo, no network. Same failure twice →
deliver the loadable subset (per the tiers) + report exactly where it broke. If
dev.wls reports a stale snapshot for some OTHER file, STOP and report (do not
rebuild).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls
  verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. How you proved the multiplicative invariant succ step (the 4-factor rearrange)
   and how the (7) length↔intervalLengthsToZero α-bridge resolved.
4. The exact final `passed: N  failed: 0` from your dev.wls run.
5. Which theorems (by tier) fully proven vs stopped.
6. Open questions (empty if none).
