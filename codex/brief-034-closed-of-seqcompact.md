# Brief 034 — M8.5 列紧⇒闭 + 列紧⟺有界闭 packaging (append to Real/CompactSet.wl)

## Goal

Finish the SEQUENTIAL side of compactness for real sets. Append to `Real/CompactSet.wl`:
the "no-compl-neighborhood ⇒ S meets every interval" helper, the `nearClosedPoint`
ε-sequence (Hilbert-select, indexed by S and x), its `_mem`/`_interval`/`_tendsto`
spec lemmas, the capstone **`closedOfSequentiallyCompactThm`** (`isSequentiallyCompact S
⇒ isClosed S`), and the 3-direction packaging **`sequentialCompactIffClosedBoundedThm`**
(`isSequentiallyCompact S = (isClosed S ∧ setBounded S)`). This closes 列紧⟺有界闭.
Append ~4 asserts to `tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate
to green.

## Blueprint (in-repo)

`tautology-ref/Tautology/RealCompactness/SequentialCompactness.lean`:
`exists_mem_interval_of_no_compl_neighborhood` (266) / `nearClosedPoint` (302) /
`nearClosedPoint_mem` (319) / `nearClosedPoint_interval` (337) / `nearClosedPoint_tendsto`
(358) / `closed_of_sequentiallyCompact` (387) / `sequentialCompact_iff_closed_bounded`
(422). The `hinvNat.small_inv_succ` step is played by our **`invSuccRadiusTendstoZeroThm`**
(brief-033, in this file); `seqTendsto_unique` = our `tendstoUniqueThm`; `abs_sub_lt_of_bounds`
= our `realAbsSubLtThm`.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- CompactSet.wl is FRONTIER. Frontier files: Connected.wl, Topology.wl, CompactSet.wl —
  dev.wls names ALL THREE (that order). Append to the END of CompactSet.wl (before
  `End[]; EndPackage[];`) + `::usage` lines at the top with the other usages.
- **The whole brief is a re-skin of code ALREADY IN THIS FILE — lean on it heavily:**
  - `existsOutsideOfNotSetBoundedThm` (lines 256–313): the EXACT template for theorem (1)
    (EM-on-goal → false-branch builds the negated hypothesis → CCONTR).
  - `unboundedEscapePointDefThm`/`Const`/`Tm`/`unfold` + `unboundedEscapePointMemThm`
    (355–404): the EXACT template for `nearClosedPoint` def + the `_mem`/`_interval` select
    specs (`selectOfExists` → `CONJUNCT1`/`CONJUNCT2` → rewrite select-arg to the unfolded
    app via `appEq`). `_interval` mirrors `unboundedEscapePointOutsideThm`'s `outLam`+APTERM
    rewrite of the SECOND conjunct.
  - `invSuccRadiusTendstoZeroThm` (714–767): the template for `nearClosedPointTendstoThm`'s
    tendsto-fold + the abs cleanup `|z + (−0)| = z`. **`csetAddNegZeroThm`** (554, in this
    file, ⊢ ∀z. realAdd z (realNeg (&ℝ0)) = z) is reusable verbatim for that cleanup.
  - `sequentiallyCompactOfClosedBoundedThm` (158–198): the CHOOSE-l / CHOOSE-phi / unfold-
    hasConvergentSubseq plumbing for the main theorem's seq-compact-elimination half.
  - `limitMemOfClosedThm` (Topology.wl 421–484): the reverse direction; reuse its
    `complMem`-fold idiom and isOpen-body shape (we BUILD that body here, it CONSUMES it).
- LCF-style: you cannot make a false theorem; the test suite decides. Acceptance is mechanical.

## Reuse (VERIFIED — snapshot + this file + frontier Topology.wl)

- **This file (reachable by bare public name; the rest are file-Private helpers — REUSE the
  helper names directly, they are in the same `` `Private` `` block you are appending to):**
  `csetRnumNat[n]` (=&ℝ(&ℚ(&ℤ n))), `csetRealLt`/`csetRealLe`/`csetRealNeg`/`csetRealAbs`,
  `csetConjTm`/`csetImpTm`/`csetForallTm`/`csetExistsTm`/`csetOrTm`/`csetNotTm`,
  `csetSetApp`/`csetSeqApp`, `csetSpecAll`/`csetApplyDef`/`csetBetaClean`/`csetForallList`,
  `csetSelectConst[ty]`, `csetSubsequenceAppEq`, `csetRealLtCong`/`csetRealLeCong`,
  `csetSeqLimitAtom[a,l,e,n]` (=realAbs (a n + −l) < e), `csetRealAddCongLeft`,
  `csetRealAbsCong`, `csetLtImpLeRule`. Public: `isSequentiallyCompactTm[S]`/
  `unfoldIsSequentiallyCompact[S]`, `unboundedEscapePoint*`, `seqTendstoSubsequenceThm`,
  `invSuccRadiusTm[n]`/`invSuccRadiusConst[]`/`unfoldInvSuccRadius[n]`/`invSuccRadiusPosThm`/
  `invSuccRadiusTendstoZeroThm`, `boundedOfSequentiallyCompactThm`,
  `sequentiallyCompactOfClosedBoundedThm`, `csetAddNegZeroThm` (file-private but in-block).
- **Topology.wl (frontier, loaded before this; PUBLIC):** `complConst[]`/`complTm[S]`/
  `complMemThm` (⊢ ∀S x. compl S x = ¬(S x)), `isClosedTm[S]`/`unfoldIsClosed[S]`
  (⊢ isClosed S = isOpen (compl S)).
- **Compact.wl (snapshot, PUBLIC):** `isOpenTm[U]`/`unfoldIsOpen[U]` — the isOpen body is
  `∀x. U x ⇒ ∃left right. realLt left x ∧ (realLt x right ∧ ∀y. openInterval left right y ⇒
  U y)` (this is the structure `csetNeighGoal` below must mirror EXACTLY);
  `openIntervalTm[a,b,y]`/`unfoldOpenInterval[a,b,y]` (⊢ openInterval a b y = (a<y ∧ y<b));
  `setBoundedTm[S]`.
- **Seq.wl (snapshot, PUBLIC):** `tendstoTm[u,l]`/`unfoldTendsto[u,l]`; `hasConvergentSubseqTm
  [u,l]`/`unfoldHasConvergentSubseq[u,l]`; `subsequenceTm[u,phi]`; `subseqIndexTm[phi]`/
  `subseqIndexGeSelfThm`; **`tendstoUniqueThm`** ⊢ ∀a L1 L2. tendsto a L1 ⇒ tendsto a L2 ⇒
  L1 = L2; **`realAbsSubLtThm`** ⊢ ∀x a e. realLt (a + −e) x ⇒ realLt x (a + e) ⇒
  realLt (realAbs (x + −a)) e.
- **Abs/Mul/Complete (snapshot, PUBLIC):** `realAbsPosThm` ⊢ ∀x. realLe 0 x ⇒ realAbs x = x;
  `realLtImpLeThm`, `realLtTransThm`; `realArithProve` (LINEAR — for the x±r bounds and
  z+(−0)=z); `realLtConst`/`realLeConst`/`realNegConst`/`realAbsConst`/`realAddConst`/
  `realOfRatConst`, `zeroRealTm[]`.
- **Num (snapshot, PUBLIC):** `HOL`Stdlib`Num`selectOfExists[predLam, exThm]` (spec at the
  @-term); `leqReflThm` if needed. **Kernel:** `DEDUCTANTISYM` (for the iff, see (7)).

## Scope

- MODIFY: `stdlib/Real/CompactSet.wl` (append + `::usage`),
  `tests/real_compactset_tests.wl` (append). No other files, NO runner lists. MUST NOT touch
  Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/Topology/docs/
  codex(except your report). No newAxiom, no new files.

## Deliverable theorems (append in this order)

Let **`csetNeighGoal[sT, xT]`** be a NEW file-private builder producing EXACTLY the isOpen
body of `compl S` at `x` (mirror `compactIsOpenBody`; use distinctive binders, e.g.
`aNbhd`/`bNbhd`/`yNbhd`):
```
∃a b. realLt a x ∧ (realLt x b ∧ ∀y. openInterval a b y ⇒ compl S y)
```
(nesting: `csetExistsTm[a, csetExistsTm[b, csetConjTm[csetRealLt[a,x],
csetConjTm[csetRealLt[x,b], csetForallTm[y, csetImpTm[openIntervalTm[a,b,y],
csetSetApp[complTm[sT], y]]]]]]]`). It must aconv `concl[unfoldIsOpen[complTm[S]]][[2]]`
applied/β-reduced at x — if a late EQMP rejects it on aconv, EXTRACT the body instead:
`bodyLam = concl[unfoldIsOpen[complTm[S]]][[2,1]]`; `impAtX = BETACONV[mkComb[bodyLam, xV]]`;
`csetNeighGoal := concl[impAtX][[2,2]]`.

1. **`existsMemIntervalOfNoComplNeighborhoodThm`**
   ⊢ ∀S x left right. ¬(csetNeighGoal S x) ⇒ realLt left x ⇒ realLt x right ⇒
   ∃y. S y ∧ openInterval left right y.
   (Template: `existsOutsideOfNotSetBoundedThm`. GEN S x left right; DISCH hno, hleft, hright.
   Goal `G = ∃y. S y ∧ openInterval left right y`. `DISCHCASES`/EM on G: true → ASSUME G.
   false (hNoG = ¬G): for a fresh `zNbhd`, ASSUME `openInterval left right z` (hInt) and
   ASSUME `S z` (hSz); EXISTS `CONJ[hSz, hInt]` into G; MP NOTELIM hNoG → False; so
   `¬(S z)`; fold to `compl S z` via SYM `complMem[S,z]` EQMP; DISCH hInt; GEN z → the
   `∀y. openInterval left right y ⇒ compl S y` conjunct. CONJ[hleft, CONJ[hright, allZ]];
   EXISTS twice (b:=right, a:=left) into `csetNeighGoal S x`; MP NOTELIM hno → False;
   CCONTR G.)

2. **`nearClosedPointDefThm`** ⊢ nearClosedPoint = (λS x n.
   @y. S y ∧ openInterval (x + −(invSuccRadius n)) (x + invSuccRadius n) y).
   Type `(real→bool) → real → num → real`. Export `nearClosedPointConst[]`,
   `nearClosedPointTm[S,x]` (= mkComb[mkComb[const,S],x], a num→real seq),
   `unfoldNearClosedPoint[S,x]` (csetApplyDef on {S,x}, then it is still a λn — keep it as
   the 2-arg unfold like `unfoldUnboundedEscapePoint`), and an app-eq helper
   `csetNearClosedPointAppEq[S,x,n]` (APTHM at n + BETACONV + csetBetaClean) ⊢
   nearClosedPoint S x n = @y. ... . (Template: `unboundedEscapePointDefThm` +
   `unfoldUnboundedEscapePoint` + `csetUnboundedEscapePointAppEq`.) Define the select
   predicate via a `csetNearPred[S,x,n] = mkAbs[yW, csetConjTm[csetSetApp[S,yW],
   openIntervalTm[lo, hi, yW]]]` builder with `lo = realAdd x (realNeg (invSuccRadiusTm n))`,
   `hi = realAdd x (invSuccRadiusTm n)`, distinctive `yW = mkVar["yCsetNear", realTy]`.

3. **`nearClosedPointMemThm`** ⊢ ∀S x. ¬(csetNeighGoal S x) ⇒
   ∀n. S (nearClosedPoint S x n).
   (Template: `unboundedEscapePointMemThm`. GEN S x; DISCH hno; GEN n. Build the two interval
   bounds `realLt lo x` and `realLt x hi` from `invSuccRadiusPosThm SPEC n` via
   `realArithProve`-helpers `∀x r. 0<r ⇒ realLt (realAdd x (realNeg r)) x` and `∀x r. 0<r ⇒
   realLt x (realAdd x r)` (build these once as small file-private thms, SPEC+MP). `exMem =
   existsMemIntervalOfNoComplNeighborhood SPEC {S,x,lo,hi}, MP hno, MP loBound, MP hiBound`
   → `∃y. S y ∧ openInterval lo hi y`. `sat = csetBetaClean[selectOfExists[csetNearPred[S,x,n],
   exMem]]`; `CONJUNCT1[sat]` = S (@y...); rewrite @ → nearClosedPoint S x n via APTERM[S,
   SYM appEq] EQMP.)

4. **`nearClosedPointIntervalThm`** ⊢ ∀S x. ¬(csetNeighGoal S x) ⇒
   ∀n. openInterval (x + −(invSuccRadius n)) (x + invSuccRadius n) (nearClosedPoint S x n).
   (Same scaffold as (3) but `CONJUNCT2[sat]` = openInterval lo hi (@y...); rewrite the
   THIRD arg @ → nearClosedPoint S x n via `intLam = mkAbs[wW, openIntervalTm[lo, hi, wW]]`,
   `csetBetaClean[APTERM[intLam, SYM appEq]]` EQMP — mirror `unboundedEscapePointOutsideThm`'s
   `outLam`.)

5. **`nearClosedPointTendstoThm`** ⊢ ∀S x. ¬(csetNeighGoal S x) ⇒
   tendsto (nearClosedPoint S x) x.
   (GEN S x; DISCH hno. Let `u = nearClosedPointTm[S,x]`. unfold goal `tendsto u x`; GEN e,
   DISCH 0<e. From `invSuccRadiusTendstoZeroThm` UNFOLDED (= ∀e. 0<e ⇒ ∃N. ∀n. N≤n ⇒
   realAbs (invSuccRadius n + −(&ℝ0)) < e): SPEC e, MP 0<e → ∃N…; CHOOSE N (distinctive
   `bigN`); EXISTS same N; GEN n, DISCH N≤n.
   - `hRadiusAbs = hN SPEC n MP (N≤n)` → realAbs (invSuccRadius n + −0) < e. Clean to
     `rLtE : invSuccRadius n < e`: `csetAddNegZeroThm SPEC (invSuccRadius n)` (z+(−0)=z) →
     APTERM realAbsConst → realAbs(invSuccRadius n); `invSuccRadiusPosThm SPEC n` →
     `csetLtImpLeRule` → realLe 0 (invSuccRadius n) → `realAbsPosThm MP` → realAbs(invSuccRadius
     n)=invSuccRadius n; EQMP the chained abs-eq (LtCong) into hRadiusAbs.
   - `hInt = nearClosedPointIntervalThm SPEC {S,x} MP hno SPEC n` → openInterval lo hi (u n);
     `unfoldOpenInterval[lo,hi, u n]` EQMP → `lo<u n ∧ u n<hi`; CONJUNCT1/2.
   - `absLtR = realAbsSubLtThm SPEC {u n, x, invSuccRadius n} MP loBound MP hiBound` →
     realAbs (u n + −x) < invSuccRadius n.   [lemma slots: x:=u n, a:=x, e:=invSuccRadius n]
   - `realLtTransThm SPEC {realAbs(u n + −x), invSuccRadius n, e} MP absLtR MP rLtE` →
     realAbs (u n + −x) < e = `csetSeqLimitAtom[u, x, e, n]` body. Fold tendsto.)

6. **`closedOfSequentiallyCompactThm`** ⊢ ∀S. isSequentiallyCompact S ⇒ isClosed S.
   (GEN S; DISCH `hSC = isSequentiallyCompact S`. Build inner
   `openAll : ⊢ ∀x. compl S x ⇒ csetNeighGoal S x`:
   - GEN x; DISCH `hComplX = compl S x`; `hNotSx = complMem[S,x] EQMP hComplX` → ¬(S x).
   - EM on `csetNeighGoal S x`; DISJCASES:
     - true: ASSUME(csetNeighGoal S x) — IS the body.
     - false: `hno = ¬(csetNeighGoal S x)`. `u = nearClosedPointTm[S,x]`.
       `huS = nearClosedPointMemThm SPEC {S,x} MP hno` → ∀n. S(u n).
       `huTend = nearClosedPointTendstoThm SPEC {S,x} MP hno` → tendsto u x.
       `openSC = unfoldIsSequentiallyCompact[S] EQMP hSC`; `seqEx = openSC SPEC u MP huS`
       → ∃l. S l ∧ hasConvergentSubseq u l. CHOOSE l (distinctive `lClosed`); hL.
       `hLS = CONJUNCT1 hL`; `hHas = CONJUNCT2 hL`; `openHas = unfoldHasConvergentSubseq[u,l]
       EQMP hHas`; CHOOSE phi (distinctive `phiClosed`); `hIdx`/`hTend` from CONJUNCT1/2.
       `subTendX = seqTendstoSubsequenceThm SPEC {u,phi,x} MP hIdx MP huTend` →
       tendsto (subsequence u phi) x. `lEqX = tendstoUniqueThm SPEC {subsequence u phi, l, x}
       MP hTend MP subTendX` → l = x. `hSx = APTERM[S, lEqX] EQMP hLS` → S x.
       `false = NOTELIM hNotSx MP hSx`. `CONTR (csetNeighGoal S x) false`. CHOOSE-discharge
       phi, l.
   - `openCompl = SYM unfoldIsOpen[complTm[S]] EQMP openAll` → isOpen (compl S);
     `closed = SYM unfoldIsClosed[S] EQMP openCompl` → isClosed S. GEN S, DISCH hSC.)

7. **`sequentialCompactIffClosedBoundedThm`**
   ⊢ ∀S. isSequentiallyCompact S = (isClosed S ∧ setBounded S).
   (GEN S. `hSC = ASSUME(isSequentiallyCompact S)`; `closedBoundedFromSC = CONJ[
   closedOfSequentiallyCompactThm SPEC S MP hSC, boundedOfSequentiallyCompactThm SPEC S MP
   hSC]` (hyp = isSequentiallyCompact S). `hCB = ASSUME(isClosed S ∧ setBounded S)`;
   `scFromCB = sequentiallyCompactOfClosedBoundedThm SPEC S MP CONJUNCT1 hCB MP CONJUNCT2 hCB`
   (hyp = the conjunction). `eq = DEDUCTANTISYM[scFromCB, closedBoundedFromSC]` →
   ⊢ isSequentiallyCompact S = (isClosed S ∧ setBounded S) (hyps cancel — first arg's concl is
   the LHS; mirror `connectedIffIntervalSetThm`, Connected.wl 1374). GEN S.)

## Stop-loss / graded delivery

Tier 1: (1)(2)(3)(4) — the helper + nearClosedPoint def + mem + interval (pure re-skin of the
unboundedEscapePoint family). Tier 2: (5) nearClosedPointTendsto (the squeeze + abs cleanup).
Tier 3: (6) closedOfSequentiallyCompact (the capstone). Tier 4: (7) the iff (trivial once (6)
lands). If a tier stalls (same failure twice — most likely the `csetNeighGoal` aconv vs
unfoldIsOpen in (6), or the abs cleanup in (5)), deliver the green tiers with the rest omitted
and STOP with a precise report (which sub-goal, exact payload, the two terms compared by
aconv). Never fake a green count.

## Tests (append ~4 asserts)

- `nearClosedPointMem`/`nearClosedPointTendsto`: their concls embed `csetNeighGoal` — do NOT
  rebuild it; assert `isThm`, `hyp == {}`, and a SHALLOW probe (`Head[concl] === <∀ const>`,
  or `concl[th][[1]]` is the `isSequentiallyCompact`/expected head). NO deep MatchQ.
- `closedOfSequentiallyCompact`: aconv on built expected
  `forallRCST[S, impRCST[isSequentiallyCompactTm[S], isClosedTm[S]]]`.
- `sequentialCompactIffClosedBounded`: aconv on built
  `forallRCST[S, mkEq[isSequentiallyCompactTm[S], andRCST[isClosedTm[S], setBoundedTm[S]]]]`.
  (`isClosedTm`/`setBoundedTm` are public.) **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. Private-context symbols don't cross
   files — BUT you are appending INSIDE CompactSet.wl's `` `Private` `` block, so every
   `cset*` helper above IS reachable by bare name; only cross-file Topology/Compact/Seq
   symbols must be PUBLIC (all the ones listed are). New PUBLIC names are FREE (grep to
   confirm): `existsMemIntervalOfNoComplNeighborhood`, `nearClosedPoint*`,
   `closedOfSequentiallyCompact`, `sequentialCompactIffClosedBounded`. 4. HOL var identity is
   (name,type): give CHOOSE witnesses + select binders DISTINCTIVE names (`lClosed`,
   `phiClosed`, `bigN`, `yCsetNear`, `zNbhd`, `aNbhd`/`bNbhd`) — NEVER bare `x/y/l/n` a
   caller's term carries. 5. holError HoldRest. 6. dev.wls is the only verifier. 7. aconv
   tests, no deep MatchQ, NO testExit. 8. mkVar/mkConst/mkComb/mkAbs only. 9. narrow probes.
   10. No Return in Do/For/While. 11. realArithProve is LINEAR — the x±r bounds (`0<r ⇒
   x−r<x`, `0<r ⇒ x<x+r`) and `z+(−0)=z` are linear (r/z opaque); the abs/select steps are
   NOT realArithProve. 12. select-def-with-spec = the unboundedEscapePoint template VERBATIM
   (def → unfold → appEq → selectOfExists → CONJUNCTi → APTERM-rewrite the @-arg). 13. **β**:
   csetBetaClean every selectOfExists result and every appEq; the tendsto/openInterval
   predicates are `(λ…) arg` redexes — BETACONV so terms aconv-match (this is the deep-beta
   trap [[wl-unfold-deep-beta-select]]). 14. The `nearClosedPoint` interval lower bound MUST
   be `realAdd x (realNeg (invSuccRadius n))` (NOT a `realSub` — there is none) so it matches
   `realAbsSubLtThm`'s `a + −e` slot and `csetAddNegZeroThm`'s shape.

## Verification (MANDATORY — you run wolframscript)

```
wolframscript -file tests/dev.wls stdlib/Real/Connected.wl stdlib/Real/Topology.wl stdlib/Real/CompactSet.wl real_compactset
```
Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste the final
`passed: N  failed: 0` VERBATIM. Do NOT run build_snapshot/extend_snapshot, do NOT modify
bootstrap.mx, do NOT run run_all, no other command, nothing outside the repo, no network.
Same failure twice → deliver the loadable subset + report. If dev.wls reports a stale
snapshot for some OTHER (non-frontier) file, STOP and report — do not rebuild.

Reading failures: `Throw::nocatch` at load = a proof/term bug (localize by which asserts
stopped); `Syntax::sntx`+line = bracket/quote typo; `failed:K` with FAIL lines = aconv
expected-term mismatch (usually `csetNeighGoal` shape or a missing betaClean).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did not reach
  it, say so explicitly — do NOT claim green without the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused symbol → file:line; new public names confirmed free).
3. How `csetNeighGoal` was built (mirrored vs extracted) and whether the (6) EQMP aconv held
   first try.
4. How the (5) abs cleanup + (7) DEDUCTANTISYM orientation went.
5. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
6. Which tier fully proven vs stopped.
7. Open questions (empty if none).
