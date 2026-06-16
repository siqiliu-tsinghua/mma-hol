# Brief 033 — M8.5 prereq: subsequence-of-convergent + invSuccRadius→0 (append to Real/CompactSet.wl)

## Goal

Append the two analytic prerequisites the closed-direction (brief-034) needs:
`seqTendstoSubsequenceThm` (a subsequence of a convergent sequence converges to the
same limit) and the `invSuccRadius` sequence `1/(n+1)` with `invSuccRadiusPosThm`,
`invSuccRadiusAntitoneThm`, and **`invSuccRadiusTendstoZeroThm`** (1/(n+1) → 0, our
inverse-natural Archimedean fact). Append ~4 asserts to
`tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint (in-repo)

`tautology-ref/Tautology/RealCompactness/SequentialCompactness.lean` `invSuccRadius`
(10) + `_pos` (13) + `_antitone` (18); the subsequence-tendsto fact mirrors HOL Light's
`SEQ_SUBLE`/limit-of-subsequence. (Our `invSuccRadiusTendstoZero` plays the role of
the blueprint's `InvNatArchimedeanPrinciple` — build it from `realArchThm`.)

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- CompactSet.wl is FRONTIER (briefs 031/032). Frontier files: Connected.wl, Topology.wl,
  CompactSet.wl — dev.wls names ALL THREE (that order). Append to the END of CompactSet.wl
  + `::usage` lines.
- **Reuse (snapshot — VERIFIED):**
  - Seq.wl: `tendstoTm[a,L]`/`unfoldTendsto[a,L]` (⊢ tendsto a L = ∀e. 0<e ⇒ ∃N. ∀n. N≤n ⇒
    realAbs (a n + realNeg L) < e); `subsequenceTm[u,phi]`/`unfoldSubsequence` (⊢ subsequence
    u phi n = u (phi n)); `subseqIndexTm[phi]`; `subseqIndexGeSelfThm` ⊢ ∀phi. subseqIndex
    phi ⇒ ∀n. n ≤ phi n.
  - Complete.wl: `realArchThm` ⊢ ∀x. ∃n:num. realLt x (&ℝ (&ℚ (&ℤ n))).
  - Inv.wl: `realMulInvThm` ⊢ ∀x. ¬(x = &ℝ0) ⇒ realMul x (realInv x) = &ℝ1; `realInvPosThm`/
    `invPosNonnegThm` (inv of positive is positive/nonneg — grep for the cleanest
    `0<x ⇒ 0<realInv x`; if only `invPos` forms exist, `realInvPosThm` rewrites realInv→invPos
    under 0<x). Mul.wl: `realLtMulPosThm` (0<x⇒0<y⇒0<x·y), `realLtMulMonoThm` (0<c⇒a<b⇒
    c·a<c·b), `realLeMulMonoThm`, `realMulOneThm`, `realMulCommThm`, `realMulAssocThm`.
  - brief-032 (CompactSet.wl, reachable): `natRealLeThm` ⊢ ∀m n. m≤n ⇒ realLe (rnumNat m)
    (rnumNat n); the `rnumNat[n]` (= &ℝ(&ℚ(&ℤ n))) builder (grep — `seqAuxNatReal` is the
    shared-folder private; reuse). Embedding-Lt iffs for nat-pos: `realOfRatLtThm`/
    `ratOfIntLtThm`/`intOfNumLtThm` (`intLt (&ℤ m)(&ℤ n) = m<n`) — build `realLt 0 (rnumNat
    (SUC n))` via these (0 < SUC n by arith).
  - Order: `realLtLeTransThm`/`realLeLtTransThm`/`realLtTransThm`, `realLtNotLeThm`,
    `realAbsPosThm` (Abs: ∀x. realLe 0 x ⇒ realAbs x = x). `realArithProve` (LINEAR — the
    `x+(−0)=x` identity, the `realLt 0 ε`/`0<gap` shuffles). `HOL`Auto`Arith`arithProve`
    (N≤n stuff). Bool: CHOOSE/EXISTS/CONJ/SPEC/GEN/MP/DISCH/ASSUME/EQMP/SYM/BETACONV.

## Scope

- MODIFY: `stdlib/Real/CompactSet.wl` (append + `::usage`),
  `tests/real_compactset_tests.wl` (append). No other files, NO runner lists. MUST NOT
  touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/Topology/
  docs/codex(except report). No newAxiom, no new files.

## Deliverable theorems

1. `seqTendstoSubsequenceThm` ⊢ ∀u phi l.
   subseqIndex phi ⇒ tendsto u l ⇒ tendsto (subsequence u phi) l.
   (GEN u phi l; DISCH subseqIndex phi (hIdx), tendsto u l (hTend). unfold the GOAL
   tendsto (subsequence u phi) l → ∀e. 0<e ⇒ ∃N. ∀n. N≤n ⇒ |sub n − l|<e; GEN e, DISCH 0<e.
   From hTend (unfolded) SPEC e MP (0<e) → ∃N. ∀n. N≤n ⇒ |u n − l|<e; CHOOSE N; EXISTS the
   SAME N; GEN n, DISCH N≤n. `hGe := subseqIndexGeSelfThm SPEC phi MP hIdx SPEC n` (n ≤ phi n);
   `hNphi := realLe/arithProve N≤n ⇒ N≤phi n` — chain N≤n≤phi n via `compactNatLe`-trans /
   arithProve; the inner ∀ at phi n MP (N≤phi n) → |u (phi n) − l|<e; rewrite `u (phi n) =
   subsequence u phi n` (unfoldSubsequence, SYM) → |sub n − l|<e. Fold the tendsto body.)

2. `invSuccRadiusDefThm` ⊢ invSuccRadius = (λn. realInv (rnumNat (SUC n)))  [= 1/(n+1)].
   Export `invSuccRadiusConst[]`/`Tm[n]`/`unfold`. Plus a `natSuccPosThm` ⊢ ∀n.
   realLt 0 (rnumNat (SUC n)) (via the embedding-Lt iffs + arith 0<SUC n).

3. `invSuccRadiusPosThm` ⊢ ∀n. realLt 0 (invSuccRadius n).
   (realInvPosThm/invPos-pos at rnumNat(SUC n), MP natSuccPos.)

4. `invSuccRadiusAntitoneThm` ⊢ ∀m n. m ≤ n ⇒ realLe (invSuccRadius n) (invSuccRadius m).
   (1/(n+1) ≤ 1/(m+1) from m+1 ≤ n+1. Derive inv-antitone from `natRealLeThm` (rnumNat(SUC m)
   ≤ rnumNat(SUC n)) + the two positives, via the inv-flip: for 0<a≤b, inv b ≤ inv a —
   prove inline by `realLeMulMonoThm`/`realMulInvThm` (multiply a≤b... see the (5) recipe for
   the inv manipulation pattern). OPTIONAL — if it fights you, ship (5) without it; the
   near-point direction's tendsto can use the squeeze `|u n − x| < invSuccRadius n` + (5).)

5. `invSuccRadiusTendstoZeroThm` ⊢ tendsto invSuccRadius 0  (i.e. 1/(n+1) → 0).
   (unfoldTendsto[invSuccRadius, 0]; GEN e, DISCH 0<e. `realArchThm SPEC (realInv e)` →
   ∃m. realLt (realInv e) (rnumNat m); CHOOSE m, hm. EXISTS N:=m; GEN n, DISCH m≤n. Goal:
   |invSuccRadius n + realNeg 0| < e, i.e. invSuccRadius n < e (after `x+(−0)=x` realArith +
   realAbsPos since invSuccRadius n ≥ 0). **Core inequality `realInv (rnumNat (SUC n)) < e`:**
   let M := rnumNat (SUC n) (>0 natSuccPos), so suffices `1 < e·M` (then inv M < e). `m ≤ n`
   ⇒ `m ≤ SUC n` (arith) ⇒ `rnumNat m ≤ M` (natRealLeThm); `realInv e < rnumNat m ≤ M` →
   `realInv e < M` (realLtLeTrans). Multiply by `e>0` (realLtMulMonoThm c:=e): `e·(realInv e)
   < e·M`; `e·realInv e = 1` (realMulInvThm, e≠0 from 0<e) → `1 < e·M`. Now `inv M < e`:
   multiply `1 < e·M` by `realInv M > 0` (realLtMulMono): `realInv M · 1 < realInv M · (e·M)`;
   LHS = realInv M (realMulOne); RHS = e · (M · realInv M) (assoc/comm) = e·1 = e
   (realMulInv M, M≠0); so `realInv M < e` = invSuccRadius n < e. Close the tendsto body.)

## Stop-loss / graded delivery

Tier 1: (1) seqTendstoSubsequence. Tier 2: (2)(3) invSuccRadius def + pos + natSuccPos.
Tier 3: (5) invSuccRadiusTendstoZero (the inv-manipulation core). (4) antitone is OPTIONAL
— ship if cheap, skip if it fights. If a tier stalls (same failure twice — likely the
inv-inequality chain in (5)), deliver the green tiers + STOP with a precise report (which
sub-goal, exact payload, the inv terms compared).

## Tests (append ~4 asserts)

- `seqTendstoSubsequence`/`invSuccRadiusPos`/`invSuccRadiusTendstoZero` concl shapes
  (aconv on built expected; isThm + probes). No deep MatchQ. **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. Public-symbol shadow — new names
FREE (grep): `seqTendstoSubsequence`/`invSuccRadius`/`invSuccRadiusPos`/`Antitone`/
`TendstoZero`/`natSuccPos`. 4. HOL var identity: distinctive CHOOSE witnesses (N, m). 5.
holError HoldRest. 6. dev.wls verifier. 7. aconv tests, no deep MatchQ, no testExit. 8.
mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes. 10. No Return in Do/For/While. 11.
realArithProve LINEAR (the `x+(−0)=x` + `0<e` shuffles); the inv-inequalities are
realMulInv/realLtMulMono by hand (nonlinear — NOT realArithProve); arithProve for ℕ ≤.
12. seq = num→real; `u n`/`subsequence u phi n` via mkComb/unfoldSubsequence (β). 13.
**β**: `(λn. …) n` for invSuccRadius/the tendsto predicate — BETACONV so terms aconv-match.
14. `e ≠ 0` from `0<e` via `seqArithPosNeZeroThm` (Seq, ⊢ ∀x. realLt 0 x ⇒ ¬(x=0)) — needed
for realMulInvThm at e.

## Verification (MANDATORY — you run wolframscript)

```
wolframscript -file tests/dev.wls stdlib/Real/Connected.wl stdlib/Real/Topology.wl stdlib/Real/CompactSet.wl real_compactset
```
Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste the final
`passed: N  failed: 0` VERBATIM. Do NOT run build_snapshot/extend_snapshot, do NOT modify
bootstrap.mx, do NOT run run_all, no other command, nothing outside the repo, no network.
Same failure twice → deliver the loadable subset + report. If dev.wls reports a stale
snapshot for some OTHER file, STOP and report.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did not reach
  it, say so explicitly — do NOT claim green without the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused symbol → file:line; new names confirmed free;
   the `rnumNat` builder you reused → file:line).
3. How the inv-inequality chain in (5) went (the `1<e·M ⇒ inv M<e` step).
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped.
6. Open questions (empty if none).
