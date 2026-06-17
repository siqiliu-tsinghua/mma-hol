# Brief 032 — M8.5: sequentially-compact ⇒ bounded (append to Real/CompactSet.wl)

## Goal

Append the FIRST hard sequential direction: `boundedOfSequentiallyCompactThm` —
a sequentially compact set is bounded. By contraposition: if S is NOT bounded,
build an "escape" sequence `unboundedEscapePoint` (point n lies in S with |·| past
the n-th natural), which is in S, so sequential compactness gives a convergent
(hence eventually bounded) subsequence — but the escape points run off to infinity
(Archimedean), a contradiction. Helper lemmas `existsOutsideOfNotSetBoundedThm`,
`ltAbsOfOutsideThm`, the `unboundedEscapePoint` ε-sequence + its mem/outside specs,
and a `natRealLeThm` embedding-monotonicity helper. Append ~3 asserts to
`tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealCompactness/SequentialCompactness.lean`
`exists_outside_of_not_setBounded` (143), `unboundedEscapePoint` (172) +
`_mem`/`_outside` (180/187), `lt_abs_of_outside` (198), `bounded_of_sequentiallyCompact`
(210–264). Read those. (`exists_nat_gt_of_linearArchimedean` is just our `realArchThm`;
`nat F (n+1)` is the real `&ℝ(&ℚ(&ℤ (SUC n)))`; `Nat.max N m` → use `N+m` with arith.)

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- CompactSet.wl is FRONTIER (brief-031). The un-graduated frontier files are
  Connected.wl, Topology.wl, CompactSet.wl — dev.wls names ALL THREE (that order).
  Append to the END of CompactSet.wl (before `End[]; EndPackage[]`) + `::usage` lines.
- **In CompactSet.wl (brief-031, reachable):** `isSequentiallyCompactTm[S]`/
  `unfoldIsSequentiallyCompact[S]` (⊢ = ∀u. (∀n. S (u n)) ⇒ ∃l. S l ∧ hasConvergentSubseq
  u l); the file's private `cset*` helpers (specAll/builders — grep, reuse/extend).
- **Reuse (snapshot — VERIFIED):**
  - Compact.wl: `setBoundedTm[S]`/`unfoldSetBounded` (`setBounded S = ∃lo hi. ∀x. S x ⇒
    (realLe lo x ∧ realLe x hi)`); `hasConvergentSubseqTm`/`unfoldHasConvergentSubseq`;
    `subsequenceTm[u,phi]`/`unfoldSubsequence` (⊢ subsequence u phi n = u (phi n)).
  - Seq.wl: `seqTendstoEventuallyBoundedThm` ⊢ ∀a L. tendsto a L ⇒ eventuallyBounded a;
    `eventuallyBoundedDefThm`/`unfoldEventuallyBounded` (`eventuallyBounded u = ∃B. 0<B ∧
    eventually (λn. realAbs (u n) < B)`); `unfoldEventually` (`eventually P = ∃N. ∀n. N≤n ⇒
    P n`); `subseqIndexGeSelfThm` ⊢ ∀phi. subseqIndex phi ⇒ ∀n. n ≤ phi n; `subseqIndexTm`.
  - Complete.wl: `realArchThm` ⊢ ∀x. ∃n:num. realLt x (&ℝ (&ℚ (&ℤ n))). Abs.wl:
    `realLeAbsSelfThm` ⊢ ∀x. realLe x (realAbs x); `realNegLeAbsThm` ⊢ ∀x. realLe (realNeg x)
    (realAbs x). Order: `realLtLeTransThm`/`realLeLtTransThm`/`realLtTransThm`,
    `realNotLeLtThm` (⊢ ∀x y. ¬(realLe x y) = realLt y x), `realLtNotLeThm`; the strict
    `realNegLtThm`/neg-flip — grep Mul.wl `realLeNeg`/`realNegNeg` for `x<−B ⇒ B<−x`.
  - Embedding iffs (for `natRealLe`): `realOfRatLeThm` (⊢ realLe (&ℝ a)(&ℝ b) = ratLe a b),
    `ratOfIntLeThm` (⊢ ratLe (&ℚ a)(&ℚ b) = intLe a b), `intOfNumLeThm` (⊢ intLe (&ℤ m)(&ℤ n)
    = (m ≤ n)). Builders `realOfRatTm`/`ratOfIntTm`/`intOfNumTm`; the real-of-nat literal
    `rnumNat[n] := realOfRatTm[ratOfIntTm[intOfNumTm[n]]]` (= &ℝ(&ℚ(&ℤ n))) — grep Compact/
    SeqAux for an existing `*NatReal*`/`rnum`/`seqAuxNatReal` builder and reuse.
  - Select (pointwise ε): `selectAx` ⊢ ∀P x. P x ⇒ P (@ P); use `ISPEC` for the
    polymorphic binder. From `⊢ ∃x. P x` get `⊢ P (@ P)`: grep Seq.wl/SeqAux for
    `selectOfExists` (brief-012/017 used it) and reuse — `@ P` = `mkComb[mkConst["@",
    tyFun[tyFun[realTy,boolTy],realTy]], P]`.
  - `HOL`Auto`Arith`arithProve` (ℕ: `N ≤ N+m`, `m ≤ N+m`, `m ≤ SUC(phi K)` from `m≤K≤phi K`);
    `HOL`Stdlib`Num`plusConst`/`sucConst`; Bool: EXCLUDEDMIDDLE/DISJCASES/CHOOSE/EXISTS/CONJ/
    CONJUNCT1/2/CONTR/NOTINTRO/NOTELIM/DISJ1/DISJ2/SPEC/GEN/MP/DISCH/ASSUME; EQMP/SYM/BETACONV.

## Scope

- MODIFY: `stdlib/Real/CompactSet.wl` (append + `::usage`),
  `tests/real_compactset_tests.wl` (append). No other files, NO runner lists. MUST NOT
  touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/Topology/
  docs/codex(except report). No newAxiom, no new files.

## Deliverable theorems

1. `natRealLeThm` ⊢ ∀m n. m ≤ n ⇒ realLe (rnumNat m) (rnumNat n).
   (DISCH m≤n; intOfNumLeThm SPEC (m,n) backward (EQMP) → intLe (&ℤ m)(&ℤ n);
   ratOfIntLeThm SPEC backward → ratLe (&ℚ(&ℤ m))(&ℚ(&ℤ n)); realOfRatLeThm SPEC
   backward → realLe (rnumNat m)(rnumNat n). GEN m n.)

2. `existsOutsideOfNotSetBoundedThm` ⊢ ∀S B. ¬(setBounded S) ⇒
   ∃x. (S x) ∧ (realLt x (realNeg B) ∨ realLt B x).
   (EXCLUDEDMIDDLE on the ∃; if it holds, done; ELSE show setBounded S (witness lo:=−B,
   hi:=B; for x∈S, ¬(x<−B ∨ B<x) since otherwise the ∃ holds; so ¬(x<−B) → −B≤x via
   realNotLeLt, ¬(B<x) → x≤B; CONJ; EXISTS −B,B; fold setBounded), contradicting ¬setBounded.)

3. `ltAbsOfOutsideThm` ⊢ ∀x B. (realLt x (realNeg B) ∨ realLt B x) ⇒ realLt B (realAbs x).
   (DISJCASES: x<−B → B<−x (neg-flip: from x<−B, neg both sides + realNegNeg → B<−x) and
   −x≤|x| (realNegLeAbs) → B<|x| (realLtLeTrans). B<x → x≤|x| (realLeAbsSelf) → B<|x|.)

4. `unboundedEscapePoint` (a `num→real` ε-sequence): define
   `unboundedEscapePoint = (λS. (λn. @ (λx. (S x) ∧ (realLt x (realNeg (rnumNat (SUC n)))
   ∨ realLt (rnumNat (SUC n)) x))))` — NO recursion, a pointwise Hilbert select. Export
   `unboundedEscapePointConst[]`/`Tm[S]`/`unfold` + the two specs (β-reduced):
   - `unboundedEscapePointMemThm` ⊢ ∀S. ¬(setBounded S) ⇒ ∀n. S (unboundedEscapePoint S n).
   - `unboundedEscapePointOutsideThm` ⊢ ∀S. ¬(setBounded S) ⇒ ∀n.
     realLt (unboundedEscapePoint S n) (realNeg (rnumNat (SUC n))) ∨
     realLt (rnumNat (SUC n)) (unboundedEscapePoint S n).
   Both from `existsOutsideOfNotSetBoundedThm S (rnumNat (SUC n))` MP (¬setBounded) →
   ∃x. P x; `selectOfExists` → P (@P); `@P` = `unboundedEscapePoint S n` (after the def
   β-unfolds — DEEP-β so the `@`-term aconv-matches, [[wl-unfold-deep-beta-select]]);
   CONJUNCT1 → mem, CONJUNCT2 → outside.

5. `boundedOfSequentiallyCompactThm` ⊢ ∀S. isSequentiallyCompact S ⇒ setBounded S.
   (GEN S; DISCH isSeqCompact S (hSC). EXCLUDEDMIDDLE on `setBounded S`: TRUE → that IS
   the goal. FALSE (hNotBd): u := unboundedEscapePoint S; `huS := unboundedEscapePointMemThm
   S MP hNotBd` (∀n. S (u n)); `unfoldIsSequentiallyCompact` on hSC, SPEC u, MP huS →
   ∃l. S l ∧ hasConvergentSubseq u l; CHOOSE l, split → hConv (hasConvergentSubseq u l);
   unfoldHasConvergentSubseq → ∃phi. subseqIndex phi ∧ tendsto (subsequence u phi) l;
   CHOOSE phi, split → hIdx, hTend. `eb := seqTendstoEventuallyBoundedThm SPEC
   (subsequence u phi, l) MP hTend`; unfoldEventuallyBounded → ∃B. 0<B ∧ eventually
   (λn. |sub n| < B); CHOOSE B, split → hBpos, hEv; unfoldEventually → ∃N. ∀n. N≤n ⇒
   |sub n|<B; CHOOSE N, hN. `realArchThm SPEC B` → ∃m. B < rnumNat m; CHOOSE m, hm.
   K := plusTm[N, m]; `hNK := arithProve N≤K`, `hmK := arithProve m≤K`. `hKphi :=
   subseqIndexGeSelfThm SPEC phi MP hIdx SPEC K` (K ≤ phi K). `hmPhi := arithProve
   m ≤ SUC(phi K)` (from m≤K≤phi K). `hBlt := realLtLeTransThm (B < rnumNat m)(rnumNat m
   ≤ rnumNat (SUC(phi K)) via natRealLeThm MP hmPhi)` → B < rnumNat (SUC(phi K)).
   `hOut := unboundedEscapePointOutsideThm S MP hNotBd SPEC (phi K)`; `hAbs :=
   ltAbsOfOutsideThm SPEC (u (phi K), rnumNat (SUC(phi K))) MP hOut` → rnumNat(SUC(phi K))
   < |u (phi K)|. `hBabs := realLtTransThm hBlt hAbs` → B < |u (phi K)|. Now |sub K| =
   |u (phi K)| (subsequence rewrite at K). `hClose := hN SPEC K MP hNK` → |sub K| < B,
   i.e. |u (phi K)| < B. B < |u(φK)| and |u(φK)| < B → realLtTrans → B<B, realLtIrrefl → F.
   CONTR[setBounded S, F]. DISJCASES → setBounded S. GEN/DISCH.)

## Stop-loss / graded delivery

Tier 1: (1) natRealLe + (2) existsOutside + (3) ltAbsOfOutside. Tier 2: (4)
unboundedEscapePoint + its two specs. Tier 3: (5) boundedOfSequentiallyCompact. If a
tier stalls (same failure twice — likely the deep-β `@`-select aconv in (4) or the
`subsequence K = u(phi K)` / nat-mono chain in (5)), deliver the green tiers + STOP
with a precise report (which sub-goal, exact payload, the term shapes compared).

## Tests (append ~3 asserts)

- `boundedOfSequentiallyCompact` concl shape; `existsOutside`/`ltAbsOfOutside` concl
  shapes (aconv on built expected; isThm + probes). No deep MatchQ. **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. Public-symbol shadow — new names
(`natRealLe`/`existsOutsideOfNotSetBounded`/`ltAbsOfOutside`/`unboundedEscapePoint`/
`boundedOfSequentiallyCompact`) FREE (grep); reuse snapshot/CompactSet publics. 4. HOL
var identity=(name,type): distinctive CHOOSE witnesses (l, phi, B, N, m). 5. holError
HoldRest. 6. dev.wls verifier. 7. aconv tests, no deep MatchQ, no testExit. 8.
mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes. 10. No Return in Do/For/While. 11.
arithProve for the ℕ ≤ facts (N≤K, m≤K, m≤SUC(phi K)); realArchThm for B<nat. 12. set/seq
= real→bool / num→real. 13. **DEEP-β `@`-select** — `unboundedEscapePoint S n` is
`@(λx. …)`; `selectOfExists` deep-reduces the predicate's inner redexes, so unfold with
`seqBetaClean`/DEPTHCONV-BETACONV (not one BETACONV) or the `@`-terms won't aconv-match
([[wl-unfold-deep-beta-select]], bit brief-012). 14. `subsequence u phi K = u (phi K)`
via unfoldSubsequence (β); the eventuallyBounded/eventually predicates are λ-redexes —
β-reduce so they aconv-match.

## Verification (MANDATORY — you run wolframscript)

```
wolframscript -file tests/dev.wls stdlib/Real/Connected.wl stdlib/Real/Topology.wl stdlib/Real/CompactSet.wl real_compactset
```
Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste the
final `passed: N  failed: 0` VERBATIM. Do NOT run build_snapshot/extend_snapshot, do
NOT modify bootstrap.mx, do NOT run run_all, no other command, nothing outside the
repo, no network. Same failure twice → deliver the loadable subset + report. If
dev.wls reports a stale snapshot for some OTHER file, STOP and report.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did not
  reach it, say so explicitly — do NOT claim green without the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused symbol → file:line; new names confirmed free;
   the `rnumNat`/`selectOfExists` builders you reused → file:line).
3. How the `@`-select deep-β + the nat-mono chain + the subsequence-K rewrite went.
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped.
6. Open questions (empty if none).
