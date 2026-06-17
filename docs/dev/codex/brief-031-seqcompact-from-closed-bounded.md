# Brief 031 — M8.5: sequentially-compact ⇐ closed+bounded (NEW FILE Real/CompactSet.wl)

## Goal

Start M8.5 (general compactness, the 列紧 ⟺ 有界闭 ⟺ 紧 endpoint). Create
`stdlib/Real/CompactSet.wl` and do the SEQUENTIAL side's easy direction:
`isSequentiallyCompact` (def), `seqBoundedOfSetBoundedThm` (a sequence drawn from a
bounded set is a bounded sequence), and `sequentiallyCompactOfClosedBoundedThm`
(closed + bounded ⇒ sequentially compact — via Bolzano–Weierstrass + limit-in-closed).
Create `tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate to green.
(The other two sequential directions + the iff are brief-032; the open-cover side
`isCompact`/`compact_iff_closed_bounded` is LATER and NOT in scope here — its blueprint
`IsCompact` uses TYPE quantification `∀{ι}` which HOL lacks, needing a separate
set-of-sets encoding decision; do NOT attempt it.)

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealCompactness/Compact.lean` `IsSequentiallyCompact`
(line 54); `RealCompactness/SequentialCompactness.lean` `seqBounded_of_setBounded`
(106) + `sequentiallyCompact_of_closed_bounded` (119). Read those. Plain predicates;
NO type quantification on this side (sequences are `num→real`, a fixed type).

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **New file is FRONTIER** (`HOL`Stdlib`Real`). It loads AFTER Topology.wl (uses
  `limitMemOfClosed`/`isClosed` from it). The un-graduated frontier files are
  Connected.wl, Topology.wl, CompactSet.wl — dev.wls names ALL THREE in dependency
  order (Connected, Topology, CompactSet) or its staleness guard refuses.
- **Imitate `stdlib/Real/Topology.wl`'s file skeleton** (same context + import list;
  the `*DefThm`/`*Const`/`*Tm`/`unfold*` idiom + private `topo*`-style `specAll`/
  builders — define your own `cset*` analogues).
- **Reuse (snapshot, Compact.wl — VERIFIED, do NOT redefine):**
  - `setBoundedTm[S]`/`setBoundedConst[]`/`unfoldSetBounded` — `setBounded S =
    ∃lo hi. ∀x. S x ⇒ (realLe lo x ∧ realLe x hi)`.
  - `seqBoundedTm[u]`/`unfoldSeqBounded` — `seqBounded u = ∃lo hi. ∀n. (realLe lo (u n)
    ∧ realLe (u n) hi)`.
  - `bwSequentialThm` ⊢ ∀u. seqBounded u ⇒ ∃l. hasConvergentSubseq u l.
  - `hasConvergentSubseqTm[u,l]`/`unfoldHasConvergentSubseq[u,l]` — `= ∃phi. subseqIndex
    phi ∧ tendsto (subsequence u phi) l`. `subsequenceTm[u,phi]`, `subseqIndexTm[phi]`.
- **Reuse (Topology.wl, frontier — VERIFIED):** `isClosedTm[S]`; `limitMemOfClosedThm`
  ⊢ ∀S u l. isClosed S ⇒ (∀n. S (u n)) ⇒ tendsto u l ⇒ S l.
- Bool/Equal: CHOOSE/EXISTS/CONJ/CONJUNCT1/2/SPEC/GEN/MP/DISCH/ASSUME; EQMP/SYM/BETACONV.
  A set is `real→bool`, a sequence `num→real`; `S x`/`u n` = mkComb; `numTy`, `realTy`.

## Scope

- CREATE: `stdlib/Real/CompactSet.wl`, `tests/real_compactset_tests.wl`. NO runner
  lists (Claude wires at acceptance). MUST NOT touch Kernel/Types/Terms/Bootstrap/
  bootstrap.mx/Compact/Seq/SeqAux/Connected/Topology/docs/codex(except report). No
  newAxiom. **Do NOT define `isCompact` or `setBounded`/`seqBounded` (reuse).**

## Definitions (pin)

```
isSequentiallyCompactDefThm: ⊢ isSequentiallyCompact = (λS.
  ∀u. (∀n. S (u n)) ⇒ ∃l. (S l) ∧ hasConvergentSubseq u l)
```
`isSequentiallyCompact : (real→bool)→bool`. The bound `u` is `num→real`. Export
`isSequentiallyCompactConst[]`/`isSequentiallyCompactTm[S]`/`unfoldIsSequentiallyCompact[S]`.

## Deliverable theorems

1. `seqBoundedOfSetBoundedThm` ⊢ ∀S u. setBounded S ⇒ (∀n. S (u n)) ⇒ seqBounded u.
   (CHOOSE lo, hi from `unfoldSetBounded`+the setBounded hyp; build `∀n. (lo≤u n ∧
   u n≤hi)`: GEN n, the setBounded body SPEC (u n) MP (S (u n) from the ∀n hyp); EXISTS
   lo, hi into the seqBounded body; fold via SYM unfoldSeqBounded. Mind the ∃lo∃hi
   nesting — CHOOSE both, EXISTS both.)

2. `sequentiallyCompactOfClosedBoundedThm` ⊢ ∀S.
   isClosed S ⇒ setBounded S ⇒ isSequentiallyCompact S.
   (unfold isSequentiallyCompact; GEN S; DISCH isClosed S (hCl), setBounded S (hBd);
   GEN u; DISCH `∀n. S (u n)` (hAll). `huBdd := seqBoundedOfSetBoundedThm S u MP hBd
   MP hAll` → seqBounded u. `bwSequentialThm SPEC u MP huBdd` → ∃l. hasConvergentSubseq
   u l. CHOOSE l (distinctive); `unfoldHasConvergentSubseq[u,l]` EQMP → ∃phi. subseqIndex
   phi ∧ tendsto (subsequence u phi) l. CHOOSE phi; split → hIdx (subseqIndex phi),
   hTend (tendsto (subsequence u phi) l). `hSubS := ∀n. S (subsequence u phi n)`: GEN n,
   note `subsequence u phi n` — need `S (subsequence u phi n)` from hAll. The subsequence
   value `subsequence u phi n` = `u (phi n)` after the subsequence def β-reduces — grep
   Seq.wl `unfoldSubsequence`/`subsequenceMemThm` (⊢ subsequence u phi n = u (phi n)) and
   rewrite, then hAll SPEC (phi n) gives S (u (phi n)), EQMP back → S (subsequence u phi n).
   `hlS := limitMemOfClosedThm SPEC (S, subsequence u phi, l) MP hCl MP hSubS MP hTend`
   → S l. Build the goal body `∃l. S l ∧ hasConvergentSubseq u l`: CONJ hlS
   (hasConvergentSubseq u l — fold the ∃phi back via SYM unfoldHasConvergentSubseq +
   EXISTS phi (CONJ hIdx hTend)); EXISTS l. GEN/DISCH wrap.)

## Stop-loss / graded delivery

Tier 1: def + `seqBoundedOfSetBoundedThm`. Tier 2: `sequentiallyCompactOfClosedBoundedThm`.
If Tier 2 stalls (same failure twice — likely the `subsequence u phi n = u (phi n)`
rewrite or a CHOOSE-witness hygiene issue with l/phi), deliver Tier 1 + STOP with a
precise report (which sub-goal, exact payload). Loadable subset acceptable.

## Tests (create tests/real_compactset_tests.wl, ~4 asserts)

- Imitate `tests/real_topology_tests.wl`'s header. `isSequentiallyCompact` unfold body
  shape; `seqBoundedOfSetBounded` + `sequentiallyCompactOfClosedBounded` concl shapes
  (aconv on built expected; isThm + no-hyps after DISCH). No deep MatchQ. **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. Public-symbol shadow — new
`isSequentiallyCompact`/`seqBoundedOfSetBounded`/`sequentiallyCompactOfClosedBounded`
FREE; REUSE `setBounded`/`seqBounded`/`bwSequentialThm`/`hasConvergentSubseq`/`isClosed`/
`limitMemOfClosed` (do NOT redefine — they are snapshot/Topology publics). 4. HOL var
identity=(name,type): distinctive CHOOSE witnesses (l, phi, lo, hi). 5. holError
HoldRest. 6. dev.wls verifier. 7. aconv tests, no deep MatchQ, no testExit. 8.
mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes. 10. No Return in Do/For/While. 11.
set/seq types: `real→bool` / `num→real`. 12. **β**: `(subsequence u phi) n` and the
def bodies are redexes; reduce with the Seq `subsequence`/`hasConvergentSubseq` unfolds
so terms aconv-match (the redex-vs-normal trap from briefs 024/027/028). 13. The
`∃lo∃hi` in setBounded/seqBounded is NESTED — CHOOSE/EXISTS each level separately.

## Verification (MANDATORY — you run wolframscript)

Three un-graduated frontier files, dependency order:
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
2. Name-verification table (each reused symbol → file:line; new names confirmed free).
3. How the `subsequence u phi n = u (phi n)` rewrite + the CHOOSE/EXISTS nesting went.
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped.
6. Open questions (empty if none).
