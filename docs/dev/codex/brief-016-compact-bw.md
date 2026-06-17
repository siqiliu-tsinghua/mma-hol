# Brief 016 — M8.2 Branch A.1: Bolzano–Weierstrass sequential compactness (new file Real/Compact.wl)

## Goal

Start the M8.2 compactness layer with a NEW file `stdlib/Real/Compact.wl`
(shares the `HOL`Stdlib`Real`` folder context). Define `seqBounded` and
`hasConvergentSubseq`, then prove **Bolzano–Weierstrass sequential
compactness**: every bounded sequence has a convergent subsequence —
`⊢ ∀u. seqBounded u ⇒ ∃l. hasConvergentSubseq u l`. This is the ONE genuinely
new proof of M8.2 (a self-assembly of existing Seq.wl results), and it is what
finally USES `existsMonoSubseqThm` (Stage 4a). New test file
`tests/real_compact_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint

`tautology-ref/Tautology/RealCompactness/Compact.lean` (defs `SeqBounded`,
`HasConvergentSubsequence`) + `RealCompactness/ClosedInterval/Statements.lean`
(`BolzanoWeierstrassSequentialPrinciple.convergent_subsequence`). The PROOF is
our own short assembly (the blueprint reaches sequential compactness via
accumulation/FiniteToSeq, but per the owner's M8.2 re-plan we assemble it
directly from `existsMonoSubseqThm` + `monoConverges*` — that is the whole point,
so Stage 4a is on the critical path). Mirror the blueprint only for the DEFS.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **Seq.wl is now IN bootstrap.mx (graduated).** Its publics are available by
  short name after the snapshot restore. The dev loop for THIS frontier file is
  `tests/dev.wls stdlib/Real/Compact.wl real_compact`.
- **Available, verified (grep ::usage in stdlib/Real/Seq.wl before use):**
  - `existsMonoSubseqThm` ⊢ ∀u. ∃phi. subseqIndex phi ∧
    (monoInc (subsequence u phi) ∨ monoDec (subsequence u phi)).
  - `monoConvergesIncThm` ⊢ ∀u. monoInc u ⇒ seqBddAbove u ⇒ ∃L. tendsto u L.
  - `monoConvergesDecThm` ⊢ ∀u. monoDec u ⇒ seqBddBelow u ⇒ ∃L. tendsto u L.
  - `seqBddAboveDefThm` ⊢ seqBddAbove = (λu. ∃B. ∀n. realLe (u n) B);
    `seqBddBelowDefThm` ⊢ seqBddBelow = (λu. ∃B. ∀n. realLe B (u n)) — with
    `seqBddAboveConst[]`/`seqBddAboveTm`/`unfoldSeqBddAbove` (+ Below).
  - `subseqIndexConst[]`/`subseqIndexTm`, `subsequenceConst[]`/
    `subsequenceTm[uT, phiT]` (= λn. u (phi n)), `unfoldSubsequence`,
    `monoIncTm`/`monoDecTm`, `tendstoTm`.
  - the seq type (num→real) builders and term-helpers in Seq.wl (grep `seqTy`).
- Bool: `CHOOSE`, `DISJCASES`, `CONJ`, `CONJUNCT1/2`, `EXISTS`, `GEN`, `SPEC`,
  `MP`, `DISCH`.

## Scope

- Files you may CREATE: `stdlib/Real/Compact.wl`, `tests/real_compact_tests.wl`.
- Do NOT touch runner load lists (the reviewer wires `Compact.wl` into
  run_all/run_all_stable after Seq.wl at acceptance; the new `*_tests.wl` is
  auto-discovered). MUST NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/
  docs/codex(except report). No newAxiom.
- `Compact.wl` package: `BeginPackage["HOL`Stdlib`Real`", {…}]` importing the
  same context list the other Real files use (grep `stdlib/Real/Seq.wl`'s
  BeginPackage and copy it — it pulls Error/Types/Terms/Kernel/Bootstrap/Equal/
  Bool/Drule/Num/…/Real folder/RealArith). Public symbols get ::usage before
  `Begin["`Private`"]`.

## Definitions (pin; mirror the blueprint shapes)

```
seqBoundedDefThm:        ⊢ seqBounded = (λu. ∃lo. ∃hi.
    ∀n. realLe lo (u n) ∧ realLe (u n) hi)
hasConvergentSubseqDefThm: ⊢ hasConvergentSubseq = (λu l.
    ∃phi. subseqIndex phi ∧ tendsto (subsequence u phi) l)
```
- u : num→real; l, lo, hi : real; phi : num→num. Export
  `seqBoundedConst[]`/`seqBoundedTm[uT]`, `hasConvergentSubseqConst[]`/
  `hasConvergentSubseqTm[uT,lT]` + unfold helpers.

## Deliverable theorems

Helpers (private):
1. `seqBoundedSubseqAboveThm` ⊢ ∀u phi. seqBounded u ⇒ seqBddAbove (subsequence u phi).
   Unfold seqBounded (CHOOSE lo, hi); witness B := hi; GEN n; (subsequence u
   phi) n β-reduces to u (phi n); the hi-bound at index `phi n`. Fold into
   seqBddAbove.
2. `seqBoundedSubseqBelowThm` ⊢ ∀u phi. seqBounded u ⇒ seqBddBelow (subsequence u phi).
   Symmetric with lo.

Public:
3. `bwSequentialThm` ⊢ ∀u. seqBounded u ⇒ ∃l. hasConvergentSubseq u l.
   ASSUME seqBounded u. `existsMonoSubseqThm` SPEC u → ∃phi. subseqIndex phi ∧
   (monoInc (sub u phi) ∨ monoDec (sub u phi)); CHOOSE phi (distinctive `phiW`);
   CONJUNCT1 = subseqIndex phi, CONJUNCT2 = the disjunction. DISJCASES:
   - monoInc (sub u phi): `seqBoundedSubseqAboveThm` MP ⇒ seqBddAbove (sub u phi);
     `monoConvergesIncThm` (SPEC (sub u phi), MP monoInc, MP bddAbove) ⇒
     ∃L. tendsto (sub u phi) L; CHOOSE L; build hasConvergentSubseq u L via
     EXISTS phi + CONJ (subseqIndex phi) (tendsto (sub u phi) L); EXISTS L.
   - monoDec: symmetric via `seqBoundedSubseqBelowThm` + `monoConvergesDecThm`.
   Both branches give `∃l. hasConvergentSubseq u l`; close DISJCASES; DISCH; GEN.

If a step stalls, deliver defs + helpers + whatever lands and STOP per
stop-loss with a report.

## Tests (`tests/real_compact_tests.wl`, ~10 asserts; copy real_seq_tests.wl scaffolding)

- Import harness + `HOL`Stdlib`Real`` (+ Seq is in the snapshot). Structure
  like real_seq_tests.wl (runTests/testExit).
- Defs unfold at fresh vars; shape checks.
- `seqBoundedSubseq{Above,Below}Thm` and `bwSequentialThm` concl-shape at fresh
  u (aconv on built expected terms).
- Constant sequence `λn. c`: seqBounded (lo=hi=c, c≤c via realLeRefl);
  `bwSequentialThm` MP'd ⇒ ∃l. hasConvergentSubseq (λn.c) l; assert theorem,
  empty hyps.
- aconv against folder builders; no deep MatchQ.

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder +
Seq.wl publics reachable; Bool/Num publics only. 4. HOL var identity=(name,type):
CHOOSE witnesses (`phiW`,`loW`,`hiW`,`lW`) + GEN binders (`nW`) distinctive,
never bare u/phi/n/l the statement carries. 5. holError HoldRest. 6. dev.wls is
your verifier (Verification). 7. aconv tests, no deep MatchQ. 8. mkVar/mkConst/
mkComb/mkAbs only. 9. Narrow probes. 10. No Return in Do/For/While. 11. **SPEC
does not β-reduce** — `(subsequence u phi) n` leaves a redex after unfolding the
def; clean with BETACONV. 12. New file: get the `BeginPackage` import list +
`Begin["`Private`"]`/`End[]`/`EndPackage[]` exactly right (copy Seq.wl's).

## Verification (MANDATORY — you run wolframscript)

Full machine access. Verify and iterate to green before delivering. The ONLY
command you run:

```
wolframscript -file tests/dev.wls stdlib/Real/Compact.wl real_compact
```

(dev.wls restores the snapshot — which now includes Seq.wl — loads Compact.wl
as the frontier file on top, and runs tests/real_compact_tests.wl.) Loop edit →
run → read failure → fix until the tail prints `failed: 0`; paste that final
`passed: N  failed: 0` into your report. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other
command, nothing outside the repo, no network. If the same failure recurs twice,
deliver the loadable subset and report. Reading failures: `Throw::nocatch` at
load = proof/term bug; `Syntax::sntx`+line = bracket typo; `failed:K`+`FAIL` =
assertion/aconv mismatch. **If dev.wls says the snapshot is STALE (an upstream
file changed), STOP and report — do not rebuild.**

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one
  dev.wls verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. The exact final `passed: N  failed: 0` from your dev.wls run.
4. Which theorems fully proven vs stopped.
5. Open questions (empty if none).
