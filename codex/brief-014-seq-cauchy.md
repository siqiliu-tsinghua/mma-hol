# Brief 014 — stdlib/Real/Seq.wl Stage 5: Cauchy criterion (Cauchy ⇒ convergent) — M7 bridge capstone

## Goal

Extend `stdlib/Real/Seq.wl` (Stages 1–4, briefs 008–012 — read the whole file
first) with the **Cauchy criterion**: every Cauchy sequence converges, proved
directly from the sup principle (the limit is the sup of the sequence's
"eventual lower bounds"). This is the LAST sequence-layer stage and the M7
bridge capstone `⊢ ∀u. seqCauchy u ⇒ ∃L. tendsto u L`. Append tests. After this
Seq.wl is done and graduates (Claude handles graduation).

## Blueprint (in-repo, gitignored — READ and mirror closely)

`tautology-ref/Tautology/RealSequence/Principles/FromSupCauchy.lean` — the
COMPLETE 0-sorry reference for EXACTLY this. Mirror its structure 1:1:
`SeqCauchy` (def, in `Statements.lean`), `EventualLowerBound`,
`cauchy_tail_center_lower`/`_upper`, `eventual_lower_nonempty_of_cauchy`,
`eventual_lower_bounded_above_of_cauchy`, `tail_center_lower_mem`,
`tail_center_upper_bound`, `limitCandidate` (= sup of the ELB set),
`limitCandidate_is_lub`, `limitCandidate_tendsto`, `cauchyCriterion`.
Surface translation: `F.lt/le/add/sub/abs`, `SeqTendsto`, `Classical.choose`-
`limitCandidate` → our `realLt/realLe/realAdd/(realAdd x (realNeg y))/realAbs/
tendsto/realSup`. `Nat.max N M` → use `N+M` with `seqLeqAddSelf` (we have no num
max; same trick Stage 3/4 used). Their `half`/`add_half_add_half`/
`sub_half_add_self`/linear ε-steps → `realArithProve` (it handles `e·(1/2)` —
Stage 1's g1 and brief-008's half-double are realArithProve facts).

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- In context `HOL`Stdlib`Real`` — all Seq.wl + Real-folder privates reachable.
- **Available, verified (grep ::usage before use):**
  - Abs.wl: `realLeAbsSelfThm` ⊢ ∀x. realLe x (realAbs x);
    `realNegLeAbsThm` ⊢ ∀x. realLe (realNeg x) (realAbs x).
  - Seq.wl Stage 3 (brief-011): `realAbsSubLtThm` ⊢ ∀x a e. realLt (a+(−e)) x ⇒
    realLt x (a+e) ⇒ realLt (realAbs (x+(−a))) e (bounds ⇒ |·|<e — THE closer
    for limitCandidate_tendsto); `realSupLtMemThm`; the `monoInc…sup` machinery
    showed the realSup set idiom (raw `λx. ∃…` predicate). Also `seqLeqAddSelf`
    (`m ≤ m+k`) + `seqLeqToSumLeft`/right for the N+M two-index combine.
  - Complete.wl: `realSupUpperThm` (∀a. S a ⇒ a ≤ realSup S = "le_lub_of_mem"
    when you flip: a member ≤ sup), `realSupLeastThm` (sup ≤ any upper bound =
    "lub_le_of_upper"), both conditional on (∃a.S a)+(∃u.∀a.S a⇒a≤u);
    `realLtImpLeThm`, `realLeLtTransThm`, `realLtLeTransThm`, `realLeTransThm`.
  - RealArith.wl: `realArithProve[goalTm]` (LINEAR — for every ε/half/bound
    rearrangement over the opaque atoms u N, u n, realSup …, e); `rnumLt` etc.
  - Stage 1: `tendstoTm`/`unfoldTendsto`/`tendstoConstThm`; the `0<e ⇒ 0<e·(1/2)`
    glue (grep — reuse, don't re-prove).
  - Num: `leqReflThm`, `leqConst[]`, `sucConst[]`, `zeroConst[]`,
    `numInductionThm` (only for index ℕ facts; ARITH `arithProve` also available
    for ℕ ≤-chains).
  - Bool: `CHOOSE`, `EXISTS`, `CONJ`, `CONJUNCT1/2`, `GEN`, `SPEC`, `MP`, `DISCH`.

## Scope

- MODIFY: `stdlib/Real/Seq.wl` (append Stage 5), `tests/real_seq_tests.wl`.
- Do NOT touch other files or runner lists. MUST NOT touch Kernel/Types/Terms/
  Bootstrap/bootstrap.mx/docs/codex(except report). No newAxiom. No new files.

## Definitions (pin; new constants + unfold helpers)

```
seqCauchyDefThm:  ⊢ seqCauchy = (λu. ∀e. realLt 0 e ⇒
                     ∃N. ∀n m. N ≤ n ⇒ N ≤ m ⇒
                       realLt (realAbs (realAdd (u n) (realNeg (u m)))) e)
elbDefThm:        ⊢ elb = (λu x. ∃N. ∀n. N ≤ n ⇒ realLe x (u n))
```
- u : num→real; `0` = zeroRealTm[]; `≤` on n,m,N is Num leq. `elb u x` = "x is
  an eventual lower bound of u". Export `seqCauchyConst[]`/`seqCauchyTm[uT]`,
  `elbConst[]`/`elbTm[uT,xT]` + unfold helpers (APTHM+BETACONV, possibly
  deep-beta `seqBetaClean` if a redex remains — cf. [[wl-unfold-deep-beta-select]]).

## Deliverable theorems (mirror the blueprint)

### Prerequisites (abs direction — converse of realAbsSubLtThm)
1. `realAbsSubLtLeftThm` ⊢ ∀a b e. realLt (realAbs (realAdd a (realNeg b))) e ⇒
   realLt (realAdd b (realNeg e)) a.  (b−e < a from |a−b|<e.) Route:
   `realNegLeAbsThm` at `(a−b)` gives `−(a−b) ≤ |a−b|`; `realLeLtTransThm` with
   the hyp ⇒ `−(a−b) < e`; `realArithProve` linear-equiv `−(a−b) < e ⟺ b−e < a`.
2. `realAbsSubLtRightThm` ⊢ ∀a b e. realLt (realAbs (realAdd a (realNeg b))) e ⇒
   realLt a (realAdd b e).  (a < b+e.) Via `realLeAbsSelfThm` (a−b ≤ |a−b|) +
   realLeLtTrans + realArithProve (`a−b < e ⟺ a < b+e`).

### Cauchy → the ELB set is nonempty + bounded above
3. `cauchyTailLowerThm` ⊢ (the Cauchy tail at center N): given the unfolded
   Cauchy witness `∀n m. N≤n ⇒ N≤m ⇒ |u n − u m|<e` and `N≤n`, conclude
   `realLt (realAdd (u N) (realNeg e)) (u n)`. = `realAbsSubLtLeftThm` applied to
   the close fact `|u n − u N|<e` (instantiate the witness at n,N + leqRefl N).
4. `cauchyTailUpperThm` ⊢ same hyps + `N≤n` ⇒ `realLt (u n) (realAdd (u N) e)`.
   = `realAbsSubLtRightThm` on `|u n − u N|<e`.
5. `elbNonemptyThm` ⊢ ∀u. seqCauchy u ⇒ ∃x. elb u x. Cauchy at e:=1 (use the
   `1` literal) gives N; witness x := `u N + (−1)`; the ELB witness index N;
   for n≥N, `cauchyTailLower` gives `u N − 1 < u n`, `realLtImpLe` ⇒ `≤`.
6. `elbBddAboveThm` ⊢ ∀u. seqCauchy u ⇒ ∃w. ∀x. elb u x ⇒ realLe x w. Cauchy at
   1 gives N; w := `u N + 1`; for `elb u x` (CHOOSE its index M): at K:=N+M
   (seqLeqAddSelf both ways), `x ≤ u K` (the ELB at K) and `u K < u N + 1`
   (`cauchyTailUpper` at K) ⇒ `x ≤ w` (realLeLtTrans + realLtImpLe).

### The two membership/upper facts at center N (for the main proof)
7. `tailLowerMemThm` ⊢ (Cauchy witness at e, center N) ⇒ `elb u (u N + (−e))`.
   (ELB witness N; `cauchyTailLower` + realLtImpLe.)
8. `tailUpperBoundThm` ⊢ (same) ⇒ `∀x. elb u x ⇒ realLe x (u N + e)`. (like
   elbBddAbove but with e instead of 1.)

### limitCandidate = sup of ELB, and it is the limit
9. `cauchyConvergesThm` ⊢ ∀u. seqCauchy u ⇒ ∃L. tendsto u L. THE capstone.
   Let `elbSet[uT] = λx. ∃N. ∀n. N ≤ n ⇒ realLe x (u n)` (raw real→bool; or
   reuse `elbTm[uT]` partially applied — whichever makes the realSup lemmas
   SPEC cleanly; distinctive bound names xE, NE, nE). Nonempty + bdd-above from
   (5)+(6). s := `realSup (elbSet u)`. EXISTS L := s. Unfold tendsto: GEN e,
   DISCH 0<e; d := `realMul e (realInv 2)` (= e/2), `0<d` from the Stage-1 glue;
   Cauchy at d gives N (CHOOSE). EXISTS N; GEN n, DISCH N≤n. Now (mirror
   `limitCandidate_tendsto`):
   - `u N − d ∈ elbSet` (tailLowerMem at d) ⇒ `u N − d ≤ s` (realSupUpper /
     "member ≤ sup": SPEC the set + nonempty+bdd hyps, apply at the member).
   - `u N + d` upper-bounds elbSet (tailUpperBound at d) ⇒ `s ≤ u N + d`
     (realSupLeast).
   - `|u N − u n| < d` (Cauchy witness at N,n) ⇒ `u N < u n + d` (cauchyTailUpper
     shape / realAbsSubLtRight) and `u n < u N + d` (cauchyTailUpper at n).
   - LEFT bound `s − e < u n`: from `s ≤ u N + d` and `u N < u n + d`, plus
     `(u n + d) + d = u n + e` — all linear ⇒ `realArithProve` chains
     `s ≤ u N+d < u n + d + ... ` to `s − e < u n` (give realArithProve the
     two strict/le facts as hyps; it closes the linear conclusion `s+(−e)<u n`).
   - RIGHT bound `u n < s + e`: from `u n < u N + d` and `u N − d ≤ s` (so
     `u N ≤ s + d`), plus `(s + d) + d`-style — `realArithProve` from
     `u n < u N + d` and `u N + (−d) ≤ s` to `u n < s + e`.
   - `realAbsSubLtThm` x:=u n, a:=s, e:=e with the two bounds ⇒
     `realLt (realAbs (u n + (−s))) e` = the tendsto body.
   (The half-identities `(u n+d)+d = u n+e`, `(u N−d)+e = u N+d` are
   realArithProve facts; feed them or let realArithProve derive the bound
   directly from the ≤/< facts since it knows d = e·(1/2).)

If a step stalls, deliver the loadable subset (defs + prerequisites + (3)–(8)
at minimum) and STOP per stop-loss with a precise report.

## Tests (append ~12 asserts)

- Defs unfold at fresh vars; shape checks.
- `realAbsSubLtLeft/Right` SPEC at rnum literals + MP a `|·|<e` fact (from
  realArithProve/rnum) ⇒ concrete bound.
- `cauchyConvergesThm` concl-shape at a fresh u (aconv on built expected term).
- Constant sequence end-to-end: `λn. c` is seqCauchy (|c−c|=0<e via
  realArithProve + realAbsZero; witness N:=0); `cauchyConvergesThm` MP'd ⇒
  ∃L. tendsto (λn.c) L; assert theorem, empty hyps.
- aconv against folder-builder expected; no deep MatchQ.

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder
privates reachable; Abs/Complete/Num/Bool publics only. 4. HOL var
identity=(name,type): the ELB set's bound vars (xE,NE,nE), CHOOSE witnesses
(NW,MW,xW,lW), GEN binders distinctive — never bare n/m/N/x the caller carries.
5. holError HoldRest. 6. dev.wls is your verifier (see Verification).
7. aconv tests, no deep MatchQ. 8. mkVar/mkConst/mkComb/mkAbs only. 9. Narrow
probes. 10. No Return in Do/For/While. 11. **SPEC does not β-reduce** — clean
redexes (the ELB set applied to a member, unfold outputs) with BETACONV /
seqBetaClean; if an unfold of a `@`-defined or λ-heavy constant leaves an inner
redex use deep-beta ([[wl-unfold-deep-beta-select]]). 12. **realArithProve is
LINEAR** — realSup/realAbs/u-n opaque atoms; sup ORDER facts come from
realSupUpper/Least, only ε/half rearrangements are realArithProve's; it DOES
know `realInv 2` as a literal (×LCD). 13. The realSup set is a RAW predicate fed
as `S`; nonempty hyp `∃a. S a`, bound hyp `∃w. ∀a. S a ⇒ realLe a w` — match the
lemma shapes (they SPEC on S).

## Verification (MANDATORY — you run wolframscript)

Full machine access. Verify and iterate to green before delivering. The ONLY
command you run:

```
wolframscript -file tests/dev.wls stdlib/Real/Seq.wl real_seq
```

Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste
that final `passed: N  failed: 0` line into your report. Do NOT run
build_snapshot/extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all,
no other command, nothing outside the repo, no network. If the same failure
recurs twice, deliver the loadable subset and report where you stopped — never
fake a green count. Reading failures: `Throw::nocatch` at load = a proof/term
bug (localize by which theorem stopped binding); `Syntax::sntx`+line = bracket/
quote typo; `failed:K` with `FAIL` lines = assertion/aconv mismatch.

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
