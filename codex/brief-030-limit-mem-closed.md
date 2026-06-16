# Brief 030 — M8.4b: tendsto→open-interval + limit_mem_of_closed (append to Real/Topology.wl)

## Goal

Append the two sequence/closed-set bridge lemmas that M8.5's sequential direction
needs: `pointInOpenIntervalOfTendstoThm` (a convergent sequence is EVENTUALLY inside
any open interval around its limit) and `limitMemOfClosedThm` (a closed set contains
the limit of any convergent sequence drawn from it). Append ~4 asserts to
`tests/real_topology_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealCompactness/SequentialCompactness.lean`
`point_in_open_interval_of_tendsto` (line 52) and `limit_mem_of_closed` (line 81).
Read those. Plain tendsto/eventually + the closed-set def from brief-029.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- Topology.wl is FRONTIER (brief-029, committed). Connected.wl is ALSO an
  un-graduated frontier file; dev.wls names BOTH (Connected first) or its staleness
  guard refuses. Append to the END of Topology.wl (before `End[]; EndPackage[]`) +
  `::usage` lines.
- **In Topology.wl (brief-029 — reachable):** `complConst[]`/`complTm[S]`/`complMemThm`
  (⊢ ∀S x. compl S x = ¬(S x)); `isClosedTm[S]`/`unfoldIsClosed[S]`/`isClosedComplOpenThm`
  (⊢ ∀S. isClosed S = isOpen (compl S)); the file's private helpers `topoSpecAll`/
  `topoConjTm`/`topo*` (grep — mirror them, or define analogues).
- **Snapshot (VERIFIED, reachable by bare name in this folder):**
  - Seq.wl: `tendstoTm[a,L]`; `tendstoEventuallyThm` ⊢ ∀a L e. tendsto a L ⇒ 0<e ⇒
    eventually (λn. realAbs (a n + realNeg L) < e); `eventuallyTm[P]`/`unfoldEventually[P]`
    (⊢ eventually P = ∃N. ∀n. N≤n ⇒ P n); `eventuallyAndThm` ⊢ ∀P Q. eventually P ⇒
    eventually Q ⇒ eventually (λn. P n ∧ Q n); `eventuallyMonoThm` ⊢ ∀P Q. (∀n. P n ⇒
    Q n) ⇒ eventually P ⇒ eventually Q; `realAbsSubLtLeftThm` ⊢ ∀a b e. realLt (realAbs
    (realAdd a (realNeg b))) e ⇒ realLt (realAdd b (realNeg e)) a; `realAbsSubLtRightThm`
    ⊢ … ⇒ realLt a (realAdd b e).
  - Compact.wl: `isOpenTm[U]`/`unfoldIsOpen[U]` (⊢ isOpen U = ∀x. U x ⇒ ∃l r. realLt l x
    ∧ realLt x r ∧ ∀y. openInterval l r y ⇒ U y); `openIntervalTm[l,r,x]`/`openIntervalMemThm`
    (⊢ openInterval l r x = (realLt l x ∧ realLt x r)).
  - Order/arith: `realArithProve` (LINEAR — `0 < l−left` from left<l, and the identities
    `l + (−(l−left)) = left` / `l + (right−l) = right`); `realLtTm`/`realLeTm`/`realAddTm`/
    `realNegTm`; `compactNatLe`-style num ≤ (grep Compact `compactNatLe`); `realLeReflThm`
    is real — for `num` N≤N use ARITH `arithProve` or grep Seq for a num-leq-refl.
  - num type `numTy`; sequence type `num→real`; Bool: EXCLUDEDMIDDLE/CHOOSE/EXISTS/CONJ/
    CONJUNCT1/2/CONTR/NOTELIM/SPEC/GEN/MP/DISCH/ASSUME; EQMP/SYM/APTERM/BETACONV; propTaut.

## Scope

- MODIFY: `stdlib/Real/Topology.wl` (append + `::usage`),
  `tests/real_topology_tests.wl` (append). No other files, NO runner lists. MUST NOT
  touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/docs/
  codex(except report). No newAxiom, no new files.

## Deliverable theorems

1. `pointInOpenIntervalOfTendstoThm` ⊢ ∀u l left right.
   tendsto u l ⇒ realLt left l ⇒ realLt l right ⇒
   eventually (λn. openInterval left right (u n)).
   Sketch (mirror blueprint): `gapL := realAdd l (realNeg left)` (= l−left),
   `gapR := realAdd right (realNeg l)`; `hgapL := realArithProve[left<l ⇒ 0<gapL]` MP
   (left<l); `hgapR` similarly. `evL := tendstoEventuallyThm SPEC (u, l, gapL) MP
   (tendsto) MP hgapL` → eventually (λn. realAbs (u n + realNeg l) < gapL). `evR`
   similarly (e:=gapR). `andEv := eventuallyAndThm SPEC (Pl, Pr) MP evL MP evR` (Pl,Pr
   the two λ-predicates) → eventually (λn. Pl n ∧ Pr n). Build the pointwise implication
   `∀n. (Pl n ∧ Pr n) ⇒ openInterval left right (u n)`: GEN n, DISCH; CONJUNCT →
   `|u n − l| < gapL`, `|u n − l| < gapR`; `realAbsSubLtLeftThm SPEC (u n, l, gapL)` →
   `realLt (l + (−gapL)) (u n)`, realArithProve identity `l + (−(l−left)) = left` +
   EQMP/cong → `left < u n`; `realAbsSubLtRightThm SPEC (u n, l, gapR)` → `u n < (l + gapR)`,
   identity `l + (right−l) = right` → `u n < right`; openIntervalMem (SYM) fold →
   `openInterval left right (u n)`. `eventuallyMonoThm SPEC (P∧, openLam) MP (pointwise
   impl) MP andEv` → the goal. **Beta-reduce `(λn. …) n` redexes (BETACONV) so the
   eventuallyAnd/Mono predicates aconv-match** (the redex-vs-normal trap from briefs
   024/027). GEN/DISCH wrap.

2. `limitMemOfClosedThm` ⊢ ∀S u l.
   isClosed S ⇒ (∀n. S (u n)) ⇒ tendsto u l ⇒ S l.
   Sketch: GEN S u l; DISCH isClosed S (hCl), (∀n. S(u n)) (hAll), tendsto u l (hLim).
   EXCLUDEDMIDDLE on `S l` (= mkComb[S,l]): TRUE → that IS the goal. FALSE (hNotSl):
   - `(compl S) l` from complMem SYM + hNotSl (complMem: compl S l = ¬(S l), EQMP backward).
   - `isOpen (compl S)` := EQMP[isClosedComplOpenThm SPEC S, hCl].
   - unfoldIsOpen (compl S), SPEC l, MP ((compl S) l) → ∃left right. left<l ∧ l<right ∧
     ∀y. openInterval left right y ⇒ (compl S) y. CHOOSE left, right (distinctive);
     split the conjunction (hll: left<l, hlr: l<right, hInside: the ∀y).
   - `ev := pointInOpenIntervalOfTendstoThm SPEC (u, l, left, right) MP hLim MP hll MP hlr`
     → eventually (λn. openInterval left right (u n)).
   - EQMP[unfoldEventually[that λ], ev] → ∃N. ∀n. N≤n ⇒ openInterval left right (u n).
     CHOOSE N. SPEC N, MP (N≤N : the num reflexive ≤ — grep Seq/Num for `leqReflThm` or
     ARITH) → openInterval left right (u N). (β-reduce the `(λn. …) N` redex.)
   - hInside SPEC (u N), MP that → (compl S)(u N); complMem → ¬(S (u N)). hAll SPEC N →
     S (u N). MP[NOTELIM …, that] → F. CONTR[mkComb[S,l], F] → S l.
   - DISJCASES[em, ASSUME (S l), the FALSE branch] → S l. GEN/DISCH wrap.

## Stop-loss / graded delivery

Tier 1: (1) pointInOpenIntervalOfTendsto. Tier 2: (2) limitMemOfClosed (depends on 1).
If a tier stalls (same failure twice — likely an eventually-predicate β-redex aconv
mismatch in (1), or the CHOOSE witness hygiene / num-N≤N in (2)), deliver the green
tier + STOP with a precise report (which sub-goal, exact payload, the term shapes).

## Tests (append ~4 asserts)

- `pointInOpenIntervalOfTendsto`/`limitMemOfClosed` concl shape (aconv on built
  expected; isThm + no-hyps after DISCH). No deep MatchQ. **NO `testExit[]`.**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. Public-symbol shadow — new
names `pointInOpenIntervalOfTendsto`/`limitMemOfClosed` FREE; reuse Seq/Compact/
brief-029 publics. 4. HOL var identity=(name,type): distinctive CHOOSE witnesses
(left/right/N). 5. holError HoldRest. 6. dev.wls verifier. 7. aconv tests, no deep
MatchQ, no testExit. 8. mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes. 10. No
Return in Do/For/While. 11. realArithProve LINEAR (the gap-positivity + the two
`l+(−gap)=…` identities only). 12. set/seq = real→bool / num→real; `S x`/`u n` =
mkComb. 13. **β-redex hygiene** — the `eventually (λn. P n)` predicates and `(λn. …) n`
/ `(λn. …) N` applications are redexes; BETACONV them so eventuallyAnd/Mono/unfoldEventually
targets aconv-match (this exact trap broke a CHOOSE in 024 and a DISJ in 027). 14.
`tendstoEventuallyThm`'s eventually predicate is `λn. realAbs (a n + realNeg L) < e` —
match that shape exactly when SPEC-feeding eventuallyAnd.

## Verification (MANDATORY — you run wolframscript)

Both un-graduated frontier files named (Connected first):
```
wolframscript -file tests/dev.wls stdlib/Real/Connected.wl stdlib/Real/Topology.wl real_topology
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
  reach it, say so explicitly and report where it stopped — do NOT claim green without
  the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused symbol → file:line; new names confirmed free).
3. How the eventually-and/mono assembly + β-reduction went; the num N≤N step.
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped.
6. Open questions (empty if none).
