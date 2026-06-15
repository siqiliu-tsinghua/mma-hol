# Brief 024 — M8.2 Branch B: Heine–Borel finish (compactnessPrinciple) — append to Real/Compact.wl

## Goal

Append the closed-interval **Heine–Borel** capstone to `stdlib/Real/Compact.wl`:
from an open cover of `[left,right]` with NO finite subcover, the bisection
produces a nested sequence of bad intervals whose lengths → 0 (brief-023), whose
unique limit point `x` lies in some cover set `U i` (open), so a small enough
bisection interval around `x` fits inside `(a,b) ⊆ U i` — a single-set (finite!)
subcover, contradicting "bad". Hence every open cover of a closed interval has a
finite subcover:

```
compactnessPrincipleThm ⊢ ∀U left right.
  realLe left right ⇒ (∀i. isOpen (U i)) ⇒ covers U (closedInterval left right)
  ⇒ finiteSubcover U (closedInterval left right).
```

Two helper theorems lead up to it (mirror the blueprint). Append ~6 asserts to
`tests/real_compact_tests.wl`. Self-verify with dev.wls, iterate to green; graded
delivery (see Stop-loss). This CLOSES Branch B except brief-025 (FiniteToLebesgue).

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealCompactness/ClosedInterval/FromNestedFinite.lean`:
`interval_subset_open_interval` (388), `singleton_subcover_of_small_interval`
(411), `finiteSubcoverFromNested` (426–494), `compactnessPrinciple` (496). Read
those. We MERGE `finiteSubcoverFromNested` + `compactnessPrinciple` into one
`compactnessPrincipleThm` (no typeclass-record packaging). Two deviations:

- **No `Nat.max`.** Where the blueprint takes `K := Nat.max NL NR`, use
  `K := NL + NR` (`HOL\`Stdlib\`Num\`plusTm`) and discharge `NL ≤ K`, `NR ≤ K`
  with `HOL\`Auto\`Arith\`arithProve` (linear ℕ).
- **abs orientation.** Our `intervalPointsCloseThm` concludes `|x − y|` (x first);
  the blueprint's `interval_points_close` gives `|y − x|`. To land `|y − x|`,
  SPEC `intervalPointsCloseThm` with its point slots SWAPPED (x-slot := y,
  y-slot := x) — see the sketch.

## Context pointers

- `CLAUDE.md` (Conventions + **capture hygiene**) first.
- Compact.wl AND SeqAux.wl are BOTH frontier (committed, not in `bootstrap.mx`);
  dev.wls names BOTH. Append to the END of Compact.wl (before `End[]; EndPackage[]`)
  + `::usage` lines in its usage block.
- **In-file (Compact.wl `` `Private` ``, reachable by bare name — VERIFIED):**
  - Cover vocab + unfolds: `openIntervalTm`/`closedIntervalTm` (left,right,x);
    `openIntervalMemThm` (⊢ ∀l r x. openInterval l r x = (l<x ∧ x<r)),
    `closedIntervalMemThm` (⊢ … closedInterval l r x = (l≤x ∧ x≤r)); `isOpenTm[U]`,
    `unfoldIsOpen[U]` (⊢ isOpen U = ∀x. U x ⇒ ∃l r. l<x ∧ x<r ∧ ∀y. openInterval
    l r y ⇒ U y); `coversTm[U,S]`, `unfoldCovers[U,S]` (⊢ covers U S = ∀x. S x ⇒
    ∃i. U i x); `listSubcoverTm[U,S,js]`, `unfoldListSubcover[U,S,js]` (⊢ = ∀x.
    S x ⇒ ∃i. MEM i js ∧ U i x); `finiteSubcoverTm[U,S]`, `unfoldFiniteSubcover[U,S]`
    (⊢ = ∃js. listSubcover U S js); `noFiniteSubcoverTm[U,a,b]`,
    `unfoldNoFiniteSubcover[U,a,b]` (⊢ = ¬(finiteSubcover U (closedInterval a b)));
    `badIntervalTm`? use `unfoldBadInterval[U,a,b]` (⊢ badInterval U a b = (a≤b ∧
    noFiniteSubcover U a b)).
  - iota-list builders: `compactCoverIndexTy[U]` (= U's index type ι),
    `compactIotaListTy` (= ι list at the abstract ιtyvar — for binders),
    `compactConsConstAt[ty]`/`compactConsTmAt[ty,x,xs]` (CONS at ty),
    `compactMemTmAt[ty,x,l]` (MEM at ty), `compactAppendTmAt`. **NIL at ι:** grep
    for `compactNil`; if absent build `HOL\`Kernel\`INSTTYPE[{<αtyvar>->ty},
    HOL\`Stdlib\`List\`nilConst[]]` or `mkConst["NIL", HOL\`Stdlib\`List\`listTy[ty]]`.
  - Branch-B theorems (this file): `badIntervalsThm`, `nestedIntervalsThm`,
    `lengthsToZeroThm` (all ⊢ ∀U l r. l≤r ⇒ noFiniteSubcover U l r ⇒ …);
    `compactIntervalOrderAt[U,l,r,hLeTh,hBadTh,n]` (⊢ realLe (lower…n)(upper…n));
    `compactLowerZeroEq`/`compactUpperZeroEq[U,l,r]` (⊢ lower…0=left / upper…0=right);
    `lowerTm`/`upperTm[U,l,r]`, `compactLowerAt`/`compactUpperAt[U,l,r,n]`.
  - Combinators: `compactSpecAll[th,{…}]`, `compactTransList[{…}]`,
    `compactRealLtCong[eqL,eqR]`, `compactRealLeCong`, `compactNotTm[t]`,
    `compactNatLe[a,b]`, `compactCoverTy` (U : ι→real→bool with ι the abstract
    tyvar), `compactBetaClean`; builders `realAddTm`/`realNegTm`, `zeroRealTm[]`.
  - `HOL\`Auto\`RealArith\`realArithProve[goalTm]` — LINEAR over opaque atoms.
- **Snapshot-available (VERIFIED):**
  - SeqAux: `intervalPointsCloseThm` ⊢ ∀a b x y eps. a≤x ⇒ x≤b ⇒ a≤y ⇒ y≤b ⇒
    (b−a)<eps ⇒ realLt (realAbs (realAdd x (realNeg y))) eps; `lengthLtOfCloseThm`
    ⊢ ∀a b eps. a≤b ⇒ realLt (realAbs (realAdd (realAdd b (realNeg a))
    (realNeg 0))) eps ⇒ realLt (realAdd b (realNeg a)) eps.
  - Seq: `realAbsSubLtLeftThm` ⊢ ∀a b e. realLt (realAbs (realAdd a (realNeg b))) e
    ⇒ realLt (realAdd b (realNeg e)) a (i.e. |a−b|<e ⇒ b−e < a);
    `realAbsSubLtRightThm` ⊢ … ⇒ realLt a (realAdd b e) (|a−b|<e ⇒ a < b+e);
    `nestedUniquePointThm` ⊢ ∀a b. nestedIntervals a b ⇒ intervalLengthsToZero a b
    ⇒ ∃x. (∀n. a n ≤ x ∧ x ≤ b n) ∧ (∀y. (∀n. a n ≤ y ∧ y ≤ b n) ⇒ y = x);
    `intervalLengthsToZeroTm[a,b]`, `unfoldIntervalLengthsToZero[a,b]` (⊢ = tendsto
    (λn. realAdd (b n)(realNeg (a n))) 0); `tendstoTm`, `unfoldTendsto[a,L]` (⊢ =
    ∀e. 0<e ⇒ ∃N. ∀n. N≤n ⇒ realAbs (a n + realNeg L) < e).
  - List: `memConsThm` ⊢ ∀x y l. MEM x (CONS y l) = (x=y ∨ MEM x l); `nilConst[]`,
    `consConst[]`, `listTy[ty]`. Num: `plusTm[m,n]`, `numInductionThm`, leq lemmas.
  - Bool: `EXCLUDEDMIDDLE`, `DISJCASES`, `CONTR`, `CHOOSE`, `EXISTS`, `CONJ`,
    `CONJUNCT1`/`CONJUNCT2`, `SPEC`/`GEN`/`MP`/`DISCH`/`ASSUME`/`UNDISCH`.

## Scope

- MODIFY: `stdlib/Real/Compact.wl` (append + `::usage`), `tests/real_compact_tests.wl`
  (append). No other files, no runner lists. MUST NOT touch Kernel/Types/Terms/
  Bootstrap/bootstrap.mx/docs/SeqAux.wl/Seq.wl/codex(except report). No newAxiom,
  no new files.

## Deliverable theorems (mirror the blueprint)

1. `intervalSubsetOpenIntervalThm` ⊢ ∀left right x a b y.
   closedInterval left right x ⇒ closedInterval left right y ⇒
   realLt (realAdd right (realNeg left)) (realAdd x (realNeg a)) ⇒
   realLt (realAdd right (realNeg left)) (realAdd b (realNeg x)) ⇒
   openInterval a b y.
   Sketch: `closedIntervalMemThm` on hx → (left≤x ∧ x≤right), CONJUNCT split; on
   hy → (left≤y ∧ y≤right). **Left bound `a<y`:** `intervalPointsCloseThm` SPEC
   `{left, right, y, x, (realAdd x (realNeg a))}` (point slots swapped: x-slot:=y,
   y-slot:=x), MP the four bounds (left≤y, y≤right, left≤x, x≤right) and the length
   hyp `(right−left) < (x−a)` → `|y − x| < (x−a)`. `realAbsSubLtLeftThm` SPEC
   `{y, x, (x−a)}`, MP that → `(x − (x−a)) < y`. `realArithProve` identity
   `realAdd x (realNeg (realAdd x (realNeg a))) = a` → EQMP (via `compactRealLtCong`
   on the left arg) → `a < y`. **Right bound `y<b`:** `intervalPointsCloseThm`
   SPEC `{left,right,y,x,(realAdd b (realNeg x))}`, MP bounds + `(right−left)<(b−x)`
   → `|y−x| < (b−x)`. `realAbsSubLtRightThm` SPEC `{y,x,(b−x)}`, MP → `y < (x+(b−x))`.
   `realArithProve` identity `realAdd x (realAdd b (realNeg x)) = b` → EQMP →
   `y < b`. Fold `openInterval a b y` = `(a<y ∧ y<b)` via `openIntervalMemThm` SYM
   (EQMP). GEN the six.

2. `singletonSubcoverOfSmallIntervalThm` ⊢ ∀U left right x a b i.
   closedInterval left right x ⇒
   realLt (realAdd right (realNeg left)) (realAdd x (realNeg a)) ⇒
   realLt (realAdd right (realNeg left)) (realAdd b (realNeg x)) ⇒
   (∀y. openInterval a b y ⇒ U i y) ⇒
   finiteSubcover U (closedInterval left right).
   Sketch: `js := [i]` = `compactConsTmAt[ι, i, NIL@ι]`. Prove
   `listSubcover U (closedInterval left right) [i]`: via `unfoldListSubcover` SYM,
   build `∀y. closedInterval left right y ⇒ ∃j. MEM j [i] ∧ U j y`. Take fresh
   `yB`, ASSUME `closedInterval left right yB`; `intervalSubsetOpenIntervalThm`
   SPEC `{left,right,x,a,b,yB}` MP (hx, the two length hyps, this closed-mem) →
   `openInterval a b yB`; hinside SPEC yB MP → `U i yB`. `memConsThm` INSTTYPE ι,
   SPEC `{i,i,NIL@ι}` → `MEM i [i] = (i=i ∨ MEM i NIL)`; EQMP backward with
   `DISJ1[REFL[i], …]` → `MEM i [i]`. EXISTS j:=i: `MEM i [i] ∧ U i yB`. GEN yB /
   DISCH → the listSubcover body; EQMP SYM unfoldListSubcover → `listSubcover …[i]`.
   Then `finiteSubcover` via `unfoldFiniteSubcover` SYM + EXISTS js:=[i]. GEN the seven.

3. `compactnessPrincipleThm` (statement in Goal). Module sketch — **the big one**:
   - uV=mkVar["U",compactCoverTy]; leftV,rightV:real. ι := compactCoverIndexTy[uV].
     hLeTm=realLe left right; hOpenTm=`∀i. isOpen (U i)` (forallTm[iV, isOpenTm[
     mkComb[uV,iV]]], iV:ι); hCovTm=coversTm[U, closedInterval left right].
     goalTm := finiteSubcoverTm[U, closedInterval left right].
   - `em = EXCLUDEDMIDDLE[goalTm]`. DISJCASES:
     - **TRUE branch:** `ASSUME[goalTm]` IS the conclusion.
     - **FALSE branch:** `hNot = ASSUME[compactNotTm[goalTm]]`. Fold to bad:
       `hBadInit = EQMP[SYM unfoldNoFiniteSubcover[U,left,right], hNot]` →
       `noFiniteSubcover U left right`. Then:
       - `hBad = MP[MP[compactSpecAll[badIntervalsThm,{U,left,right}], hLe], hBadInit]`
         → ∀n. badInterval U (lower n)(upper n).
       - `hNest = MP[MP[compactSpecAll[nestedIntervalsThm,…], hLe], hBadInit]`.
       - `hLen = MP[MP[compactSpecAll[lengthsToZeroThm,…], hLe], hBadInit]`
         → intervalLengthsToZero (lower)(upper).
       - `pt = MP[MP[compactSpecAll[nestedUniquePointThm,{lowerTm[…],upperTm[…]}],
         hNest], hLen]` → ∃x. (∀n. lower n ≤ x ∧ x ≤ upper n) ∧ uniqueness. CHOOSE
         `xPt` (distinctive name), `hPt` its body; `hxAll = CONJUNCT1[hPt]`
         (∀n. lower n ≤ xPt ∧ xPt ≤ upper n).
       - `hx0 = SPEC[0, hxAll]` → lower…0 ≤ xPt ∧ xPt ≤ upper…0; rewrite endpoints
         with `compactLowerZeroEq`/`compactUpperZeroEq` (congruence via
         `compactRealLeCong` on each conjunct) → left ≤ xPt ∧ xPt ≤ right; fold
         `closedInterval left right xPt` (EQMP SYM closedIntervalMemThm).
       - covers: `hCovBody = EQMP[unfoldCovers[U, closedInterval left right],
         ASSUME hCovTm]`; SPEC xPt, MP hx0 → ∃i. U i xPt. CHOOSE `iIdx`, `hUi`.
       - open: `hOpenI = SPEC[iIdx, ASSUME hOpenTm]` → isOpen (U iIdx);
         `EQMP[unfoldIsOpen[mkComb[U,iIdx]], hOpenI]` → ∀x. U iIdx x ⇒ ∃l r. …;
         SPEC xPt, MP hUi → ∃aO bO. aO<xPt ∧ xPt<bO ∧ ∀y. openInterval aO bO y ⇒
         U iIdx y. CHOOSE `aOpen`, CHOOSE `bOpen`, `hOB`. Split (nested CONJUNCT):
         hax=aOpen<xPt, hxb=xPt<bOpen, hinside=∀y. openInterval aOpen bOpen y ⇒ U iIdx y.
       - gaps: gapL := realAdd xPt (realNeg aOpen); gapR := realAdd bOpen (realNeg xPt).
         `hGapL = realArithProve[realLt 0 gapL]`-from-hax — actually feed hax as ⇒:
         use `realArithProve[ aOpen<xPt ⇒ 0<gapL ]` then MP hax (gapL,aOpen,xPt linear).
         Similarly hGapR.
       - tendsto: `tLen = EQMP[unfoldIntervalLengthsToZero[lowerTm,upperTm], hLen]`
         → tendsto (λn. upper n − lower n) 0; `tBody = EQMP[unfoldTendsto[<that λ>,0],
         tLen]` → ∀e. 0<e ⇒ ∃N. ∀n. N≤n ⇒ |(λ…)(n) + realNeg 0| < e. **The `(λ…)(n)`
         is an unreduced redex — keep it; you will SPEC n:=K and `compactBetaClean`
         to get `(upper K − lower K) + realNeg 0`.**
       - `gotL = MP[SPEC[gapL, tBody], hGapL]` → ∃NL. ∀n≥NL. |(λ)(n)+−0|<gapL.
         CHOOSE `bigNL`, hNL. `gotR` similarly → CHOOSE `bigNR`, hNR.
       - K := plusTm[bigNL, bigNR]. `hNLK = arithProve[∀a b. a ≤ a+b]`-SPEC'd → bigNL≤K;
         `hNRK = arithProve[∀a b. b ≤ a+b]`-SPEC'd → bigNR≤K (build the ∀ goal with
         plusTm + compactNatLe, prove with arithProve, SPEC {bigNL,bigNR}).
       - `hCloseL0 = MP[SPEC[K, hNL], hNLK]` → |(λ)(K)+−0|<gapL; `compactBetaClean`
         (or APTERM β on the `(λ)(K)`) → `|(upper K − lower K)+−0| < gapL`. Same for R.
       - `hOrdK = compactIntervalOrderAt[U,left,right, hLe, hBadInit, K]` → lower K ≤ upper K.
       - `hLenL = MP[MP[compactSpecAll[lengthLtOfCloseThm,{compactLowerAt[…K],
         compactUpperAt[…K], gapL}], hOrdK], hCloseL]` → (upper K − lower K) < gapL
         = (upper K − lower K) < (xPt − aOpen). `hLenR` similarly < (bOpen − xPt).
       - `hxK = SPEC[K, hxAll]` → lower K ≤ xPt ∧ xPt ≤ upper K; fold
         `closedInterval (lower K)(upper K) xPt` (EQMP SYM closedIntervalMemThm).
       - `hSmall = MP[MP[MP[MP[compactSpecAll[singletonSubcoverOfSmallIntervalThm,
         {U, lowerAtK, upperAtK, xPt, aOpen, bOpen, iIdx}], hxK], hLenL], hLenR],
         hinside]` → finiteSubcover U (closedInterval (lower K)(upper K)).
       - `hBadK = SPEC[K, hBad]`; `EQMP[unfoldBadInterval[U, lowerAtK, upperAtK],
         hBadK]` → (lower K ≤ upper K) ∧ noFiniteSubcover U (lower K)(upper K);
         CONJUNCT2 → noFiniteSubcover; `EQMP[unfoldNoFiniteSubcover[U,lowerAtK,upperAtK],
         that]` → ¬finiteSubcover U (closedInterval (lower K)(upper K)).
       - `absurd = MP[that ¬, hSmall]` (⊢ F). `falseBranch = CONTR[goalTm, absurd]`.
         **Discharge ALL the local hyps** that CHOOSE/ASSUME introduced so the
         DISJCASES branch has only `compactNotTm[goalTm]` left (CHOOSE auto-discharges
         its witness hyp; covers/open `ASSUME hCovTm`/`ASSUME hOpenTm` are the
         theorem's own hyps, kept till the final DISCH).
   - `point = DISJCASES[em, ASSUME[goalTm], falseBranch]`.
   - GEN U/left/right + DISCH hLeTm + DISCH hOpenTm + DISCH hCovTm.

## Stop-loss / graded delivery (capstone brief)

Tier 1 (must): (1) `intervalSubsetOpenIntervalThm`. Tier 2: (2)
`singletonSubcoverOfSmallIntervalThm`. Tier 3: (3) `compactnessPrincipleThm`. If a
tier stalls (same failure twice), deliver the green lower tiers and STOP with a
precise report (theorem + exact thrown payload). A loadable subset is fully
acceptable — do NOT thrash. Likeliest sticking points: the abs-orientation SPEC in
(1); the iota-list NIL/`[i]` + memConsThm INSTTYPE in (2); in (3) the CHOOSE
witness hygiene (distinctive names `xPt`/`iIdx`/`aOpen`/`bOpen`/`bigNL`/`bigNR` so
no GEN/SPEC term recaptures them) and the tendsto-lambda β at K. If (3)'s
contradiction assembly fights an ABS "binder occurs free in hyps", suspect a
witness leaked into the hyp set — CHOOSE it earlier / give it a distinctive name.

## Tests (append ~6 asserts to tests/real_compact_tests.wl)

- (1)/(2)/(3) conclusion shape after GEN/DISCH (aconv against built expected
  terms): (1) `openInterval a b y` under 4 hyps; (2) `finiteSubcover U
  (closedInterval left right)` under 4 hyps; (3) `finiteSubcover U (closedInterval
  left right)` under the 3 hyps. Use `isThm` + shallow concl/hyp probes where full
  instantiation is heavy. aconv against folder builders; no deep MatchQ. **NO
  `testExit[]`** — end the file with the last `runTests[...]`.

## WL / project pitfalls (read twice)

1. No `_` idents (Module locals too). 2. comments close at first `*)`. 3. in-file
Compact privates + snapshot publics reachable; wrong-context symbol stays
UNEVALUATED → fails far below. 4. **HOL var identity=(name,type)** — every CHOOSE
witness and per-branch binder gets a DISTINCTIVE name (`xPt`,`iIdx`,`aOpen`,
`bOpen`,`bigNL`,`bigNR`,`yB`), NEVER bare `x/a/b/i/n` that a SPEC'd term carries
(this is THE risk in (3); a leaked witness → ABS "binder occurs free in
hypotheses"). 5. holError HoldRest. 6. dev.wls verifier (below). 7. aconv tests,
no deep MatchQ, **no testExit**. 8. mkVar/mkConst/mkComb/mkAbs only. 9. **Narrow
probes** — Compact.wl is load-heavy; localize a load throw by per-theorem `isThm`,
do NOT dump terms. 10. No Return in Do/For/While. 11. **realArithProve is LINEAR**
— use it ONLY for: the `x−(x−a)=a` / `x+(b−x)=b` identities in (1), the `a<x ⇒
0<x−a` gap-positivity in (3); everything abs/order-structural is the SeqAux/Seq
lemmas. 12. **iota polymorphism** — build CONS/NIL/MEM at `compactCoverIndexTy[U]`
(reuse `compactConsTmAt`/`compactMemTmAt`); INSTTYPE `memConsThm`/`nilConst` to ι.
13. **tendsto λ at K** — after SPEC n:=K the `a n` is `(λn. upper n − lower n) K`,
an unreduced redex; `compactBetaClean` it before feeding `lengthLtOfCloseThm`. 14.
`CONTR[goalTm, falseThm]` gives the goal from `⊢ F`; the FALSE DISJCASES branch
must end at `goalTm` with hyp set = {¬goalTm} ∪ {hCovTm,hOpenTm,hLeTm} only.

## Verification (MANDATORY — you run wolframscript)

Full machine access. Both frontier files named (dependency order) or dev.wls hits
its staleness guard:

```
wolframscript -file tests/dev.wls stdlib/Real/SeqAux.wl stdlib/Real/Compact.wl real_compact
```

Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste the
final `passed: N  failed: 0` line verbatim. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other command,
nothing outside the repo, no network. Same failure twice → deliver the loadable
subset (per the tiers) + report exactly where it broke. If dev.wls reports a stale
snapshot for some OTHER file, STOP and report (do not rebuild).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls
  verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. How you handled: the abs-orientation SPEC in (1), the iota `[i]`/memConsThm in
   (2), and the CHOOSE-witness hygiene + tendsto-λ β in (3).
4. The exact final `passed: N  failed: 0` from your dev.wls run.
5. Which theorems (by tier) fully proven vs stopped.
6. Open questions (empty if none).
