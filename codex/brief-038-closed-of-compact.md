# Brief 038 — M8.6 compact ⇒ closed (append to Real/CompactSet.wl)

## Goal

Prove the LAST and heaviest open-cover consumer direction `compact ⇒ closed`. Append to
`Real/CompactSet.wl`: a `half` helper (+ positivity + doubling), the analytic core
`puncturedMemFarThm` (a point in the punctured interval around c is ≥ its radius away from
x), the punctured cover `compactClosedCover x`, a list-induction `puncturedRadiusThm`
(a finite subcover of the punctured cover keeps S a uniform distance δ>0 from x), and
**`closedOfCompactThm`** (`isCompact S ⇒ isClosed S`). Append ~1 assert to
`tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate to green. (The two iffs
come in a separate brief — do NOT attempt them here.)

## Blueprint (in-repo)

`tautology-ref/Tautology/RealCompactness/HeineBorel.lean` `closed_of_compact` (340) +
`compactClosedCover` (152) + `compactClosedRadius` (162) + `compactClosedRadius_pos` (171) +
`compactClosedRadius_le_half_dist_of_mem` (185). We replace the ULift-indexed
`compactClosedRadius` fold + member lemmas with a SINGLE list induction
`puncturedRadiusThm` threading `∃δ. 0<δ ∧ (y in ⋃Vs ⇒ δ ≤ |y−x|)` (min at each CONS) —
exactly the `boundedOfFiniteIntervalCoverThm` pattern (brief-037, in this file).

## The math (read once)

To show `compl S` open at a point x with `¬S x`: cover S by punctured intervals around each
other point, `compactClosedCover x = λV. ∃c. ¬(c=x) ∧ V = openInterval (c − r_c)(c + r_c)`
with radius `r_c = half |c−x|` (`half t = t · realInv 2`). Each y∈S (y≠x since x∉S) sits in
its own member (c:=y, r_y>0). Compactness ⇒ a finite subcover Vs. δ := the min member radius
(>0). Then `(x−δ, x+δ) ∩ S = ∅`: if y∈S∩(x−δ,x+δ), y∈ some V=openInterval(c−r_c)(c+r_c)∈Vs,
so |y−c|<r_c and |y−x|<δ≤r_c; triangle `|c−x| ≤ |c−y|+|y−x| < r_c+r_c = 2·r_c = |c−x|` —
contradiction. So x has neighborhood (x−δ,x+δ) ⊆ compl S.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- CompactSet.wl is FRONTIER. dev.wls names Connected.wl, Topology.wl, CompactSet.wl (that
  order). Append to the END (before `End[]; EndPackage[];`) + `::usage` lines.
- **Reuse by bare name (append inside this file's `` `Private` ``):** all `cset*` builders;
  esp. `csetRealAdd`(=realAddTm)/`csetRealNeg`/`csetRealMul`(=realMulTm)/`csetRealAbs`/
  `csetRealLe`/`csetRealLt`/`csetRealInv`/`csetOneReal[]`/`csetRnumNat[n]`(=&ℝ(&ℚ(&ℤ n)))/
  `csetForallTm`/`csetExistsTm`/`csetConjTm`/`csetImpTm`/`csetNotTm`/`csetSetApp`/`csetSetMem`/
  `csetSetAppV`/`csetOpenIntervalSet[a,b]`/`csetSpecAll`/`csetApplyDef`/`csetBetaClean`/
  `csetForallList`/`csetMemTmAt`/`csetNilAt[]`/`csetConsTmAt`/`csetRealLtCong`/`csetRealLeCong`/
  `csetRealAbsCong`; types `csetSetTy`/`csetSetOfSetsTy`/`csetSetListTy`/`csetRealTy`.
  Templates in-file: `boundedOfFiniteIntervalCoverThm` (THE list-induction template — copy
  its shape), `centerCover*`/`boundedOfCompactThm` (cover-def + isCompact-consumer plumbing),
  `closedOfSequentiallyCompactThm` (isClosed/compl/isOpen fold — but here we build it the
  OTHER way; see below), `memFilterThm` (`listInductionThm` two hyps CONJOINED).
- LCF-style: cannot make a false theorem; the suite decides.

## Reuse (VERIFIED — snapshot + frontier Topology + this file)

- **This file (PUBLIC):** `isCompactTm[S]`/`unfoldIsCompact[S]`; `setCoversTm`/`unfoldSetCovers`;
  `setListSubcoverTm`/`unfoldSetListSubcover`; `setFiniteSubcoverTm`/`unfoldSetFiniteSubcover`;
  `isOpenTm`/`openIntervalIsOpenThm`; `centerCover`-style def idiom. Reachable file-private:
  `seqRealInvPositiveThm` (⊢ ∀x. realLt 0 x ⇒ realLt 0 (realInv x) — grep to confirm exact),
  `seqArithPosNeZeroThm` (⊢ ∀x. realLt 0 x ⇒ ¬(x = 0)) — both already USED in this file.
- **Topology.wl (frontier, PUBLIC):** `complTm[S]`/`complMemThm` (⊢ ∀S x. compl S x = ¬(S x));
  `isClosedTm[S]`/`unfoldIsClosed[S]` (⊢ isClosed S = isOpen (compl S)).
- **Compact.wl (snapshot, PUBLIC):** `isOpenTm[U]`/`unfoldIsOpen[U]` — isOpen body is
  `∀x. U x ⇒ ∃l r. realLt l x ∧ (realLt x r ∧ ∀y. openInterval l r y ⇒ U y)`;
  `openIntervalTm[l,r,x]`/`unfoldOpenInterval`; `closedIntervalConst[]`.
- **Abs.wl (snapshot, PUBLIC):** `realAbsTriangleThm` (⊢ ∀x y. |x+y| ≤ |x|+|y|), `realAbsNegThm`
  (⊢ |−x| = |x|), `realNeAbsPosThm` (Seq, ⊢ ∀x. ¬(x=0) ⇒ 0 < |x|).
- **Mul/Inv (snapshot, PUBLIC):** `realLtMulPosThm` (0<x⇒0<y⇒0<x·y), `realMulInvThm`
  (¬(x=&ℝ0) ⇒ x·realInv x = &ℝ1), `realMulOneThm`, `realMulCommThm`, `realMulAssocThm`.
- **Order:** `realLtImpLeThm`, `realLeTransThm`, `realLtLeTransThm`, `realLeLtTransThm`,
  `realLtTransThm`, `realNotLeLtThm`/`realLtNotLeThm` (Cut), `realLtIrreflThm`. **MinMax:**
  `realMinLeLeftThm`/`realMinLeRightThm`, `realMinLeCaseThm` (⊢ x≤y ⇒ min x y = x),
  `realMinGtCaseThm` (⊢ ¬(x≤y) ⇒ min x y = y), `realMinConst[]`. **realArithProve** (LINEAR —
  the `a+a = 2·a` doubling, `(c−y)+(y−x) = c−x`, `c−x = −(x−c)`, `x−δ<x`/`x<x+δ` from 0<δ,
  `0<a ⇒ 0<b ⇒ 0<min`-style is NOT linear — see (T0)). **Num:** `selectOfExists`.

## Scope

- MODIFY: `stdlib/Real/CompactSet.wl` (append + `::usage`),
  `tests/real_compactset_tests.wl` (append). No other files, NO runner lists, NO new imports.
  MUST NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/
  Topology/docs/codex(except report). No newAxiom, no new files.

## Deliverable (append in this order)

Builders: `csetTwoReal[] = csetRnumNat[SUC(SUC 0)]` (&ℝ2; SUC/0 = `HOL`Stdlib`Num`sucConst[]`/
`zeroConst[]`). `csetHalf[tT] = csetRealMul[tT, csetRealInv[csetTwoReal[]]]` (t·inv2).
`csetSub[aT,bT] = csetRealAdd[aT, csetRealNeg[bT]]` (a−b). `csetDist[aT,bT] =
csetRealAbs[csetSub[aT,bT]]` (|a−b|). `csetPunctured[cT,xT] = csetOpenIntervalSet[
csetSub[cT, csetHalf[csetDist[cT,xT]]], csetRealAdd[cT, csetHalf[csetDist[cT,xT]]]]`
(= openInterval (c − half|c−x|)(c + half|c−x|)).

**(T0) half + analytic core:**
- `csetTwoNeZeroThm` ⊢ ¬(&ℝ2 = &ℝ0) (via `seqArithPosNeZeroThm` MP `0<&ℝ2` — `0<&ℝ2` from
  the rnum order chain or `realArithProve`). `halfPosThm` ⊢ ∀t. realLt 0 t ⇒ realLt 0
  (half t) (`realLtMulPosThm` with 0<t and 0<inv2; 0<inv2 from `seqRealInvPositiveThm` MP
  0<&ℝ2). `halfDoubleThm` ⊢ ∀t. realAdd (half t) (half t) = t: `half t + half t = 2·(half t)`
  (`realArithProve` ∀a. a+a = 2·a, a:=half t opaque) = `2·(t·inv2)`; rearrange
  `2·(t·inv2) = t·(2·inv2)` (realMulComm/Assoc); `2·inv2 = &ℝ1` (`realMulInvThm` at &ℝ2 via
  csetTwoNeZero — NOTE realMulInv gives `x·realInv x`, so `&ℝ2 · inv2 = 1`); `t·1 = t`
  (realMulOne). Chain via TRANS.
- **`puncturedMemFarThm`** ⊢ ∀c x y. ¬(c = x) ⇒ openInterval (c − half|c−x|)(c + half|c−x|) y
  ⇒ realLe (half |c−x|) (realAbs (y − x)).  [the analytic core]
  GEN c x y; DISCH `hNe`, DISCH `hMem`. Let d = |c−x|, r = half d. `0<d` (`realNeAbsPosThm`
  with `¬(c−x = 0)` from hNe via realArithProve `¬(c=x) ⇒ ¬(c−x=0)` — or
  `realArithProve[¬(c=x) ⇒ ¬(realAdd c (realNeg x) = 0)]`). `0<r` (halfPos MP 0<d).
  From hMem (`unfoldOpenInterval`): `c−r < y ∧ y < c+r` ⇒ `|y−c| < r`
  (`realAbsSubLtThm` SPEC {y, c, r}: needs `c + −r < y` and `y < c + r` — exactly the bounds).
  Goal `r ≤ |y−x|`: CCONTR — ASSUME `¬(r ≤ |y−x|)` → `|y−x| < r` (`realNotLeLtThm`). Triangle:
  `realAbsTriangleThm SPEC {c−y, y−x}` → `|(c−y)+(y−x)| ≤ |c−y| + |y−x|`; rewrite
  `(c−y)+(y−x) = c−x` (realArith APTERM under realAbs) → `|c−x| ≤ |c−y| + |y−x|`; `|c−y| =
  |y−c|` (realAbsNeg: c−y = −(y−c), realArith) so `|c−y| < r`; `|c−x| ≤ |c−y|+|y−x| < r+r`
  (add two strict `<r` — `realLtAddMono`-style, or `realLeLtTrans` + `realLtAddMono2`; the
  `|c−y|+|y−x| < r+r` from `|c−y|<r` ∧ `|y−x|<r` is realArith-LINEAR with the two as opaque
  atoms); `r+r = d = |c−x|` (halfDouble at d); so `|c−x| < |c−x|` (realLeLtTrans + the eq) —
  `realLtIrreflThm` → False. CCONTR closes `r ≤ |y−x|`.

**(T1) cover:**
- `compactClosedCoverDefThm` ⊢ compactClosedCover = (λx. λV. ∃c. ¬(c=x) ∧ V = openInterval
  (c − half|c−x|)(c + half|c−x|)). Type `real → (real→bool) → bool`. Export
  `compactClosedCoverConst[]`/`compactClosedCoverTm[x]` (a set-of-sets) /
  `compactClosedCoverMemThm` ⊢ ∀x V. compactClosedCover x V = (∃c. ¬(c=x) ∧ V =
  csetPunctured c x). Distinctive binders `cCcc`/`vCcc`/`xCcc`.
- `compactClosedCoverOpenThm` ⊢ ∀x V. compactClosedCover x V ⇒ isOpen V. (mem EQMP → ∃c.
  ¬(c=x) ∧ V = punctured; CHOOSE c; CONJUNCT2 (V = openInterval…); `openIntervalIsOpenThm`
  SPEC + EQMP `APTERM[isOpenConst[], SYM]`.)
- `compactClosedCoverCoversThm` ⊢ ∀S x. ¬(S x) ⇒ setCovers (compactClosedCover x) S.
  (DISCH ¬(S x); target ∀y. S y ⇒ ∃V. compactClosedCover x V ∧ V y; GEN y DISCH (S y);
  `¬(y = x)` (else S x from S y by rewrite, contra ¬S x — realArith-free: `y=x ⇒ S y = S x`
  via APTERM, EQMP); V := `csetPunctured[y, x]`; member: EXISTS c:=y into the mem body
  (¬(y=x) ∧ V = openInterval(y−half|y−x|)(y+half|y−x|) by REFL); `V y`: `0<|y−x|`
  (realNeAbsPos) → `0<half|y−x|` (halfPos) → `y−half|y−x| < y ∧ y < y+half|y−x|` (realArith
  with half|y−x| opaque-positive: `0<h ⇒ y−h<y ∧ y<y+h`) → openInterval…y. EXISTS V; CONJ.)

**(T2) `puncturedRadiusThm`** ⊢ ∀x Vs. (∀V. MEM V Vs ⇒ compactClosedCover x V) ⇒
∃δ. realLt 0 δ ∧ ∀y. (∃V. MEM V Vs ∧ V y) ⇒ realLe δ (realAbs (y − x)).
  **List induction on Vs** (copy `boundedOfFiniteIntervalCoverThm` shape; CONJ[base,step] MP;
  the `x` is GEN'd OUTSIDE the induction, the predicate is over Vs only).
  - base (NIL): δ := &ℝ1, `0<&ℝ1` (realArithProve); ∀y. (∃V. MEM V NIL ∧ V y) ⇒ …: the ∃ is
    false (memNil) → CONTR.
  - step (CONS V0 rest): IH (β-reduced) MP `hRest` (∀V. MEM V rest ⇒ ccc x V, derived from
    hAll via memCons DISJ2) → `∃δ. 0<δ ∧ …`; CHOOSE δ' (`dRest`), hRestPair; `0<δ'`,
    `hRestFar`. `compactClosedCover x V0` (memCons refl → MEM V0; hAll MP); mem EQMP → ∃c.
    ¬(c=x) ∧ V0 = punctured; CHOOSE c0 (`cStep`), hNe, hV0eq. r0 := `csetHalf[csetDist[c0,x]]`,
    `0<r0` (realNeAbsPos ¬(c0−x=0) → 0<|c0−x| → halfPos). δ := `realMin r0 δ'`; `0<δ`
    (`realMin r0 δ' = r0` or `δ'`, both >0: EM on `realLe r0 δ'`; realMinLeCase/GtCase rewrite;
    DISJCASES). EXISTS δ; GEN y DISCH `∃V. MEM V (V0:rest) ∧ V y`; CHOOSE V hVy; memCons →
    V=V0 ∨ MEM V rest; DISJCASES:
      · V=V0: V y → V0 y → punctured y (hV0eq rewrite); `puncturedMemFarThm SPEC {c0,x,y} MP
        hNe MP (the punctured-mem)` → `r0 ≤ |y−x|`. δ=min r0 δ' ≤ r0 (realMinLeLeft) ≤ |y−x|
        (realLeTrans). 
      · MEM V rest: EXISTS V into (∃V. MEM V rest ∧ V y); hRestFar MP → `δ' ≤ |y−x|`. δ ≤ δ'
        (realMinLeRight) → δ ≤ |y−x| (realLeTrans).
    CHOOSE-discharge c0, V, δ'.

**(T3) `closedOfCompactThm`** ⊢ ∀S. isCompact S ⇒ isClosed S.
  GEN S; DISCH `hCompact`. Build inner `openAll : ⊢ ∀x. compl S x ⇒ <isOpen-body of compl S
  at x>` (the body = `∃a b. a<x ∧ (x<b ∧ ∀y. openInterval a b y ⇒ compl S y)` — build it to
  mirror `compactIsOpenBody`, like `closedOfSequentiallyCompactThm`'s `csetNeighGoal`; if a
  late EQMP rejects on aconv, EXTRACT from `concl[unfoldIsOpen[complTm[S]]][[2]]`):
  - GEN x; DISCH `hComplX = compl S x`; `hNotSx = complMem[S,x] EQMP hComplX` → ¬(S x).
  - `cover = compactClosedCoverTm[x]`. `openSC = unfoldIsCompact[S] EQMP hCompact`;
    `finite = openSC SPEC cover MP (compactClosedCoverOpenThm SPEC-x partial — it is ∀x V, so
    GEN V form) MP (compactClosedCoverCoversThm SPEC {S,x} MP hNotSx)` → `setFiniteSubcover
    cover S`. (For the `∀V. cover V ⇒ isOpen V` hypothesis: `compactClosedCoverOpenThm` is
    `∀x V. … ⇒ isOpen V`; SPEC x then it's `∀V. cover V ⇒ isOpen V` — GEN-ready.)
  - `unfoldSetFiniteSubcover` EQMP → ∃Vs. setListSubcover cover S Vs; CHOOSE Vs (`vsClosed`);
    `unfoldSetListSubcover` EQMP → CONJ; `hMemCover = CONJUNCT1` (∀V. MEM V Vs ⇒ cover V),
    `hCovS = CONJUNCT2` (∀y. S y ⇒ ∃V. MEM V Vs ∧ V y).
  - `puncturedRadiusThm SPEC {x, Vs} MP hMemCover` → ∃δ. 0<δ ∧ ∀y. (∃V. MEM V Vs ∧ V y) ⇒
    δ ≤ |y−x|; CHOOSE δ (`deltaClosed`); `hDpos = CONJUNCT1` (0<δ), `hFar = CONJUNCT2`.
  - a := `csetSub[x, deltaClosed]` (x−δ), b := `csetRealAdd[x, deltaClosed]` (x+δ). `a<x`
    (realArith from 0<δ), `x<b` (realArith). `∀y. openInterval a b y ⇒ compl S y`: GEN y DISCH
    (openInterval(x−δ)(x+δ) y); `unfoldOpenInterval` → `x−δ<y ∧ y<x+δ` ⇒ `|y−x|<δ`
    (`realAbsSubLtThm` SPEC {y,x,δ}: `x+−δ<y` ∧ `y<x+δ`). `compl S y` = `¬(S y)`: ASSUME (S y)
    for CCONTR; `hCovS SPEC y MP (S y)` → ∃V. MEM V Vs ∧ V y; `hFar SPEC y MP that` → `δ ≤
    |y−x|`; with `|y−x|<δ` → `δ<δ` (realLeLtTrans) → realLtIrrefl False; CCONTR/NOTINTRO →
    ¬(S y); fold to `compl S y` (SYM complMem EQMP).
  - EXISTS a, b into the isOpen-body; fold; CHOOSE-discharge Vs, δ. `openCompl =
    SYM unfoldIsOpen[complTm[S]] EQMP openAll` → isOpen (compl S); `SYM unfoldIsClosed[S] EQMP`
    → isClosed S. GEN S, DISCH hCompact.

## Stop-loss / graded delivery

Tier 0: half + `puncturedMemFarThm` (the analytic core — the riskiest; triangle + half-double).
Tier 1: cover def + open + covers. Tier 2: `puncturedRadiusThm` (list induction, reuses T0).
Tier 3: `closedOfCompactThm` (assembly). If a tier stalls (same failure twice — most likely
T0's half-double / triangle chain, or T3's isOpen-body aconv), deliver the green tiers + STOP
with a precise report (sub-goal, payload, terms compared). Tier 0+1+2 green WITHOUT Tier 3 is
still useful progress. Never fake a green count.

## Tests (append ~1 assert)

- `closedOfCompact`: aconv `forall S. isCompact S ⇒ isClosed S` (`isCompactTm`/`isClosedTm`
  public). Optionally `puncturedMemFar` isThm + shallow. No deep MatchQ. **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. append INSIDE `` `Private` `` — cset*
   reachable bare; cross-file must be PUBLIC. New PUBLIC names FREE (grep):
   `half`/`compactClosedCover`/`puncturedMemFar`/`puncturedRadius`/`closedOfCompact`. 4. HOL
   var identity: distinctive binders/witnesses (`cCcc`/`cStep`/`cOpen`/`dRest`/`deltaClosed`/
   `vsClosed`/`yFar`), NEVER bare `c/x/y/V/Vs/δ`. 5. holError HoldRest. 6. dev.wls only
   verifier. 7. aconv tests, no deep MatchQ, NO testExit. 8. mkVar/mkConst/mkComb/mkAbs only;
   `&ℝ2` = `csetRnumNat[SUC(SUC 0)]`. 9. narrow probes. 10. No Return in Do/For/While. 11.
   **`listInductionThm`'s two hyps are CONJOINED (`P NIL ∧ step`) — `MP[induction, CONJ[base,
   step]]`; the IH hyp is the REDEX `predLam rest` (β-reduce to use, fold CONS conclusion back
   via SYM BETACONV — copy `boundedOfFiniteIntervalCoverThm`).** 12. **β**: csetBetaClean all
   cover/punctured/half applications + the induction redexes. 13. realArithProve is LINEAR:
   the `a+a=2a`, `(c−y)+(y−x)=c−x`, `c−x=−(x−c)`, `0<h⇒y−h<y∧y<y+h`, `0<δ⇒x−δ<x`, the
   `p<r ∧ q<r ⇒ p+q < r+r` (p,q,r opaque atoms) are all linear; the `2·inv2=1` / half-double
   product steps are NOT (realMulInv by hand). `0<min` is NOT realArith — do it by EM on
   `realLe r0 δ'` + realMinLeCase/GtCase. 14. set-of-sets ops RAW lambdas; `c−x` =
   `csetSub[c,x]` = `csetRealAdd[c, csetRealNeg[x]]`.

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
stopped); `Syntax::sntx`+line = bracket/quote typo; `failed:K` with FAIL = aconv mismatch; an
`MP` "equation LHS" error on the induction = the CONJOINED-hyp shape (pitfall 11) or a
redex/β-normal divergence (pitfall 12); a realArithProve throw = a nonlinear goal you must
hand-prove (pitfall 13).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did not reach
  it, say so explicitly — do NOT claim green without the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (reused symbol → file:line; new public names confirmed free;
   `seqRealInvPositiveThm`/`seqArithPosNeZeroThm`/`realAbsSubLtThm` → file:line).
3. How T0 (half-double + triangle) and T3 (isOpen-body aconv) went.
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped.
6. Open questions (empty if none).
