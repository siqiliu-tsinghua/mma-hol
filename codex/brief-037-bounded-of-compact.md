# Brief 037 — M8.6 compact ⇒ bounded (append to Real/CompactSet.wl)

## Goal

Prove the open-cover CONSUMER direction `compact ⇒ bounded`. Append to
`Real/CompactSet.wl`: the unit-radius center cover, a list-induction lemma
`boundedOfFiniteIntervalCoverThm` (a finite list of unit open intervals is bounded), and
**`boundedOfCompactThm`** (`isCompact S ⇒ setBounded S`). Append ~1 assert to
`tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint (in-repo)

`tautology-ref/Tautology/RealCompactness/HeineBorel.lean` `bounded_of_compact` (308): cover
by `U c = OpenInterval (c−1) (c+1)` indexed by reals; the finite subcover's centers give
`finiteLower`/`finiteUpper` bounds. We do NOT port the ULift-indexed `finiteLower`/`finite
Upper` fold + two member lemmas — instead a SINGLE list induction
`boundedOfFiniteIntervalCoverThm` threads the `∃lo hi` directly (min/max at each CONS).

## Plan (the design — read once)

Cover S with the set-of-sets `centerCover = λV. ∃c. V = openInterval (c + −1) (c + 1)`.
Every x∈S lies in `openInterval (x−1)(x+1)` (a member). `isCompact S` ⇒ a finite sublist Vs
of centerCover members covering S. A finite list of unit open intervals is bounded (induction
below), and S ⊆ ⋃Vs, so S is bounded. Center recovery: under `centerCover V`, the witness
`@c. V = openInterval(c−1)(c+1)` reconstructs the interval (no injectivity needed —
`selectOfExists`, exactly the `unboundedEscapePoint`/`nearClosedPoint` idiom).

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- CompactSet.wl is FRONTIER. Frontier files: Connected.wl, Topology.wl, CompactSet.wl —
  dev.wls names ALL THREE (that order). Append to the END (before `End[]; EndPackage[];`) +
  `::usage` lines.
- **Reuse by bare name (you append inside this file's `` `Private` ``):** all `cset*`
  builders incl. `csetForallTm`/`csetExistsTm`/`csetConjTm`/`csetImpTm`/`csetOrTm`/
  `csetSetApp`/`csetRealLe`/`csetRealLt`/`csetRealAdd` (= realAddTm) /`csetRealNeg`/
  `csetSpecAll`/`csetApplyDef`/`csetBetaClean`/`csetForallList`/`csetSetMem`/`csetSetAppV`/
  `csetOneReal[]` (= &ℝ1)/`csetOpenIntervalSet[a,b]` (= openInterval a b, a SET)/
  `csetMemTmAt[ty,x,xs]`/`csetNilAt[]`/`csetConsTmAt[h,t]`/`csetMemConstAt[ty]`; types
  `csetSetTy`/`csetSetOfSetsTy`/`csetSetListTy`/`csetRealTy`. Templates in-file:
  `memFilterThm` (list induction via `listInductionThm` whose two hyps are CONJOINED
  `P NIL ∧ step`, NOT curried — bit me; use `MP[induction, CONJ[base, step]]`),
  `nearClosedPoint*` (select-def + `selectOfExists` spec idiom), `closedIntervalSetCompactThm`
  /`compactOfClosedBoundedThm` (set-cover plumbing: `unfoldSetCovers`/`unfoldIsCompact`/
  `unfoldSetFiniteSubcover`/`unfoldSetListSubcover`).
- LCF-style: cannot make a false theorem; the suite decides.

## Reuse (VERIFIED — snapshot + this file)

- **This file (PUBLIC):** `isCompactTm[S]`/`unfoldIsCompact[S]`; `setCoversTm[C,S]`/
  `unfoldSetCovers`; `setListSubcoverTm[C,S,Vs]`/`unfoldSetListSubcover`;
  `setFiniteSubcoverTm[C,S]`/`unfoldSetFiniteSubcover`; `setBoundedTm[S]`/`unfoldSetBounded`
  (⊢ setBounded S = ∃lo hi. ∀x. S x ⇒ lo≤x ∧ x≤hi); `isOpenTm`; `openIntervalIsOpenThm`
  ⊢ ∀l r. isOpen (openInterval l r); `memFilterThm`.
- **Compact.wl (snapshot, PUBLIC):** `openIntervalTm[l,r,x]`/`unfoldOpenInterval[l,r,x]`
  (⊢ openInterval l r x = (l<x ∧ x<r)); `closedIntervalConst[]`.
- **MinMax.wl (snapshot, PUBLIC):** `realMinLeLeftThm` (⊢ ∀x y. realMin x y ≤ x),
  `realMinLeRightThm` (≤ y), `realLeMaxLeftThm` (⊢ ∀x y. x ≤ realMax x y), `realLeMaxRightThm`
  (y ≤ …), `realMinConst[]`/`realMaxConst[]`.
- **Order (snapshot, PUBLIC):** `realLtImpLeThm`, `realLeTransThm`, `realLeLtTransThm`,
  `realLtLeTransThm`; `realArithProve` (LINEAR — `x−1<x`, `x<x+1`).
- **List.wl (snapshot, PUBLIC):** `listInductionThm` (two hyps CONJOINED), `memNilThm`/
  `memConsThm`; consts `memConst[]` (build via `csetMemTmAt`). **Num:** `HOL`Stdlib`Num`
  selectOfExists[predLam, exThm]`.

## Scope

- MODIFY: `stdlib/Real/CompactSet.wl` (append + `::usage`),
  `tests/real_compactset_tests.wl` (append). No other files, NO runner lists, NO new imports.
  MUST NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/
  Topology/docs/codex(except report). No newAxiom, no new files.

## Deliverable (append in this order)

Builders: `csetSubOne[xT] = csetRealAdd[xT, csetRealNeg[csetOneReal[]]]` (x−1),
`csetAddOne[xT] = csetRealAdd[xT, csetOneReal[]]` (x+1),
`csetUnitInterval[cT] = csetOpenIntervalSet[csetSubOne[cT], csetAddOne[cT]]`
(= openInterval (c−1)(c+1)).

1. **`centerCoverDefThm`** ⊢ centerCover = (λV. ∃c. V = openInterval (c + −1) (c + 1)).
   `centerCover : (real→bool)→bool`. Export `centerCoverConst[]`/`centerCoverTm[]` (it's a
   constant — no args; `centerCoverTm[] = centerCoverConst[]`)/`centerCoverMemThm`
   ⊢ ∀V. centerCover V = (∃c. V = openInterval (c−1)(c+1)). (Build the body with a distinctive
   `cCenter`/`vCenter`; def via newDefinition; centerCoverMem via APTHM+BETACONV+GEN.)

2. **`centerCoverOpenThm`** ⊢ ∀V. centerCover V ⇒ isOpen V.
   (GEN V DISCH; centerCoverMem EQMP → ∃c. V = openInterval(c−1)(c+1); CHOOSE c (`cOpen`);
   hVeq; `openIntervalIsOpenThm SPEC {c−1, c+1}` → isOpen (openInterval(c−1)(c+1)); EQMP
   `APTERM[isOpenConst[], SYM hVeq]` → isOpen V. CHOOSE-discharge c.)

3. **`centerCoverCoversThm`** ⊢ ∀S. setCovers centerCover S.
   (GEN S; target ∀x. S x ⇒ ∃V. centerCover V ∧ V x (via SYM unfoldSetCovers EQMP); GEN x
   DISCH (S x). V := `csetUnitInterval[x]` = openInterval(x−1)(x+1). `centerCover V`: EXISTS
   c:=x into the centerCoverMem body (`V = openInterval(x−1)(x+1)` by REFL), EQMP SYM
   centerCoverMem. `V x`: `unfoldOpenInterval[x−1, x+1, x]` SYM EQMP from CONJ[`x−1<x`,`x<x+1`]
   (both `realArithProve`). EXISTS V; CONJ.)

4. **`boundedOfFiniteIntervalCoverThm`**
   ⊢ ∀Vs. (∀V. MEM V Vs ⇒ centerCover V) ⇒
   ∃lo hi. ∀x. (∃V. MEM V Vs ∧ V x) ⇒ (realLe lo x ∧ realLe x hi).
   **List induction on Vs** (`listInductionThm` ISPEC the predicate
   `λVs. (∀V. MEM V Vs ⇒ centerCover V) ⇒ ∃lo hi. ∀x. (∃V. MEM V Vs ∧ V x) ⇒ lo≤x∧x≤hi`;
   remember CONJ[base, step] for the MP). 
   - **base (NIL)**: DISCH (∀V. MEM V NIL ⇒ …); EXISTS lo:=&ℝ0, hi:=&ℝ0; GEN x DISCH
     (∃V. MEM V NIL ∧ V x); CHOOSE V; `MEM V NIL = F` (memNilThm) so the CONJUNCT1 (MEM V NIL)
     is F → CONTR to (0≤x ∧ x≤0). (Antecedent unsatisfiable.)
   - **step (CONS V0 rest)**: DISCH `hAll : ∀V. MEM V (V0:rest) ⇒ centerCover V`. Derive
     `hRest : ∀V. MEM V rest ⇒ centerCover V` (GEN V DISCH (MEM V rest); memCons DISJ2 →
     MEM V (V0:rest); hAll MP). Apply IH (the redex `predLam rest`, β-reduce) MP hRest →
     `∃lo hi. ∀x. (∃V. MEM V rest ∧ V x) ⇒ lo≤x∧x≤hi`; CHOOSE lo' (`loRest`), hi' (`hiRest`),
     hRestBound. `centerCover V0` (memCons refl/DISJ1 → MEM V0 (V0:rest); hAll MP); 
     centerCoverMem EQMP → ∃c. V0 = openInterval(c−1)(c+1); CHOOSE c0 (`cStep`), hV0eq.
     lo := `realMin (c0−1) loRest`, hi := `realMax (c0+1) hiRest`. EXISTS lo, hi; GEN x DISCH
     `∃V. MEM V (V0:rest) ∧ V x`; CHOOSE V hVx; memCons on (MEM V (V0:rest)) → V=V0 ∨ MEM V
     rest; DISJCASES:
       · V=V0: V x → V0 x (rewrite hV=V0) → openInterval(c0−1)(c0+1) x (hV0eq) →
         (c0−1<x ∧ x<c0+1) (unfoldOpenInterval). lo≤x: `realMinLeLeftThm SPEC {c0−1, loRest}`
         (lo≤c0−1) + `realLtImpLe` (c0−1<x → c0−1≤x) + `realLeTransThm` → lo≤x. x≤hi:
         `realLeMaxLeftThm SPEC {c0+1, hiRest}` (c0+1≤hi) + realLtImpLe (x<c0+1 → x≤c0+1) +
         realLeTrans → x≤hi. CONJ.
       · MEM V rest: EXISTS V into (∃V. MEM V rest ∧ V x); hRestBound MP → lo'≤x∧x≤hi'.
         lo≤x: `realMinLeRightThm` (lo≤loRest) + realLeTrans (loRest≤x). x≤hi:
         `realLeMaxRightThm` (hiRest≤hi) + realLeTrans. CONJ.
     CHOOSE-discharge c0, V, lo', hi'.

5. **`boundedOfCompactThm`** ⊢ ∀S. isCompact S ⇒ setBounded S.
   GEN S; DISCH `hCompact = isCompact S`. `openSC = unfoldIsCompact[S] EQMP hCompact`
   → ∀C. (∀V. C V ⇒ isOpen V) ⇒ setCovers C S ⇒ setFiniteSubcover C S. SPEC centerCover, MP
   `centerCoverOpenThm`, MP `centerCoverCoversThm SPEC S` → `setFiniteSubcover centerCover S`.
   `unfoldSetFiniteSubcover` EQMP → ∃Vs. setListSubcover centerCover S Vs; CHOOSE Vs
   (`vsBound`); `unfoldSetListSubcover` EQMP → CONJ; `hMemC = CONJUNCT1` (∀V. MEM V Vs ⇒
   centerCover V); `hCovS = CONJUNCT2` (∀x. S x ⇒ ∃V. MEM V Vs ∧ V x).
   `boundedOfFiniteIntervalCoverThm SPEC Vs MP hMemC` → ∃lo hi. ∀x. (∃V. MEM V Vs ∧ V x) ⇒
   lo≤x∧x≤hi; CHOOSE lo, hi, hBound. Build setBounded S (via SYM unfoldSetBounded EXISTS lo hi):
   ∀x. S x ⇒ lo≤x∧x≤hi: GEN x DISCH (S x); `hCovS SPEC x MP` → ∃V. MEM V Vs ∧ V x;
   `hBound SPEC x MP that` → lo≤x∧x≤hi. EXISTS lo, hi; fold setBounded; CHOOSE-discharge.

## Stop-loss / graded delivery

Tier 1: (1)(2)(3) centerCover def + open + covers. Tier 2: (4)
boundedOfFiniteIntervalCover (the list induction — the hard part). Tier 3: (5)
boundedOfCompact (assembly, short once (4) lands). If a tier stalls (same failure twice —
most likely (4)'s CONS-step min/max bounds or the center recovery / `MP[induction, CONJ[...]]`
shape), deliver the green tiers + STOP with a precise report (sub-goal, payload, terms
compared). Never fake a green count.

## Tests (append ~1 assert)

- `boundedOfCompact`: aconv `forall S. isCompact S ⇒ setBounded S` (`isCompactTm`/
  `setBoundedTm` public). Optionally `centerCoverCovers` isThm + shallow. No deep MatchQ.
  **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. append INSIDE `` `Private` `` — cset*
   reachable bare; cross-file must be PUBLIC. New PUBLIC names FREE (grep):
   `centerCover`/`boundedOfFiniteIntervalCover`/`boundedOfCompact`. 4. HOL var identity
   (name,type): distinctive binders/witnesses (`cCenter`/`cOpen`/`cStep`/`loRest`/`hiRest`/
   `vsBound`), NEVER bare `V/x/c/lo/Vs`. 5. holError HoldRest. 6. dev.wls only verifier. 7.
   aconv tests, no deep MatchQ, NO testExit. 8. mkVar/mkConst/mkComb/mkAbs only. 9. narrow
   probes. 10. No Return in Do/For/While. 11. **`listInductionThm`'s two hyps are CONJOINED
   `(P NIL ∧ step) ⇒ ∀l. P l` — use `MP[induction, CONJ[base, step]]` (NOT curried; this bit
   memFilterThm).** 12. **β**: csetBetaClean the `predLam rest`/`predLam (CONS V0 rest)`
   redexes and the centerCover/openInterval applications so terms aconv-match; the induction
   step's IH hyp is the REDEX `predLam rest` (β-reduce it to USE, fold the CONS conclusion
   back to the redex via SYM BETACONV — see memFilterThm's `step`). 13. center recovery:
   `selectOfExists` on `centerCover V0`'s ∃, then `csetBetaClean`. 14. `c−1` =
   `csetRealAdd[c, csetRealNeg[csetOneReal[]]]`, `c+1` = `csetRealAdd[c, csetOneReal[]]`;
   `x−1<x` / `x<x+1` are LINEAR `realArithProve` (1 opaque-free).

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
redex/β-normal divergence (pitfall 12).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did not reach
  it, say so explicitly — do NOT claim green without the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (reused symbol → file:line; new public names confirmed free).
3. How (4) the list induction went (the CONS min/max bounds + center recovery + the
   CONJOINED-hyp MP).
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped.
6. Open questions (empty if none).
