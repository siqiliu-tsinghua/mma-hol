# Brief 035 — M8.6 open-cover compactness: vocab + isCompact def + Heine–Borel bridge (append to Real/CompactSet.wl)

## Goal

Open the OPEN-COVER side of compactness for real sets. Append to `Real/CompactSet.wl`:
the set-of-sets cover vocabulary (`setCovers`/`setListSubcover`/`setFiniteSubcover`) +
the abstract **`isCompact`** predicate, three small support lemmas (`isOpenEmptyThm`,
`openIntervalIsOpenThm`, a FILTER-membership lemma), and the **bridge**
`closedIntervalSetCompactThm` (closed intervals satisfy set-of-sets finite-subcover
compactness — reusing the GRADUATED polymorphic `compactnessPrincipleThm` via a clamp
family at index type `real→bool`). Optionally (Tier 4) **`compactOfClosedBoundedThm`**
(`isClosed S ⇒ setBounded S ⇒ isCompact S`, the Heine–Borel producer). Append ~4 asserts
to `tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate to green.

## Why set-of-sets (the design — read once)

The Lean blueprint's `IsCompact S = ∀{ι}(U:ι→set). (∀i. isOpen(U i)) ⇒ covers U S ⇒
finiteSubcover U S` quantifies over an arbitrary INDEX TYPE ι — no HOL analogue. We encode
a cover as a SET OF OPEN SETS `C : (real→bool)→bool` (index type fixed at `real→bool`,
each member set indexes itself). The blueprint's `Option ι` index-extension (adding `compl
S` to the cover) becomes a plain set INSERT here. The existing GRADUATED
`compactnessPrincipleThm` (polymorphic family `U:ι→set`) is reused by instantiating
ι:=real→bool with the CLAMP family `λV. COND (C V) V (λx.F)` (members pass through, non-members
collapse to the empty set).

## Blueprint (in-repo)

`tautology-ref/Tautology/RealCompactness/Compact.lean`: `ListSubcover`/`FiniteSubcover`/
`IsCompact` (43–55). `HeineBorel.lean`: `closedSubsetIntervalCover` (232) +
`compact_of_closed_subset_closedInterval` (238) + `compact_of_closed_bounded` (284) — our
Tier 4 collapses the `Option ι` cover into a set INSERT. The closed-interval principle
`ClosedIntervalCompactnessPrinciple` is exactly our graduated `compactnessPrincipleThm`.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- CompactSet.wl is FRONTIER. Frontier files: Connected.wl, Topology.wl, CompactSet.wl —
  dev.wls names ALL THREE (that order). Append to the END of CompactSet.wl (before
  `End[]; EndPackage[];`) + `::usage` lines at the top.
- **Heavy reuse — the cset* helpers ALREADY IN this file's `` `Private` `` block are
  reachable by bare name** (you are appending inside it): `csetForallTm`/`csetExistsTm`/
  `csetConjTm`/`csetImpTm`/`csetOrTm`/`csetNotTm`/`csetSetApp`/`csetSpecAll`/`csetApplyDef`/
  `csetBetaClean`/`csetForallList`, `csetRealLe`, the type aliases `csetRealTy`/`csetSetTy`/
  `csetNumTy`. Templates in-file: `existsMemIntervalOfNoComplNeighborhoodThm` /
  `closedOfSequentiallyCompactThm` (EM + build-a-set-predicate proofs); `unboundedEscapePoint`
  family (def + unfold pattern).
- LCF-style: you cannot make a false theorem; the test suite decides. Acceptance is mechanical.

## Reuse (VERIFIED — snapshot + frontier Topology/Connected + this file)

- **Compact.wl (snapshot, PUBLIC, polymorphic over the tyvar `iota`):**
  - `compactnessPrincipleThm` ⊢ ∀U left right. realLe left right ⇒ (∀i. isOpen (U i)) ⇒
    covers U (closedInterval left right) ⇒ finiteSubcover U (closedInterval left right).
    (U : iota→real→bool; the builders auto-INSTTYPE `iota` from U's type.)
  - `coversTm[U,S]`/`unfoldCovers[U,S]` (⊢ covers U S = ∀x. S x ⇒ ∃i. U i x);
    `listSubcoverTm[U,S,js]`/`unfoldListSubcover` (⊢ = ∀x. S x ⇒ ∃i. MEM i js ∧ U i x);
    `finiteSubcoverTm[U,S]`/`unfoldFiniteSubcover` (⊢ = ∃js. listSubcover U S js).
  - `isOpenTm[U]`/`unfoldIsOpen[U]` (⊢ isOpen U = ∀x. U x ⇒ ∃l r. realLt l x ∧ (realLt x r
    ∧ ∀y. openInterval l r y ⇒ U y)); `openIntervalTm[l,r,x]`/`unfoldOpenInterval[l,r,x]`
    (⊢ openInterval l r x = (l<x ∧ x<r)); `closedIntervalTm[l,r,x]`/`unfoldClosedInterval`;
    the closed interval AS A SET = `mkComb[mkComb[closedIntervalConst[], l], r]`
    (`closedIntervalConst[]` is PUBLIC; the in-file builder `compactClosedIntervalSetTm` is
    Compact-PRIVATE — build the mkComb yourself); `setBoundedTm[S]`/`unfoldSetBounded[S]`
    (⊢ setBounded S = ∃lo hi. ∀x. S x ⇒ lo≤x ∧ x≤hi).
- **Topology.wl (frontier, before this; PUBLIC):** `complTm[S]`/`complMemThm` (⊢ ∀S x.
  compl S x = ¬(S x)); `isClosedTm[S]`/`isClosedComplOpenThm` (⊢ ∀S. isClosed S = isOpen
  (compl S)).
- **Bool.wl (snapshot):** `HOL`Bool`condConst[ty]`, `HOL`Bool`condTThm` (⊢ COND T a b = a),
  `HOL`Bool`condFThm` (⊢ COND F a b = b), `HOL`Bool`EQTINTRO`. **COND-rewrite idiom is in
  Compact.wl ~1646** (`APTERM[condConst[ty], EQTINTRO[hCond]]` then `condTThm` / the eqf form
  then `condFThm`) — mirror it to rewrite `COND (C V) V (λx.F)` after case-splitting `C V`.
- **List.wl (snapshot, PUBLIC):** `filterNilThm`/`filterConsThm` (⊢ FILTER p (CONS x l) =
  COND (p x) (CONS x (FILTER p l)) (FILTER p l)); `memNilThm`/`memConsThm` (⊢ MEM x (CONS y
  l) = (x=y ∨ MEM x l)); `listInductionThm`. **There are NO `filterTm`/`memTm` builders** —
  only the POLYMORPHIC consts `HOL`Stdlib`List`filterConst[]` (= `mkConst["FILTER", filterTy]`,
  α a tyvar) and `memConst[]`; build `FILTER p l` = `mkComb[mkComb[filterConst[], p], l]` and
  `MEM x l` = `mkComb[mkComb[memConst[], x], l]` yourself. **State+prove `memFilterThm`
  POLYMORPHICALLY (α a tyvar, generic consts) by `listInductionThm`; at the bridge use-site
  the `(real→bool) list` forces α:=real→bool, so `ISPEC`/`INSTTYPE` `memFilterThm` there.**
- **Kernel/Bool:** `HOL`Bool`ISPEC[t, th]` (polymorphic SPEC — one-way matches binder type
  to typeOf[t] and INSTTYPEs first; USE THIS to instantiate `compactnessPrincipleThm`'s `∀U`
  at the clamp family of type `(real→bool)→(real→bool)`, see [[spec-polymorphic]]);
  `DEDUCTANTISYM`; standard CHOOSE/EXISTS/CONJ/DISJCASES/EXCLUDEDMIDDLE/MP/DISCH/GEN/EQMP/SYM.
- **realArithProve** (LINEAR) for any real-order glue.

## Scope

- MODIFY: `stdlib/Real/CompactSet.wl` (append + `::usage`),
  `tests/real_compactset_tests.wl` (append). No other files, NO runner lists, NO new imports
  (build set-of-sets ops + the empty set as RAW lambdas — do NOT add `HOL`Stdlib`Set``).
  MUST NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/
  Topology/docs/codex(except report). No newAxiom, no new files.

## Deliverable (append in this order)

Notation: `setOfSetsTy = tyFun[csetSetTy, boolTy]` (= (real→bool)→bool). The empty real set
`emptyRealSet = mkAbs[xV:real, falseTm]` (falseTm = `mkConst["F", boolTy]`). Build a
`csetSetMem[cT, vT] = mkComb[cT, vT]` (C applied to a set V) and `csetSetAppV[vT, xT] =
mkComb[vT, xT]` (set V applied to a point x).

1. **`setCoversDefThm`** ⊢ setCovers = (λC S. ∀x. S x ⇒ ∃V. C V ∧ V x).
   `setCovers : ((real→bool)→bool) → (real→bool) → bool`. Export
   `setCoversConst[]`/`setCoversTm[C,S]`/`unfoldSetCovers[C,S]` (mirror the `compl`/
   `isSequentiallyCompact` def+unfold pattern). Distinctive binders `xSc`/`vSc`.

2. **`setListSubcoverDefThm`** ⊢ setListSubcover = (λC S Vs. (∀V. MEM V Vs ⇒ C V) ∧
   (∀x. S x ⇒ ∃V. MEM V Vs ∧ V x)).  `… → (real→bool) list → bool`. Export const/Tm/unfold.

3. **`setFiniteSubcoverDefThm`** ⊢ setFiniteSubcover = (λC S. ∃Vs. setListSubcover C S Vs).
   Export const/Tm/unfold.

4. **`isCompactDefThm`** ⊢ isCompact = (λS. ∀C. (∀V. C V ⇒ isOpen V) ⇒ setCovers C S ⇒
   setFiniteSubcover C S).  `isCompact : (real→bool)→bool`. Export `isCompactConst[]`/
   `isCompactTm[S]`/`unfoldIsCompact[S]`. (The `∀V. C V ⇒ isOpen V` clause uses `isOpenTm`.)

5. **`isOpenEmptyThm`** ⊢ isOpen (λx. F).  (unfold isOpen at `emptyRealSet`; ∀x. F ⇒ … is
   vacuous — DISCH the `F` hyp, CONTR to the ∃-body; GEN x; fold. Or `propTaut`/`arithProve`
   the `F ⇒ anything`.)

6. **`openIntervalIsOpenThm`** ⊢ ∀l r. isOpen (openInterval l r).  (unfold isOpen at
   `openInterval l r`: GEN x, DISCH `openInterval l r x`; EXISTS l, r; from
   `unfoldOpenInterval[l,r,x]` get `l<x ∧ x<r`; the inner `∀y. openInterval l r y ⇒
   openInterval l r y` is reflexive DISCH; fold.)

7. **`memFilterThm`** ⊢ ∀p x l. MEM x (FILTER p l) = (p x ∧ MEM x l).  (list induction on l
   via `listInductionThm`: NIL — both sides F (`memNilThm`/`filterNilThm`); CONS y t — use
   `filterConsThm` COND-split on `p y` and `memConsThm`, close each propositionally with
   `propTaut`. This is the one genuinely fiddly support lemma — if it fights, see stop-loss.)

8. **`closedIntervalSetCompactThm`** ⊢ ∀a b C. realLe a b ⇒ (∀V. C V ⇒ isOpen V) ⇒
   setCovers C (closedInterval a b) ⇒ setFiniteSubcover C (closedInterval a b).
   **THE BRIDGE (novel — the one hard technique).** GEN a b C; DISCH hLe, hCopen, hCov.
   - `clamp = mkAbs[vCl, condTm[csetSetMem[C, vCl], vCl, emptyRealSet]]` where condTm builds
     `COND (C V) V (λx.F)` at type `real→bool` (= `mkComb[mkComb[mkComb[condConst[
     csetSetTy], cond], thenSet], elseSet]`; check `condConst` arity/type). `clamp :
     (real→bool)→(real→bool)`.
   - `clampAt[vT]` (= clamp applied + β) and a per-V rewrite `clampEqV : C V ⇒ clamp V = V`
     (case `C V` true: `condTThm` after EQTINTRO of `C V = T`) and `clampMissEmpty :
     ¬(C V) ⇒ clamp V = (λx.F)` (condFThm after eqf). Mirror Compact.wl ~1646.
   - `hUopen : ∀V. isOpen (clamp V)`: GEN V; EM on `C V`; true → rewrite clamp V = V (clampEqV)
     EQMP, MP hCopen → isOpen V; false → clamp V = (λx.F), isOpenEmptyThm. DISJCASES.
   - `hUcov : covers clamp (closedInterval a b)`: build via `unfoldCovers[clamp,
     closedIntervalSet]` SYM EQMP from `∀x. [a,b]x ⇒ ∃V. clamp V x`: GEN x DISCH; from hCov
     (unfoldSetCovers) get `∃V. C V ∧ V x`; CHOOSE V; clamp V = V (clampEqV under C V) so
     `clamp V x`; EXISTS V into `∃V. clamp V x`. (covers' body is `∃i. U i x` — here i:=V.)
   - `hFin = compactnessPrincipleThm` ISPEC clamp, then SPEC a b, MP hLe, MP hUopen, MP hUcov
     → `finiteSubcover clamp (closedInterval a b)`. `unfoldFiniteSubcover` EQMP →
     `∃js. listSubcover clamp [a,b] js`. CHOOSE js.
   - **Translate to setFiniteSubcover with Vs := FILTER C js:** prove `setListSubcover C
     (closedInterval a b) (FILTER C js)`: (i) `∀V. MEM V (FILTER C js) ⇒ C V` from
     `memFilterThm` (the `p x` = `C V` conjunct); (ii) `∀x. [a,b]x ⇒ ∃V. MEM V (FILTER C js)
     ∧ V x`: from listSubcover (unfold) get `∃i. MEM i js ∧ clamp i x`; CHOOSE i; clamp i x is
     true ⇒ ¬(clamp i = (λx.F)) ⇒ C i (contrapositive of clampMissEmpty: if ¬C i then clamp
     i = λx.F so clamp i x = F, contradiction) ⇒ clamp i = i so `i x`; `MEM i (FILTER C js)`
     by memFilterThm (C i ∧ MEM i js). EXISTS i. Fold setListSubcover (CONJ of (i),(ii)),
     then EXISTS (FILTER C js) into setFiniteSubcover; fold via SYM unfoldSetFiniteSubcover.

9. **(Tier 4 — OPTIONAL) `compactOfClosedBoundedThm`** ⊢ ∀S. isClosed S ⇒ setBounded S ⇒
   isCompact S.  GEN S; DISCH hClosed, hBdd. unfold isCompact goal: GEN C, DISCH
   `hCopen : ∀V. C V ⇒ isOpen V`, DISCH `hCov : setCovers C S`; goal `setFiniteSubcover C S`.
   - From hBdd (`unfoldSetBounded`): `∃lo hi. ∀x. S x ⇒ lo≤x ∧ x≤hi`. CHOOSE lo, hi (`hB`).
     Need `lo≤hi`: by_cases (EM) `∃x. S x`? — actually take the bound straight: if S empty,
     Vs:=NIL works (vacuous); else from some xS, lo≤xS≤hi gives lo≤hi (realArithProve /
     realLeTrans). **Do the EM on `setCovers`-style nonemptiness via EM on `∃x. S x`** (mirror
     the blueprint's `by_cases Nonempty`): empty branch → EXISTS NIL, `setListSubcover` with
     the `∀x.Sx⇒…` vacuous (S x ⇒ False) ; nonempty branch below.
   - `C' = mkAbs[vCp, csetOrTm[mkEq[vCp, complTm[S]], csetSetMem[C, vCp]]]` (= λV. V = compl S
     ∨ C V), the INSERTed cover.
   - `hC'open : ∀V. C' V ⇒ isOpen V`: GEN V DISCH (V=compl S ∨ C V); DISJCASES: V=compl S →
     rewrite, isClosedComplOpenThm gives isOpen(compl S); C V → hCopen. 
   - `hC'cov : setCovers C' (closedInterval lo hi)`: GEN x DISCH `[lo,hi]x`; EM on `S x`:
     S x → from hCov get V∈C with V x, V∈C' (right disjunct), EXISTS; ¬S x → compl S x
     (complMem SYM), compl S ∈ C' (left disjunct, refl), EXISTS compl S.
   - `closedIntervalSetCompactThm` SPEC lo hi C', MP (lo≤hi), MP hC'open, MP hC'cov →
     `setFiniteSubcover C' (closedInterval lo hi)`. CHOOSE Vs'.
   - **Drop compl S:** Vs := FILTER (λV. C V) Vs' (or `FILTER (λV. ¬(V = compl S)) Vs'`; C is
     cleaner). `setListSubcover C S Vs`: (i) MEM⇒C via memFilterThm; (ii) ∀x. S x ⇒ ∃V∈Vs. V x:
     x∈S⊆[lo,hi] (hB), so from Vs' get V∈Vs' with V x; V∈C' so V=compl S ∨ C V; V=compl S ⇒
     compl S x = ¬S x contradicts S x ⇒ C V; MEM V (FILTER C Vs') via memFilterThm. EXISTS.
     Fold setFiniteSubcover.

## Stop-loss / graded delivery

Tier 1: (1)(2)(3)(4) vocab + isCompact def (pure def+unfold re-skin). Tier 2: (5)(6)(7)
support lemmas. Tier 3: (8) the clamp bridge `closedIntervalSetCompact` (THE deliverable —
the novel technique). Tier 4: (9) compactOfClosedBounded (ship if it goes; skip if it fights).
If a tier stalls (same failure twice — most likely (7) memFilter induction, or (8)'s ISPEC of
the clamp family / the COND-rewrite, or (8)'s listSubcover→setListSubcover translation),
deliver the green tiers with the rest omitted and STOP with a precise report (which sub-goal,
exact payload, the terms compared). Tier 3 green is a SUCCESS even without Tier 4. Never fake
a green count.

## Tests (append ~4 asserts)

- `setCovers`/`isCompact` def shapes: aconv on built expected (use the RCST helpers +
  `mkConst`/`mkAbs`). `closedIntervalSetCompact`: aconv on built `forall a b C. realLe a b ⇒
  (∀V. C V ⇒ isOpen V) ⇒ setCovers C (closedInterval a b) ⇒ setFiniteSubcover C
  (closedInterval a b)` — or, if that term is fiddly, `isThm` + `hyp=={}` + a shallow head
  probe. `openIntervalIsOpen`/`isOpenEmpty`/`memFilter`: isThm + shallow shape. If Tier 4
  ships, `compactOfClosedBounded`: aconv `forall S. isClosed S ⇒ setBounded S ⇒ isCompact S`.
  No deep MatchQ. **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. you append INSIDE this file's
   `` `Private` `` — `cset*` helpers reachable bare; cross-file symbols must be PUBLIC (all
   listed are). New PUBLIC names FREE (grep): `setCovers`/`setListSubcover`/`setFiniteSubcover`/
   `isCompact`/`isOpenEmpty`/`openIntervalIsOpen`/`memFilter`/`closedIntervalSetCompact`/
   `compactOfClosedBounded`. 4. HOL var identity (name,type): distinctive binders (`vSc`/`xSc`/
   `vCl`/`vCp`/`jsBridge`/`VsDrop`), NEVER bare `V/x/i` a caller's term carries. 5. holError
   HoldRest. 6. dev.wls is the only verifier. 7. aconv tests, no deep MatchQ, NO testExit. 8.
   mkVar/mkConst/mkComb/mkAbs only — the empty set is `mkAbs[xV, mkConst["F", boolTy]]`. 9.
   narrow probes. 10. No Return in Do/For/While. 11. **`compactnessPrincipleThm`'s `∀U` is
   POLYMORPHIC (binder type `iota→real→bool`, iota a tyvar) — instantiate with `ISPEC[clamp,
   …]` NOT `SPEC` (SPEC checks typeOf===binder exactly and will reject; ISPEC INSTTYPEs iota
   first). The covers/finiteSubcover BUILDERS auto-INSTTYPE iota from the family's type, so
   `coversTm[clamp, S]` already targets iota:=real→bool.** 12. **COND**: `COND (C V) V (λx.F)`
   — to rewrite you must case-split `C V` (EM) and use `condTThm`/`condFThm` after EQTINTRO/
   eqf; the bare COND term does NOT auto-reduce (mirror Compact.wl ~1646). 13. **β**: csetBetaClean
   the clamp-applied and def-applied terms so they aconv-match. 14. The set-of-sets ops are RAW
   lambdas over `real→bool` (no Set.wl import): `C V` = `mkComb[C, V]`, `V x` = `mkComb[V, x]`.

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
mismatch (usually a def shape or a missing betaClean); an `INST`/`SPEC` type error on the
bridge = you used SPEC where ISPEC is needed (pitfall 11).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did not reach
  it, say so explicitly — do NOT claim green without the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused symbol → file:line; new public names confirmed free;
   the FILTER/MEM builder names you used → file:line).
3. How the clamp bridge (8) went: did `ISPEC[clamp, compactnessPrincipleThm]` typecheck first
   try; how the COND-rewrite + the listSubcover→setListSubcover (FILTER) translation went.
4. Whether Tier 4 shipped, and if so how the INSERT/FILTER-drop went.
5. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
6. Which tier fully proven vs stopped.
7. Open questions (empty if none).
