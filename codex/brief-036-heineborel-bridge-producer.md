# Brief 036 — M8.6 Heine–Borel bridge + producer (append to Real/CompactSet.wl)

## Goal

Prove the open-cover Heine–Borel PRODUCER direction. Append to `Real/CompactSet.wl`:
the **bridge** `closedIntervalSetCompactThm` (closed intervals satisfy set-of-sets
finite-subcover compactness, reusing the GRADUATED polymorphic `compactnessPrincipleThm`
via a clamp family at index type `real→bool`), then **`compactOfClosedBoundedThm`**
(`isClosed S ⇒ setBounded S ⇒ isCompact S`). Append ~2 asserts to
`tests/real_compactset_tests.wl`. Self-verify with dev.wls, iterate to green.

## Status / what already exists in this file (brief-035 + memFilter — VERIFIED green, 61/0)

The set-of-sets vocabulary and all support lemmas are DONE and PUBLIC in CompactSet.wl:
- `setCoversTm[C,S]`/`unfoldSetCovers[C,S]` ⊢ setCovers C S = ∀x. S x ⇒ ∃V. C V ∧ V x.
- `setListSubcoverTm[C,S,Vs]`/`unfoldSetListSubcover` ⊢ = (∀V. MEM V Vs ⇒ C V) ∧
  (∀x. S x ⇒ ∃V. MEM V Vs ∧ V x).
- `setFiniteSubcoverTm[C,S]`/`unfoldSetFiniteSubcover` ⊢ = ∃Vs. setListSubcover C S Vs.
- `isCompactTm[S]`/`unfoldIsCompact[S]` ⊢ isCompact S = ∀C. (∀V. C V ⇒ isOpen V) ⇒
  setCovers C S ⇒ setFiniteSubcover C S.
- `isOpenEmptyThm` ⊢ isOpen (λx. F); `openIntervalIsOpenThm` ⊢ ∀l r. isOpen (openInterval
  l r); **`memFilterThm` ⊢ ∀p x l. MEM x (FILTER p l) = (p x ∧ MEM x l)** (element type
  `real→bool` — the exact type you need; SPEC/no INSTTYPE).
- File-private helpers you can REUSE by bare name (you append inside the same `` `Private` ``):
  `csetEmptyRealSet[]` (= λx. F), `csetFalseTm[]`, `csetSetMem[C,V]` (= C V),
  `csetSetAppV[V,x]` (= V x), `csetOpenIntervalSet[a,b]` (= openInterval a b, a SET),
  `csetMemConstAt[ty]`/`csetMemTmAt[ty,x,xs]`, `csetNilAt[]` (NIL : list[real→bool]),
  `csetConsConstAt[]`/`csetConsTmAt[h,t]`, `csetFilterConstAt[]`/`csetFilterTmAt[p,l]`,
  `csetCondListConst[]` (= COND : bool→list[real→bool]→…), the type aliases
  `csetSetTy`/`csetSetOfSetsTy`/`csetSetListTy`/`csetRealTy`, and all the term builders
  (`csetForallTm`/`csetExistsTm`/`csetConjTm`/`csetImpTm`/`csetOrTm`/`csetNotTm`/
  `csetSetApp`/`csetRealLe`/`csetSpecAll`/`csetApplyDef`/`csetBetaClean`/`csetForallList`).
  Template proofs in-file: `existsMemIntervalOfNoComplNeighborhoodThm` (EM + build-a-set),
  `closedOfSequentiallyCompactThm` (DISJCASES), `memFilterThm` (COND-rewrite + ISPEC of
  polymorphic List lemmas).

## Why set-of-sets / the clamp (recap)

`compactnessPrincipleThm` is polymorphic over the index TYPE (family `U:ι→set`). We
instantiate ι:=real→bool with the CLAMP family `λV. COND (C V) V (λx.F)` (members pass
through; non-members collapse to the empty set, which is open). The Lean `Option ι`
index-extension in `compact_of_closed_bounded` becomes a plain set INSERT
`λV. V = compl S ∨ C V`.

## Blueprint (in-repo)

`tautology-ref/Tautology/RealCompactness/HeineBorel.lean`: `closedSubsetIntervalCover`
(232) + `compact_of_closed_subset_closedInterval` (238) + `compact_of_closed_bounded`
(284). The closed-interval principle is our `compactnessPrincipleThm`.

## Reuse (VERIFIED — snapshot + frontier Topology/Connected + this file)

- **Compact.wl (snapshot, PUBLIC, polymorphic over tyvar `iota`):**
  `compactnessPrincipleThm` ⊢ ∀U left right. realLe left right ⇒ (∀i. isOpen (U i)) ⇒
  covers U (closedInterval left right) ⇒ finiteSubcover U (closedInterval left right).
  `coversTm[U,S]`/`unfoldCovers` (⊢ covers U S = ∀x. S x ⇒ ∃i. U i x);
  `listSubcoverTm[U,S,js]`/`unfoldListSubcover` (⊢ = ∀x. S x ⇒ ∃i. MEM i js ∧ U i x);
  `finiteSubcoverTm[U,S]`/`unfoldFiniteSubcover` (⊢ = ∃js. listSubcover U S js);
  the builders AUTO-INSTTYPE `iota` from the family's type. The closed interval AS A SET =
  `mkComb[mkComb[closedIntervalConst[], a], b]` (`closedIntervalConst[]` PUBLIC);
  `setBoundedTm[S]`/`unfoldSetBounded[S]` (⊢ setBounded S = ∃lo hi. ∀x. S x ⇒ lo≤x ∧ x≤hi).
- **Topology.wl (frontier, PUBLIC):** `complTm[S]`/`complMemThm` (⊢ ∀S x. compl S x = ¬(S x));
  `isClosedTm[S]`/`isClosedComplOpenThm` (⊢ ∀S. isClosed S = isOpen (compl S)).
- **Bool.wl (snapshot):** `HOL`Bool`condConst[ty]`, `condTThm` (⊢ ∀a b. COND T a b = a),
  `condFThm` (⊢ ∀a b. COND F a b = b), `EQTINTRO`, `ISPEC` (polymorphic SPEC — USE for
  `compactnessPrincipleThm`'s `∀U` at the clamp family; the COND-rewrite idiom is already
  demonstrated in this file's `memFilterThm`). `DEDUCTANTISYM`, `propTaut`.
- **realArithProve** (LINEAR) for `lo≤hi` / interval glue.

## Scope

- MODIFY: `stdlib/Real/CompactSet.wl` (append + `::usage`),
  `tests/real_compactset_tests.wl` (append). No other files, NO runner lists, NO new
  imports (set ops are RAW lambdas over `real→bool`). MUST NOT touch Kernel/Types/Terms/
  Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/Topology/docs/codex(except report).
  No newAxiom, no new files.

## Deliverable (append in this order)

A `csetClampFamily[cT]` builder: `mkAbs[vCl, mkComb[mkComb[mkComb[csetCondListConst-but-at-
real→bool... NO: COND here is at the SET type real→bool, build condConst[csetSetTy]],
csetSetMem[cT, vCl]], vCl], csetEmptyRealSet[]]]`, i.e. `λV. COND (C V) V (λx.F)` of type
`(real→bool)→(real→bool)`. (NOTE: this COND is at `csetSetTy`, NOT `csetListTyAt` —
`HOL`Bool`condConst[csetSetTy]`.) Plus per-V rewrites `csetClampHit : C V ⇒ clamp V = V`
(EQTINTRO of `C V = T` → condTThm-at-csetSetTy) and `csetClampMiss : ¬(C V) ⇒ clamp V =
(λx.F)` (eqf of `C V = F` → condFThm); mirror `memFilterThm`'s COND-rewrite exactly, only
the COND type changes to `csetSetTy`.

1. **`closedIntervalSetCompactThm`** ⊢ ∀a b C. realLe a b ⇒ (∀V. C V ⇒ isOpen V) ⇒
   setCovers C (closedInterval a b) ⇒ setFiniteSubcover C (closedInterval a b).
   GEN a b C; DISCH hLe, hCopen, hCov. Let `clamp = csetClampFamily[C]`,
   `ivSet = mkComb[mkComb[closedIntervalConst[], a], b]`.
   - **hUopen : ∀V. isOpen (clamp V)**: GEN V; EM on `C V`; true → `clamp V = V`
     (csetClampHit MP) EQMP-rewrite the goal, MP hCopen (SPEC V) → isOpen V; false →
     `clamp V = (λx.F)`, rewrite, `isOpenEmptyThm`. DISJCASES → isOpen (clamp V).
     (Build the goal `isOpen (clamp V)` and rewrite clamp V via the eq + `APTERM[isOpenConst[],
     clampEq]` EQMP — isOpen is a 1-arg function so APTERM works.)
   - **hUcov : covers clamp ivSet**: target (via SYM `unfoldCovers[clamp, ivSet]` EQMP)
     `∀x. ivSet x ⇒ ∃V. clamp V x`. GEN x DISCH (ivSet x); from `unfoldSetCovers[C, ivSet]`
     EQMP hCov, SPEC x MP → `∃V. C V ∧ V x`; CHOOSE V (distinctive `vCov`); `C V`, `V x`;
     `clamp V = V` (csetClampHit MP C V); so `clamp V x` (EQMP APTERM at x of SYM clampEq,
     or rewrite `V x` ⇒ `clamp V x`); EXISTS V into `∃V. clamp V x`. (covers' body is `∃i.
     U i x` — i:=V, U:=clamp.)
   - **hFin** = `ISPEC[clamp, compactnessPrincipleThm]`, then SPEC a, b, MP hLe, MP hUopen,
     MP hUcov → `finiteSubcover clamp ivSet`. `unfoldFiniteSubcover[clamp, ivSet]` EQMP →
     `∃js. listSubcover clamp ivSet js`. CHOOSE js (distinctive `jsBridge`).
   - **setFiniteSubcover C ivSet with Vs := FILTER C js** (build via SYM
     `unfoldSetFiniteSubcover` after EXISTS (FILTER C js)). Need `setListSubcover C ivSet
     (FILTER C js)` = CONJ of:
     (i) `∀V. MEM V (FILTER C js) ⇒ C V`: GEN V DISCH; `memFilterThm SPEC {C,V,js}` →
         `MEM V (FILTER C js) = (C V ∧ MEM V js)`; EQMP the hyp, CONJUNCT1 → C V.
     (ii) `∀x. ivSet x ⇒ ∃V. MEM V (FILTER C js) ∧ V x`: GEN x DISCH; from `listSubcover
         clamp ivSet js` (unfold) SPEC x MP → `∃i. MEM i js ∧ clamp i x`; CHOOSE i
         (distinctive `iBridge`); `MEM i js`, `clamp i x`. Show `C i`: EM on `C i`; if ¬C i
         then `clamp i = (λx.F)` (csetClampMiss) so `clamp i x = (λx.F) x = F` (BETACONV) —
         contradiction with `clamp i x`; so `C i`. Then `clamp i = i` (csetClampHit) so
         `i x` (EQMP APTERM at x). `MEM i (FILTER C js)` via `memFilterThm` SYM (C i ∧ MEM i
         js). EXISTS i.
     CONJ (i)(ii), fold setListSubcover (SYM unfoldSetListSubcover EQMP), EXISTS (FILTER C
     js), fold setFiniteSubcover.

2. **`compactOfClosedBoundedThm`** ⊢ ∀S. isClosed S ⇒ setBounded S ⇒ isCompact S.
   GEN S; DISCH hClosed, hBdd. unfold isCompact goal (SYM `unfoldIsCompact[S]` EQMP at the
   end): GEN C, DISCH `hCopen : ∀V. C V ⇒ isOpen V`, DISCH `hCov : setCovers C S`; goal
   `setFiniteSubcover C S`.
   - EM on `∃x. S x` (nonemptiness):
     - empty (`¬∃x. S x`): EXISTS Vs:=NIL into setFiniteSubcover; setListSubcover C S NIL =
       CONJ[ `∀V. MEM V NIL ⇒ C V` (memNilThm: MEM V NIL = F, so F ⇒ C V by propTaut/CONTR),
       `∀x. S x ⇒ …` (S x ⇒ False since ¬∃, then CONTR) ]. (Mirror the blueprint empty case.)
     - nonempty: from hBdd (`unfoldSetBounded`) CHOOSE lo, hi; `hB : ∀x. S x ⇒ lo≤x ∧ x≤hi`.
       CHOOSE the witness `xS` from `∃x. S x`; `lo≤xS ∧ xS≤hi` (hB SPEC xS MP); `lo≤hi`
       (realArithProve / realLeTrans).
       - `cPrime = mkAbs[vCp, csetOrTm[mkEq[vCp, complTm[S]], csetSetMem[C, vCp]]]` (λV. V =
         compl S ∨ C V); `cPrimeMem[V] : C' V = (V = compl S ∨ C V)` (BETACONV).
       - `hC'open : ∀V. C' V ⇒ isOpen V`: GEN V DISCH (C' V → V=compl S ∨ C V); DISJCASES:
         V=compl S → rewrite, `isClosedComplOpenThm` SPEC S MP hClosed → isOpen (compl S);
         C V → hCopen SPEC V MP. 
       - `hC'cov : setCovers C' (closedInterval lo hi)`: target `∀x. [lo,hi]x ⇒ ∃V. C' V ∧
         V x`; GEN x DISCH; EM on `S x`: S x → hCov gives `∃V. C V ∧ V x`, CHOOSE V, `C' V`
         via right disjunct (DISJ2), EXISTS; ¬S x → `compl S x` (complMem SYM EQMP),
         `C' (compl S)` via left disjunct (refl, DISJ1), EXISTS (compl S).
       - `closedIntervalSetCompactThm` SPEC lo hi C', MP (lo≤hi), MP hC'open, MP hC'cov →
         `setFiniteSubcover C' (closedInterval lo hi)`. CHOOSE Vs' (`vsProd`).
       - **Vs := FILTER C Vs'** : `setListSubcover C S (FILTER C Vs')` = CONJ:
         (i) `∀V. MEM V (FILTER C Vs') ⇒ C V` (memFilterThm CONJUNCT1).
         (ii) `∀x. S x ⇒ ∃V. MEM V (FILTER C Vs') ∧ V x`: x∈S ⇒ [lo,hi]x (hB); from
             `setListSubcover C' [lo,hi] Vs'` (CONJUNCT2, unfold) get `∃V. MEM V Vs' ∧ V x`;
             CHOOSE V; `C' V` (from CONJUNCT1 of the setListSubcover, MEM V Vs' ⇒ C' V) →
             V=compl S ∨ C V; DISJCASES: V=compl S → `compl S x` = `¬S x` (complMem)
             contradicts `S x` (CONTR); C V → MEM V (FILTER C Vs') (memFilterThm SYM, C V ∧
             MEM V Vs'). EXISTS V. 
         CONJ, fold setFiniteSubcover with witness (FILTER C Vs').
   - Fold the isCompact body (GEN C, DISCH hCopen, DISCH hCov over `setFiniteSubcover C S`),
     SYM unfoldIsCompact EQMP → isCompact S. GEN S, DISCH hClosed, DISCH hBdd.

## Stop-loss / graded delivery

Tier 1: (1) `closedIntervalSetCompactThm` — THE bridge (clamp ISPEC + COND-rewrite +
memFilter translation). Tier 2: (2) `compactOfClosedBoundedThm` (INSERT compl S + FILTER
drop; reuses (1)). Tier 1 green is a SUCCESS even without Tier 2. If a tier stalls (same
failure twice — most likely the `ISPEC[clamp, compactnessPrincipleThm]` typecheck, the
clamp COND type (csetSetTy not csetListTyAt!), or the `covers`/`listSubcover` body-vs-
setCovers translation), deliver the green tier + STOP with a precise report (which sub-goal,
exact payload, the terms compared by aconv). Never fake a green count.

## Tests (append ~2 asserts)

- `closedIntervalSetCompact`: aconv on built `forall a b C. realLe a b ⇒ (∀V. C V ⇒ isOpen
  V) ⇒ setCovers C (closedInterval a b) ⇒ setFiniteSubcover C (closedInterval a b)` — or, if
  fiddly, isThm + hyp=={} + shallow head probe. If Tier 2 ships,
  `compactOfClosedBounded`: aconv `forall S. isClosed S ⇒ setBounded S ⇒ isCompact S`.
  No deep MatchQ. **NO testExit[].**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. you append INSIDE this file's
   `` `Private` `` — all `cset*` + the brief-035 helpers reachable bare; cross-file symbols
   must be PUBLIC (all listed are). New PUBLIC names FREE (grep):
   `closedIntervalSetCompact`/`compactOfClosedBounded`. 4. HOL var identity (name,type):
   distinctive binders/witnesses (`vCl`/`vCov`/`jsBridge`/`iBridge`/`vsProd`/`xS`/`vCp`),
   NEVER bare `V/x/i/js`. 5. holError HoldRest. 6. dev.wls is the only verifier. 7. aconv
   tests, no deep MatchQ, NO testExit. 8. mkVar/mkConst/mkComb/mkAbs only; empty set =
   `csetEmptyRealSet[]`. 9. narrow probes. 10. No Return in Do/For/While. 11. **`compactness
   PrincipleThm`'s `∀U` is POLYMORPHIC — instantiate with `ISPEC[clamp, …]` NOT `SPEC`; the
   `coversTm`/`finiteSubcoverTm` BUILDERS auto-INSTTYPE iota from the clamp's type. `memFilter
   Thm` is at element type real→bool already (plain SPEC).** 12. **CLAMP COND is at
   `csetSetTy`** (`condConst[csetSetTy]`, branches are SETS real→bool) — NOT `csetListTyAt`
   (that was memFilter's COND over lists). Build the per-V rewrites mirroring memFilter but at
   csetSetTy. 13. **β**: csetBetaClean the clamp-applied terms and `(λx.F) x` reductions so
   they aconv-match; the `listInductionThm` two hypotheses are CONJOINED (`P NIL ∧ step`),
   not curried — but you do NOT do list induction here, only memFilterThm (done) did. 14. The
   set-of-sets ops are RAW lambdas: `C V`=`csetSetMem[C,V]`=mkComb[C,V], `V x`=`csetSetAppV
   [V,x]`=mkComb[V,x].

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
stopped); `Syntax::sntx`+line = bracket/quote typo; `failed:K` with FAIL = aconv mismatch;
an `INST`/`SPEC`/`ISPEC` type error on the bridge = clamp instantiation (pitfall 11/12).

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
3. How the bridge (1) went: did `ISPEC[clamp, compactnessPrincipleThm]` typecheck first try;
   the clamp COND type; the covers/listSubcover ↔ setCovers/memFilter translation.
4. Whether Tier 2 shipped and how the INSERT compl S + FILTER-drop went.
5. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
6. Which tier fully proven vs stopped.
7. Open questions (empty if none).
