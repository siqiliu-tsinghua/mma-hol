# TODO — divergences from HOL Light worth tracking

Audit pass against `fusion.ml` / `equal.ml` / `drule.ml` / `bool.ml` / `meson.ml` reference. Items grouped by impact. Cross-reference `PLAN.md` for milestone scope.

## Soundness (real or potential)

### A. MESON search: ancestor-stack pollution under k>1 starts ✓ DONE
- **Where**: was `auto/Meson.wl:480` `attemptProveLits`.
- **Resolution**: split into `expandOne` (single goal) + `expandSiblings` (list, ancestors stay constant across siblings, σ + depth thread sequentially). Trace nodes for `start` / `extension` now carry sub-tree *lists*; `reduction` is a leaf (no `sub` slot); `["closed", {}]` retired. Replay rewritten: `closeLitProp` returns just the false-thm, `processStartProp` for k>1 ASSUMEs each lit and right-folds DISJCASES against the original clause theorem. MVP unit-start restriction lifted in `mesonProveProp`.
- **Side note** (deferred): the iterative-deepening search has no subsumption / clause ordering, so symmetric tautologies like `(p∨¬p) ∧ (q∨¬q) ∧ (r∨¬r)` (8 three-lit clauses, no units) are provable but combinatorial. Address when α-5 lands.

### B. MESON `@` tag stripping vs. user variable names
- **Where**: `auto/Meson.wl:551` `stripTagAtom` cuts at the first `@`; `renameClauseApart:420` produces `name@N`.
- **Symptom**: a user-supplied `var["foo@bar", _]` would be misparsed by the strip; `mkVar` does not forbid `@`.
- **HOL Light reference**: `variant` in `fusion.ml` produces fresh names by appending primes/digits and never relies on a single character being a forbidden separator.
- **Action**: simplest — reject `@` at `mkVar` (or use a structured wrapper head, e.g. `taggedVar[base, n]`, so stripping does not depend on character splitting).
- **Status**: pending; small.

## Expressiveness (limits later modules)

### C. `REWRCONV` is first-order match only ✓ DONE
- **Where**: was `Drule.wl:154` + `tryTermMatch:122`.
- **Resolution**: `tryTermMatch` now threads a `depth` parameter and dispatches at every `comb` node — when the spine is `comb[var[P, _], bvar1, …, bvarn]` with all args distinct in-scope binders, `tryHOMatch` binds `P ↦ λfv1…λfvn. tgt'` where `tgt'` replaces the matching-context bvars with fresh free vars (`millerSubstWalk` walks tgt depth-aware; fails on a context-bvar not in {ki}). First-order `var[_,_]` binding now rejects substitutes that contain matching-context bvars (`hasContextBvar`) so capturing rewrites can't slip through. `REWRCONV` post-INST runs `DEPTHCONV[TRYCONV[BETACONV]]` via `CONVRULE` to reduce the introduced redexes. Tests cover: single-arg Miller (`(∀x. P x) = Q` against `(∀y. f y)` and against `(∀y. y > 0)` with a non-trivial body); two-arg Miller; capturing-FO rejection; vacuous-binder still works when target has no matching-context bvars; inconsistent multi-occurrence `P` rejected; HO match under DEPTHCONV inside REWRITERULE.
- **Side note** (deferred): no eta-handling — pattern `(λx. P x)` matched against `f` binds `P ↦ λfv. f fv` instead of `P ↦ f`, so a non-Miller occurrence of `P` elsewhere in the same eqTh would fail the aconv consistency check. Term-net indexing for fast rule lookup also still TBD (mentioned in TODO.E side note).

### D. `INST` / `INSTTYPE` rely on `bvar`/`var` head disjointness for capture-freeness
- **Where**: `Kernel.wl:224, 231`.
- **Symptom**: capture-safe by construction (de-Bruijn), but two distinct free vars `var["x", α]` / `var["x", β]` collapse under a type instantiation that unifies α and β; merge happens silently in `normHyps`. Sound but surprising.
- **HOL Light reference**: `inst` raises `Clash` and renames via `variant` in the `Abs` branch.
- **Action**: optional cleanup — emit a clearer message when `INSTTYPE` collapses distinct free vars, or rename to keep them distinct.
- **Status**: pending; low priority.

## Robustness

### E. `REWRITERULE` has no loop / non-productivity detection ✓ DONE
- **Where**: was `Drule.wl:211` + `PropTaut.wl:fixpointConvRule`.
- **Resolution**: moved `fixpointConvRule` to `Drule.wl` as public, added cycle detection (record concls in a seen-set; break if a concl recurs without being equal to the previous one). Added `productiveEqThm[eqTh]` (returns False when LHS aconv RHS). `REWRITERULE` now accepts a single eq or a list, filters non-productive rules, combines via `ORELSEC`, and iterates to fixpoint via `fixpointConvRule`. Tests cover non-productive filtering and cycle termination on `p ↔ q` rule pairs.
- **Side note** (deferred): term-net indexing for fast rule lookup is still TBD — needed for SIMP scaling but not soundness.

### F. `CHOOSE` freshness errors leak to kernel layer ✓ DONE
- **Where**: `Bool.wl:303`.
- **Resolution**: `CHOOSE` now checks bodyTh hypotheses up front and throws `CHOOSE: v must not be free in body-hypotheses` before the proof reaches `GEN`/kernel `ABS`.
- **Regression**: added a negative test for v leaking through an extra body hypothesis and a positive control that the discharged body instance is still allowed.

### G. `SUBCONV` / `onceDepthConv` / `topDownAllConv` fresh-name uses body free-vars only ✓ DONE
- **Where**: `Drule.wl:77, 179, 214`.
- **Symptom**: `pickFreshName[origin, freesIn[body]]` ignores any free var the inner conversion `c` might introduce. Final `ABS[v, convTh]` will fail at the kernel if the chosen v gets shadowed, so soundness is preserved, but error surfaces at ABS.
- **HOL Light reference**: `ABS_CONV` retries via `Clash` exception with a re-variant'd binder.
- **Resolution**: added shared `absConvWithRetry` in `Drule.wl`; it catches only the kernel `ABS: binder occurs free in hypotheses` failure, extends the avoid-set with the converted theorem's free names, re-opens under a variant, and re-runs the inner conversion before `ABS`.
- **Regression**: `drule_tests.wl` covers the colliding `λx. T` / `T = x` case and keeps the existing normal `SUBCONV` abstraction case as a positive control.

## Performance

### H. `propTaut` is O(2^n) on free bool vars
- **Where**: `auto/PropTaut.wl:283`.
- **Note**: matches HOL Light's `TAUT` order. Fine for the schema lemmas (≤ 3 vars). Watch when SIMP starts auto-proving larger boolean side-conditions.
- **Status**: monitor.

### I. MESON preprocessing builds raw `comb[...]` bypassing `mkComb`
- **Where**: `auto/Meson.wl:157-166, 273` (Skolem term construction).
- **Note**: documented in-file as safe because the constants/types are pre-registered; replay re-runs through the kernel so any ill-typed term is caught downstream. Risk only if these terms escape into a non-replay path.
- **Status**: monitor.
