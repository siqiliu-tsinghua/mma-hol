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

### C. `REWRCONV` is first-order match only
- **Where**: `Drule.wl:154` + `tryTermMatch:122`.
- **Symptom**: cannot rewrite under binders when the LHS encodes a higher-order pattern (e.g. `∀x. P x ⇒ Q x`). Standard HOL Light rewrite rules rely on Miller-pattern higher-order matching (`term_match` / `PART_MATCH`).
- **Action**: add HO-pattern matching when M7 SIMP work begins; until then stay with first-order on hand-written schemas.
- **Status**: pending; blocks SIMP / SET_TAC / REAL_ARITH.

### D. `INST` / `INSTTYPE` rely on `bvar`/`var` head disjointness for capture-freeness
- **Where**: `Kernel.wl:224, 231`.
- **Symptom**: capture-safe by construction (de-Bruijn), but two distinct free vars `var["x", α]` / `var["x", β]` collapse under a type instantiation that unifies α and β; merge happens silently in `normHyps`. Sound but surprising.
- **HOL Light reference**: `inst` raises `Clash` and renames via `variant` in the `Abs` branch.
- **Action**: optional cleanup — emit a clearer message when `INSTTYPE` collapses distinct free vars, or rename to keep them distinct.
- **Status**: pending; low priority.

## Robustness

### E. `REWRITERULE` has no loop / non-productivity detection
- **Where**: `Drule.wl:211` via `fixpointConvRule:370`.
- **Symptom**: cyclic rule sets (e.g. `p = q` and `q = p`) loop; productivity check is concl-stability only — exponential blowup before that fires.
- **HOL Light reference**: `REWRITE_CONV` analyses each rule and indexes via term nets; rules whose RHS aconv LHS are dropped, term nets prune candidates.
- **Action**: add (i) per-rule `aconv` non-productivity drop; (ii) eventually a term-net index. Required before SIMP scaling.
- **Status**: pending; required before SIMP.

### F. `CHOOSE` freshness errors leak to kernel layer
- **Where**: `Bool.wl:303`.
- **Symptom**: explicit checks for v ∉ FV(qRes), v ∉ hyps(existsTh); the v-not-in-bodyTh-hyps check is implicit via `GEN`'s internal `ABS`, so the user sees "ABS: binder occurs free in hypotheses" instead of a CHOOSE-tagged error. Sound, but UX.
- **Action**: add the bodyTh-hyps check up front in CHOOSE, with its own tag.
- **Status**: pending; cosmetic.

### G. `SUBCONV` / `onceDepthConv` / `topDownAllConv` fresh-name uses body free-vars only
- **Where**: `Drule.wl:77, 179, 214`.
- **Symptom**: `pickFreshName[origin, freesIn[body]]` ignores any free var the inner conversion `c` might introduce. Final `ABS[v, convTh]` will fail at the kernel if the chosen v gets shadowed, so soundness is preserved, but error surfaces at ABS.
- **HOL Light reference**: `ABS_CONV` retries via `Clash` exception with a re-variant'd binder.
- **Action**: catch the kernel ABS failure and retry with a fresh variant.
- **Status**: pending; low impact at current scale.

## Performance

### H. `propTaut` is O(2^n) on free bool vars
- **Where**: `auto/PropTaut.wl:283`.
- **Note**: matches HOL Light's `TAUT` order. Fine for the schema lemmas (≤ 3 vars). Watch when SIMP starts auto-proving larger boolean side-conditions.
- **Status**: monitor.

### I. MESON preprocessing builds raw `comb[...]` bypassing `mkComb`
- **Where**: `auto/Meson.wl:157-166, 273` (Skolem term construction).
- **Note**: documented in-file as safe because the constants/types are pre-registered; replay re-runs through the kernel so any ill-typed term is caught downstream. Risk only if these terms escape into a non-replay path.
- **Status**: monitor.
