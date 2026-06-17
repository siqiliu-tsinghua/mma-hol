# Brief 029 — M8.4 Topology: complement + closed sets + subspace-closed (NEW FILE Real/Topology.wl)

## Goal

Create `stdlib/Real/Topology.wl` (a NEW frontier file in the `HOL`Stdlib`Real`
folder) with the static closed-set topology that general compactness (M8.5) will
consume: `compl` (set complement), `isClosed` (= isOpen of the complement),
`relativeClosed`/`closedIn` (subspace-closed, the closed analogue of brief-026/027's
`openIn`), `closedInSubsetThm`, and `closedIntervalIsClosedThm` (a closed interval
is a closed set). Create `tests/real_topology_tests.wl`. Self-verify with dev.wls,
iterate to green; graded delivery. (The sequence-interaction lemma
`limit_mem_of_closed` is a LATER brick — NOT in scope here.)

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealTopology/SetOps.lean` `Compl` (line 19);
`RealTopology/Closed.lean` `IsClosed` (line 10, `= IsOpen (Compl S)`);
`RealTopology/Subspace.lean` `RelativeClosed` (line 15) / `ClosedIn` (24) /
`closedIn_subset` (60); `RealTopology/Intervals.lean` (closed interval is closed —
mirror its `closedInterval`-is-closed lemma). Plain predicates, no records/countability.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **New file is FRONTIER** (`HOL`Stdlib`Real`, not in `bootstrap.mx`); dev loop:
  `wolframscript -file tests/dev.wls stdlib/Real/Topology.wl real_topology`.
  Connected.wl is ALSO an un-graduated frontier file but Topology.wl does NOT
  depend on it (it only uses Compact.wl's `isOpen`/`openInterval`/`closedInterval`,
  all graduated) — so name ONLY Topology.wl as frontier. If dev.wls's staleness
  guard complains about Connected.wl, add it: `… stdlib/Real/Connected.wl
  stdlib/Real/Topology.wl real_topology` (Connected first). Try Topology.wl-only first.
- **Imitate `stdlib/Real/Connected.wl`'s file skeleton** (same context + import list;
  the `*DefThm`/`*Const`/`*Tm`/`unfold*`/`*MemThm` idiom; the `connectedApplyDef`/
  `connectedSpecAll`-style private helpers — define your own `topo*` analogues or
  copy the pattern). GREP Connected.wl for `openInDefThm`/`openInConst`/`openInTm`/
  `unfoldOpenIn`/`openInSubsetThm` and MIRROR them for the closed versions.
- **Available (snapshot — VERIFIED, reachable by bare name in this folder):**
  - Compact.wl: `isOpenConst[]`/`isOpenTm[U]`/`unfoldIsOpen[U]` (⊢ isOpen U = ∀x.
    U x ⇒ ∃l r. realLt l x ∧ realLt x r ∧ ∀y. openInterval l r y ⇒ U y);
    `openIntervalConst[]`/`openIntervalTm[l,r,x]`/`openIntervalMemThm` (⊢ = realLt l x
    ∧ realLt x r); `closedIntervalConst[]`/`closedIntervalTm[l,r,x]`/`unfoldClosedInterval`/
    `closedIntervalMemThm` (⊢ closedInterval l r x = (realLe l x ∧ realLe x r)).
  - Order (Cut/Complete): `realLeReflThm`, `realLtNotLeThm` (⊢ ∀x y. realLt x y =
    ¬(realLe y x)), `realNotLeLtThm` (⊢ ∀x y. ¬(realLe x y) = realLt y x); `realLeTm`/
    `realLtTm`, `realAddTm`/`realNegTm`. `HOL`Auto`RealArith`realArithProve` (LINEAR —
    proves `realLt (x−1) x`, `realLt x (x+1)`); `HOL`Auto`PropTaut`propTaut` (the
    ¬(p∧q) bool reshuffles). A set is `real→bool`; `S x` = `mkComb[S,x]`; iff = `=`.
  - Bool/Equal/Kernel: CONJ/CONJUNCT1/2, DISJ1[thp,q]/DISJ2[thq,p], DISJCASES,
    EXISTS/CHOOSE, SPEC/GEN/MP/DISCH/ASSUME, EXCLUDEDMIDDLE, NOTINTRO/NOTELIM/CONTR,
    DEDUCTANTISYM, MKCOMB/APTERM/APTHM, EQMP/TRANS/REFL/SYM/BETACONV. The `¬`/`∧`/`∨`
    consts: `mkConst["¬", tyFun[boolTy,boolTy]]`, `mkConst["∧"/"∨", tyFun[boolTy,
    tyFun[boolTy,boolTy]]]` (or grep Connected.wl for `connectedAndConst`/`connectedNot…`).

## Scope

- CREATE: `stdlib/Real/Topology.wl`, `tests/real_topology_tests.wl`. Do NOT modify
  any other file, NO runner lists (Claude wires those at acceptance). MUST NOT touch
  Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/Connected/docs/
  codex(except report). No newAxiom.

## Definitions (pin — pointwise; reuse Compact's `isOpen`/`closedInterval`, do NOT redefine)

```
complDefThm:          ⊢ compl = (λS. (λx. ¬(S x)))
isClosedDefThm:       ⊢ isClosed = (λS. isOpen (compl S))
relativeClosedDefThm: ⊢ relativeClosed = (λS U. ∃V. isClosed V ∧ (∀x. (U x) = ((S x) ∧ (V x))))
closedInDefThm:       ⊢ closedIn = relativeClosed   (an alias; or define closedIn = relativeClosed directly)
```
`compl : (real→bool)→(real→bool)`; `isClosed : (real→bool)→bool`;
`relativeClosed`/`closedIn : (real→bool)→(real→bool)→bool`. Export `*Const[]`/`*Tm`/
`unfold*` (+ a `complMemThm` ⊢ ∀S x. (compl S) x = ¬(S x), β-reduced membership)
per constant, mirroring Connected.wl's idiom. Distinctive internal binders.

## Deliverable theorems

1. `complMemThm` ⊢ ∀S x. (compl S) x = ¬(S x). (APTHM complDef twice + BETACONV.)
2. `isClosedComplOpenThm` ⊢ ∀S. isClosed S = isOpen (compl S). (unfold isClosed —
   essentially the def; gives the working form.)
3. `closedInSubsetThm` ⊢ ∀S U. closedIn S U ⇒ ∀x. U x ⇒ S x. (mirror `openInSubsetThm`:
   unfold closedIn/relativeClosed, CHOOSE V, the iff at x → U x = (S x ∧ V x), CONJUNCT1.)
4. `closedIntervalIsClosedThm` ⊢ ∀a b. isClosed (closedInterval a b).
   Proof: isClosed = isOpen (compl (closedInterval a b)). unfoldIsOpen; intro x,
   hx : (compl (closedInterval a b)) x = ¬(closedInterval a b x) = ¬(a≤x ∧ x≤b)
   (complMem + closedIntervalMem rewrite). EXCLUDEDMIDDLE on `realLe a x`:
   - ¬(a≤x): `realNotLeLtThm` (a,x) → x<a. Witness l := a−1? NO — use l := realAdd x
     (realNeg 1) (= x−1), r := a. realArithProve `realLt (x−1) x`; x<r=a is the x<a.
     ∀y. openInterval (x−1) a y ⇒ (compl …) y: openIntervalMem → y<a (the right part);
     `realLtNotLeThm`(a,y) → ¬(a≤y); propTaut `¬(realLe a y) ⇒ ¬(realLe a y ∧ realLe y b)`;
     fold to `(compl (closedInterval a b)) y` via complMem + closedIntervalMem SYM.
   - a≤x: then ¬(x≤b) — propTaut from hx (¬(a≤x ∧ x≤b)) and (a≤x): `¬(p∧q) ⇒ p ⇒ ¬q`.
     `realNotLeLtThm`(x,b)... careful: ¬(x≤b) → b<x via `realNotLeLtThm` (b,x)? want b<x
     from ¬(realLe x b): realNotLeLtThm at (x,b) gives `¬(realLe x b) = realLt b x`. → b<x.
     Witness l := b, r := realAdd x 1 (= x+1). l=b<x, x<r=x+1 (realArith). ∀y. openInterval
     b (x+1) y ⇒ (compl …) y: openIntervalMem → b<y; `realLtNotLeThm`(y,b)→¬(y≤b); propTaut
     `¬(realLe y b) ⇒ ¬(realLe a y ∧ realLe y b)`; fold.
   DISJCASES; GEN a b.

## Stop-loss / graded delivery

Tier 1 (must): defs/const/tm/unfold + (1) complMem + (2) isClosedComplOpen + (3)
closedInSubset. Tier 2: (4) closedIntervalIsClosed (the only nontrivial proof — the
EXCLUDEDMIDDLE on a≤x + the two openInterval-neighbourhood witnesses + propTaut
reshuffles). If Tier 2 stalls (same failure twice), deliver Tier 1 green + STOP with
a precise report (which sub-goal, exact payload). A loadable subset is acceptable.

## Tests (create tests/real_topology_tests.wl, ~8 asserts)

- Imitate `tests/real_connected_tests.wl`'s header (`Needs[…]` + a `*TPT` prelude).
- Each def's `unfold*`/`*MemThm` body shape; `closedInSubset` concl shape;
  `closedIntervalIsClosed` concl shape (aconv on built expected; isThm + shallow
  probes). aconv against builders; no deep MatchQ. **NO `testExit[]`.**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. **Public-symbol shadow** —
`compl`/`isClosed`/`relativeClosed`/`closedIn` are FREE (verified); REUSE
`closedInterval`/`isOpen`/`openInterval` (TAKEN — Compact's), do NOT redefine. A bare
`foo=…` resolving to an imported symbol overwrites it ([[wl-public-symbol-shadow-collision]]).
4. HOL var identity=(name,type): distinctive binders. 5. holError HoldRest. 6. dev.wls
verifier. 7. aconv tests, no deep MatchQ, no testExit. 8. mkVar/mkConst/mkComb/mkAbs
only. 9. Narrow probes. 10. No Return in Do/For/While. 11. realArithProve is LINEAR
(the x−1<x / x<x+1 gaps only); ¬-of-∧ reshuffles are propTaut; ≤/< flips are
realLtNotLe/realNotLeLt. 12. set = real→bool; `S x` = mkComb[S,x]; iff = kernel `=`.
13. **β**: `(compl S) x`, `(closedInterval a b) x`, `(openInterval l r) y` are redexes
— reduce with complMem / closedIntervalMem / openIntervalMem so terms aconv-match.

## Verification (MANDATORY — you run wolframscript)

```
wolframscript -file tests/dev.wls stdlib/Real/Topology.wl real_topology
```
(If staleness-guarded on Connected.wl, use `… stdlib/Real/Connected.wl
stdlib/Real/Topology.wl real_topology`.) Loop edit → run → read failure → fix until
the tail prints `failed: 0`; paste the final `passed: N  failed: 0` VERBATIM. Do NOT
run build_snapshot/extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all,
no other command, nothing outside the repo, no network. Same failure twice → deliver
the loadable subset + report. If dev.wls reports a stale snapshot for some OTHER file,
STOP and report.

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
2. Name-verification table (each reused snapshot symbol → file:line; each NEW name
   confirmed free by grep).
3. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
4. Which tier fully proven vs stopped.
5. Open questions (empty if none).
