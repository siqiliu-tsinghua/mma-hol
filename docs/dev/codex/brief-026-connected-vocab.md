# Brief 026 — M8.3 Connectedness: vocabulary + interval-set basics (NEW FILE Real/Connected.wl)

## Goal

Create `stdlib/Real/Connected.wl` (a NEW frontier file in the `HOL`Stdlib`Real`
folder) and establish the whole connectedness/IVT vocabulary plus its trivial
consequences: the subspace-open predicate `openIn`, the set-predicate helpers
`setNonempty`/`setDisjoint`/`coversByTwo`, the connectedness defs
`isSeparation`/`isConnected`, the order defs `between`/`isIntervalSet`, the four
ray sets, then the easy lemmas — `openInSubset`, ray openness, the two small
order helpers (`ltOrGtOfNe`, `existsRightBetween`), `isSeparationSymm`,
`connectedEmpty`, and the nine `intervalSet_*` membership lemmas. This is the
broad-but-shallow foundation brief (like brief-020 for compactness); the two HARD
directions (`connected ⇒ interval`, `interval ⇒ connected`/IVT) are briefs
027/028 and are NOT in scope here. Create `tests/real_connected_tests.wl`.
Self-verify with dev.wls, iterate to green; graded delivery.

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealConnectedness/Connected.lean` lines 11–182 (defs +
ray openness + `lt_or_gt_of_ne` + `exists_right_between` + `isSeparation_symm` +
`connected_empty` + the `intervalSet_*` block) and
`tautology-ref/Tautology/RealTopology/Subspace.lean` lines 9–13 (`RelativeOpen`)
+ 52–58 (`openIn_subset`). Read those. Mirror their statements; our proofs are
the same shape (plain predicates + order lemmas — NO records, NO countability).

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **New file is FRONTIER** (`HOL`Stdlib`Real`, not in `bootstrap.mx`); the dev
  loop names it: `wolframscript -file tests/dev.wls stdlib/Real/Connected.wl real_connected`.
  SeqAux.wl + Compact.wl are now IN the snapshot (graduated 2026-06-16), so do NOT
  name them as frontier files.
- **Imitate `stdlib/Real/Compact.wl`'s structure** for the file skeleton:
  `BeginPackage["HOL`Stdlib`Real`", {…same import list as Compact.wl…}]`, a usage
  block with `::usage` for every PUBLIC symbol, `Begin["`Private`"]`, the term-
  builder + `*DefThm`/`*Const`/`*Tm`/`unfold*` pattern, `End[]`, `EndPackage[]`.
  Grep Compact.wl for `openIntervalDefThm`/`openIntervalConst`/`openIntervalTm`/
  `unfoldOpenInterval`/`openIntervalMemThm` (lines ~490–520) and COPY that exact
  def→const→tm→unfold→mem idiom for each new constant.
- **Available (snapshot — VERIFIED, reachable by bare name in this folder):**
  - From Compact.wl: `isOpenConst[]`/`isOpenTm[U]`/`unfoldIsOpen[U]` (⊢ isOpen U =
    ∀x. U x ⇒ ∃l r. realLt l x ∧ realLt x r ∧ ∀y. openInterval l r y ⇒ U y);
    `openIntervalConst[]`/`openIntervalTm[l,r,x]`/`openIntervalMemThm` (⊢ ∀l r x.
    openInterval l r x = (realLt l x ∧ realLt x r)); `midpoint`/`leftLtMidpointThm`
    (⊢ ∀a b. realLt a b ⇒ realLt a (midpoint a b)) / `midpointLtRightThm`
    (⊢ … realLt (midpoint a b) b) / `leftLeMidpointThm` / `midpointLeRightThm`
    (≤ versions). (These are Compact.wl publics — reachable since same folder/context.)
  - Order (Cut.wl/Complete.wl): `realLeReflThm`, `realLeTransThm`, `realLeAntisymThm`,
    `realLeTotalThm` (⊢ ∀x y. realLe x y ∨ realLe y x), `realLtNotLeThm`
    (⊢ ∀x y. realLt x y ⇒ ¬(realLe y x)); `realNotLeLtThm` (⊢ ∀x y. ¬(realLe x y) =
    realLt y x — in Compact.wl); `realLtImpLeThm`, `realLtLeTransThm`,
    `realLeLtTransThm`, `realLtTransThm`. Builders `realLtTm`/`realLeTm`,
    `realAddTm`/`realNegTm`, `realOfRat`-based `oneReal`… for `1`: grep Compact for
    `compactTwoReal`/`compactHalfScalar` to see how a real literal is built; build
    `x−1` / `x+1` with `realAddTm` + `realNegTm` + a real `1` (= `realOfRatTm[oneQ[]]`
    or the literal Compact uses — VERIFY by grep).
  - `HOL`Auto`RealArith`realArithProve[goalTm]` — LINEAR; proves `realLt (x−1) x`,
    `realLt x (x+1)` (the ray-openness gap facts) and any linear order rearrangement.
  - Bool/Equal/Drule: `CONJ`/`CONJUNCT1`/`CONJUNCT2`, `DISJ1`/`DISJ2`/`DISJCASES`,
    `EXISTS`/`CHOOSE`, `SPEC`/`GEN`/`MP`/`DISCH`/`ASSUME`, `EXCLUDEDMIDDLE`,
    `NOTINTRO`/`NOTELIM`/`CCONTR`/`CONTR`; `BETACONV`, `APTHM`, `EQMP`, `REFL`, `SYM`;
    `eqfIntro` is Bool-PRIVATE — if you need ¬p⊢p=F, rebuild locally (per CLAUDE).
  - bool `T`/`F` = `HOL`Bool`trueTm[]`-style; grep Bool.wl for the truth/false term
    builders. For the empty set use `λx. F`, universal `λx. T`, singleton a `λx. x=a`.

## Scope

- CREATE: `stdlib/Real/Connected.wl`, `tests/real_connected_tests.wl`. Do NOT
  modify any other file, NO runner lists (Claude wires those at graduation). MUST
  NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact.wl/Seq.wl/SeqAux.wl/
  docs/codex(except report). No newAxiom.

## Definitions (pin — pointwise, mirror the blueprint; `(S x)` = application `mkComb[S,x]`; iff on bool = kernel `=`)

```
openInDefThm:       ⊢ openIn = (λS U. ∃V. isOpen V ∧ (∀x. (U x) = ((S x) ∧ (V x))))
setNonemptyDefThm:  ⊢ setNonempty = (λS. ∃x. S x)
setDisjointDefThm:  ⊢ setDisjoint = (λU V. ∀x. ¬((U x) ∧ (V x)))
coversByTwoDefThm:   ⊢ coversByTwo = (λS U V. ∀x. (S x) = ((U x) ∨ (V x)))
isSeparationDefThm:  ⊢ isSeparation = (λS U V. openIn S U ∧ openIn S V ∧
                        setNonempty U ∧ setNonempty V ∧ coversByTwo S U V ∧ setDisjoint U V)
isConnectedDefThm:   ⊢ isConnected = (λS. ∀U V. ¬(isSeparation S U V))
betweenDefThm:       ⊢ between = (λx y z. realLe x y ∧ realLe y z)
isIntervalSetDefThm: ⊢ isIntervalSet = (λS. ∀x y z. S x ⇒ S z ⇒ between x y z ⇒ S y)
openLowerRayDefThm:  ⊢ openLowerRay = (λcut x. realLt x cut)
openUpperRayDefThm:  ⊢ openUpperRay = (λcut x. realLt cut x)
closedLowerRayDefThm:⊢ closedLowerRay = (λcut x. realLe x cut)
closedUpperRayDefThm:⊢ closedUpperRay = (λcut x. realLe cut x)
```
Set types: a set is `real→bool`; `openIn : (real→bool)→(real→bool)→bool`;
`setNonempty : (real→bool)→bool`; `coversByTwo/isSeparation` take 2/3 set args;
rays `real→real→bool` (cut→x→bool). Export `*Const[]`/`*Tm[…]`/`unfold*[…]`
(+ a `*MemThm`-style applied form where a downstream lemma needs it) per constant,
mirroring Compact.wl's openInterval idiom. Use DISTINCTIVE internal binder names
(`xCn`, `yCn`, `vCn` — never bare `x/y/V` a caller's term might carry).

## Deliverable theorems (mirror the blueprint; all EASY)

1. `openInSubsetThm` ⊢ ∀S U. openIn S U ⇒ ∀x. U x ⇒ S x.
   (unfold openIn, CHOOSE V (distinctive `vCn`), the iff at x gives U x = (S x ∧ V x);
   from U x get (S x ∧ V x), CONJUNCT1.)
2. `openLowerRayIsOpenThm` ⊢ ∀cut. isOpen (openLowerRay cut).
   (unfoldIsOpen; intro x, hx : x<cut; witness l := x−1, r := cut; EXISTS both;
   realArithProve `realLt (x−1) x`; x<cut = hx (rewrite openLowerRay at x via unfold);
   ∀y. openInterval (x−1) cut y ⇒ y<cut: openIntervalMemThm gives y<cut = the right
   conjunct, fold to `openLowerRay cut y` via SYM unfold.)
3. `openUpperRayIsOpenThm` ⊢ ∀cut. isOpen (openUpperRay cut). (witness cut, x+1; symmetric.)
4. `ltOrGtOfNeThm` ⊢ ∀x y. ¬(x = y) ⇒ realLt x y ∨ realLt y x.
   (`realLeTotalThm` SPEC x y → x≤y ∨ y≤x; DISJCASES. In the x≤y branch, EXCLUDEDMIDDLE
   on `realLe y x`: if y≤x then `realLeAntisymThm` gives x=y, contradict the hyp via
   CONTR→the disjunction; if ¬(y≤x) then `realNotLeLtThm` gives realLt x y, DISJ1.
   Symmetric in the y≤x branch with DISJ2.)
5. `existsRightBetweenThm` ⊢ ∀x y z. realLt x y ⇒ realLt x z ⇒
   ∃d. realLt x d ∧ realLe d y ∧ realLt d z.
   (EXCLUDEDMIDDLE on `realLe y z`: TRUE → d := midpoint x y; realLt x d =
   `leftLtMidpointThm` MP (x<y); realLe d y = `midpointLeRightThm` MP (realLtImpLe x<y);
   realLt d z = `realLtLeTransThm` (midpointLtRight x<y : d<y)(y≤z). FALSE → from
   ¬(y≤z) `realNotLeLtThm`/`realLeTotalThm` get z≤y; d := midpoint x z; realLt x d =
   leftLtMidpoint (x<z); realLe d y = `realLeTransThm`(midpointLeRight (le x<z): d≤z)(z≤y);
   realLt d z = midpointLtRight (x<z).)
6. `isSeparationSymmThm` ⊢ ∀S U V. isSeparation S U V ⇒ isSeparation S V U.
   (unfold both; reassemble the 6-conjunction swapping U↔V: openIn S V, openIn S U,
   nonempty V, nonempty U, coversByTwo S V U (from coversByTwo S U V: at x,
   (S x)=(U x ∨ V x); ∨-comm to (V x ∨ U x) — propTaut/`HOL`Auto`PropTaut`propTaut`
   on the bool eq, or APTERM disj-comm), setDisjoint V U (from setDisjoint U V:
   ¬(U x ∧ V x) ⇒ ¬(V x ∧ U x), propTaut).)
7. `connectedEmptyThm` ⊢ isConnected (λxCn. F) (the empty set).
   (unfold isConnected; GEN U V, assume isSeparation (λx.F) U V; from it nonempty U =
   ∃x. U x, CHOOSE x with U x; openInSubsetThm on (openIn (λx.F) U) gives U x ⇒ (λx.F) x
   = F; so F holds → CONTR / `CCONTR` to ¬isSeparation.)
8. `intervalSet{Empty,Universal,Singleton,OpenInterval,ClosedInterval,OpenLowerRay,
   OpenUpperRay,ClosedLowerRay,ClosedUpperRay}Thm` — the nine. Each: unfold
   isIntervalSet, intro x y z, hx hz hbetween, prove S y:
   - Empty (λx.F): hx : F → CONTR. Universal (λx.T): S y = T = TRUTH.
   - Singleton a: hx : x=a, hz : z=a; between x y z = (a≤y ∧ y≤a) → y=a (antisym) = S y.
   - OpenInterval l r: hx : l<x ∧ x<r, hz, hbetween : x≤y ∧ y≤z; S y = l<y ∧ y<r via
     `realLtLeTransThm`(l<x)(x≤y) and `realLeLtTransThm`(y≤z)(z<r). ClosedInterval: ≤ via realLeTrans.
   - Rays: openLowerRay cut: hz : z<cut, hbetween y≤z → y<cut (realLeLtTrans).
     openUpperRay: hx : cut<x, x≤y → cut<y (realLtLeTrans). closed rays via realLeTrans.

## Stop-loss / graded delivery

Tier 1 (must): ALL defs/const/tm/unfold + `openInSubsetThm` + `betweenDefThm`/
`isIntervalSetDefThm` + the nine `intervalSet_*` (8). Tier 2: ray openness (2,3) +
`ltOrGtOfNeThm` (4) + `existsRightBetweenThm` (5). Tier 3: `isSeparationSymmThm` (6)
+ `connectedEmptyThm` (7). If a tier stalls (same failure twice), deliver the green
lower tiers and STOP with a precise report. A loadable subset is fully acceptable.

## Tests (create tests/real_connected_tests.wl, ~12 asserts)

- Imitate `tests/real_compact_tests.wl`'s header (the `Needs[…]` block + the `*RCT`
  term-builder prelude — copy what you need; you may define a fresh `*CNT` prelude).
- Each def's `unfold*` body shape (aconv on a built expected term); `openInSubset`
  concl shape; ray-openness `isThm` + concl shape; the nine `intervalSet_*` concl
  shape (or `isThm` + a shallow probe). aconv against builders; NO deep MatchQ.
  **NO `testExit[]`** — end the file with the last `runTests[...]`.

## WL / project pitfalls (read twice)

1. No `_` idents (Module locals too). 2. comments close at first `*)`. 3. **Public
symbols collide across imported contexts** — before naming a constant, grep the
snapshot files for a same-short-name `::usage` (e.g. do NOT reuse `between`/`isOpen`
if taken); `isOpen`/`openInterval`/`midpoint` ARE taken (reuse them, don't redefine).
A bare `foo = …` that resolves to an imported symbol overwrites it (see
[[wl-public-symbol-shadow-collision]]) — keep new names distinct (`openIn`,
`coversByTwo`, `isSeparation`, `isConnected`, `between`, `isIntervalSet`,
`openLowerRay`… are all free — VERIFY by grep). 4. HOL var identity=(name,type):
distinctive internal binders. 5. holError HoldRest. 6. dev.wls verifier (below).
7. aconv tests, no deep MatchQ, **no testExit**. 8. mkVar/mkConst/mkComb/mkAbs only.
9. Narrow probes. 10. No Return in Do/For/While. 11. realArithProve is LINEAR (the
x−1<x / x<x+1 gaps + the order rearrangements only; the ∨/¬ bool reshuffles in
isSeparationSymm are `propTaut`, NOT realArithProve). 12. **A set is `real→bool`**;
`S x` is `mkComb[S, x]`; iff between bools is kernel `=` (so `(U x) = ((S x)∧(V x))`
is a bool equation). 13. Reuse Compact.wl's def→const→tm→unfold idiom verbatim;
each `unfold*[…]` = APTHM the def per arg + BETACONV (grep `unfoldOpenInterval`).

## Verification (MANDATORY — you run wolframscript)

Full machine access. ONE frontier file (SeqAux/Compact are graduated):

```
wolframscript -file tests/dev.wls stdlib/Real/Connected.wl real_connected
```

Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste the
final `passed: N  failed: 0` line VERBATIM into your report. Do NOT run
build_snapshot/extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no
other command, nothing outside the repo, no network. Same failure twice → deliver
the loadable subset (per the tiers) + report exactly where it broke. If dev.wls
reports a stale snapshot for some OTHER file, STOP and report (do not rebuild).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls
  verification command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did
  not reach it, say so explicitly and report where it stopped — do NOT claim green
  without the verbatim count line (this was a problem on a prior brief).**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused snapshot symbol → file:line; each NEW
   constant name → confirmed free by grep).
3. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
4. Which theorems (by tier) fully proven vs stopped.
5. Open questions (empty if none).
