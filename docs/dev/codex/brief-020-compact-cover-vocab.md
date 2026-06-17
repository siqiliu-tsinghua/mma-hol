# Brief 020 — M8.2 Branch B: open-cover / topology vocabulary (append to Real/Compact.wl)

## Goal

Append the open-cover and basic point-set-topology VOCABULARY that the
Heine–Borel proof (FromNestedFinite, next brief) and the Lebesgue-number proof
need: `openInterval`, `closedInterval`, `isOpen`, `covers`, `listSubcover`,
`finiteSubcover`. This is a DEFINITIONS brief (newDefinition + builders + unfold
helpers + a couple of trivial shape lemmas), low proof content. Append to
`tests/real_compact_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint (in-repo — mirror the defs exactly)

- `tautology-ref/Tautology/RealTopology/Basic.lean`: `OpenInterval` (line 46),
  `IsOpen` (49), `Covers` (58).
- `tautology-ref/Tautology/RealTopology/Closed.lean`: `ClosedInterval` (16).
- `tautology-ref/Tautology/RealCompactness/Compact.lean`: `ListSubcover` (40),
  `FiniteSubcover` (45).
(These specific defs do NOT touch `Foundation.Cardinal` — only the
CountableSubcover/Lindelöf def does, which we skip.)

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **POLYMORPHIC INDEX TYPE.** `covers`/`listSubcover`/`finiteSubcover` are
  polymorphic in the cover's index type ι: the cover `U : ι → real → bool`.
  In HOL, introduce a type variable `iotaTy = mkVarType["iota"]` (or
  `tyVar["iota"]` — match how Set.wl/List.wl build polymorphic constants) and
  give these constants types containing it, e.g.
  `covers : (iota → real → bool) → (real → bool) → bool`. `newDefinition`
  accepts polymorphic constants (the defining term carries the type variable).
  `listSubcover` additionally uses `iota list` and `MEM : iota → iota list →
  bool` (List.wl's `memConst[]`/`nilConst[]`/`consConst[]` are polymorphic —
  instantiate at `iota`). Look at how `stdlib/Set.wl` defines polymorphic set
  operators and `stdlib/List.wl` builds `iota list` for the exact idiom.
- **Available:** List.wl `memConst[]` (MEM : α→α list→bool), `listTy[ty]`
  (builds `ty list`). Real folder: `realLtConst[]`/`realLeConst[]`,
  `forallTm`/`existsTm`/`conjTm`/`impTm` (grep Cut.wl / Compact.wl). Bool/Equal
  for the trivial unfold helpers (APTHM+BETACONV).

## Scope

- MODIFY: `stdlib/Real/Compact.wl` (append), `tests/real_compact_tests.wl`
  (append). Do NOT touch other files / runner lists. MUST NOT touch
  Kernel/Types/Terms/Bootstrap/bootstrap.mx/docs/codex(except report). No
  newAxiom. No new files.

## Definitions (pin EXACTLY; new constants + unfold helpers)

```
openIntervalDefThm:   ⊢ openInterval = (λleft right x. realLt left x ∧ realLt x right)
closedIntervalDefThm: ⊢ closedInterval = (λleft right x. realLe left x ∧ realLe x right)
isOpenDefThm:         ⊢ isOpen = (λU. ∀x. U x ⇒
    ∃left right. realLt left x ∧ realLt x right ∧
      (∀y. openInterval left right y ⇒ U y))
coversDefThm:         ⊢ covers = (λU S. ∀x. S x ⇒ ∃i. U i x)
listSubcoverDefThm:   ⊢ listSubcover = (λU S js. ∀x. S x ⇒ ∃i. MEM i js ∧ U i x)
finiteSubcoverDefThm: ⊢ finiteSubcover = (λU S. ∃js. listSubcover U S js)
```
- `openInterval`/`closedInterval` : real→real→(real→bool). `isOpen` :
  (real→bool)→bool. `covers`/`finiteSubcover` : (iota→real→bool)→(real→bool)→bool.
  `listSubcover` : (iota→real→bool)→(real→bool)→(iota list)→bool. (iota a type
  variable.) `U i x` is `mkComb[mkComb[U, i], x]`; `MEM i js` is
  `mkComb[mkComb[memConst[] @ iota, i], js]`.
- Export each `*Const[]`/`*Tm[…]` builder + `unfold*` helper (APTHM chain +
  BETACONV; for the multi-arg ones APTHM each arg then BETACONV, like
  `unfoldSubsequence` in Seq.wl).

## Deliverable theorems (trivial — just to exercise the unfolds)

1. The six `*DefThm` (newDefinition) + builders + unfold helpers.
2. `closedIntervalMemThm` ⊢ ∀left right x. closedInterval left right x =
   (realLe left x ∧ realLe x right) (the unfold at a point, β-reduced — a
   one-liner from unfoldClosedInterval).
3. `openIntervalMemThm` ⊢ ∀left right x. openInterval left right x =
   (realLt left x ∧ realLt x right).
(These two membership-unfold theorems are what the Heine–Borel proof will use
to open up interval membership; keep them public.)

## Tests (append ~8 asserts)

- Each `*DefThm` is a theorem with empty hyps; each `*Const[]` has the expected
  type (assert `typeOf`).
- `unfoldClosedInterval`/`unfoldOpenInterval` at fresh vars: concl is the
  expected mkEq (aconv).
- `closedIntervalMemThm`/`openIntervalMemThm` concl shape.
- For the polymorphic ones (`covers`/`finiteSubcover`): build a `covers U S`
  term at fresh `U : iota→real→bool`, `S : real→bool` and check
  `unfoldCovers` concl shape.
- aconv against built expected terms; no deep MatchQ. **NO `testExit[]` — end
  with the last `runTests[...]`.**

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder +
List/Set publics reachable. 4. **Polymorphic constants**: the type variable
`iota` must be the SAME `tyVar["iota"]` everywhere in a given def; `newDefinition`
on a polymorphic constant works but the const's type must contain the tyvar
(grep Set.wl `inConst`/`subsetConst` for the pattern). When building `U i x` /
`MEM i js`, instantiate `memConst[]` at iota (it's `α list` polymorphic).
5. holError HoldRest. 6. dev.wls is your verifier. 7. aconv tests, no deep
MatchQ, **no testExit**. 8. mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes.
10. No Return in Do/For/While. 11. SPEC/APTHM doesn't β-reduce — the unfold
helpers must BETACONV after the APTHM chain (multi-arg: APTHM each arg). 12. New
defs only — no heavy proofs; if a newDefinition is rejected (type error in the
defining term), the const type and the body type don't match — check the iota
tyvar threading.

## Verification (MANDATORY — you run wolframscript)

Full machine access. Compact.wl AND SeqAux.wl are BOTH un-graduated frontier
files; name BOTH (dependency order: SeqAux before Compact, since Compact's
Branch B will consume SeqAux):

```
wolframscript -file tests/dev.wls stdlib/Real/SeqAux.wl stdlib/Real/Compact.wl real_compact
```

Loop edit → run → read failure → fix until `failed: 0`; paste the final
`passed: N  failed: 0` into your report. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other
command, nothing outside the repo, no network. Same failure twice → deliver the
loadable subset + report. If dev.wls reports a stale snapshot for some OTHER
file, STOP and report (do not rebuild).

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls
  verification command.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (def/builder → file:line) + how you threaded the
   `iota` type variable.
3. The exact final `passed: N  failed: 0` from your dev.wls run.
4. Which defs/theorems landed vs stopped.
5. Open questions (empty if none).
