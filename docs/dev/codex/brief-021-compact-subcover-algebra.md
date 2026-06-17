# Brief 021 — M8.2 Branch B: midpoint + mem-append + subcover-combine (append to Real/Compact.wl)

## Goal

Append to `stdlib/Real/Compact.wl` the foundations the Heine–Borel bisection
proof (FromNestedFinite, the next brief) needs: `midpoint` (+ its order/length
facts), two MEM/APPEND list lemmas, the `noFiniteSubcover` predicate, and the
subcover-combining lemmas `combineHalfSubcoverThm` / `finiteSubcoverOfHalvesThm`
/ `rightHalfBadThm`. Mostly mechanical; the only real proofs are two small list
inductions. Append to `tests/real_compact_tests.wl`. Self-verify with dev.wls,
iterate to green.

## Blueprint (in-repo — mirror)

`tautology-ref/Tautology/RealCompactness/ClosedInterval/FromNestedFinite.lean`:
`combine_half_subcovers` (line 28), `finiteSubcover_of_halves` (49),
`right_half_bad_of_left_finite` (61), `NoFiniteSubcover` (def, line ~20).
`midpoint` is in `RealSequence/Algebra.lean` (`midpoint a b = (a+b)/2`, with
`left_le_midpoint`/`midpoint_le_right`/`left_lt_midpoint`/`midpoint_lt_right`).

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- Compact.wl + SeqAux.wl are graduated? NO — both frontier (committed, not in
  snapshot). The dev.wls command (Verification) names BOTH.
- **Available (grep ::usage):**
  - Compact.wl (brief-020, same file): `closedInterval`/`closedIntervalTm`/
    `unfoldClosedInterval`/`closedIntervalMemThm`, `finiteSubcover`/`…Tm`/unfold,
    `listSubcover`/`…Tm`/unfold, `covers`, `isOpen`, the `iota` tyvar idiom +
    `compactMemTmAt`-style MEM-at-iota builders (grep how brief-020 threaded
    iota). Use the SAME iota tyvar.
  - List.wl: `appendConst[]` (APPEND), `appendNilThm` ⊢ ∀l. APPEND NIL l = l;
    `appendConsThm` ⊢ ∀x l1 l2. APPEND (CONS x l1) l2 = CONS x (APPEND l1 l2);
    `memNilThm` ⊢ ∀x. MEM x NIL = F; `memConsThm` ⊢ ∀x y l. MEM x (CONS y l) =
    (x = y ∨ MEM x l); `listInductionThm` (list induction); `nilConst`/`consConst`.
    All polymorphic — instantiate at iota.
  - Real: `realArithProve` (for ALL midpoint order/length facts — it knows the
    `1/2` literal); `realLeTotalThm`; Bool (`EXCLUDEDMIDDLE`, `DISJCASES`,
    `CHOOSE`, `CONJ`, `CONJUNCT1/2`, `EXISTS`, `MP`, `propTaut`).

## Scope

- MODIFY: `stdlib/Real/Compact.wl` (append), `tests/real_compact_tests.wl`
  (append). Do NOT touch other files / runner lists. MUST NOT touch Kernel/Types/
  Terms/Bootstrap/bootstrap.mx/docs/codex(except report). No newAxiom. No new files.

## Definitions (pin)

```
midpointDefThm:         ⊢ midpoint = (λa b. realMul (realAdd a b) (realInv <2 literal>))
noFiniteSubcoverDefThm: ⊢ noFiniteSubcover = (λU a b. ¬(finiteSubcover U (closedInterval a b)))
```
- `<2 literal>` = `&ℝ(&ℚ(&ℤ(SUC(SUC 0))))` (grep SeqAux.wl `seqAuxTwoReal` for the
  builder — but that's SeqAux-private; rebuild locally with the folder builders).
  `midpoint : real→real→real`. `noFiniteSubcover : (iota→real→bool)→real→real→bool`.
  Export `*Const[]`/`*Tm`/unfold helpers.

## Deliverable theorems

Midpoint (all via `realArithProve` after unfolding midpoint to `(a+b)·(1/2)`):
1. `leftLeMidpointThm` ⊢ ∀a b. realLe a b ⇒ realLe a (midpoint a b).
2. `midpointLeRightThm` ⊢ ∀a b. realLe a b ⇒ realLe (midpoint a b) b.
3. `leftLtMidpointThm` ⊢ ∀a b. realLt a b ⇒ realLt a (midpoint a b).
4. `midpointLtRightThm` ⊢ ∀a b. realLt a b ⇒ realLt (midpoint a b) b.
5. `midpointSubLeftThm` ⊢ ∀a b. realAdd (midpoint a b) (realNeg a) =
   realMul (realAdd b (realNeg a)) (realInv <2>) (i.e. midpoint−a = (b−a)/2).
6. `rightSubMidpointThm` ⊢ ∀a b. realAdd b (realNeg (midpoint a b)) =
   realMul (realAdd b (realNeg a)) (realInv <2>) (b−midpoint = (b−a)/2).
   (For 1–6: SPEC midpointDefThm, rewrite the `midpoint a b` occurrences to
   `(a+b)·(1/2)` via the unfold, then the goal is a LINEAR fact over a,b with the
   1/2 literal — one `realArithProve` call each. realArithProve treats `realInv
   <2>` as the literal 1/2.)

MEM/APPEND (list induction on the first list, at iota):
7. `memAppendLeftThm` ⊢ ∀i js ks. MEM i js ⇒ MEM i (APPEND js ks).
   `listInductionThm` on js: NIL → MEM i NIL = F (memNilThm), so the hyp is F,
   CONTR/EQF. CONS y t → APPEND (CONS y t) ks = CONS y (APPEND t ks)
   (appendConsThm); MEM i (CONS y t) = (i=y ∨ MEM i t) (memConsThm); IH:
   MEM i t ⇒ MEM i (APPEND t ks); so i=y → MEM i (CONS y (APPEND t ks)) (memCons
   head); MEM i t → IH + memCons tail. propTaut/DISJCASES glue.
8. `memAppendRightThm` ⊢ ∀i js ks. MEM i ks ⇒ MEM i (APPEND js ks).
   listInduction on js: NIL → APPEND NIL ks = ks (appendNilThm), MEM i ks given;
   CONS y t → MEM i (APPEND t ks) by IH, then memCons tail into CONS y (APPEND t ks).

Subcover combine (mirror the blueprint):
9. `combineHalfSubcoverThm` ⊢ ∀U a m b js ks.
   listSubcover U (closedInterval a m) js ⇒ listSubcover U (closedInterval m b) ks ⇒
   listSubcover U (closedInterval a b) (APPEND js ks).
   GEN x, DISCH (closedInterval a b x); unfold to `a≤x ∧ x≤b`. EXCLUDEDMIDDLE
   `realLe x m`: if x≤m → closedInterval a m x (a≤x from the conj, x≤m), apply
   hleft (it's `∀x. closedInterval a m x ⇒ ∃i. MEM i js ∧ U i x` after unfold) →
   CHOOSE i, `MEM i js ∧ U i x`; `memAppendLeftThm` → MEM i (APPEND js ks); EXISTS.
   else `realLeTotalThm` gives m≤x → closedInterval m b x → hright → memAppendRight.
   Fold back into listSubcover (SYM unfold).
10. `finiteSubcoverOfHalvesThm` ⊢ ∀U a m b.
    finiteSubcover U (closedInterval a m) ⇒ finiteSubcover U (closedInterval m b) ⇒
    finiteSubcover U (closedInterval a b). CHOOSE js, ks; EXISTS (APPEND js ks) +
    combineHalfSubcoverThm.
11. `rightHalfBadThm` ⊢ ∀U a b m.
    noFiniteSubcover U a b ⇒ finiteSubcover U (closedInterval a m) ⇒
    noFiniteSubcover U m b. Unfold noFiniteSubcover (both); contrapositive:
    DISCH (finiteSubcover U [m,b]), `finiteSubcoverOfHalvesThm` ⇒ finiteSubcover
    U [a,b], contradict the `¬finiteSubcover U [a,b]` hyp; NOTINTRO.

Stop-loss: if the list inductions (7,8) stall, deliver midpoint (1–6) + defs and
STOP with a report.

## Tests (append ~10 asserts)

- Defs unfold + builder types.
- midpoint facts (1–6) concl shapes at fresh a,b (aconv); a concrete: midpoint
  0 2 = 1 via realArithProve-checkable (SPEC + the unfold; assert).
- memAppendLeft/Right concl shapes; a concrete: MEM i (CONS i NIL) ++ … (small).
- combineHalfSubcover / rightHalfBad concl shapes at fresh U,a,m,b,js,ks (aconv).
- aconv against folder builders; no deep MatchQ. **NO `testExit[]`.**

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder +
Compact/SeqAux/List publics reachable. 4. **iota tyvar**: same `mkVarType["iota"]`
as brief-020; MEM/APPEND/listSubcover all instantiated at iota; combine's `U` is
`iota→real→bool`. 5. holError HoldRest. 6. dev.wls is your verifier. 7. aconv
tests, no deep MatchQ, **no testExit**. 8. mkVar/mkConst/mkComb/mkAbs only.
9. Narrow probes. 10. No Return in Do/For/While. 11. SPEC/APTHM doesn't β-reduce
(unfold midpoint then BETACONV before realArithProve). 12. **realArithProve is
LINEAR + knows the 1/2 literal** — all midpoint order/length facts are one
realArithProve call after unfolding `midpoint a b → (a+b)·(1/2)`; do NOT hand-build
them. 13. `MEM x (CONS y l) = (x=y ∨ MEM x l)` and APPEND equations are
EQUATIONS — rewrite with EQMP/SUBS, MEM/APPEND are bool/list-valued, not Props.
14. `listInductionThm` shape: SPEC the predicate `λl. <goal about l>`, MP the NIL
base + the CONS step (∀x l. P l ⇒ P (CONS x l)); β-clean.

## Verification (MANDATORY — you run wolframscript)

Full machine access. Both frontier files named:

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
2. Name-verification table (lemma/builder → file:line).
3. The exact final `passed: N  failed: 0` from your dev.wls run.
4. Which theorems fully proven vs stopped.
5. Open questions (empty if none).
