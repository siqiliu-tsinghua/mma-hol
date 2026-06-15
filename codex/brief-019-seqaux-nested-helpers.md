# Brief 019 — M8.2 Branch B prereq: two nested-interval helper lemmas (append to Real/SeqAux.wl)

## Goal

Append two small helper lemmas to `stdlib/Real/SeqAux.wl` (the sequence-layer
prereq file from brief-018) that the Heine–Borel proof (FromNestedFinite, the
next brief) needs: `intervalPointsCloseThm` (two points of a short interval are
within its length) and `lengthLtOfCloseThm` (a nonneg length whose distance to 0
is < eps is itself < eps). Both are short and build on existing lemmas. Append
to `tests/real_seqaux_tests.wl`. Self-verify with dev.wls, iterate to green.

## Blueprint

`tautology-ref/Tautology/RealSequence/Principles/NestedBasic.lean` —
`interval_points_close` (line 57) and `length_lt_of_close_to_zero` (line 44).
These are the ONLY two NestedBasic lemmas FromNestedFinite consumes. Mirror their
statements; the proofs here are even shorter because we have `realAbsSubLtThm`
and `realArithProve`.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- **Available, verified (grep ::usage):**
  - Seq.wl (graduated, in snapshot): `realAbsSubLtThm` ⊢ ∀x a e.
    realLt (realAdd a (realNeg e)) x ⇒ realLt x (realAdd a e) ⇒
    realLt (realAbs (realAdd x (realNeg a))) e (bounds ⇒ |x−a|<e).
  - Abs.wl: `realAbsPosThm` ⊢ ∀x. realLe 0 x ⇒ realAbs x = x.
  - RealArith.wl: `realArithProve[goalTm]` (LINEAR over opaque atoms — for the
    bound rearrangements; `realAbs …` is opaque so it cannot conclude an
    abs-atom, but it CAN prove the linear hyps you feed to realAbsSubLtThm and
    the `(b−a)+(−0) = b−a` identity).
  - SeqAux.wl helpers (brief-018, same file — reachable): `seqAuxRealLtCong`
    (APTERM realLt over two eqs), `seqAuxSpecAll`, the term builders; grep the
    file. `zeroRealTm[]` for the real 0.
  - Kernel/Equal: `APTERM`, `TRANS`, `REFL`, `EQMP`, `MP`, `SPEC`, `GEN`,
    `DISCH`; `realAbsConst[]` (Abs.wl) for APTERM onto |·|.

## Scope

- MODIFY: `stdlib/Real/SeqAux.wl` (append), `tests/real_seqaux_tests.wl`
  (append). Do NOT touch runner lists or any other file. MUST NOT touch
  Kernel/Types/Terms/Bootstrap/bootstrap.mx/docs/codex(except report). No
  newAxiom. No new files.

## Deliverable theorems

1. `intervalPointsCloseThm` ⊢ ∀a b x y eps.
   realLe a x ⇒ realLe x b ⇒ realLe a y ⇒ realLe y b ⇒
   realLt (realAdd b (realNeg a)) eps ⇒
   realLt (realAbs (realAdd x (realNeg y))) eps.
   Proof: from the four ≤ bounds + `(b + (−a)) < eps`, `realArithProve` proves
   both `realLt (realAdd y (realNeg eps)) x` (i.e. y−eps < x: because
   y−x ≤ b−a < eps) and `realLt x (realAdd y eps)` (x < y+eps: because
   x−y ≤ b−a < eps). Feed those two into `realAbsSubLtThm` SPEC'd at
   (x := x, a := y, e := eps) (MP MP) ⇒ realLt (realAbs (realAdd x (realNeg y))) eps.
   (Give realArithProve the bounds as ⇒-hypotheses; it abstracts a,b,x,y,eps as
   atoms — all linear.)
2. `lengthLtOfCloseThm` ⊢ ∀a b eps.
   realLe a b ⇒
   realLt (realAbs (realAdd (realAdd b (realNeg a)) (realNeg (zeroRealTm[])))) eps ⇒
   realLt (realAdd b (realNeg a)) eps.
   Let `len = realAdd b (realNeg a)`. (i) `realArithProve`: `0 ≤ len` from
   `a ≤ b` (linear). (ii) `realArithProve`: `realAdd len (realNeg 0) = len`
   (linear identity) → `eId`. (iii) `APTERM[realAbsConst[], eId]` →
   `realAbs (len + (−0)) = realAbs len`. (iv) `realAbsPosThm` SPEC len, MP the
   `0 ≤ len` → `realAbs len = len`. (v) TRANS (iii)(iv) →
   `realAbs (len + (−0)) = len`. (vi) `EQMP[seqAuxRealLtCong[that, REFL[eps]],
   hyp]` rewrites the hypothesis `realAbs (len + (−0)) < eps` to `len < eps`.
   DISCH/GEN.

## Tests (append ~6 asserts)

- `intervalPointsCloseThm`/`lengthLtOfCloseThm` concl-shape at fresh vars
  (aconv on built expected terms; full instantiation is heavy — shape + empty
  hyps suffices).
- A concrete check: SPEC at rnum literals where the bounds hold (e.g. a:=0,
  b:=1, x:=0, y:=1, eps:=2) + MP the rnum bound facts ⇒ a concrete |·|<2.
- aconv against folder builders; no deep MatchQ. **NO `testExit[]` — end with
  the last `runTests[...]`.**

## WL / project pitfalls (read twice)

1. No `_` in identifiers. 2. WL comments close at first `*)`. 3. In-folder +
SeqAux/Seq publics reachable. 4. HOL var identity=(name,type): GEN binders
canonical (a b x y eps), no stray scaffolding collisions. 5. holError HoldRest.
6. dev.wls is your verifier (Verification). 7. aconv tests, no deep MatchQ, **no
testExit**. 8. mkVar/mkConst/mkComb/mkAbs only. 9. Narrow probes. 10. No Return
in Do/For/While. 11. **realArithProve is LINEAR** — it proves the bound
rearrangements + the `len+(−0)=len` identity (atoms a,b,x,y,eps,len opaque); the
abs step is realAbsSubLtThm / realAbsPosThm, NOT realArithProve. 12. realAbsSubLtThm's
binder names are (x a e) — SPEC in that order: x:=x, a:=y, e:=eps.

## Verification (MANDATORY — you run wolframscript)

Full machine access. SeqAux.wl AND Compact.wl are BOTH un-graduated frontier
files, so name BOTH (dependency order) or dev.wls hits its staleness guard:

```
wolframscript -file tests/dev.wls stdlib/Real/SeqAux.wl stdlib/Real/Compact.wl real_seqaux
```

Loop edit → run → read failure → fix until `failed: 0`; paste the final
`passed: N  failed: 0` into your report. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other
command, nothing outside the repo, no network. Same failure twice → deliver the
loadable subset + report. If dev.wls still reports a stale snapshot for some
OTHER file, STOP and report (do not rebuild).

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
