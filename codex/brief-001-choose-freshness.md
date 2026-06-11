# Brief 001 — CHOOSE: front-load the bodyTh-hyps freshness check (TODO.md item F)

## Goal

`HOL`Bool`CHOOSE[v, existsTh, bodyTh]` currently checks v ∉ FV(conclusion of
bodyTh) and v ∉ FV(hyps of existsTh), but NOT v ∉ FV(the *other* hypotheses
of bodyTh). When a caller violates that, the failure surfaces much later as
the kernel's "ABS: binder occurs free in hypotheses" (thrown by GEN deep
inside CHOOSE's implementation) — sound, but a confusing UX. Add the missing
up-front check with a CHOOSE-tagged error, add regression tests, and mark
TODO.md item F as done.

## Context pointers

- Read `CLAUDE.md` (Conventions + Trust boundary sections) first.
- `Bool.wl` lines ~359–395: the `CHOOSE` implementation. Read it fully before
  editing — in particular figure out WHICH hypothesis of bodyTh is discharged
  (the assumed instance is `pv = mkComb[P, v]` β-reduced via
  `bodyFromPv = EQMP[betaPv, assPv]`; trace the `withHyp/dischTh` lines that
  follow to see the exact term form that gets discharged).
- Error style to copy: the existing checks at Bool.wl:372–377
  (`HOL`Error`holError["rule", "CHOOSE: …", <|…|>]`).
- `TODO.md` item F describes this task (status: pending; cosmetic).
- Existing CHOOSE tests: `grep -n "CHOOSE" tests/*.wl` to find the right test
  file and its local conventions; add your tests next to them.

## Scope

- Files you MAY modify: `Bool.wl` (inside the `CHOOSE[v : var[...], ...]`
  definition only), the one tests file that already tests CHOOSE, `TODO.md`
  (item F only).
- Files you MUST NOT touch: `Kernel.wl`, `Types.wl`, `Terms.wl`,
  `Bootstrap.wl`, `bootstrap.mx`, `CLAUDE.md`, `PLAN.md`, `PROGRESS.md`,
  everything under `stdlib/`, `auto/`, `codex/`.
- Do NOT add new axioms or call `newAxiom`.

## Deliverable

- A new up-front check in `CHOOSE`: v (by name, matching the existing
  `vName`-based checks) must not occur free in any hypothesis of `bodyTh`
  EXCEPT the discharged instance itself. **Getting the exception right is
  the whole task**: the discharged hypothesis necessarily contains v free,
  so a naive "v ∉ FV(all bodyTh hyps)" check would reject every legitimate
  CHOOSE call. Exclude the discharged instance by comparing with `aconv`
  against the exact term form the implementation discharges (verify whether
  that is the β-reduced body instance, the un-β-reduced `P v`, or both —
  decide from the code, and exclude exactly what DISCH later removes).
- Error: `holError["rule", "CHOOSE: v must not be free in body-hypotheses", <|"v" -> v|>]`
  (same style as the two adjacent checks).
- Tests (in the existing CHOOSE test file, using its conventions):
  1. Negative: a CHOOSE call where v occurs free in an extra hypothesis of
     bodyTh now throws with the CHOOSE message/tag —
     `HOLTest`assertThrows` (look at how neighbouring tests assert on
     thrown HOLErrors and copy that exactly).
  2. Positive control: a normal CHOOSE call (v free ONLY in the discharged
     hypothesis) still succeeds — this guards against over-rejection.
- `TODO.md` item F: change status to ✓ DONE with a 2–3 line resolution note
  in the same style as items A/C/E.

## WL / project pitfalls

(From TEMPLATE.md — all nine apply. The ones most likely to bite here:)

1. No `_` in identifiers, including Module locals (camelCase only).
2. WL comments close at the first `*)`.
5. Errors via `HOL`Error`holError`; tests assert on the tag/message.
6. `wolframscript -file …` always.
7. `assertThrows` usage: copy an existing instance from the same test file.
9. Debug with narrow probes, never whole-term dumps.

Additional, task-specific:

- `freesIn` returns a list of `var[name, ty]`-like entries; the existing
  checks use `MemberQ[Map[First, freesIn[#]], vName]` — checking BY NAME.
  Keep the new check consistent with that (by name, not by full var), and
  keep it cheap (it runs on every CHOOSE call; CHOOSE is on hot proof paths
  — thousands of calls per suite run).
- `hyp[bodyTh]` gives the hypothesis list.

## Verification (in order; record exact numbers)

1. `wolframscript -file tests/build_snapshot.wls` (~7 min — Bool.wl is in the
   snapshot, so it must be rebuilt before fast tests).
2. `wolframscript -file tests/run_fast.wls` — expect `failed: 0`. This is the
   critical over-rejection guard: CHOOSE is used pervasively, so if your
   check is too strict, dozens of existing tests will fail here.
3. If `wolframscript` cannot run in your sandbox: say so and deliver
   unverified — do not fake outputs.

## Hard rules

- No git commit/branch/push. Leave changes in the working tree.
- Stop-loss: same failure twice → stop and report.
- Minimal diff.

## Report format

1. What changed — per file, line ranges, one-line why. State explicitly which
   term form(s) you exclude as "the discharged instance" and why.
2. Verification — commands + exact pass/fail counts.
3. Open questions.
