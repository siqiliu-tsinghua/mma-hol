# Brief 002 — SUBCONV/onceDepthConv/topDownAllConv: retry ABS with a fresh variant (TODO.md item G)

## Goal

The three abstraction-descending conversion combinators in `Drule.wl` pick a
fresh binder name via `pickFreshName[origin, freesIn[body]]` — i.e. from the
*body's* free variables only. If the inner conversion `c` introduces a NEW
free variable that happens to collide with the chosen binder, the final
kernel `ABS[v, convTh]` fails with a kernel-level error instead of the
combinator recovering. Soundness is intact (the kernel rejects), but the fix
is to do what HOL Light's `ABS_CONV` does: catch that failure and retry once
with a binder name that also avoids the free variables of the inner
conversion's RESULT. Mark TODO.md item G done; add regression tests.

## Context pointers

- Read `CLAUDE.md` (Conventions; the error-protocol bullet especially).
- `Drule.wl` around lines 77, 179, 214 — the three sites (`SUBCONV`'s abs
  branch, `onceDepthConv`, `topDownAllConv`). Read all three plus
  `pickFreshName` before editing; factor the shared retry into ONE local
  helper rather than three copies if the three sites are structurally alike.
- Error protocol: kernel failures arrive as
  `Throw[Failure["HOLError", <|"tag"->…, "msg"->…|>], HOL`Error`holErrorTag]`.
  You can intercept with `Catch[expr, HOL`Error`holErrorTag]` and inspect the
  result: a `Failure` head means it threw. Read the payload via
  `f[[2, "msg"]]` (NOT `f[[1, …]]`). Re-throw anything that is not the ABS
  binder-collision failure (match on the msg text the kernel actually emits —
  find it in `Kernel.wl`'s ABS implementation by grep, but DO NOT modify
  Kernel.wl).
- Retry strategy: on ABS collision, re-pick the binder via `pickFreshName`
  with the avoid-set extended by the free names of the failed attempt's
  conversion result (and the body), re-instantiate, re-run the inner
  conversion, re-ABS. One retry is mathematically sufficient in practice;
  cap at 3 and let the kernel error propagate beyond that (no infinite loop).

## Scope

- Files you MAY modify: `Drule.wl` (the three combinators + one new private
  helper), the existing Drule test file (find it: `grep -ln "SUBCONV" tests/*.wl`),
  `TODO.md` (item G only).
- Files you MUST NOT touch: `Kernel.wl`, `Types.wl`, `Terms.wl`,
  `Bootstrap.wl`, `bootstrap.mx`, `Bool.wl`, `CLAUDE.md`, `PLAN.md`,
  `PROGRESS.md`, `stdlib/`, `auto/`, `codex/`.
- Do NOT add new axioms.

## Deliverable

- The catch-retry in all three combinators (shared helper preferred).
- Tests in the existing Drule test file:
  1. A conversion that introduces a colliding free variable inside an
     abstraction now SUCCEEDS through SUBCONV (and/or onceDepthConv), with
     the result binder renamed to a variant. Construction sketch: an eq
     theorem whose RHS contains a free variable named exactly like the
     abstraction's binder (e.g. `ASSUME[mkEq[c0, mkVar["x", ty]]]` used as a
     REWRCONV rule against a target `λx. …c0…` — the combinator picks "x",
     the inner conversion's result now has a free "x", ABS would clash).
     Verify the pre-fix behaviour first (it should throw) to make sure your
     test actually exercises the path, then confirm the fix makes it pass.
  2. A normal SUBCONV call still works unchanged (positive control).
- `TODO.md` item G → ✓ DONE with a 2–3 line resolution note in the style of
  items A/C/E.

## WL / project pitfalls

All nine from `codex/TEMPLATE.md` apply. Task-specific:

- Failure payload access is `f[[2, "tag"]]` / `f[[2, "msg"]]`.
- `Catch` must use the tag `HOL`Error`holErrorTag` — a bare `Catch[expr]`
  would swallow unrelated throws.
- The retry must re-run the INNER conversion on the re-instantiated body —
  you cannot reuse the failed attempt's convTh (its free/bound structure is
  tied to the old binder).
- Keep the no-collision fast path allocation-free: do not restructure the
  combinators; wrap only the failing step.

## Verification

1. `wolframscript -file tests/build_snapshot.wls` (~8 min; Drule.wl is in the
   snapshot).
2. `wolframscript -file tests/run_fast.wls` — expect `failed: 0`.
3. If `wolframscript` is unavailable in your sandbox, state so and deliver
   unverified; do not fake outputs.

## Hard rules

- No git commit/branch/push; leave changes in the working tree.
- Stop-loss: same failure twice → stop and write the report.
- Minimal diff.

## Report format

1. What changed — files, line ranges, the shared-helper signature, and the
   exact kernel msg text you match on for the collision case.
2. Verification — commands + exact counts (or "unavailable in sandbox").
3. Open questions.
