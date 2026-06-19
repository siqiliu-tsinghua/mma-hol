# Contributing

This is primarily a personal learning and research project, so development is not
fast-paced and the scope is intentionally bounded (see `docs/dev/PLAN.md`). That said,
issues, questions, and pull requests are welcome.

## The one rule that matters

Soundness of the whole system reduces to a single small kernel. **No code outside
`Kernel.wl` may construct a value of the theorem type, and nothing outside `Kernel.wl`
may read or write the private kernel state** (`thmTag`, the constant/arity tables, the
axiom/definition registries — everything in `` HOL`Kernel`Private` ``). Term construction
above the kernel goes through `mkVar` / `mkConst` / `mkComb` / `mkAbs`, never raw
`comb[...]` / `abs[...]`. Adding a new axiom is a deliberate decision, not a casual one —
the axiom API is withdrawn after bootstrap on purpose.

A PR that needs to touch the kernel boundary should say so explicitly and explain why; a
PR that touches it *by accident* is a bug. Because the boundary is greppable (in Strict
mode there is no stable private name to grab), this is easy to check.

## Practical notes

- **Run the tests.** The authoritative gate is the cold Strict run:
  `wolframscript -file tests/run_all.wls`. For a fast inner loop use
  `wolframscript -file tests/run_fast.wls <pattern>` (restores the `bootstrap.mx`
  snapshot, ~3 s). Both must stay green, and the `passed:` count must not drop.
- **Style.** No `_` in identifiers (the Wolfram parser reads `FOO_BAR` as a pattern);
  libraries are `.wl` packages, entry points / tests / demos are `.wls`. Comments explain
  *why*, not *what* — names carry the *what*. More conventions live in `CLAUDE.md` and
  `docs/dev/PLAN.md`.
- **Where things go.** New milestones are folders, not monoliths; see `docs/dev/PLAN.md`
  §8.1. A new module must be added to the load lists in all three runners
  (`tests/run_all.wls`, `tests/run_all_stable.wls`, `tests/build_snapshot.wls`).

By contributing you agree that your contributions are licensed under the project's
[MIT License](LICENSE).
