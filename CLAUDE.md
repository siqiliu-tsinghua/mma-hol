# mma-hol — operational notes

Kernel-minimal higher-order logic theorem prover in Wolfram Language, LCF-style, modeled on HOL Light. Long-term target: mechanize undergraduate analysis through general Stokes and Fourier analysis, all within the Riemann-integral + Lebesgue-null-set framework (no full Lebesgue measure).

**Design document: `PLAN.md`** — authoritative for all architectural questions. This file is only the session-startup summary.

## Environment

- Wolfram Language 14.3 via `wolframscript` 1.13 (Linux). Notebooks are optional front-end only.
- All library code must be script-executable: `wolframscript foo.wls` — exit 0 pass, nonzero fail. This is a hard requirement, not a nice-to-have.

## Trust boundary (the one thing to never get wrong)

The **kernel** (types + terms + 10 primitive rules + axioms + `new_{constant,definition,basic_type_definition,axiom}`) is wrapped in a single `Module` whose `Unique["thm$"]`-gensymmed head is the sole legal constructor of `thm` values. Anything outside is untrusted. Worst-case bug in untrusted code is "can't prove a true theorem"; it must never be able to produce a false theorem.

Hard rules:

1. **`new_axiom` must disappear from the Kernel Association after bootstrap.** Three axioms (`ETA_AX`, `SELECT_AX`, `INFINITY_AX`) are declared during init; after that the API is withdrawn. Adding a new axiom is a user decision, not a Claude decision.
2. **Term construction above the kernel goes through `mkVar` / `mkConst` / `mkComb` / `mkAbs`.** Raw `comb[...]` / `abs[...]` literals bypass type-checking and α-normalization — forbidden outside the kernel module.
3. **Kernel is a singleton.** `makeKernel[]` runs once at load; no reset. To clear state, restart `wolframscript`.
4. **Bound variables are canonicalized to `_b0, _b1, …`** by `mkAbs`; the original name lives in the 3rd slot of `abs[v, body, origin]` for the printer only. Structural equality ⟺ α-equivalence by construction.
5. **Printer correctness is independent of soundness.** A printer bug that renders `⊢ False` as `⊢ True` won't break the kernel but will deceive readers — printer needs regression tests.

## Conventions

- **File extensions**: libraries in `.wl` (`BeginPackage`/`EndPackage`); entry points, tests, demos in `.wls`; interactive notebooks `.nb` are optional.
- **Contexts**: `HOL`Kernel``, `HOL`Bool``, `HOL`Real``, … Private helpers in `` `Private` `` subcontext.
- **Errors**: kernel throws `Throw[Failure["HOLError", <|"tag" -> ..., "msg" -> ...|>], holErrorTag]`; top-level `Catch` in wolframscript entries. Tests assert on tag. **Do not use `Message` + `$Failed`** — cannot distinguish failure modes.
- **Tests**: `tests/harness.wl` provides `assertEq` / `assertTrue` / `assertThrows` / `runTests` / `testExit`; `tests/run_all.wls` is the CI entry — it auto-discovers `tests/*_tests.wl`. Nonzero exit = failure.
- **Package loading**: every entry script (`*.wls`) sets `$Path` to include the repo root and `tests/`, then `Get[...]`s `ErrorUtil.wl` + `tests/harness.wl` before any test file. Never rely on global `$Path` configuration.
- **Failure payload access**: `Failure[tag, assoc]` — `[[1]]` is the tag string, `[[2]]` is the association. Always read keys via `f[[2, "tag"]]`, never `f[[1, "tag"]]`.
- **No comments describing what code does** — names should carry that. Comments only for non-obvious *why*.

## Directory layout (see PLAN §8 for the full tree)

```
Kernel.wl  Basics.wl  Bool.wl  Equal.wl  Drule.wl  Tactics.wl  Parser.wl  Printer.wl
auto/        — MESON / SIMP / SET / ARITH / REAL_ARITH
stdlib/      — Pair, Sum, Option, Set, Num, Int, Rat, Real, List, Finite, (Complex)
analysis1/   — M8: one-variable analysis → Lebesgue integrability criterion
analysis2/   — M9: multivariable, Jordan, forms, general Stokes
analysis3/   — M10: function series, parametric integrals, Fourier
tests/  demos/
```

## Milestones (PLAN §7 has the detail)

M1 Types · M2 Terms · M3 Kernel (10 rules + bootstrap) · M4 Derived rules · M5 Tactics · M6 Parser/Printer · M7 stdlib + 5 automation tactics (`MESON`/`SIMP`/`SET`/`ARITH`/`REAL_ARITH`) · M8 one-var analysis · M9 multivariable → Stokes · M10 function series + parametric integrals → Fourier.

Capstones: M3 `⊢ T`; M8 Lebesgue criterion for Riemann integrability; M9 general Stokes; M10 Parseval + Schwartz-class Fourier inversion.

## Git

- Branch `main`. Local config: `Si-Qi Liu <liusq@tsinghua.edu.cn>`.
- Commit only when asked. Prefer new commits over `--amend`. Don't touch global git config.

## Current state

Harness committed: `ErrorUtil.wl`, `tests/harness.wl`, `tests/run_all.wls`, plus self-tests `tests/{harness,errorutil}_tests.wl`. Running `wolframscript -file tests/run_all.wls` at repo root passes 19/0. Next step is M1 (types).
