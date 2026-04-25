# mma-hol — operational notes

Kernel-minimal higher-order logic theorem prover in Wolfram Language, LCF-style, modeled on HOL Light. Long-term target: mechanize undergraduate analysis through general Stokes and Fourier analysis, all within the Riemann-integral + Lebesgue-null-set framework (no full Lebesgue measure).

**Design document: `PLAN.md`** — authoritative for all architectural questions. This file is only the session-startup summary.

## Environment

- Wolfram Language 14.3 via `wolframscript` 1.13 (Linux). Notebooks are optional front-end only.
- All library code must be script-executable: `wolframscript foo.wls` — exit 0 pass, nonzero fail. This is a hard requirement, not a nice-to-have.

## Trust boundary (the one thing to never get wrong)

The **kernel** (types + terms + 10 primitive rules + axioms + `new_{constant,definition,basic_type_definition,axiom}`) is wrapped in a single `Module` whose `Unique["thm$"]`-gensymmed head is the sole legal constructor of `thm` values. Anything outside is untrusted. Worst-case bug in untrusted code is "can't prove a true theorem"; it must never be able to produce a false theorem.

Hard rules:

0. **Closure-based encapsulation is the project's originating design goal — non-negotiable.** All mutable kernel state (`thmTag`, `arityTable`, `constTypeTable`, `axiomList`, `defnList`, and any future registries) lives exclusively inside the `makeKernel[]` `Module` closure. External code — including other packages in the `HOL`` context tree — has no read or write path to these values; the only interface is the set of top-level functions the kernel installs. This models C++/Java-style private members with *true* inaccessibility via Wolfram's `Module` gensym mechanism. It overrides convenience: if a package elsewhere would be simpler with its own private `Association`, that's still not allowed. Previous code that kept state in a package-private context (e.g., M1's `arityTable` in `HOL`Types`Private``, M2's `constTypeTable` in `HOL`Terms`Private``) must be refactored to delegate into the kernel closure.
1. **`new_axiom` must disappear from the Kernel Association after bootstrap.** Three axioms (`ETA_AX`, `SELECT_AX`, `INFINITY_AX`) are declared during init; after that the API is withdrawn. Adding a new axiom is a user decision, not a Claude decision.
2. **Term construction above the kernel goes through `mkVar` / `mkConst` / `mkComb` / `mkAbs`.** Raw `comb[...]` / `abs[...]` literals bypass type-checking and α-normalization — forbidden outside the kernel module.
3. **Kernel is a singleton.** `makeKernel[]` runs once at load; no reset. To clear state, restart `wolframscript`.
4. **Bound variables are canonicalized to `_b0, _b1, …`** by `mkAbs`. The scheme is de-Bruijn *levels-from-binder*: inside any `abs`, the immediately enclosing binder's var is `_b0`; references to a binder k levels further out are `_b{k}`. So `λx. λy. x` ≡ `abs[_b0, abs[_b0, _b1, "y"], "x"]` — each abs binds its own `_b0`, and the `_b1` in the innermost body points one level out. The original binder name lives in the 3rd slot of `abs[v, body, origin]` for the printer only. **α-equivalence is `aconv`, not `===`** — `===` distinguishes the origin slot; `aconv` strips it. Kernel rules that compare terms up to α must use `aconv`.
5. **Printer correctness is independent of soundness.** A printer bug that renders `⊢ False` as `⊢ True` won't break the kernel but will deceive readers — printer needs regression tests.

## Conventions

- **File extensions**: libraries in `.wl` (`BeginPackage`/`EndPackage`); entry points, tests, demos in `.wls`; interactive notebooks `.nb` are optional.
- **Contexts**: `HOL`Kernel``, `HOL`Bool``, `HOL`Real``, … Private helpers in `` `Private` `` subcontext.
- **Errors**: kernel throws `Throw[Failure["HOLError", <|"tag" -> ..., "msg" -> ...|>], holErrorTag]`; top-level `Catch` in wolframscript entries. Tests assert on tag. **Do not use `Message` + `$Failed`** — cannot distinguish failure modes.
- **Tests**: `tests/harness.wl` provides `assertEq` / `assertTrue` / `assertThrows` / `runTests` / `testExit`; `tests/run_all.wls` is the CI entry — it auto-discovers `tests/*_tests.wl`. Nonzero exit = failure.
- **Package loading**: `tests/run_all.wls` holds an ordered list of library files (`ErrorUtil.wl`, `tests/harness.wl`, `Types.wl`, …) and `Get[]`s them in dependency order before discovering `tests/*_tests.wl`. Test files use `Needs["HOL`Whatever`"]` which is a no-op once the context is in `$Packages`. `Needs` cannot locate a flat-layout file on its own — always add new modules to the run_all load list.
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

Capstones: M3 `⊢ T`; M8 Lebesgue criterion for Riemann integrability; M9 general Stokes; M10 Poisson summation formula + Radon transform (the mathematical principle of CT reconstruction).

## Git

- Branch `main`. Local config: `Si-Qi Liu <liusq@tsinghua.edu.cn>`.
- Commit only when asked. Prefer new commits over `--amend`. Don't touch global git config.

## Current state

M1 + M2 + M3 + M4 done. Next is M5 (goal-oriented tactic layer).

- `Types.wl` (M1): pure type-layer — `tyVar`/`tyApp` heads, `mkVarType`, destructors, `tyvars`, `typeSubst`. No state.
- `Terms.wl` (M2): pure term-layer — `var`/`const`/`comb`/`abs` heads, `mkVar`/`mkComb`/`mkAbs` (α-canonicalizing), destructors/predicates, `typeOf`, `freesIn`, `vsubst`, `instType`, `aconv`, `stripOrigin`. No state, no `mkEq`/`mkConst`.
- `Kernel.wl` (M3a+b): the trust boundary. One `Module` closure owns `arityTable`, `constTypeTable`, `axiomList`, `defnList`, `axiomIntakeOpen`, and the `thmTag` gensym. Provides `mkType`/`typeArity`/`boolTy`/`indTy`/`tyFun` (state-aware), `mkConst`/`constType`/`listConstants`/`mkEq`, the 10 primitive rules (`REFL`, `TRANS`, `MKCOMB`, `ABS`, `BETA`, `ASSUME`, `EQMP`, `DEDUCTANTISYM`, `INST`, `INSTTYPE`), the 4 extension points (`newConstant`, `newType`, `newDefinition`, `newBasicTypeDefinition`, `newAxiom`), `lockAxioms`, and the theorem accessors (`destThm`, `hyp`, `concl`, `isThm`, `listAxioms`, `listDefinitions`). `=` is pre-registered as `α→α→bool`.
- `Bootstrap.wl` (M3c): declares the HOL logical constants — `T`, `∀`, `∧`, `⇒`, `∃`, `F`, `¬` via `newDefinition`; `@` (Hilbert ε) via `newConstant`; `ONE_ONE` and `ONTO` via `newDefinition`; then posts the three axioms `ETA_AX`, `SELECT_AX`, `INFINITY_AX` and calls `lockAxioms[]`. Exposes the returned theorems as `HOL`Bootstrap`tDef`, `forallDef`, …, `etaAx`, `selectAx`, `infinityAx`.
- `Equal.wl` (M4a): equality-flavored derived rules — `SYM`, `APTERM`, `APTHM`, and `BETACONV` (β-reduces any redex, generalizing the kernel's α-restricted `BETA`).
- `Bool.wl` (M4b): full boolean / quantifier toolkit on top of the bootstrap defs — `TRUTH`, `EQTINTRO`/`EQTELIM`, `GEN`/`SPEC`, `CONJ`/`CONJUNCT1`/`CONJUNCT2`, `MP`/`DISCH`/`UNDISCH`, `NOTINTRO`/`NOTELIM`/`CONTR`, `EXISTS`/`CHOOSE`, `orDef` (declared here, not in Bootstrap), `DISJ1`/`DISJ2`/`DISJCASES`, and the classical pair `EXCLUDEDMIDDLE` (Diaconescu via `selectAx`) + `CCONTR`.
- `Drule.wl` (M4c+d): conversion combinators (`ALLCONV`, `NOCONV`, `THENC`, `ORELSEC`, `TRYCONV`, `REPEATC`, `SUBCONV`, `DEPTHCONV`), first-order match-based `REWRCONV`, rule lifters `CONVRULE` / `ONCEREWRITERULE` / `REWRITERULE`, and `SUBS[{eq1,…,eqn}, th]` (literal-equality top-down substitution, single-pass; matches HOL Light SUBS semantics — no recursion into rewritten subterms, no unification of free LHS vars).

`tests/bootstrap_tests.wl` has the M3 capstone ⊢ T. `tests/bool_tests.wl` has the M4 capstone — `⊢ ∀x y. x = y ⇒ y = x` via `SYM` + `DISCH` + `GEN`. Running `wolframscript -file tests/run_all.wls` at repo root passes 354/0. Next: M5 — `goalstack` Module closure (another use of the closure-encapsulation idiom), `prove[term, tactic]` driver, basic tactics (`CONJ_TAC`, `DISJ1_TAC`, `GEN_TAC`, `EXISTS_TAC`, `REWRITE_TAC`, `ASSUME_TAC`) + combinators (`THEN`, `THENL`, `ORELSE`, `REPEAT`, `ALL_TAC`, `NO_TAC`).
