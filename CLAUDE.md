# mma-hol — operational notes

Kernel-minimal higher-order logic theorem prover in Wolfram Language, LCF-style, modeled on HOL Light. **Phase-1 release target (scope tightened 2026-05): first-semester single-variable real analysis — M8, through the Lebesgue-null-set criterion for Riemann integrability; declare stage-complete, then publish to GitHub.** Multivariable → general Stokes (M9) and Fourier → Poisson summation / Radon inversion (M10) are deferred to future phases. All within the Riemann-integral + Lebesgue-null-set framework (no full Lebesgue measure).

**Design document: `PLAN.md`** — authoritative for all architectural questions. This file is the session-startup summary only; per-milestone proof detail lives in git commit messages and code comments.

## Environment

- Wolfram Language 14.3 via `wolframscript` 1.13 (Linux). Notebooks are optional front-end only.
- All library code must be script-executable: `wolframscript foo.wls` — exit 0 pass, nonzero fail. Hard requirement.

## Trust boundary (the one thing to never get wrong)

The **kernel** (types + terms + 10 primitive rules + axioms + `new_{constant,definition,basic_type_definition,axiom}`) owns all `thm` value construction. Anything outside is untrusted. Worst-case bug in untrusted code is "can't prove a true theorem"; it must never produce a false theorem.

Hard rules:

0. **All mutable kernel state — `thmTag`, `arityTable`, `constTypeTable`, `axiomList`, `defnList`, `axiomIntakeOpen`, and any future registries — lives in `HOL`Kernel`Private`*`. Read or write outside `Kernel.wl` is forbidden.** Two modes via `Global` $HOLEncapsulationMode`: **`"Strict"`** (default, CI) hides the six state symbols as Module-local gensyms; **`"Stable"`** (dev/persistence) gives them fixed names so `DumpSave` snapshots survive cold boots — there the boundary is convention + CI lint (any `HOL`Kernel`Private`*` reference outside `Kernel.wl` is a bug). Both modes share one `Kernel.wl` body via the `defineKernel[...]` installer; CI runs the full suite in both. Don't add new mutable kernel state outside `HOL`Kernel`Private`*`.
1. **`new_axiom` must disappear after bootstrap.** `ETA_AX`/`SELECT_AX`/`INFINITY_AX` are declared during init, then the API is withdrawn (`lockAxioms[]`). Adding a new axiom is a user decision, not a Claude decision.
2. **Term construction above the kernel goes through `mkVar`/`mkConst`/`mkComb`/`mkAbs`.** Raw `comb[...]`/`abs[...]` literals bypass type-checking and α-normalization — forbidden outside the kernel module.
3. **Kernel is a singleton.** `makeKernel[]` runs once at load; no reset. To clear state, restart `wolframscript`.
4. **Bound variables use a separate head `bvar[k_Integer, ty]`** (de-Bruijn levels-from-binder): inside any `abs`, the immediately enclosing binder is `bvar[0, ty]`, k levels out is `bvar[k, ty]`. The origin name lives in `abs[bv, body, origin]`'s 3rd slot for the printer only. Free vars (`var[name, ty]`) and bound vars are structurally distinct heads. **α-equivalence is `aconv`, not `===`** (`===` distinguishes origin) — kernel rules comparing up to α must use `aconv`.
5. **Printer correctness is independent of soundness.** A printer bug rendering `⊢ False` as `⊢ True` won't break the kernel but deceives readers — printer needs regression tests.

## Conventions

- **工作语言 / Working language**: 与用户交流的首选语言为**中文**，其次为**英文**;禁止使用其它任何语言(包括日语)。代码、标识符、commit message 仍用英文。
- **File extensions**: libraries `.wl` (`BeginPackage`/`EndPackage`); entry points/tests/demos `.wls`; notebooks `.nb` optional.
- **Contexts**: `HOL`Kernel``, `HOL`Bool``, … Private helpers in `` `Private` `` subcontext. **Private symbols don't cross files** — a helper/value defined in one file's `` `Private` `` (e.g. `numInductBy`, `numTy`, `plusTm` in Num.wl) is unreachable by bare name elsewhere; reference the full `HOL`Pkg`Private`name` path or redefine locally, else it silently stays unevaluated and trips a "not a theorem" / "mkComb type mismatch" far downstream.
- **Errors**: kernel throws `Throw[Failure["HOLError", <|"tag"->…, "msg"->…|>], holErrorTag]`; top-level `Catch` in `.wls` entries. Tests assert on tag. **Never `Message` + `$Failed`.** Read payload via `f[[2, "tag"]]` (not `f[[1, …]]`).
- **Tests**: `tests/harness.wl` gives `assertEq`/`assertTrue`/`assertThrows`/`runTests`/`testExit`. Runners: `tests/run_all.wls` (cold-boot Strict, CI, ~10-15 min); `tests/run_all_stable.wls` (cold-boot Stable, CI sanity); `tests/run_fast.wls [pattern…]` (restore `bootstrap.mx` snapshot, run matching files, ~3 s). Rebuild snapshot via `tests/build_snapshot.wls` after any library/`Kernel.wl` change (runner checks mtimes). `kernel_tests.wl` is skipped from the fast runner.
- **Adding a module**: add it to the load lists in all three runners — `tests/run_all.wls`, `tests/run_all_stable.wls`, and `tests/build_snapshot.wls` (dependency order). Forgetting `run_all_stable.wls` is how the Stable suite silently drifts out of sync with Strict. Test files use `Needs["HOL`…`"]` which is a no-op once loaded but can't locate flat-layout files on its own.
- **No comments describing what code does** — names carry that. Comments only for non-obvious *why*.
- **No `_` in identifiers**: WL parses `FOO_BAR` as `Pattern[FOO, Blank[BAR]]`, silently introducing separate symbols that can shadow imports. Applies to Module locals too (`x_eq` → `xEq`). Tactics camelCase (`conjTac`, `asmSimp`); combinators ALL-CAPS underscore-free (`THEN`, `REPEAT`, `SIMP`, `MESON`).
- **No `Function[{_}, body]`**: `_` is not a valid Function parameter; WL emits `Function::flpar`, leaves the call unevaluated, and garbage propagates into kernel functions. Use a real symbol.
- **WL comments close at the first `*)`** — `(a*)`, `(SUC k*)` etc. in comment prose silently terminate the comment; error points far below the cause.
- **`mkAbs` binds by (name, type), not reference** — an internal binder `mkVar["j", ty]` captures a caller-supplied free var of the same name. Use distinctive internal binder names (`jBnd`, `kBnd`) or `freshName`.
- **Resource cost vs convenience**: on hot paths (anything per-node in proof traversal — `freesIn`, `vsubst`, `instType`, `betaSubst`, `tyvarsInTerm`, `aconv`) prefer the costlier-to-write but cheaper-to-run alternative. (Worked precedent: structural `bvar[k, ty]` head over name-encoded indices — ~2× faster per traversal at the price of a `bvar` clause in every term walker.)
- **Debug with narrow probes, never whole-term dumps.** When a kernel rule fails mid-proof, do NOT `Print` the full term tree (`Print[concl[th]]` / `Print[…Short[#,5]&]` on a deep term) — one such dump is thousands of chars, and every later turn re-pays for it in context. Instead probe narrowly: `Head[th]` (is it a `thmTag` or an unevaluated call?), `hyp[th]`, `MatchQ[concl[th], <small pattern>]`, or print a single sub-slot (`concl[th][[1,2]]`). Binary-search the failing step by moving a single shape check, not by dumping everything. Token cost is dominated by accumulated context, so a few KB of term-tree spam per build round compounds fast. (Snapshot rebuilds are wall-clock-heavy but token-cheap; the expensive thing is large tool output.)

## Directory layout (see PLAN §8 for the full tree)

```
Kernel.wl  Basics.wl  Bool.wl  Equal.wl  Drule.wl  Tactics.wl  Parser.wl  Printer.wl
auto/        — MESON / SIMP / SET / ARITH / REAL_ARITH
stdlib/      — Pair, Sum, Option, Set, Num, Int, Rat, Real, List, Finite, (Complex)
analysis1/   — M8: one-variable analysis → Lebesgue integrability criterion  [Phase-1 release target]
analysis2/   — M9: multivariable, Jordan, forms, general Stokes  [deferred]
analysis3/   — M10: function series, parametric integrals, Fourier  [deferred]
tests/  demos/
```

## Milestones (PLAN §7 has the detail)

M1 Types · M2 Terms · M3 Kernel (10 rules + bootstrap) · M4 Derived rules · M5 Tactics · M6 Parser/Printer · M7 stdlib + 5 automation tactics (`MESON`/`SIMP`/`SET`/`ARITH`/`REAL_ARITH`) · **M8 one-var analysis [Phase-1 release target]** · M9 multivariable → Stokes [deferred] · M10 function series + parametric integrals → Fourier [deferred].

Capstones: M3 `⊢ T`; **M8 Lebesgue criterion for Riemann integrability (Phase-1 release capstone)**; M9 general Stokes [deferred]; M10 Poisson summation + Radon transform [deferred].

## Git

- Branch `main`. Local config: `Si-Qi Liu <liusq@tsinghua.edu.cn>`.
- Commit only when asked. Prefer new commits over `--amend`. Don't touch global git config.

## Current state

M1–M6 done (kernel, derived rules, tactics, parser+printer; **M6b notebook front-end CUT 2026-05**).

**M7 automation** — `MESON`/`SIMP`/`asmSimp`/`SET` substantially complete. `ARITH` (auto/Arith.wl) does **linear ℕ (∀/∃/= + atom abstraction)** via a Fourier–Motzkin oracle + kernel verifier (Farkas certificates, ℕ-native — NOT internal Cooper QE; Cooper cut 2026-05-28, see memory `project_arith_oracle_verifier`). `REAL_ARITH` (M7-ε) not started; MESON Brand-modulation + NOT_FORALL/NOT_EXISTS NNF deferred till a goal forces them.

**M7 stdlib** — Pair, Sum, Option, Set, Num, List, Finite, FTA done. **`stdlib/Int.wl` COMPLETE** — ordered integral domain: `&ℤ` embedding; `intNeg`/`intSucc`/`intPred`; `intAdd`/`intMul` (comm·assoc·distrib·identity); no-zero-divisors `intMulEqZeroThm` + cancellation `intMulCancelThm`; order `intLe`/`intLt` (refl/antisym/trans/total + add/neg/mul-nonneg monotonicity); `intAbs`; bidirectional induction `intInductionThm`. Engine: Grothendieck-equivalence `canon{Equiv,Inj,Respects}` + `repInt{Add,Mul}`, ARITH discharging FST/SND-atom num glue. **`stdlib/Rat.wl` — ℚ IS A DENSELY-ORDERED FIELD (M7-6 COMPLETE, stages a–g)** (cold Strict run_all 1994/0, dev_rat 177/0): reduced fractions over `int×num`, kernel `=` IS rational equality (no setoid); additive abelian group (`ratAdd` comm/assoc/zero + `ratNeg`) + commutative ring (`ratMul` comm/one/zero/assoc/distrib) + `ratInv`/`ratMulInvThm`; lowest-terms uniqueness `ratEqCrossThm`. **Order** `ratLe`/`ratLt` via cross-multiplication (reduces to Int's `intLe` on cross-products): linear-order axioms + compatibility `ratLeAddMonoThm`/`ratLeMulNonnegThm` (Int helpers `intLeMulNonnegCancelThm` + `pairLeCong{Left,Right}Thm`); strict-order `ratLtAddMonoThm`/`ratLtMulPosCancelThm` + `ratAddSubCancelThm`. **`&ℚ` ring/order homomorphism** `ratOfInt{Add,Mul,Le}Thm` + **density** `ratDenseThm` (`q<r ⇒ q<½(q+r)<r`, midpoint via `ratMulTwoThm` `x·2=x+x` + `ratMulInv`). Engine: **ratCanon-respects + add/mul cong tower** + the pairLeCong order tower. Still carries ℕ Bezout/Gauss (`bezoutNatThm`/…) + int magnitude lemmas (`intSqNatAbsThm`/…) **pending migration to Num/Int.wl**.

**NEXT TASK (fresh session resumes here): ℝ (after M7-6 + its housekeeping, both done).** ℚ is complete and the snapshot housekeeping is done — `bootstrap.mx` now **includes Rat** (rebuilt 2026-06-02, 823 KB) and `tests/dev_rat.wls` is **deleted**; the Rat dev loop is now `tests/run_fast.wls rat_tests` (~3 s, from the snapshot, 177/0). Remaining before/alongside ℝ: (1) optionally migrate the ℕ Bezout/Gauss + int magnitude lemmas from `stdlib/Rat.wl` to their proper homes `Num.wl`/`Int.wl` (currently "pending migration" — a refactor, needs a snapshot rebuild after). (2) The next number-tower step **ℝ** (`stdlib/Real.wl`) — Dedekind cuts or Cauchy sequences over ℚ, using ℚ's dense order + field structure; see memory `m7_finite_and_number_tower_plan`. The ratCanon-respects + cong tower + pairLeCong order tower are reusable patterns.

**Live gaps:** ARITH `arithProve` rejects `¬(=)` hyps (`toLeqFact` throw) — convert via `ltZeroNotZeroThm` to `0<·` first. Audit issues in `TODO.md`.

**Detailed per-stage proof history → `PROGRESS.md`** (moved out of this file 2026-06-02 to keep it lean). Authoritative detail: `git log` + code comments. Design rationale: `PLAN.md`.

## Module map (public role + key exports; internals in the source)

- `Types.wl` (M1): type layer — `tyVar`/`tyApp`, `mkVarType`, `tyvars`, `typeSubst`. No state.
- `Terms.wl` (M2): term layer — `var`/`bvar`/`const`/`comb`/`abs`, `mkVar`/`mkComb`/`mkAbs` (α-canonical), `typeOf`/`freesIn`/`vsubst`/`instType`/`aconv`/`stripOrigin`. No state.
- `Kernel.wl` (M3a+b): trust boundary — 10 primitive rules (`REFL` `TRANS` `MKCOMB` `ABS` `BETA` `ASSUME` `EQMP` `DEDUCTANTISYM` `INST` `INSTTYPE`), `mkType`/`mkConst`/`mkEq`, the 4 extension points + `lockAxioms`, accessors `destThm`/`hyp`/`concl`/`isThm`. `=` pre-registered as `α→α→bool`.
- `Bootstrap.wl` (M3c): logical constants `T ∀ ∧ ⇒ ∃ F ¬` (newDefinition), `@` (newConstant), `ONE_ONE`/`ONTO`; axioms `etaAx`/`selectAx`/`infinityAx`; then `lockAxioms[]`.
- `Equal.wl` (M4a): `SYM`, `APTERM`, `APTHM`, `BETACONV` (β-reduces any redex).
- `Bool.wl` (M4b): `TRUTH`, `EQTINTRO`/`EQTELIM`, `GEN`/`SPEC`/`ISPEC`, `CONJ`/`CONJUNCT1`/`CONJUNCT2`, `MP`/`DISCH`/`UNDISCH`, `NOTINTRO`/`NOTELIM`/`CONTR`, `EXISTS`/`CHOOSE`, `DISJ1`/`DISJ2`/`DISJCASES`, `EXCLUDEDMIDDLE`/`CCONTR`, `freshName`; `COND` (`condConst`/`condDefThm`/`condTThm`/`condFThm`).
- `Drule.wl` (M4c+d): conversion combinators (`ALLCONV`/`NOCONV`/`THENC`/`ORELSEC`/`TRYCONV`/`REPEATC`/`SUBCONV`/`DEPTHCONV`), Miller-pattern `REWRCONV`, rule lifters `CONVRULE`/`ONCEREWRITERULE`/`REWRITERULE`, `SUBS`.
- `Tactics.wl` (M5): `goal[asms,concl]`, `tacResult`; basic tactics (`allTac`/`conjTac`/`disj1Tac`/`disj2Tac`/`genTac`/`existsTac`/`dischTac`/`assumeTac`/`acceptTac`/`popAssum`/`rewriteTac`); `THEN`/`THENL`/`ORELSE`/`REPEAT`/`TRY`; `prove[tm,tac]`; `makeGoalstack[]`.
- `Printer.wl` (M6a): pretty printer + operator registry (package-private Assoc, not in kernel). `formatTerm`/`formatThm` in Unicode/ASCII.
- `Parser.wl` (M6c): string → term/type, `parseTerm`/`parseType`. Tokenizer + W-algorithm inference + unify. **No `ToExpression`** (trust boundary intact).
- `auto/PropTaut.wl`: `propTaut[t]` propositional decision procedure; `nnfThm`/`cnfThm`/`splitConjThm`/`clausifyPropThm`/`clausifyContrapositives` (thm-tracked clausifier for MESON).
- `auto/Meson.wl`: `MESON[thms]` tactic + `mesonProve` — `mLit`/`mClause` rep, NNF/Skolem/CNF preprocessing, Robinson MGU (bool vars rigid), iterative-deepening connection-tableaux search + proof-tree replay; equality lemmas `eqRefl/Sym/TransThm` user-supplied.
- `auto/Simp.wl`: `SIMP[thms]`/`asmSimp[thms]` tactics + `simpConv`/`simpProve`. Equation + conditional (`P⇒…⇒lhs=rhs`) rewrites, `basicSimpset[]` (19 propositional schemas), `⇒`/`∧`/`∨` congruences with context threading.
- `auto/Set.wl`: `setProve[goalTm]` + `SET[]` — set equality (α→bool with UNION/INTER/DIFF/EMPTY/UNIV) via funcExt → simpConv unfold → propTaut.
- `stdlib/Pair.wl`: `α×β`, constructor `,`, `FST`/`SND`, pair injectivity. (`mkPair` underlying.)
- `stdlib/Sum.wl`: `α+β`, `INL`/`INR`, injectivity + disjointness.
- `stdlib/Option.wl`: `α option`, `NONE`/`SOME`, injectivity + `noneNotEqSomeThm`; `isOptionPredicate` for case analysis.
- `stdlib/Set.wl`: sets as `α→bool` — `IN`/`SUBSET`/`UNION`/`INTER`/`DIFF`/`EMPTY`/`UNIV`/`INSERT`/`SING`/`DELETE`/`POW`/`IMAGE`/`PREIMAGE`/`BALL`/`BEX`/`COMPOSE`/`I`/`INJ`/`SURJ`/`BIJ` + membership/subset theorems. Parser supports `{x | P}` set-builder.
- `stdlib/Num.wl`: ℕ from `ind`+INFINITY_AX. `0`/`SUC`/Peano/`numInductionThm`; `ITER`/`numIterationThm`; `+`/`*`/`^` (comm/assoc/distrib/cancel); `≤`/`<` (refl/trans/antisym/total); `strongInductionThm`; `wellOrderingThm`; `divisionThm`/`DIV`/`MOD`; `divides` arithmetic; `gcd` (+ `gcdSpecThm` universal property); `prime`; `euclidLemmaThm`.
- `stdlib/List.wl`: `α list` = `num → α option` finite-support subtype (`isListP` carrier predicate). `NIL`/`CONS`, `repNil`/`repConsHead`/`repConsTail`, `consInjThm`, `nilNotEqConsThm`, `listInductionThm`; `LENGTH`/`HD`/`TL`; `LIST_ITER_GRAPH` + `listIterationThm`; `FOLDR`/`FOLDL`/`APPEND`/`MAP`/`FILTER`/`ALL`/`MEM` (all with NIL/CONS clauses, built via `listRecExists`); `foldrAppendThm` / `allAppendThm` distributions; helpers `optionCasesThm`, tail/shift toolkit, `funcExtThm`.
- `stdlib/Finite.wl`: inductive `FINITE` (`finiteConst`/`finiteDefThm`); `finiteEmptyThm`/`finiteInsertThm`/`finiteSingThm`; strong `finiteInductThm`; closure `finiteUnionThm`/`finiteSubsetThm`/`finiteDeleteThm`/`finiteImageThm`; FINREC/ITSET/FINITE_RECURSION + `CARD`/`NSUM`. Local helpers: `propSetEq` (propositional set-eq via simpConv+propTaut+funcExt), `setExtFromInEq`, `condDeleteEqLeft`/`Right`, `imageEmptyEq`/`imageInsertEq`, INST-based membership accessors `inInsertAt`/`inDeleteAt`/`inImageAt`.
- `stdlib/FTA.wl`: prime factorization — `primeFactorsExistsThm` + `primeFactorsUniqueThm` (modulo `PERM`); ℕ multiplicative helpers `multLeftCancelThm` (`¬(x=0) ⇒ x*a=x*b ⇒ a=b`). (`multEqZeroThm` moved to Num.wl.)
- `stdlib/Int.wl`: ℤ via canonical reps over `num × num` (carve `INT_REP = λp. FST p=0 ∨ SND p=0`; `ABS_int`/`REP_int`). Ordered integral domain: `&ℤ` embedding (`intOfNum…`); `intNeg`/`intSucc`/`intPred`; `intAdd` (comm/assoc/`intAddZeroThm`/`intAddNegThm`); `intMul` (comm/`intMulOneThm`/`intMulZeroThm`/distrib/assoc); no-zero-divisors `intMulEqZeroThm` + cancellation `intMulCancelThm`; order `intLe`/`intLt` (refl/antisym/trans/total + add/neg/mul-nonneg monotonicity); `intAbs`; bidirectional induction `intInductionThm`. Grothendieck-equivalence engine `canonEquivThm`/`canonInjThm`/`canonRespectsThm` + `repIntAddThm`/`repIntMulThm` underpin op well-definedness; ARITH (loaded just before) discharges the FST/SND-atom num glue.
- `stdlib/Rat.wl`: ℚ via canonical **reduced** fractions over `int × num` (carve `RAT_REP = λp. ¬(SND p=0) ∧ gcd (intNatAbs (FST p)) (SND p) = SUC 0`; `ABS_rat`/`REP_rat`; kernel `=` IS rational equality, **no setoid**). **DENSELY-ORDERED FIELD** (M7-6 complete, stages a–g): `&ℚ` embedding (`ratOfInt…`) — ring/order homomorphism `ratOfInt{Add,Mul,Le}Thm`; `ratAdd` (comm/assoc/`ratAddZeroThm`/`ratAddNegThm`) + `ratNeg` — additive abelian group; `ratMul` (comm/`ratMulOneThm`/`ratMulZeroThm`/distrib/assoc) + `ratInv`/`ratMulInvThm`; lowest-terms uniqueness `ratEqCrossThm`; order `ratLe`/`ratLt` (cross-mult to Int's `intLe`; linear-order `ratLe{Refl,Antisym,Trans,Total}Thm` + `ratLtNotLeThm` + compat `ratLeAddMonoThm`/`ratLeMulNonnegThm` + strict `ratLtAddMonoThm`/`ratLtMulPosCancelThm`/`ratAddSubCancelThm`; `intLeMulNonnegCancelThm`, `pairLeCong{Left,Right}Thm`); density `ratDenseThm` (`ratMulTwoThm` `x·2=x+x`). Machinery: `intNatAbs`/`exDiv` (Hilbert-ε exact quotient)/`intDivNat`/`ratCanon` (gcd-reduction, `ratCanonLands`/`ratCanonId`/`ratCanonSelf`/`ratCanonZeroNum`); the **ratCanon-respects + cong tower** (`ratCanonEquiv`/`Inj`/`CrossTrans`/`Respects`, `ratAddCongLeft/Right`, `ratMulCongLeft/Right`, `repAddEquivAt`/`repMulEquivAt`/`repInvEquivAt`) is the cross-multiplication analog of Int's Grothendieck layer, underpinning op well-definedness. Carries (pending migration to Num/Int) ℕ Bezout/Gauss (`bezoutNatThm`/`coprimeDividesProductThm`/`gcdRecThm`/`dividesAntisymThm`/`gcdComm`/`gcdSelf`/…) + int magnitude lemmas (`intSqNatAbsThm`/`intNatAbsMulOfNumThm`/`intMulDivNatCancelThm`/…). **M7-6 ℚ COMPLETE (stages a–g): densely-ordered field.** Housekeeping done (`bootstrap.mx` rebuilt with Rat; `dev_rat.wls` deleted; Rat dev loop = `run_fast.wls rat_tests`). Pending: migrate carried ℕ/int lemmas to Num/Int.wl. Next number-tower step = ℝ (`stdlib/Real.wl`).
