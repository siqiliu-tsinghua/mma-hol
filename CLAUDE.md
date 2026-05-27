# mma-hol — operational notes

Kernel-minimal higher-order logic theorem prover in Wolfram Language, LCF-style, modeled on HOL Light. Long-term target: mechanize undergraduate analysis through general Stokes and Fourier analysis, all within the Riemann-integral + Lebesgue-null-set framework (no full Lebesgue measure).

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

- **File extensions**: libraries `.wl` (`BeginPackage`/`EndPackage`); entry points/tests/demos `.wls`; notebooks `.nb` optional.
- **Contexts**: `HOL`Kernel``, `HOL`Bool``, … Private helpers in `` `Private` `` subcontext. **Private symbols don't cross files** — a helper/value defined in one file's `` `Private` `` (e.g. `numInductBy`, `numTy`, `plusTm` in Num.wl) is unreachable by bare name elsewhere; reference the full `HOL`Pkg`Private`name` path or redefine locally, else it silently stays unevaluated and trips a "not a theorem" / "mkComb type mismatch" far downstream.
- **Errors**: kernel throws `Throw[Failure["HOLError", <|"tag"->…, "msg"->…|>], holErrorTag]`; top-level `Catch` in `.wls` entries. Tests assert on tag. **Never `Message` + `$Failed`.** Read payload via `f[[2, "tag"]]` (not `f[[1, …]]`).
- **Tests**: `tests/harness.wl` gives `assertEq`/`assertTrue`/`assertThrows`/`runTests`/`testExit`. Runners: `tests/run_all.wls` (cold-boot Strict, CI, ~6 min); `tests/run_all_stable.wls` (cold-boot Stable, CI sanity); `tests/run_fast.wls [pattern…]` (restore `bootstrap.mx` snapshot, run matching files, ~3 s). Rebuild snapshot via `tests/build_snapshot.wls` after any library/`Kernel.wl` change (runner checks mtimes). `kernel_tests.wl` is skipped from the fast runner.
- **Adding a module**: add it to the load lists in both `tests/run_all.wls` and `tests/build_snapshot.wls` (dependency order). Test files use `Needs["HOL`…`"]` which is a no-op once loaded but can't locate flat-layout files on its own.
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
analysis1/   — M8: one-variable analysis → Lebesgue integrability criterion
analysis2/   — M9: multivariable, Jordan, forms, general Stokes
analysis3/   — M10: function series, parametric integrals, Fourier
tests/  demos/
```

## Milestones (PLAN §7 has the detail)

M1 Types · M2 Terms · M3 Kernel (10 rules + bootstrap) · M4 Derived rules · M5 Tactics · M6 Parser/Printer · M7 stdlib + 5 automation tactics (`MESON`/`SIMP`/`SET`/`ARITH`/`REAL_ARITH`) · M8 one-var analysis · M9 multivariable → Stokes · M10 function series + parametric integrals → Fourier.

Capstones: M3 `⊢ T`; M8 Lebesgue criterion for Riemann integrability; M9 general Stokes; M10 Poisson summation + Radon transform.

## Git

- Branch `main`. Local config: `Si-Qi Liu <liusq@tsinghua.edu.cn>`.
- Commit only when asked. Prefer new commits over `--amend`. Don't touch global git config.

## Current state

M1–M6 done (kernel, derived rules, tactics, parser+printer; M6b notebook MakeBoxes deferrable).

**M7 automation** — `MESON` (auto/Meson.wl) and `SIMP`/`asmSimp` (auto/Simp.wl) substantially complete; `SET` (auto/Set.wl) done. Pending: MESON α-5-c Brand modulation + NOT_FORALL/NOT_EXISTS NNF schemas (deferred till a goal forces them); `ARITH`/`REAL_ARITH` not started.

**M7 stdlib** — Pair, Sum, Option, Set done. **Num done through M7-3** (Peano via `ind`+INFINITY_AX; iteration theorem; `+ × ^`; `≤ <`; strong induction; well-ordering; division `m = n*q+r`; `DIV`/`MOD`; `divides`; `gcd` + universal property; `prime`; Euclid's lemma — all no integer Bezout). **FTA complete** in `stdlib/FTA.wl`: existence (`primeFactorsExistsThm`) + uniqueness modulo permutation (`primeFactorsUniqueThm`). **List done through M7-4-d.5** (α list as `num → α option` finite-support subtype: NIL/CONS, injectivity, NIL≠CONS disjointness, list induction; `LENGTH`/`HD`/`TL`; list iteration theorem; `FOLDR`/`FOLDL`/`APPEND`/`MAP`/`FILTER`/`ALL`/`MEM` + NIL/CONS clauses; `foldrAppendThm`/`allAppendThm` distributions). **`COND` + COND_CLAUSES** added to Bool.wl (needed by FILTER).

**Finite.wl done through closure lemmas (M7-4-e)** — `INSERT`/`SING`/`DELETE` added to Set.wl; **inductive `FINITE`** (smallest predicate with ∅ + INSERT-closure) with `finiteEmptyThm`/`finiteInsertThm`/`finiteSingThm`, strong `finiteInductThm` (FINITE s in the step), and all four closure lemmas `finiteUnionThm`/`finiteSubsetThm`/`finiteDeleteThm`/`finiteImageThm`. `finiteSubset`/`finiteImage` do `x∈t` case-split / ∃-distribution with membership Leibniz via kernel `SUBS` (no MESON — its equality has no congruence). Membership eqs built by INST-ing Set.wl theorems (not simpConv, whose basicSimpset absorbs `a∨(b∧¬a)`). β-instances of EMPTY/INSERT/FINITE built directly/INSTTYPE'd. Pending: `CARD`/`∑`.

**M7-4 done (Finite.wl complete through CARD/∑)** — FINREC machinery (f.1–f.4.a) + ITSET + FINITE_RECURSION (f.4.b) + **CARD** (`= λs. ITSET (λx n. SUC n) s 0`) and **NSUM** (`= λg s. ITSET (λx a. g x + a) s 0`). CARD/NSUM clauses derived by INSTTYPE [β→num] + INST itsetEmpty/itsetInsert at the step + SUBS-rewrite back to CARD/NSUM + CONVRULE beta. CARD step's comm is trivial (REFL after beta); NSUM step's comm uses addAssoc + addComm chain.

**M7-3 FTA stage 1 done (stdlib/FTA.wl)** — `dividesPosThm`/`dividesTransThm`/`notOneNorZeroLtThm` helpers + `primeOrCompositeThm` (n>1 ⇒ prime or has a proper divisor) + **`primeDivExistsThm`** (every n>1 has a prime divisor). Strong induction + EM.

**M7-3 FTA stage 2 done (stdlib/FTA.wl)** — `posAddLtThm` (¬(d=0) ⇒ c < c+d via numCases + leqDef unfold) + `ltMultIfOneLtThm` (1<p ⇒ ¬(c=0) ⇒ c < p*c, via SUC(SUC k) decomposition) + **`primeFactorsExistsThm`** (⊢ ∀n. ¬(n=0) ⇒ ∃l. ALL prime l ∧ FOLDR * (SUC 0) l = n). Strong induction on n with leqCaseEqLt split on SUC 0 vs n. NIL works for n=1; for n>1, primeDivExistsThm + ltMultIfOneLtThm push to the cofactor c<n and prepend p to the IH list.

**M7-3 FTA stage 3.a done (stdlib/FTA.wl)** — `notLeqSucSelfThm` (¬(SUC n ≤ n), via leqSuc + leqAntisym + sucNotEqSelf) + `primeNotDivOneThm` (prime p ⇒ ¬ p|1, via primeDef + dividesLeqThm + notLeqSucSelf) + **`primeDivFoldrTimesThm`** (⊢ ∀p. prime p ⇒ ∀l. p | FOLDR * 1 l ⇒ ∃y. MEM y l ∧ p | y) — Euclid's lemma on lists by list induction on l, NIL case rejected via primeNotDivOne, CONS case splits the product via euclidLemmaThm with the head (memCons-DISJ1) and tail (IH + memCons-DISJ2) branches.

**M7-3 FTA stage 3.b done (stdlib/FTA.wl)** — PERM relation as `λl1 l2. ∀R. closedRel R ⇒ R l1 l2` (smallest binary relation closed under: NIL-NIL base, CONS-congruence, adjacent CONS-swap, transitivity). Four intro rules `permNilThm`/`permConsThm`/`permSwapThm`/`permTransThm` derived from the universal property (same skeleton as Finite.wl's FINITE intros). Then `permInductThm` (the principle restated) → `permReflThm` (list induction) → `permSymThm` (PERM induction with Q l1 l2 = PERM l2 l1) → `permFoldrTimesThm` (PERM preserves `FOLDR * 1`; swap-clause uses timesAssoc + timesComm + timesAssoc) → `permAllThm` (PERM preserves `ALL p`; swap-clause via local `andSwapMidThm: a∧(b∧c) = b∧(a∧c)` from DEDUCTANTISYM).

**M7-3 FTA stage 3.c done (stdlib/FTA.wl)** — `memSplitThm` (⊢ ∀x l. MEM x l ⇒ ∃l1 l2. l = APPEND l1 (CONS x l2); list induction on l, NIL via memNil→F→CONTR, CONS branches on memCons disjunction with head case using `APTHM[APTERM[CONS, x=y], l]` and tail case using IH+nested CHOOSE) + `permAppendConsThm` (⊢ ∀x l1 l2. PERM (APPEND l1 (CONS x l2)) (CONS x (APPEND l1 l2)); list induction on l1, NIL via reduction to refl via APTERM(PERM A) — note that SUBS would conflict here because both sides reduce to `CONS x l2`, so use APTERM-on-relation instead; CONS step via IH+permCons+permSwap+permTrans then SUBS-rewriting `CONS y (APPEND ...)` → `APPEND (CONS y ...) ...` on both PERM args).

**M7-3 FTA stage 3.d done — FTA complete (stdlib/FTA.wl)** — Six helpers + capstone: `multEqZeroThm` (no zero divisors in ℕ; numCases + timesLeftSuc + addEqZeroLeft), `multLeftCancelThm` (¬(x=0) ⇒ x*a = x*b ⇒ a=b; num induction on a with numCases on b in the step, the b=0 sub-branch contradicts x≠0), `primeNotZeroThm` (prime p ⇒ ¬(p=0); via 0<p contradiction with `¬(n<0)`), `primesEqIfDividesThm` (prime p ⇒ prime q ⇒ p|q ⇒ p=q; primeDef of q applied at d=p, ¬(p=SUC 0) from p>1 via ltImpliesNotEq), `allMemImpThm` (ALL P l ⇒ ∀x. MEM x l ⇒ P x; list induction, head case via APTERM(P) of x=y, tail case via IH), `foldrEqOneNilThm` (ALL prime l ⇒ FOLDR * 1 l = 1 ⇒ l = NIL; CONS case derives p|1 via ∃c witness, contradicting primeNotDivOne). Capstone **`primeFactorsUniqueThm`** ⊢ ∀l1 l2. ALL prime l1 ⇒ ALL prime l2 ⇒ FOLDR * (SUC 0) l1 = FOLDR * (SUC 0) l2 ⇒ PERM l1 l2 by list induction on l1: NIL case uses foldrEqOneNil to force l2=NIL; CONS x l1' case extracts prime x, gets x|FOLDR l2, primeDivFoldrTimes finds MEM y l2 ∧ x|y, allMemImp gives prime y, primesEqIfDivides gives x=y so MEM x l2, memSplit yields l2 = APPEND l2a (CONS x l2b), permAppendCons + permFoldrTimes transport FOLDR through, multLeftCancel cancels x, allAppend+allCons reassemble ALL prime (APPEND l2a l2b), IH gives PERM l1' (APPEND l2a l2b), permCons + permSym + permTrans complete the chain. Polymorphic theorems (permNil/Cons/Sym/Trans/AppendCons, memSplit, allMemImp, foldr/allCons/allAppend) all INSTTYPE'd at numTy via local helpers (`permNilNum`, `permConsNum`, …) and num-specialized term builders `memNumTm`/`appendNumTm`/`permNumTm`. **FTA complete: ⊢ existence + uniqueness modulo permutation.**

**M7-δ session 1 done (auto/Arith.wl)** — linTerm AST (`linTerm[const, <|name→coef|>]` with smart constructors `linZero`/`linConst`/`linVar`/`linAdd`/`linScale`/`linNeg`/`linSub`), HOL ↔ linTerm conversion (`parseLin` recursive descent over 0/SUC/+/`*-by-literal`; `buildLin` emits the canonical right-assoc `c_0 + c_1*x_1 + … + c_k*x_k`).

**M7-δ session 2 done (auto/Arith.wl)** — Atom + Formula AST + NNF (algorithm only, no HOL theorem yet). Atoms `aAtomEq` / `aAtomLeq` / `aAtomLt` / `aAtomDivides[c, lt]`. Formulas `aFormTrue` / `aFormFalse` / `aFormAtom` / `aFormNot` / `aFormAnd` / `aFormOr` / `aFormImp` / `aFormIff` / `aFormForall[name, body]` / `aFormExists`. `parseAtom` + `parseForm` (binder peel via `openBvarAt` walking depth-aware over de-Bruijn-level bvars, with a local `freshArithName` to avoid name collisions on nested same-name binders — note `HOL`Bool`freshName` is Bool's private helper and not accessible across files, hence the inline copy). `buildAtom` + `buildForm` emit HOL terms aconv to the original. `nnfForm` pushes ¬ inwards to the atom layer, expands `⇒`/`⇔`, and is idempotent on NNF input. `nnfFormQ` predicate certifies the output shape.

**M7-δ session 3 done (auto/Arith.wl)** — Propositional NNF certificate `nnfConv[holForm]` returning `⊢ holForm = NNF(holForm)`. The 7 schemata (¬¬, ¬∧, ¬∨, ⇒-elim, ¬⇒, ⇔-DNF, ¬⇔-DNF) are built lazily via `propTaut` from `auto/PropTaut.wl` and stored in `$arithNnfSchemata`. The conversion uses `REWRCONV` of each schema combined via `ORELSEC`, lifted to bottom-up via `DEPTHCONV`, and iterated to fixpoint via a local `fixpointConvLocal` (analogous to Drule's private `fixpointConvRule` but operating on conversions rather than theorems). Quantifier bodies pass through structurally (DEPTHCONV descends under abs). **Quirk recorded**: because DEPTHCONV is bottom-up, the inner `p = q` (iff) gets rewritten to its DNF form before the outer `¬(…)` sees it. So `¬(p ⇔ q)` ends up as `(¬p ∨ ¬q) ∧ (p ∨ q)` rather than the AST-level nnfForm's `(p ∧ ¬q) ∨ (¬p ∧ q)`. Both are NNF — only the syntactic shape differs. Renamed from `nnfThm` to `nnfConv` to avoid shadow warning against `HOL`Auto`PropTaut`nnfThm`.

**M7-δ session 4 done (auto/Arith.wl)** — Quantifier deMorgan at numTy. **`notExistsNumThm`** ⊢ ∀P. ¬(∃x:num. P x) = (∀x:num. ¬P x) by constructive proof: forward via EXISTS+MP+NOTINTRO+GEN, backward via CHOOSE+SPEC. **`notForallNumThm`** ⊢ ∀P. ¬(∀x:num. P x) = (∃x:num. ¬P x) by classical proof: forward uses CCONTR twice (inner: ¬∃¬ ⇒ ∀ by per-element CCONTR; outer: ¬∀ contradicts derived ∀), backward via CHOOSE+SPEC+NOTINTRO. Both SPEC'd at a free P and added to `$arithNnfSchemata` (now 9 entries). REWRCONV uses Miller HO pattern matching to bind `P ↦ λx. body` when rewriting under ∀/∃. `nnfConv` now complete on full Presburger ℕ.

**M7-δ session 5 done (auto/Arith.wl)** — Cooper QE AST scaffolding. `normalizeAtom`/`normalizeAtomsForm` rewrite `lt op 0` form via linSub. `linCoefOf`, `atomCoefOnX`, `formAtomsInvolvingX`, `deltaOnX` (LCM of divisibility moduli, default 1), `phiMinusInfOnX` (per-atom -∞ limits: eq→F, leq/lt coef>0→T, coef<0→F, ¬ flips, divisibility kept).

**M7-δ session 6 done (auto/Arith.wl)** — Substitution + B-set + ∃-elimination assembly. `substVarInLin[lt, x, rep]` replaces x by another linTerm. `substVarInAtom`/`substVarInForm` walk through (respect ∀/∃ binder shadowing). `bWitnessOfAtom[negated, atom, x]` extracts left-bound witnesses (only |coef-x| = 1 supported; ¬Eq skipped). `bSetOnX` collects across the form. **`cooperExistsStep[xName, body]`** assembles the final AST `(⋁_{j=1..δ} φ_{-∞}[x↦j]) ∨ (⋁_{j=1..δ} ⋁_{b∈B} body[x↦b+j])`.

**M7-δ session 7 done (auto/Arith.wl)** — AST-level propositional simplification. **`simpForm[aForm]`** evaluates ground atoms (Eq/Leq/Lt over linConst, Divides via Mod), folds T/F through ∧/∨/¬/⇒/⇔ (`simpAnd`/`simpOr`/`simpNeg`/`simpImp`/`simpIff`, with ¬¬-collapse). Composed with `cooperExistsStep`, gives an algorithm-level decision procedure: `∃x. x = 5` → T, `∃x. 10 ≤ x ∧ x ≤ 3` → F, etc.

**M7-δ session 8 done (auto/Arith.wl)** — Ground arithmetic provers. `proveGroundAddEq[m, n]` / `proveGroundMultEq[m, n]` via SUC recursion + `addLeftZeroThm`/`addLeftSucThm` / `timesZeroEqThm`/`timesSucEqThm`. `proveGroundLeq` / `proveGroundLt` / `proveGroundDivides` via EXISTS over `unfoldLeq`/`unfoldLt`/`unfoldDivides`. Pattern-guard-with-Mod failed to register DownValue; moved check inside body.

**M7-δ session 9 done (auto/Arith.wl)** — ∃-SAT → HOL theorem. `findSatWitness` searches B+δ candidates. `proveGroundAtomTm` / `proveGroundFormulaTm` / `arithProveExists` orchestrate the parse → witness → BETACONV substitute → ground prove → EXISTS pipeline. End-to-end on simple-atom ∃-SAT goals.

**M7-δ session 10 done (auto/Arith.wl)** — Compound arithmetic atoms in arithProveExists. **`proveGroundReduceTm[t]`** reduces a closed ℕ arithmetic term (built from 0, SUC, +, *) to its literal form via structural recursion: REFL on literal leaves; APTERM[SUC] for SUC; MKCOMB+APTERM congruence on +/* then chain through `proveGroundAddEq`/`proveGroundMultEq` to fold the literal result. **`proveGroundAtomTm`** now first reduces both sides of the atom via `reduceAtomSides`, then proves the literal-only reduced atom, then lifts via **`liftReducedAtomProof[reducedThm, opConst, aRed, bRed]`** which builds `⊢ opConst aLit bLit = opConst a b` via APTERM+MKCOMB on the symmetric side-equations and EQMP. **Note recorded**: initial implementation used SUBS for the lift, which over-rewrote — SUBS replaces every syntactic occurrence of aLit, including aLit-as-sub-pattern inside bLit (e.g. literal `3` inside `SUC SUC SUC SUC SUC 0 = 5`). The MKCOMB approach is position-precise. End-to-end verified on `∃x. x + 3 ≤ 5`, `∃x. (x + 1) = 4`, `∃x. x + 2 ≤ x + 5`. arithProveExists still restricted to |coef-x| = 1 atoms (multiply-through normalization for higher coefs deferred).

**Next**: M7-δ session 11+ — (i) ∀-goals via `¬∃¬` reduction (using session-4 notForallNumThm + arithProveExists on the negated existential, UNSAT means original True; needs Cooper main theorem for the UNSAT direction), (ii) nested quantifiers via iterated cooperExistsStep, (iii) higher-coef normalization (multiply atoms by δ/coef to get coef-±1), (iv) the top-level `arithProve` / `ARITH` wiring. Capstone target like `∀m n. m ≤ m + n` requires (i)+(ii). Alternative: M7-5 `stdlib/Int.wl`. **Audit issues parked in `TODO.md`.**

Detailed proof history: `git log` + code comments. Design rationale: `PLAN.md`.

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
- `stdlib/Finite.wl`: inductive `FINITE` (`finiteConst`/`finiteDefThm`); `finiteEmptyThm`/`finiteInsertThm`/`finiteSingThm`; strong `finiteInductThm`; closure `finiteUnionThm`/`finiteSubsetThm`/`finiteDeleteThm`/`finiteImageThm`. (CARD/∑ pending.) Local helpers: `propSetEq` (propositional set-eq via simpConv+propTaut+funcExt), `setExtFromInEq`, `condDeleteEqLeft`/`Right`, `imageEmptyEq`/`imageInsertEq`, INST-based membership accessors `inInsertAt`/`inDeleteAt`/`inImageAt`.
