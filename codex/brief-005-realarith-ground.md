# Brief 005 — auto/RealArith.wl Stage 1: ground ℝ-literal arithmetic + ordered-field combination toolkit

## Goal

First stage of M7-ε REAL_ARITH (linear real arithmetic decision procedure,
oracle + kernel verifier, mirroring `auto/Arith.wl`'s architecture for ℕ).
When you are done there is a NEW frontier file `auto/RealArith.wl` providing
(A) a ground rational-literal layer — term builders for ℕ-embedded real
literals `&ℝ (&ℚ (&ℤ n))` plus memoized provers for ground add / mul / ≤ /
< / ¬≤ / positivity facts — and (B) the ordered-field combination lemmas the
future Farkas verifier will consume (two-sided add-monotonicity, mul
cancellation iffs, irreflexivity, eq-as-two-≤). Plus a new test file
`tests/real_arith_tests.wl`. No existing file changes.

## Context pointers

- Read `CLAUDE.md` (especially **Conventions** and the variable-capture
  hygiene rules) before writing any code.
- `auto/Arith.wl` — the ℕ analog. Read its private `groundAdd` (around line
  1200) and the Farkas section header (around line 1908) to see the shape of
  what Stage 2/3 will consume. This stage is the ℝ analog of its ground layer.
- `stdlib/Real/{Cut,Field,Mul,Inv,Complete,Abs,MinMax}.wl` — the ℝ ordered
  field. **These files share ONE package context `HOL`Stdlib`Real`** (folder
  layout, PLAN §8.1); their `` `Private` `` helpers (`realTy`, `realAddTm`,
  `rZ`, `zeroRealTm`, …) are shared *within the folder only* and are NOT
  reachable from `HOL`Auto`RealArith`. Public `*Const[]` builders ARE
  exported — use them (list below).
- `stdlib/{Num,Int,Rat}.wl` — the embedding homomorphism chain.
- `tests/real_abs_tests.wl` — copy its structure for the new test file
  (harness import, test list, runTests/testExit idiom).
- This is an LCF-style HOL prover in Wolfram Language. You cannot create a
  false theorem from outside the kernel — but you can fail to prove a true
  one. Acceptance is mechanical: the reviewer's test run decides.

### Verified lemma / builder inventory (exact; re-grep the ::usage string before use if in any doubt)

Public term builders (call as functions, e.g. `realAddConst[]`):
- `HOL`Stdlib`Real``: `realOfRatConst[]` (const name `"&ℝ"`, rat→real),
  `realAddConst[]`, `realMulConst[]`, `realNegConst[]`, `realInvConst[]`,
  `realLeConst[]`, `realLtConst[]`.
- `HOL`Stdlib`Rat``: `ratOfIntConst[]` (const name `"&ℚ"`, int→rat).
- `HOL`Stdlib`Int``: `intOfNumConst[]` (const name `"&ℤ"`, num→int).
- `HOL`Stdlib`Num``: `zeroConst[]`, `sucConst[]`, `plusConst[]`,
  `timesConst[]`, `leqConst[]`, `ltConst[]`.
- Types: build with kernel `mkType`: `mkType["real", {}]`,
  `mkType["rat", {}]`, `mkType["int", {}]`, `mkType["num", {}]`,
  `mkType["bool", {}]`.

ℕ ground equations (Num.wl):
- `plusZeroEqThm` ⊢ ∀m. m + 0 = m; `plusSucEqThm` ⊢ ∀m n. m + SUC n = SUC (m + n).
- `timesZeroEqThm` ⊢ ∀m. m * 0 = 0; `timesSucEqThm` ⊢ ∀m n. m * SUC n = m * n + m.
- Order: `leqConst` usage says LEQ m n ⇔ ∃k. m + k = n — find the equation
  theorem (`leqDefThm`) and `ltDefThm` (m < n ⇔ SUC m ≤ n) and VERIFY their
  exact statements from their ::usage strings. Also available:
  `leqZeroThm`, `leqReflThm`, `leqSucThm`, `ltSucThm`, etc.

Embedding homomorphisms (all already proven, iff-form order embeddings):
- Int.wl: `intOfNumAddThm` ⊢ ∀m n. &ℤ (m+n) = intAdd (&ℤ m) (&ℤ n);
  `intOfNumMulThm` (same shape for *); `intOfNumLeThm` ⊢ ∀m n. intLe (&ℤ m) (&ℤ n) = (m ≤ n).
- Cut.wl: `intOfNumLtThm` ⊢ ∀m n. intLt (&ℤ m) (&ℤ n) = (m < n);
  `ratOfIntLtThm` ⊢ ∀a b. ratLt (&ℚ a) (&ℚ b) = intLt a b.
- Rat.wl: `ratOfIntAddThm`, `ratOfIntMulThm` (hom equations, same orientation
  as intOfNum versions — VERIFY orientation from usage), `ratOfIntLeThm`.
- Field.wl: `realOfRatAddThm` ⊢ ∀a b. &ℝ (ratAdd a b) = realAdd (&ℝ a) (&ℝ b);
  `realOfRatLeThm` ⊢ ∀a b. realLe (&ℝ a) (&ℝ b) = ratLe a b;
  `realAddCommThm`/`realAddAssocThm`/`realAddZeroThm` (verify exact names by grep).
- Mul.wl: `realOfRatMulThm` ⊢ ∀a b. &ℝ (ratMul a b) = realMul (&ℝ a) (&ℝ b).
- Complete.wl: `realOfRatLtThm` ⊢ ∀a b. realLt (&ℝ a) (&ℝ b) = ratLt a b.

ℝ order surface:
- Cut.wl: `realLeReflThm`, `realLeTransThm`, `realLeAntisymThm`,
  `realLeTotalThm`, `realLtNotLeThm` ⊢ ∀x y. realLt x y = ¬(realLe y x).
- Complete.wl: `realLtImpLeThm`, `realLtLeTransThm`, `realLeLtTransThm`,
  `realLtTransThm`.
- Mul.wl: `realLeAddMonoThm` ⊢ ∀a b c. realLe a b ⇒ realLe (a+c) (b+c);
  `realLtAddMonoThm` (same, strict);
  `realLeMulMonoThm` ⊢ ∀a b c. realLe 0 c ⇒ realLe a b ⇒ realLe (c·a) (c·b);
  `realLtMulMonoThm` ⊢ ∀a b c. realLt 0 c ⇒ realLt a b ⇒ realLt (c·a) (c·b);
  `realLeMulNonnegThm`, `realLtMulPosThm`;
  `realMulCommThm`/`realMulAssocThm`/`realMulOneThm`/`realMulZeroThm`/`realMulDistribThm`.
- **The literal `0` in every Mul.wl order theorem is exactly
  `&ℝ (&ℚ (&ℤ 0))`** (their private `zeroRealTm[]`) — identical to your
  `rnumTm[0]`, so SPEC/MP will aconv-match with no bridging.

Kernel/Bool/Equal rules available: `REFL TRANS MKCOMB EQMP DEDUCTANTISYM
INST ASSUME` (kernel), `SYM APTERM APTHM BETACONV` (Equal), `GEN SPEC ISPEC
CONJ CONJUNCT1 CONJUNCT2 MP DISCH UNDISCH NOTINTRO NOTELIM CONTR CCONTR
EXCLUDEDMIDDLE DISJCASES EQTINTRO EQTELIM` (Bool). `HOL`Auto`PropTaut`propTaut`
is public and fine for ≤3-variable propositional glue (e.g. double negation),
but its private helpers (e.g. `eqfIntro`) are NOT — calling one cross-file
returns unevaluated and explodes later (known gotcha).

## Scope

- Files you may CREATE: `auto/RealArith.wl`, `tests/real_arith_tests.wl`.
- Files you may MODIFY: none. In particular do NOT touch the three runner
  load lists (`tests/run_all.wls`, `tests/run_all_stable.wls`,
  `tests/build_snapshot.wls`) — this is a FRONTIER file; the reviewer
  verifies with `tests/dev.wls auto/RealArith.wl real_arith` and wires the
  runners at graduation.
- Files you MUST NOT touch: `Kernel.wl`, `Types.wl`, `Terms.wl`,
  `Bootstrap.wl` (trust boundary — NEVER, even for comments), `bootstrap.mx`,
  `CLAUDE.md`, `PLAN.md`, `PROGRESS.md`, anything under `codex/` except
  appending to your own report.
- Do NOT add new axioms or call `newAxiom` under any circumstances.

## Deliverable

`auto/RealArith.wl`: `BeginPackage["HOL`Auto`RealArith`", {…}]` importing
`HOL`Error``, `HOL`Types``, `HOL`Terms``, `HOL`Kernel``, `HOL`Bootstrap``,
`HOL`Equal``, `HOL`Bool``, `HOL`Drule``, `HOL`Auto`PropTaut``,
`HOL`Stdlib`Num``, `HOL`Stdlib`Int``, `HOL`Stdlib`Rat``, `HOL`Stdlib`Real``.
Public symbols get ::usage before `Begin["`Private`"]`; all helpers private.

### Part A — ground literal layer

Private builders:
- `natTm[n_Integer]` — SUC-stack numeral (`SUC (SUC … 0)`), n ≥ 0.
- `rnumTm[n_Integer]` — `&ℝ (&ℚ (&ℤ (natTm[n])))`, via the three embedding
  Consts. This is THE canonical nonneg real literal for all of REAL_ARITH.
- Local appliers `rAdd[a,b]`, `rMul[a,b]`, `rLe[a,b]`, `rLt[a,b]`, `rNeg[a]`
  (mkComb over the public Consts).
- Local ℕ ground recursions mirroring Arith.wl's private `groundAdd`:
  `groundNatAdd[m,n]` ⊢ m̂ + n̂ = (m+n)^ (recurse on n via
  plusZeroEqThm/plusSucEqThm + APTERM on SUC);
  `groundNatMul[m,n]` ⊢ m̂ * n̂ = (m·n)^ (recurse via timesZero/timesSucEq,
  chaining groundNatAdd);
  `groundNatLe[m,n]` (m ≤ n) ⊢ m̂ ≤ n̂ (leqDefThm + EXISTS with witness
  (n−m)^ + groundNatAdd, or any simpler Num route you verify);
  `groundNatLt[m,n]` (m < n) ⊢ m̂ < n̂ (ltDefThm reduces to SUC m̂ ≤ n̂).

Public memoized ground provers (memoize with `f[m_, n_] := f[m, n] = …`);
arguments are machine Integers ≥ 0; out-of-domain calls (e.g. `rnumLe[3,1]`)
throw `HOL`Error`holError["realarith-ground", …]`:
- `rnumAdd[m, n]` — ⊢ realAdd (rnumTm m) (rnumTm n) = rnumTm (m+n).
  Route: groundNatAdd lifted through SYM`intOfNumAddThm`, SYM`ratOfIntAddThm`,
  SYM`realOfRatAddThm` (APTERM the embeddings onto the ℕ equation, then chain
  the hom equations with TRANS — check each hom's orientation and SYM as needed).
- `rnumMul[m, n]` — ⊢ realMul (rnumTm m) (rnumTm n) = rnumTm (m·n). Same
  shape via the Mul homs.
- `rnumLe[m, n]` (m ≤ n) — ⊢ realLe (rnumTm m) (rnumTm n). Route: groundNatLe,
  then EQMP backwards through the iff chain intOfNumLeThm → ratOfIntLeThm →
  realOfRatLeThm (each is `embedded-order = base-order`; SPEC then EQMP with
  SYM as appropriate).
- `rnumLt[m, n]` (m < n) — ⊢ realLt (rnumTm m) (rnumTm n). Same via the Lt iffs.
- `rnumNotLe[m, n]` (n < m) — ⊢ ¬(realLe (rnumTm m) (rnumTm n)). Route:
  rnumLt[n, m] + realLtNotLeThm (SPEC x := rnumTm n, y := rnumTm m gives
  realLt n̂ m̂ = ¬(realLe m̂ n̂); EQMP). This is the Farkas contradiction endpoint.
- `rnumPos[n]` (n ≥ 1) — ⊢ realLt (rnumTm 0) (rnumTm n) (= rnumLt[0, n]).
- `rnumNonneg[n]` (n ≥ 0) — ⊢ realLe (rnumTm 0) (rnumTm n) (= rnumLe[0, n]).

### Part B — ordered-field combination lemmas (fixed public theorems)

Statements (0 means rnumTm[0]; `+`/`·` mean realAdd/realMul; binders are
final-statement canonical so plain names are fine, but every INTERNAL witness
or scaffolding binder gets a distinctive name per the hygiene rules):

1. `realLeAddMonoRThm` ⊢ ∀a c d. realLe c d ⇒ realLe (a+c) (a+d).
   From realLeAddMonoThm (c≤d ⇒ c+a≤d+a) + realAddCommThm rewrites on both
   sides (use APTHM/MKCOMB or SUBS with the comm instances + EQMP).
2. `realLeAddMono2Thm` ⊢ ∀a b c d. realLe a b ⇒ realLe c d ⇒ realLe (a+c) (b+d).
   realLeAddMonoThm gives a+c ≤ b+c; realLeAddMonoRThm gives b+c ≤ b+d;
   realLeTransThm.
3. `realLtAddMonoRThm` ⊢ ∀a c d. realLt c d ⇒ realLt (a+c) (a+d). (comm
   conjugate of realLtAddMonoThm, same as 1.)
4. `realLtLeAddMonoThm` ⊢ ∀a b c d. realLt a b ⇒ realLe c d ⇒ realLt (a+c) (b+d).
   realLtAddMonoThm + realLeAddMonoRThm + realLtLeTransThm.
5. `realLeLtAddMonoThm` ⊢ ∀a b c d. realLe a b ⇒ realLt c d ⇒ realLt (a+c) (b+d).
   realLeAddMonoThm + realLtAddMonoRThm + realLeLtTransThm.
6. `realLtAddMono2Thm` ⊢ ∀a b c d. realLt a b ⇒ realLt c d ⇒ realLt (a+c) (b+d).
   realLtImpLeThm on the first + (5), or strict+strict directly via (4).
7. `realLtIrreflThm` ⊢ ∀x. ¬(realLt x x).
   SPEC x x into realLtNotLeThm: realLt x x = ¬(realLe x x). NOTINTRO on
   DISCH of: ASSUME (realLt x x), EQMP to ¬(realLe x x), NOTELIM, MP with
   realLeReflThm ⟹ F.
8. `realNotLeLtThm` ⊢ ∀x y. ¬(realLe x y) = realLt y x.
   SYM of realLtNotLeThm SPEC'd at [y, x]; GEN back.
9. `realLeMulCancelThm` ⊢ ∀c a b. realLt 0 c ⇒ (realLe (c·a) (c·b) = realLe a b).
   Backward: realLeMulMonoThm with realLtImpLeThm (0≤c). Forward by
   CONTRAPOSITIVE — do NOT touch realInv: under ASSUME (c·a ≤ c·b) and the
   CCONTR assumption ¬(a≤b), realNotLeLtThm gives b < a, realLtMulMonoThm
   gives c·b < c·a, realLtNotLeThm/realNotLeLtThm turns that into
   ¬(c·a ≤ c·b), NOTELIM + MP ⟹ F, CCONTR closes a ≤ b. Build the iff with
   DEDUCTANTISYM on the two ASSUME-discharged directions, then DISCH the
   0<c hypothesis and GEN.
10. `realLtMulCancelThm` ⊢ ∀c a b. realLt 0 c ⇒ (realLt (c·a) (c·b) = realLt a b).
    Backward: realLtMulMonoThm. Forward contrapositive: ¬(a<b) ⟹ b ≤ a (via
    realLtNotLeThm at [a,b]: a<b = ¬(b≤a); so ¬(a<b) = ¬¬(b≤a); double
    negation via propTaut or CCONTR) ⟹ c·b ≤ c·a (realLeMulMonoThm, 0≤c)
    ⟹ ¬(c·a < c·b) (realLtNotLeThm) ⟹ contradiction; CCONTR. DEDUCTANTISYM
    as in (9).
11. `realEqIffLeLeThm` ⊢ ∀a b. (a = b) = (realLe a b ∧ realLe b a).
    Direction 1: from ASSUME (a=b), EQMP/SUBS realLeReflThm instances to get
    both ≤, CONJ. Direction 2: CONJUNCT1/2 + realLeAntisymThm + MP.
    DEDUCTANTISYM.

### Tests — `tests/real_arith_tests.wl`

Structure copied from `tests/real_abs_tests.wl`. ~30 asserts:
- Ground: `rnumAdd[2,3]`, `rnumAdd[7,5]` (recursion depth), `rnumAdd[0,4]`,
  `rnumMul[2,3]`, `rnumMul[6,7]`, `rnumMul[0,5]`, `rnumLe[3,9]`,
  `rnumLe[4,4]`, `rnumLt[1,3]`, `rnumNotLe[9,2]`, `rnumPos[2]`,
  `rnumNonneg[0]` — each: `concl` aconv a hand-built expected term (build
  the expected with the same public Consts; shallow asserts, no deep MatchQ),
  and `hyp` empty.
- Errors: `assertThrows` on `rnumLe[5,1]`, `rnumLt[3,3]`, `rnumPos[0]` with
  tag `realarith-ground` (read the tag via `f[[2, "tag"]]`).
- Part B: instantiate each theorem at rnum literals and MP/EQMP it shut,
  e.g. realLeMulCancelThm SPEC'd c := rnumTm 2, a := rnumTm 1, b := rnumTm 3,
  MP with rnumPos[2], EQMP backward with rnumLe[1,3] to get
  ⊢ realLe (2·1) (2·3); realLtIrreflThm at a fresh real var;
  realLeAddMono2Thm chained on rnumLe facts. Assert concl shapes by aconv.

## WL / project pitfalls (these WILL bite you — read twice)

1. **No `_` in any identifier**, including Module locals: `x_eq` parses as
   `Pattern[x, Blank[eq]]` and silently breaks evaluation. Use camelCase.
2. **WL comments close at the first `*)`** — never write `*)` (e.g. `(a*)`,
   `(SUC k*)`) inside comment prose; the error then points far below.
3. **Private-context symbols do not cross files.** `HOL`Stdlib`Real`'s
   private `realTy`/`realAddTm`/`rZ`/`zeroRealTm` are NOT reachable here —
   build your own via the public `*Const[]` exports. An unbound cross-context
   symbol stays UNEVALUATED and only fails much later ("not a theorem" /
   "mkComb type mismatch"). When a rule application returns unevaluated,
   suspect a wrong-context symbol first.
4. **HOL variable identity is (name string, type)** — `mkVar["q", ty]` in two
   places is ONE variable. `mkAbs` binds by name. Internal binders and
   per-branch witnesses need distinctive names (`qW`, `aB1`), never bare
   `x/q/r/p/s` that a caller's term might carry.
5. **Errors** are `HOL`Error`holError[tag, msg, payload]` which Throws a
   `Failure["HOLError", …]` with `holErrorTag`. Tests assert on the payload
   tag. Never use `Message` + `$Failed`.
6. **Run scripts as `wolframscript -file foo.wls`** — a bare
   `wolframscript foo.wls` drops into an interactive REPL and hangs forever.
7. **Tests** use `tests/harness.wl` (`HOLTest`assertEq/assertTrue/
   assertThrows/runTests`). Avoid deeply-nested `MatchQ` literal term
   patterns — use position extraction + shallow asserts, or build the
   expected term and compare with `aconv`.
8. Term construction above the kernel goes through `mkVar`/`mkConst`/
   `mkComb`/`mkAbs` — never raw `comb[...]`/`abs[...]` literals.
9. **Debug with narrow probes** (`Head[th]`, `hyp[th]`, one sub-slot), never
   print whole term trees.
10. **No `Return` inside `Do`/`For`/`While`** — it exits only the loop, NOT
    the surrounding Module; code after the loop still runs. Use a result
    flag (`out = Null; While[out === Null && …]`) or `Throw`/`Catch`.

## Verification

Your sandbox cannot run `wolframscript`. Deliver statically-checked code:
balanced brackets, no `_` identifiers, every referenced theorem name
grep-verified against its defining file (state in the report WHERE you
verified each non-obvious name). Do NOT fake test output. The reviewer runs
`tests/dev.wls auto/RealArith.wl real_arith` and the cold Strict suite.

## Hard rules

- Do NOT `git commit`, branch, push, or touch git config. Leave all changes
  in the working tree.
- Do NOT modify files outside Scope. If you believe you must, STOP and write
  that in the report instead.
- **Stop-loss**: if the same step fails twice for the same reason, STOP and
  write a report describing the failure instead of iterating further.
- Keep the diff minimal: no drive-by reformatting, no renames outside the task.

## Report format (your final message)

1. What changed — per file, with line ranges and a one-line why.
2. Name verification — each imported theorem/builder name and the file:line
   where you confirmed it.
3. Open questions / anything you are unsure about (empty if none).
