# Brief 008 — stdlib/Real/Seq.wl Stage 1: tendsto + limit calculus core

## Goal

First stage of M7-8 (sequences over ℝ). New file `stdlib/Real/Seq.wl` in the
Real FOLDER (same package context `HOL`Stdlib`Real``) defining the ε-N limit
relation `tendsto : (num→real)→real→bool` (REAL ε — user decision) and
`convergent`, then proving the limit-calculus core: constant sequences,
uniqueness of limits, sum / negation / difference laws. All linear-order
"ε bookkeeping" is discharged by ONE-LINE calls to
`HOL`Auto`RealArith`realArithProve` — this file is the first consumer of
REAL_ARITH and should lean on it everywhere it fits. Plus a new test file
`tests/real_seq_tests.wl`.

## Context pointers

- `CLAUDE.md` (**Conventions** + variable-capture hygiene) first.
- `stdlib/Real/{Cut,Field,Mul,Inv,Complete,Abs,MinMax}.wl` — you are IN this
  folder's context: their `` `Private` `` vocabulary IS reachable by bare
  name (folder rule, PLAN §8.1). Grep for the term builders before
  redefining anything: `forallTm`/`existsTm`/`conjTm`/`impTm`/`notTm`
  (Cut.wl), `zeroRealTm[]` (= `&ℝ(&ℚ(&ℤ 0))`, Mul.wl:125), `realTy`,
  `realLeTm`/`realLtTm`/`realAddTm`/`realNegTm`/`realMulTm` appliers,
  `realAbsTm` (Abs.wl), `unfoldRealAbs` (Abs.wl — the APTHM+BETACONV unfold
  idiom to copy for your own `unfoldTendsto`).
- `stdlib/Real/Abs.wl` exports (exact statements):
  `realAbsPosThm` ⊢ ∀x. 0≤x ⇒ |x| = x;
  `realAbsNegCaseThm` ⊢ ∀x. ¬(0≤x) ⇒ |x| = −x;
  `realAbsZeroThm` ⊢ |0| = 0; `realAbsNonnegThm` ⊢ ∀x. 0 ≤ |x|;
  `realLeAbsSelfThm`; `realNegLeAbsThm`; `realAbsNegThm` ⊢ ∀x. |−x| = |x|;
  `realAbsTriangleThm` ⊢ ∀x y. |x+y| ≤ |x| + |y|.
- Order/algebra surface (Cut/Mul/Inv/Complete): `realLeReflThm`,
  `realLeAntisymThm` ⊢ ∀x y. x≤y ⇒ y≤x ⇒ x=y, `realLeTotalThm`,
  `realLtNotLeThm` ⊢ ∀x y. (x<y) = ¬(y≤x), `realLtImpLeThm`,
  `realLe/Lt{Le,Lt}TransThm`, `realAddNegThm` ⊢ ∀x. x+(−x) = 0,
  `realNegPosThm` (Inv.wl — VERIFY exact statement; expected `x<0 ⇒ 0<−x`
  or equivalent), `realLtIrreflThm` (HOL`Auto`RealArith`, public)
  ⊢ ∀x. ¬(x<x).
- **`HOL`Auto`RealArith`` (import it in BeginPackage)** — public:
  `realArithProve[goalTm]` proves ∀-closed goals
  `∀x⃗:real. H₁ ⇒ … ⇒ Hₘ ⇒ C` where hyps/concl are `realLe`/`realLt`/`=`
  atoms over LINEAR real terms (also ¬≤/¬< atoms and ∧-conjunctions of
  hyps; equality conclusions supported). Division by a literal is written
  `realMul t (realInv <literal>)`. NOT supported: ∃, ∨, ¬(=) hypotheses,
  non-linear atoms (but any opaque real subterm is abstracted as a
  variable, so goals ABOUT `realAbs`-atoms work as long as the atom
  appears opaquely). `rnumNe[m,n]` (⊢ ¬(rnum m = rnum n)) and
  `rnumPos[n]`/`rnumLt`/`rnumLe` ground provers are also public.
  RealArith's `rnumTm` etc. are PRIVATE to `HOL`Auto`RealArith` — NOT
  reachable from Seq.wl; build literals with the Real folder's own
  builders (`zeroRealTm[]`; 2 = `&ℝ(&ℚ(&ℤ(SUC(SUC 0))))` via
  `realOfRatTm`/`ratOfIntTm`(public, Rat)/`intOfNumConst[]`(public, Int)/
  `sucConst[]`/`zeroConst[]`(public, Num) or whatever one-literal builder
  the folder already has — grep first).
- Num (public): `leqConst[]` (≤ : num→num→bool), `zeroConst[]`, `sucConst[]`,
  `plusConst[]`, `leqDefThm` (VERIFY: m ≤ n ⟺ ∃k. m+k = n),
  `leqZeroThm`, `leqReflThm`.
- Bool/Equal/Drule as usual; `HOL`Drule`CONVRULE`/`DEPTHCONV`/`TRYCONV` +
  `HOL`Equal`BETACONV` for β-cleanup after SPEC-ing λ-sequences.

## Scope

- Files you may CREATE: `stdlib/Real/Seq.wl`, `tests/real_seq_tests.wl`.
- Files you may MODIFY: none. Do NOT touch the runner load lists — the
  reviewer wires them at acceptance (load order will be …MinMax →
  auto/RealArith → Real/Seq). Verification loop for you to assume:
  `tests/dev.wls stdlib/Real/Seq.wl real_seq`.
- MUST NOT touch: `Kernel.wl`, `Types.wl`, `Terms.wl`, `Bootstrap.wl`,
  `bootstrap.mx`, `CLAUDE.md`, `PLAN.md`, `PROGRESS.md`, anything under
  `codex/` except appending to your own report. No `newAxiom`. 

## Definitions (pin EXACTLY — downstream stages parse these shapes)

Sequences are plain terms of type `num→real` (`tyFun[numTy, realTy]`).
No new HOL type.

```
tendstoDefThm:   ⊢ tendsto = (λa L. ∀e. 0 < e ⇒
                     ∃N. ∀n. N ≤ n ⇒ realAbs (a n + (−L)) < e)
convergentDefThm:⊢ convergent = (λa. ∃L. tendsto a L)
```
- `0` is `zeroRealTm[]`; `−` is realNeg; subtraction is ALWAYS spelled
  `realAdd x (realNeg y)` (no realSub constant exists).
- Binder types: a : num→real, L e : real, N n : num. `N ≤ n` is Num's leq.
- `newDefinition` via `mkEq[mkVar["tendsto", …], body]` (copy Abs.wl's
  realAbsDefThm pattern). Export `tendstoConst[]`/`tendstoTm[aT, LT]`,
  `convergentConst[]`/`convergentTm[aT]`, and an `unfoldTendsto[aT, LT]`
  helper (⊢ tendsto a L = <β-reduced body>, two APTHM + BETACONV).

## Deliverable theorems

REALARITH glue (each ONE `realArithProve` call at load time; keep private,
names up to you — suggested):
- g1 `⊢ ∀e. 0 < e ⇒ 0 < e·(1/2)`  (1/2 = realInv of the 2 literal)
- g2 `⊢ ∀x y. (x + (−y) = 0) ⇒ x = y`
- g3 `⊢ ∀x y z. (x+(−y)) + (y+(−z)) = x+(−z)`
- g4 `⊢ ∀x y u v. (x+y) + (−(u+v)) = (x+(−u)) + (y+(−v))`
- g5 `⊢ ∀x y. (−x) + (−(−y)) = −(x+(−y))`  (for tendstoNeg; check the form
  you actually need and adjust — any LINEAR equality realArithProve takes)
- g6 `⊢ ∀u v w e. u ≤ v+w ⇒ v < e·(1/2) ⇒ w < e·(1/2) ⇒ u < e`
- g7 `⊢ ∀v w e. e ≤ v+w ⇒ v < e·(1/2) ⇒ w < e·(1/2) ⇒ e < e`
  (for uniqueness; the conclusion `e<e` is a legal atom — close to F
  afterwards with `realLtIrreflThm` + NOTELIM + MP)

ℕ helper (private): `leqAddSelf[mT, kT]` ⊢ m ≤ m + k — via `leqDefThm`
backwards with EXISTS witness k and REFL[m+k] (verify leqDefThm's exact
shape first; if it is stated with the ∃ on the right, EQMP its SYM).

Public theorems:
1. `tendstoConstThm` ⊢ ∀c. tendsto (λn. c) c.
   Unfold; GEN e, DISCH 0<e; EXISTS N := 0; GEN n, DISCH 0≤n (`leqZeroThm`
   instance discharges trivially — the hypothesis is simply unused);
   the body atom: realAbs ((λn.c) n + (−c)) < e — BETACONV the redex,
   `realAddNegThm` gives c+(−c) = 0, APTERM `realAbsConst[]`, TRANS with
   `realAbsZeroThm`, then EQMP the `<`-atom from `0 < e` (use the leCong/
   MKCOMB congruence idiom on realLt: rewrite the LHS of the atom).
2. `realNeAbsPosThm` ⊢ ∀x. ¬(x = 0) ⇒ 0 < realAbs x.
   EXCLUDEDMIDDLE on `realLe 0 x`:
   - case 0≤x: `realAbsPosThm` gives |x| = x. Derive 0<x by CCONTR:
     ASSUME ¬(0<x); `realLtNotLeThm` at (0,x) gives (0<x) = ¬(x≤0), so
     ¬(0<x) yields x≤0 via propTaut double-negation (`HOL`Auto`PropTaut`
     propTaut` is public; or do it manually with CCONTR); then
     `realLeAntisymThm` x≤0, 0≤x ⇒ x=0 — wait for the ORDER of args:
     antisym gives x = 0 from x≤0 and 0≤x; NOTELIM the ¬(x=0) hyp + MP ⇒ F;
     CCONTR closes 0<x. EQMP backwards through |x| = x.
   - case ¬(0≤x): `realAbsNegCaseThm` gives |x| = −x; `realNotLeLtThm`
     (RealArith public: ¬(x≤y) = (y<x)) at (0,x) turns the case hypothesis
     into x<0; `realNegPosThm` gives 0<−x; EQMP backwards.
   DISJCASES, NOTINTRO/DISCH bookkeeping, GEN.
3. `tendstoUniqueThm` ⊢ ∀a L1 L2. tendsto a L1 ⇒ tendsto a L2 ⇒ L1 = L2.
   CCONTR ¬(L1 = L2). Let e0 = realAbs (L1 + (−L2)).
   - ¬(L1+(−L2) = 0): contrapositive of g2 (DISCH/MP juggling or prove the
     small propositional step with propTaut).
   - 0 < e0 by `realNeAbsPosThm`.
   - 0 < e0·(1/2) by g1.
   - MP both unfolded tendsto hyps at e := e0·(1/2); CHOOSE N1, N2
     (distinctive witness names per hygiene — `nW1`, `nW2`).
   - n := N1 + N2; `leqAddSelf` both ways (N2 ≤ N1+N2 needs add-comm at the
     ℕ level: `addCommThm` is public in Num — VERIFY name — or a second
     leqAddSelf at the commuted sum + EQMP).
   - Get d1 = |a n + (−L1)| < e0·(1/2) and d2 = |a n + (−L2)| < e0·(1/2).
   - Triangle: `realAbsTriangleThm` at x := L1 + (−(a n)), y := a n + (−L2)
     gives |x+y| ≤ |x|+|y|; g3 (SPEC L1, a n, L2) + APTERM realAbsConst
     rewrites |x+y| to e0. |L1 + (−(a n))| = |a n + (−L1)|: APTERM abs on
     the g5-style equality −(an+(−L1)) = L1+(−an) (adjust the exact linear
     equality and prove with realArithProve), then `realAbsNegThm`.
   - g7 with v := |a n+(−L1)|, w := |a n+(−L2)|, e := e0 gives e0 < e0;
     `realLtIrreflThm` + NOTELIM + MP ⇒ F; CCONTR; DISCH; GEN.
4. `tendstoAddThm` ⊢ ∀a b A B. tendsto a A ⇒ tendsto b B ⇒
     tendsto (λn. a n + b n) (A + B).
   Given e, 0<e: halve via g1; CHOOSE N1, N2 from the two hyps at e·(1/2);
   N := N1+N2; for N ≤ n: the goal atom |(λn. an+bn) n + (−(A+B))| < e —
   BETACONV the redex; g4 + APTERM abs rewrites the argument to
   (a n+(−A)) + (b n+(−B)); `realAbsTriangleThm` + g6 closes.
5. `tendstoNegThm` ⊢ ∀a A. tendsto a A ⇒ tendsto (λn. −(a n)) (−A).
   Same N and e as the hypothesis; the argument −(a n) + (−(−A)) rewrites
   to −(a n + (−A)) (a g5-style realArithProve equality + APTERM abs),
   then `realAbsNegThm`. No halving needed.
6. `tendstoSubThm` ⊢ ∀a b A B. tendsto a A ⇒ tendsto b B ⇒
     tendsto (λn. a n + (−(b n))) (A + (−B)).
   Corollary of 4+5 — BUT note the sequence term: instantiating
   tendstoAddThm at b := (λn. −(b n)) gives the inner sequence
   `λn. a n + (λn. −(b n)) n` with an unreduced redex. Clean it with
   CONVRULE[DEPTHCONV[TRYCONV[BETACONV]]] so the exported statement has the
   β-reduced form shown above. (SPEC does not β-reduce — this WILL bite
   you if skipped.)
7. `tendstoConvergentThm` ⊢ ∀a L. tendsto a L ⇒ convergent a (unfold +
   EXISTS).

## Tests — `tests/real_seq_tests.wl` (~20 asserts; copy real_abs_tests.wl scaffolding)

- Definition shape: `unfoldTendsto` at fresh vars — concl is an mkEq whose
  RHS starts with the ∀e binder (position extraction + shallow asserts).
- `tendstoConstThm` SPEC'd at `zeroRealTm[]` and at a var: hyp empty, concl
  aconv expected (build expected with the folder builders).
- `realNeAbsPosThm` MP'd with `HOL`Auto`RealArith`rnumNe[1,0]`-derived
  ¬(1 = 0) — NOTE rnumNe's statement is about RealArith's rnum literals,
  which are the SAME terms as the folder's `&ℝ(&ℚ(&ℤ n̂))` literals (aconv);
  result: 0 < |1|.
- `tendstoUniqueThm`: MP with two `tendstoConstThm` instances at the same c
  → ⊢ c = c.
- `tendstoAddThm`/`tendstoNegThm`/`tendstoSubThm`: instantiate at constant
  sequences and MP; assert the conclusion shape via aconv after a
  DEPTHCONV-BETACONV cleanup where needed.
- `tendstoConvergentThm` end-to-end: ⊢ convergent (λn. c).
- Negative: assertThrows is not needed this stage (no new error paths) —
  skip rather than invent.

## WL / project pitfalls (read twice)

1. No `_` in identifiers (incl. Module locals); camelCase.
2. WL comments close at the first `*)`.
3. Cross-FILE privates: Real-FOLDER privates ARE reachable (same context);
   `HOL`Auto`RealArith`/Bool/PropTaut privates are NOT — publics only.
4. HOL var identity = (name string, type): scaffolding/witness binders get
   distinctive names (`nW1`, `eH`, `aSeq`); the DEFINITION binders and
   final-statement binders use canonical names (a L e N n c A B).
5. holError is HoldRest — literal String/Association at call sites (no new
   throws expected this stage anyway).
6. `wolframscript -file` only (your sandbox can't run it — say so).
7. Tests: harness asserts + aconv on built expected terms; no deep MatchQ.
8. mkVar/mkConst/mkComb/mkAbs only — never raw comb/abs.
9. Narrow probes when debugging; never print whole term trees.
10. No `Return` inside Do/For/While.
11. **SPEC does not β-reduce.** Any instantiation that puts a λ-sequence
    in application position leaves redexes; clean with
    CONVRULE[DEPTHCONV[TRYCONV[BETACONV]]] before comparing/exporting.
12. **realArithProve goal language is narrow** (see Context). If a glue
    goal is rejected, reshape it to a ⇒-chain of ≤/</= atoms over linear
    terms (e.g. conclusion `e < e` instead of F) rather than working
    around with manual proofs.

## Verification

Sandbox cannot run wolframscript: deliver statically-checked code; report
the file:line where each borrowed builder/lemma name was verified.
Reviewer runs `tests/dev.wls stdlib/Real/Seq.wl real_seq`, wires runners
(RealArith before Seq), then cold Strict run_all.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck on scope, STOP and report.
- Stop-loss: same failure twice → STOP and report (deliver the loadable
  subset: definitions + whatever theorems are done, tests matching).
- Minimal diff.

## Report format

1. Per-file changes with line ranges + one-line why.
2. Name-verification table (builder/lemma → file:line).
3. The exact statements of the REALARITH glue lemmas you ended up using.
4. Open questions (empty if none).
