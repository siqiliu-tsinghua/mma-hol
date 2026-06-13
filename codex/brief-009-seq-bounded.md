# Brief 009 — stdlib/Real/Seq.wl Stage 2a: Eventually combinator + convergent⇒bounded

## Goal

Extend the EXISTING `stdlib/Real/Seq.wl` (Stage 1, brief-008 — read the whole
file first) with: (1) an `eventually` predicate combinator + its `mono`/`and`/
`ofForall` lemmas and a bridge from `tendsto`; (2) `convergent ⇒ eventually
bounded` and `tendsto a L ∧ L≠0 ⇒ eventually-away-from-zero`. These are the
additive/boundedness half of M7-8 Stage 2 (the multiplicative half — abs-mul,
scalar, product — is the next brief and is NOT in scope here). Append tests to
`tests/real_seq_tests.wl`.

## Blueprint (READ THESE — they are in the repo, gitignored, on disk)

A COMPLETE (0 sorry/admit/axiom) Lean reference of this exact development lives
at `tautology-ref/Tautology/RealSequence/`. Read and mirror the PROOF STRUCTURE
(witnesses, case splits, which triangle/order step where) from:
- `Basic.lean` — `Eventually`, `Eventually.of_forall/mono/and`, `SeqTendsto`
  (= our `tendsto` verbatim: `∀eps. 0<eps → Eventually (λn. |u n − l| < eps)`).
- `Bounded.lean` — `EventuallyBounded`, `abs_add_one_pos`,
  `seqTendsto_eventuallyBounded`, `EventuallyAwayFromZero`,
  `seqTendsto_eventuallyAwayFromZero`.

Surface translation: their `F.lt/F.le/F.add/F.sub/F.mul/F.zero/F.one` and
`abs F` → our concrete `realLt/realLe/realAdd/(realAdd x (realNeg y))/realMul/
zeroRealTm[]/(the real 1)/realAbsTm`. Their `Eventually.and` takes `Nat.max` of
two N's — we have no num `max`, so use `N1+N2` with the `leqAddSelf` helper
(N1≤N1+N2 and N2≤N1+N2, via Num `addCommThm` for the second), exactly as
brief-008's tendstoUnique did. Their named `half`/`add_lt_add`/linear ε-algebra
steps → ONE `HOL`Auto`RealArith`realArithProve` call each (we have REAL_ARITH;
this is our advantage — do not hand-build linear inequalities).

## Context pointers

- `CLAUDE.md` (**Conventions** + capture hygiene) first.
- You are IN the Real folder context `HOL`Stdlib`Real`` — Seq.wl's Stage-1
  privates AND the other Real files' privates are reachable by bare name. Grep
  Seq.wl for what brief-008 already defined: `tendstoConst[]`/`tendstoTm`/
  `unfoldTendsto`, the term builders it imported/aliased (`realAddTm`,
  `realNegTm`, `realAbsTm`, `realLtTm`, `realLeTm`, `zeroRealTm`, the `1`
  literal builder, `forallTm`/`existsTm`/`conjTm`/`impTm`/`notTm`), and the
  ℕ helpers it built (a `leqAddSelf`-like lemma may already exist — REUSE it,
  don't duplicate).
- Available abs/order lemmas (verify each ::usage before use):
  Abs.wl: `realAbsTriangleThm` ⊢ ∀x y. |x+y| ≤ |x|+|y|;
  `realAbsNonnegThm` ⊢ ∀x. 0 ≤ |x|; `realAbsNegThm` ⊢ ∀x. |−x| = |x|;
  `realNeAbsPosThm` (Seq.wl, brief-008) ⊢ ∀x. ¬(x=0) ⇒ 0 < |x|.
  Cut/Complete: `realLeLtTransThm`/`realLtLeTransThm`/`realLeTransThm`,
  `realLtImpLeThm`, `realLeReflThm`.
  Num (public): `addCommThm`, `leqTransThm`, `leqReflThm`, `leqDefThm`,
  `zeroConst[]`, `sucConst[]`, `plusConst[]`, `leqConst[]`.
- `HOL`Auto`RealArith`realArithProve[goalTm]` — proves ∀-closed ⇒-chains of
  realLe/realLt/= atoms over LINEAR real terms (opaque-atom abstraction, so
  goals mentioning `realAbs t` as an indivisible atom are fine). Use it for
  every linear-arithmetic step: e.g.
  `∀p q. p < (q + (the 1 literal)) ⇒ … `, `∀x. (x+(−a))+a = x` (linear
  identity), the bound `|u n − a| + |a| < |a| + 1` given `|u n − a| < 1`,
  the away-from-zero rearrangement. If a step is linear over the `realAbs`
  atoms, it is one realArithProve call.

## Scope

- Files you may MODIFY: `stdlib/Real/Seq.wl` (append Stage 2a),
  `tests/real_seq_tests.wl` (append).
- Do NOT touch runner load lists (already wired: …→ auto/RealArith →
  Real/Seq). Do NOT modify any other Real file (realAbsMul etc. is the NEXT
  brief — do not add it here). MUST NOT touch Kernel/Types/Terms/Bootstrap/
  bootstrap.mx/CLAUDE.md/PLAN.md/PROGRESS.md or codex/* except your report.
  No `newAxiom`. No new files.

## Definitions (pin exactly)

```
eventuallyDefThm:  ⊢ eventually = (λP. ∃N. ∀n. N ≤ n ⇒ P n)
                   (P : num→bool; eventually : (num→bool)→bool)
eventuallyBoundedDefThm: ⊢ eventuallyBounded =
  (λu. ∃B. 0 < B ∧ eventually (λn. realAbs (u n) < B))
eventuallyAwayFromZeroDefThm: ⊢ eventuallyAwayFromZero =
  (λu. ∃c. 0 < c ∧ eventually (λn. c < realAbs (u n)))
```
- `u : num→real`. `0` = `zeroRealTm[]`. newDefinition + an `unfoldEventually`
  helper (APTHM+BETACONV, mirror `unfoldTendsto`). Export
  `eventuallyConst[]`/`eventuallyTm[predTm]` and likewise for the two
  `eventually*` predicates, plus `unfold*` helpers.

## Deliverable theorems

1. `eventuallyOfForallThm` ⊢ ∀P. (∀n. P n) ⇒ eventually P.  (EXISTS N:=0.)
2. `eventuallyMonoThm` ⊢ ∀P Q. (∀n. P n ⇒ Q n) ⇒ eventually P ⇒ eventually Q.
   (CHOOSE N from eventually P; same N works.)
3. `eventuallyAndThm` ⊢ ∀P Q. eventually P ⇒ eventually Q ⇒
   eventually (λn. P n ∧ Q n).  (CHOOSE N1,N2; witness N1+N2; leqAddSelf both
   ways + leqTrans to feed each hypothesis; distinctive witness names nW1,nW2.)
   P,Q are higher-order var predicates of type num→bool; SPEC/instantiation of
   these needs care — apply them via mkComb and BETACONV after substitution.
4. `tendstoEventuallyThm` ⊢ ∀a L e. tendsto a L ⇒ 0 < e ⇒
   eventually (λn. realAbs (a n + (−L)) < e).
   tendsto's unfolded body inner part is DEFINITIONALLY eventually's body at
   the predicate (λn. |a n − L| < e); so: unfoldTendsto, MP with 0<e, then
   FOLD the resulting `∃N.∀n. N≤n ⇒ …` into `eventually (λn. …)` via
   SYM(unfoldEventually at that predicate). (This is the bridge every Stage-2+
   proof uses instead of re-CHOOSE-ing N by hand.)
5. `seqTendstoEventuallyBoundedThm` ⊢ ∀a L. tendsto a L ⇒ eventuallyBounded a.
   Mirror Bounded.lean: B := realAbs L + 1; 0<B by triangle/nonneg (or one
   realArithProve over the atom |L|: `0 ≤ |L| ⇒ 0 < |L| + 1`); from
   `tendstoEventuallyThm` at e:=1 get eventually(λn. |a n − L| < 1); 
   `eventuallyMonoThm` to weaken the predicate to (λn. |a n| < B): pointwise,
   |a n| = |(a n − L) + L| (linear identity (a n + (−L)) + L = a n via
   realArithProve, then APTERM realAbsConst), triangle |(a n−L)+L| ≤
   |a n−L|+|L|, then |a n−L|+|L| < B = |L|+1 from |a n−L|<1 via realArithProve
   over atoms {|a n−L|, |L|}; realLeLtTrans. EXISTS B + CONJ.
6. `seqTendstoEventuallyAwayFromZeroThm` ⊢ ∀a L. tendsto a L ⇒ ¬(L = 0) ⇒
   eventuallyAwayFromZero a.
   Mirror Bounded.lean: c := realAbs L · (1/2)  [the `half` of |L|; spell as
   realMul (realAbs L) (realInv <2 literal>)]; 0<|L| by `realNeAbsPosThm`;
   0<c by a realArithProve-style step OR reuse brief-008's g1
   (`0<x ⇒ 0<x·(1/2)`) if it is in scope — grep Seq.wl; from
   tendstoEventually at e:=c get eventually(λn. |a n − L| < c); mono to
   (λn. c < |a n|): pointwise, |L| = |L − a n| + |a n| weakened — follow the
   Lean: |L| ≤ |L − a n| + |a n| (triangle on (L − a n)+(a n)=L), |L − a n| =
   |a n − L| (`realAbsNegThm` after the linear identity L−a n = −(a n − L)),
   then c < |a n| from |a n−L|<c and |L| = 2c (i.e. c = |L|/2) via
   realArithProve over atoms {|a n−L|, |a n|, |L|, c} — note 2c=|L| is a
   genuine linear relation you must SUPPLY to realArithProve as a hypothesis
   (prove `realMul (realAbs L) (realInv 2) + realMul (realAbs L) (realInv 2) =
   realAbs L`? that is NOT linear in c unless you treat c opaquely — instead
   keep c = |L|·(1/2) and prove the half-doubling `c + c = |L|` as a separate
   realArithProve fact `∀x. x·(1/2) + x·(1/2) = x` SPEC'd at |L|, then feed
   it). Follow Bounded.lean's `sub_half_self`/`half` steps for the exact shape.

If step 6's ε-algebra proves fiddly, deliver 1–5 + the bounded theorem and
STOP per stop-loss, reporting where 6 stuck — a loadable subset is acceptable.

## Tests (append ~15 asserts; copy real_seq_tests.wl scaffolding)

- `eventuallyOfForall`/`Mono`/`And` shape checks at concrete predicates
  (e.g. P := λn. 0 < (the 1 literal), trivially eventually).
- `tendstoEventuallyThm` from `tendstoConstThm`: ⊢ eventually(λn. |c−c|<e)…
  (instantiate, MP, assert concl shape).
- `seqTendstoEventuallyBoundedThm` from `tendstoConstThm`: a constant sequence
  is eventually bounded; assert ⊢ eventuallyBounded (λn. c).
- `seqTendstoEventuallyAwayFromZeroThm` from a constant nonzero sequence (MP
  with a ¬(c=0) fact, e.g. via rnumNe for a numeral c): assert the conclusion.
- Definition shape: unfoldEventually at a fresh predicate var.

## WL / project pitfalls (read twice)

1. No `_` in identifiers (incl. Module locals); camelCase.
2. WL comments close at first `*)`.
3. In-FOLDER privates reachable; RealArith/Bool/PropTaut privates are NOT
   (publics only — realArithProve, realNeAbsPosThm are public).
4. HOL var identity = (name,type); witness/scaffold binders distinctive
   (nW1,nW2,Bw,cw); higher-order predicate vars P,Q must be applied via
   mkComb + BETACONV after any instantiation (they don't auto-reduce).
5. holError HoldRest (no new throws expected).
6. `wolframscript -file` only (sandbox can't run it — say so).
7. Tests: harness asserts + aconv on built expected terms; no deep MatchQ.
8. mkVar/mkConst/mkComb/mkAbs only.
9. Narrow probes when debugging.
10. No `Return` in Do/For/While.
11. **SPEC does not β-reduce** — clean λ-application redexes with
    CONVRULE[DEPTHCONV[TRYCONV[BETACONV]]] before comparing/exporting.
12. **realArithProve is LINEAR** — it abstracts every non-linear/abs subterm
    as an opaque atom. A relation BETWEEN atoms that is not linear (e.g.
    2c = |L| when c is itself |L|·(1/2)) must be supplied as a separately
    proven hypothesis or SPEC'd lemma, not expected from realArithProve.

## Verification

Sandbox can't run wolframscript: deliver statically-checked code; report
file:line where each borrowed lemma/builder name was verified. Reviewer runs
`tests/dev.wls stdlib/Real/Seq.wl real_seq` then cold Strict run_all.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck on scope, STOP and report.
- Stop-loss: same failure twice → STOP, deliver the loadable subset + report.
- Minimal diff.

## Report format

1. Per-file changes with line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. Which theorems are fully proven vs stopped (if any).
4. Open questions (empty if none).
