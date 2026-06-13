# Brief 010 — stdlib/Real/Seq.wl Stage 2b: abs-mul + product & scalar limit laws

## Goal

Extend `stdlib/Real/Seq.wl` (Stages 1+2a, briefs 008/009 — read the whole file
first; reuse its `eventually` combinator, `tendstoEventuallyThm`,
`seqTendstoEventuallyBoundedThm`) with the multiplicative limit laws:
`seqTendstoMulThm` (product) and `seqTendstoScalarMulThm` (scalar multiple),
plus the two algebraic prerequisites they need — `realAbsMulThm`
(|x·y| = |x|·|y|) and a ring-identity helper. Append tests. This closes M7-8
Stage 2.

## Blueprint (in-repo, gitignored, on disk — READ and mirror the structure)

`tautology-ref/Tautology/` (a COMPLETE, 0-sorry Lean reference of this exact
development). Read:
- `RealBootstrap/Abs.lean:128` `abs_mul` — the 4-case sign split
  (0≤x|¬ × 0≤y|¬), each branch rewriting |x|,|y|,|xy| then a mul-sign lemma.
- `RealBootstrap/OrderAlgebra.lean:279` `mul_sub_mul_eq_sub_mul_add_mul_sub`
  — the ring identity `x·y − a·b = (x−a)·y + a·(y−b)` (symm + distrib +
  cancel).
- `RealSequence/Mul.lean` `seqTendsto_mul` — the product proof (THE structure
  to follow): e2:=eps/2; B from `seqTendsto_eventuallyBounded v`; A:=|a|+1;
  deltaU:=e2·(1/B), deltaV:=(1/A)·e2; scaling identities deltaU·B=e2,
  A·deltaV=e2; combine THREE eventually's via `Eventually.and`; pointwise
  decompose |uv−ab| ≤ |t1|+|t2| (ring identity + `abs_add_le_abs_add_abs`),
  bound |t1|=|u n−a|·|v n| ≤ |u n−a|·B < deltaU·B = e2 (and symmetric for t2),
  sum < eps.

Surface translation as in brief-009: `F.lt/le/add/sub/mul/zero/one`, `abs F`
→ our concrete `realLt/realLe/realAdd/(realAdd x (realNeg y))/realMul/
zeroRealTm[]/(the 1 literal)/realAbsTm`. Their named linear/half algebra steps
→ `HOL`Auto`RealArith`realArithProve` calls — BUT see pitfall 12: realArithProve
is LINEAR, so the products (deltaU·B, the ring identity, abs_mul) are NOT
realArithProve territory; only the pure ε/2-combination steps over already-
opaque atoms are.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- You are IN context `HOL`Stdlib`Real`` — all Real-folder privates reachable.
- **Available, verified (grep the ::usage before use):**
  - Abs.wl: `realAbsPosThm` ⊢ ∀x. 0≤x ⇒ |x|=x;
    `realAbsNegCaseThm` ⊢ ∀x. ¬(0≤x) ⇒ |x|=−x;
    `realAbsNonnegThm`, `realAbsTriangleThm`, `realAbsNegThm`.
  - Mul.wl: `realMulNonnegThm`=`realLeMulNonnegThm` ⊢ ∀x y. 0≤x ⇒ 0≤y ⇒
    0≤x·y; `realMulNegRightThm` ⊢ ∀x y. x·(−y)=−(x·y);
    `realMulNegLeftThm` ⊢ ∀x y. (−x)·y=−(x·y); `realNegNegThm` ⊢ −(−x)=x;
    `realLeMulMonoThm` ⊢ ∀a b c. 0≤c ⇒ a≤b ⇒ c·a≤c·b;
    `realLtMulMonoThm` ⊢ ∀a b c. 0<c ⇒ a<b ⇒ c·a<c·b;
    `realMulCommThm`/`realMulAssocThm`/`realMulDistribThm`(left distrib:
    x·(y+z)=x·y+x·z)/`realMulOneThm`/`realMulZeroThm`;
    sign: `notNonnegToLeZeroThm` ⊢ ∀x. ¬(0≤x) ⇒ x≤0 (VERIFY exact name/shape),
    `realNegNonnegThm`/`realNegNonposThm`/`realLeNegThm` (VERIFY shapes — used
    to turn y≤0 into 0≤−y and 0≤−(xy) into xy≤0).
  - Inv.wl: `realMulInvThm` ⊢ ∀x. ¬(x=0) ⇒ x·(realInv x)=1; `realInvPosThm`/
    `invPos*` for 0<x ⇒ 0<1/x (VERIFY the public name for "inv of positive is
    positive").
  - Seq.wl (briefs 008/009): `tendstoConstThm`, `tendstoEventuallyThm`,
    `eventuallyAndThm`/`eventuallyMonoThm`, `seqTendstoEventuallyBoundedThm`,
    `realNeAbsPosThm`, the `half`/`1`/`2`-literal builders + the
    `realArithProve` glue lemmas brief-008/009 already proved (grep — reuse
    `0<e ⇒ 0<e·(1/2)`, `x·(1/2)+x·(1/2)=x`, etc., DO NOT re-prove).
  - `realArithProve` for linear ε-combination over opaque atoms.

## Scope

- MODIFY: `stdlib/Real/Seq.wl` (append Stage 2b), `tests/real_seq_tests.wl`.
- Do NOT touch other Real files (realAbsMul goes in Seq.wl for now — it will
  migrate to Abs.wl at graduation; keep it local). Do NOT touch runner lists.
  MUST NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/docs/codex(except
  report). No newAxiom. No new files.

## Deliverable theorems (Seq.wl, all public unless marked private)

1. (private helper) `realAbsNonposThm` ⊢ ∀x. realLe x 0 ⇒ realAbs x = realNeg x.
   `realAbsNegCaseThm` only covers the STRICT `¬(0≤x)`; the abs_mul mixed
   cases produce `x·y ≤ 0` (boundary included). Prove: EXCLUDEDMIDDLE on
   `realLe 0 x` — if 0≤x then with x≤0, `realLeAntisymThm` gives x=0, and
   |0|=0=−0 (`realAbsZeroThm` + `realNegZeroThm`); else `realAbsNegCaseThm`.
2. `realAbsMulThm` ⊢ ∀x y. realAbs (realMul x y) = realMul (realAbs x) (realAbs y).
   Mirror RealBootstrap/Abs.lean:128 — EXCLUDEDMIDDLE on `realLe 0 x`, nested
   EXCLUDEDMIDDLE on `realLe 0 y`; 4 branches rewrite |x|,|y|,|xy| via
   realAbsPos/realAbsNonpos and the product sign via
   realMulNonneg/realMulNegRight/realMulNegLeft/realNegNeg, mirroring the Lean
   `mul_neg`/`neg_mul`/`neg_mul_neg` rewrites. Distinctive case binders.
3. (private helper) `mulSubMulThm` ⊢ ∀x y a b.
   realAdd (realMul x y) (realNeg (realMul a b)) =
   realAdd (realMul (realAdd x (realNeg a)) y) (realMul a (realAdd y (realNeg b))).
   Mirror OrderAlgebra.lean:279 — realMulDistrib (both factors) +
   realMulNegLeft/Right + additive-group rearrange (a·y cancels). NOT a
   realArithProve goal (products of variables).
4. `seqTendstoMulThm` ⊢ ∀a b A B. tendsto a A ⇒ tendsto b B ⇒
   tendsto (λn. realMul (a n) (b n)) (realMul A B).
   Mirror RealSequence/Mul.lean. Spell deltaU/deltaV with realInv; their
   scaling identities deltaU·B=e2 / A·deltaV=e2 via realMulInvThm (+ assoc/
   comm/one) — these are the `mul_inv_mul_cancel` analogs, prove as local
   `have`s. The three-way eventually = `eventuallyAndThm` nested twice
   (au-close ∧ bv-close ∧ b-bounded); `eventuallyMonoThm` to the pointwise
   goal. Per-summand: |t1| = |u n−a|·|v n| (realAbsMulThm) ≤ |u n−a|·B
   (realLeMulMono with |v n|<B ⟹ ≤, abs_nonneg) < deltaU·B = e2
   (realLtMulMono... mind left/right — follow the Lean's
   mul_le_mul_nonneg_left / mul_lt_mul_pos_right exactly); symmetric t2;
   sum<eps via the half-add fact. The final `|uv−ab| ≤ |t1|+|t2|` uses
   mulSubMulThm (rewrite the abs argument) + realAbsTriangleThm.
5. `seqTendstoScalarMulThm` ⊢ ∀a A c.
   tendsto a A ⇒ tendsto (λn. realMul c (a n)) (realMul c A).
   DERIVE as a corollary: instantiate `seqTendstoMulThm` with the SECOND
   sequence the constant `λn. c` and b:=c (use `tendstoConstThm`), giving
   tendsto (λn. (a n)·c) (A·c); then realMulComm rewrites both the sequence
   body (under the λ, via APTERM/CONVRULE) and the limit to c·(a n) / c·A.
   Mind the β-redex from instantiating a λ-sequence (pitfall 11): clean with
   CONVRULE[DEPTHCONV[TRYCONV[BETACONV]]] so the exported statement has the
   form shown. (If deriving-from-product proves awkward to reshape, prove it
   directly the same way as product with the bounded factor trivially
   constant — but try the corollary first, it is far shorter.)

If realAbsMul or the product proof stalls, deliver the loadable subset
(realAbsNonpos + realAbsMul + mulSubMul at minimum, or +product) and STOP per
stop-loss with a report — partial is acceptable.

## Tests (append ~15 asserts)

- `realAbsMulThm` at concrete sign combos: SPEC at (2,3)→|6|=|2|·|3|;
  at (−2,3) and (−2,−3) using rnum-negated literals; assert via aconv.
- `mulSubMulThm` SPEC'd at vars — concl shape.
- `seqTendstoMulThm` from two `tendstoConstThm`: ⊢ tendsto(λn. c·d)(c·d)
  (after beta-clean); and a mixed const-times-itself.
- `seqTendstoScalarMulThm` from `tendstoConstThm`: ⊢ tendsto(λn. c·d)(c·d).
- Shapes via aconv against folder-builder-constructed expected terms.

## WL / project pitfalls (read twice)

1. No `_` in identifiers (incl. Module locals). 2. WL comments close at first
`*)`. 3. In-folder privates reachable; RealArith/Bool/PropTaut privates NOT.
4. HOL var identity=(name,type); case/witness binders distinctive (xC,yC,
nW1,nW2). 5. holError HoldRest. 6. `wolframscript -file` only (sandbox can't).
7. Tests: aconv on built expected, no deep MatchQ. 8. mkVar/mkConst/mkComb/
mkAbs only. 9. Narrow probes. 10. No Return in Do/For/While.
11. **SPEC does not β-reduce** — clean λ-application redexes with
CONVRULE[DEPTHCONV[TRYCONV[BETACONV]]] before comparing/exporting (bites
scalar-mul and product's λ-sequence instantiation).
12. **realArithProve is LINEAR** — products of variables (deltaU·B, the ring
identity, |x·y|) are opaque atoms to it and CANNOT be proved by it; use the
mul lemmas (realMulInv/Distrib/Assoc/Comm, realLe/LtMulMono) for those. Only
pure ε/2 combination over already-formed opaque atoms is realArithProve's job.

## Verification

Sandbox can't run wolframscript: deliver statically-checked code; report
file:line where each borrowed lemma/builder name was verified. Reviewer runs
`tests/dev.wls stdlib/Real/Seq.wl real_seq` then cold Strict run_all.

## Hard rules

- No git commit/branch/push/config; leave changes in working tree.
- Nothing outside Scope; if stuck on scope, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff.

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (lemma/builder → file:line).
3. Which theorems fully proven vs stopped.
4. Open questions (empty if none).
