# Brief 006 — auto/RealArith.wl Stage 2: proof-producing linear normalization + atom normalizer

## Goal

Stage 2 of M7-ε REAL_ARITH. Extend the EXISTING `auto/RealArith.wl` (Stage 1,
brief-005: rnum ground layer + ordered-field combination lemmas — read it
first, you will reuse almost everything) with the proof-producing term/atom
normalization layer: `realLinNormConv[t]` ⊢ t = canonical-linear-form, and
`realAtomNormConv[atom]` turning any linear `realLe`/`realLt` atom into an
equivalent atom whose two sides are ℕ-literal-coefficient canonical linear
terms (no realNeg, no realInv, no rational coefficients — denominators
cleared, negatives balanced across the relation). This is everything the
Stage 3 Farkas verifier needs to consume atoms. Plus new tests appended to
`tests/real_arith_tests.wl`.

## Context pointers

- Read `CLAUDE.md` (**Conventions**, variable-capture hygiene) before coding.
- `auto/RealArith.wl` — YOUR base. Stage 1 publics you will use heavily:
  `rnumAdd[m,n]` ⊢ realAdd (rnum m) (rnum n) = rnum (m+n); `rnumMul`;
  `rnumLe`/`rnumLt`/`rnumNotLe`/`rnumPos`/`rnumNonneg`;
  `realLeAddMonoRThm`, `realLeAddMono2Thm`, `realLtAddMonoRThm`,
  `realLtLeAddMonoThm`, `realLeLtAddMonoThm`, `realLtAddMono2Thm`,
  `realLtIrreflThm`, `realNotLeLtThm`,
  `realLeMulCancelThm` ⊢ ∀c a b. 0<c ⇒ (realLe (c·a) (c·b) = realLe a b),
  `realLtMulCancelThm` (same for <), `realEqIffLeLeThm`.
  Stage 1 privates (same file, same `` `Private` `` context — directly
  reachable): `natTm`, `rnumTm`, `rAdd`/`rMul`/`rLe`/`rLt`/`rNeg` appliers,
  `groundNat*`, `specAll`, `groundError`, plus whatever Stage 1 defined —
  grep the file, reuse, do not duplicate.
- `auto/Arith.wl` — the ℕ analog: read `parseLin`/`buildLin` (top of file)
  and `linNormConv` for the AST + proof-producing-normalizer pattern you are
  mirroring (theirs is ℕ; yours adds signs, rational coefficients, and
  opaque atoms).
- `stdlib/Real/*.wl` — ordered-field algebra. Exact statements (verified):
  - `realAddCommThm` ⊢ ∀x y. x+y = y+x.
  - `realAddAssocThm` ⊢ ∀x y z. (x+y)+z = x+(y+z).
  - `realAddZeroThm` ⊢ ∀x. x + &ℝ(&ℚ(&ℤ 0)) = x.
  - `realAddNegThm` ⊢ ∀x. x + (−x) = &ℝ(&ℚ(&ℤ 0)).
  - `realNegZeroThm` ⊢ −(&ℝ 0) = &ℝ 0; `realNegNegThm` ⊢ ∀x. −(−x) = x.
  - `realNegAddThm` ⊢ ∀x y. −(x+y) = (−x) + (−y).
  - `realMulCommThm` ⊢ ∀x y. x·y = y·x.
  - `realMulAssocThm` ⊢ ∀x y z. (x·y)·z = x·(y·z).
  - `realMulZeroThm` ⊢ ∀x. x · &ℝ 0 = &ℝ 0.
  - `realMulOneThm` ⊢ ∀x. x · &ℝ(&ℚ(&ℤ(SUC 0))) = x.
  - `realMulNegRightThm` ⊢ ∀x y. x·(−y) = −(x·y);
    `realMulNegLeftThm` ⊢ ∀x y. (−x)·y = −(x·y).
  - `realMulDistribThm` ⊢ ∀x y z. x·(y+z) = x·y + x·z.
  - `realMulInvThm` ⊢ ∀x. ¬(x = &ℝ 0) ⇒ x·(realInv x) = &ℝ(&ℚ(&ℤ(SUC 0))).
  - (The `&ℝ 0` / `&ℝ 1` literals in these ARE `rnumTm[0]` / `rnumTm[1]`.)
- `Terms.wl`: `stripOrigin[t]` removes abs-origin decorations — use
  `stripOrigin` output as the KEY when comparing/sorting opaque atoms
  (α-equivalent atoms must get the SAME key; `aconv` is the equality).
- Kernel/Bool/Equal rules as in brief-005. `HOL`Equal`BETACONV`,
  `HOL`Drule`` conversion combinators exist but you probably need none of
  them — this is a bottom-up recursive builder, not a rewrite system.

## Scope

- Files you may MODIFY: `auto/RealArith.wl` (append Stage 2; you may add
  small private helpers anywhere in the Private section, but do not change
  the meaning of any existing public), `tests/real_arith_tests.wl` (append).
- Do NOT touch the runner load lists (`tests/run_all.wls`,
  `tests/run_all_stable.wls`, `tests/build_snapshot.wls`) — already wired.
- MUST NOT touch: `Kernel.wl`, `Types.wl`, `Terms.wl`, `Bootstrap.wl`,
  `bootstrap.mx`, `CLAUDE.md`, `PLAN.md`, `PROGRESS.md`, anything under
  `codex/` except appending to your own report. No `newAxiom`. No new files.

## Canonical forms (pin these EXACTLY — Stage 3 parses this shape)

An **atom term** ("variable") is any real-typed subterm that the linear
parser cannot decompose: a free `var[…, real]`, `realAbs u`, a `realMul`
of two non-literals, `realInv` of a non-literal, etc. Atom identity/order:
key = `stripOrigin[term]`; equal keys (`===` after stripOrigin, which on
α-canonical mkAbs output coincides with aconv) = same atom; sort by WL
`Order` on keys (any fixed total order is fine; document the one you use).

**Signed canonical form** (output of `realLinNormConv`):
```
realAdd C (realAdd S1 (realAdd S2 (… Sk)))     right-associated
```
- `C` (always present, always first): `rnumTm[c]` with c ≥ 0, or
  `realNeg (rnumTm c)` with c ≥ 1.
- Each `Si`: `realMul (rnumTm ci) xi` or `realNeg (realMul (rnumTm ci) xi)`
  with ci ≥ 1 (zero-coefficient summands eliminated), xi an atom term,
  keys strictly ascending. Coefficient 1 stays explicit: `realMul (rnumTm 1) x`.
- No vars: the form is just `C`.

**Nonneg canonical form**: same, with NO realNeg anywhere (all ci ≥ 1
nat literals, constant `rnumTm c`, c ≥ 0).

**`realLinNormConv[t]`** returns ⊢ t = t-canonical (signed). Contract: every
atom's TOTAL coefficient and the total constant must come out an INTEGER
(rational coefficients may appear inside, e.g. `x/2 + x/2`, as long as the
totals are integers); otherwise throw
`holError["realarith-norm", <literal msg>, <literal assoc>]`. Unsupported
shapes (non-real type, etc.): same tag. REMEMBER holError is HoldRest —
msg/extra must be LITERAL String/Association at the call site (Stage 1
comment in the file explains; this already bit us once).

**`realAtomNormConv[atom]`** for `realLe s t` / `realLt s t` returns
⊢ (s REL t) = (s' REL t') with s', t' BOTH in nonneg canonical form.
Equalities and negated atoms are NOT handled here (Stage 3 intake splits
them first); throw "realarith-norm" on anything but a ≤/< atom.

## Deliverable

### New public lemmas (prove first, they drive the pipeline)

1. `realLeAddCancelThm` ⊢ ∀a b c. realLe (a+c) (b+c) = realLe a b.
   Backward: `realLeAddMonoThm`. Forward: from ASSUME (a+c ≤ b+c),
   `realLeAddMonoThm` with (−c) gives (a+c)+(−c) ≤ (b+c)+(−c); rewrite both
   sides to a, b via realAddAssoc + realAddNeg + realAddZero (build the two
   equations once as a private `addNegCancelEq[x, c]` ⊢ (x+c)+(−c) = x and
   EQMP across the ≤ — to rewrite under realLe use
   MKCOMB[APTERM[realLeConst[], eqL], eqR], the `leCong` idiom from Abs.wl,
   rebuilt locally). DEDUCTANTISYM the two directions, then GEN.
2. `realLtAddCancelThm` ⊢ ∀a b c. realLt (a+c) (b+c) = realLt a b. Same
   shape with realLtAddMonoThm + the same addNegCancelEq + an ltCong.
3. `rnumNe[m, n]` (public ground prover, m ≠ n, both ≥ 0):
   ⊢ ¬(rnumTm m = rnumTm n). Let lo = Min[m,n], hi = Max[m,n]. From
   ASSUME (rnum m = rnum n), EQMP into `realEqIffLeLeThm` instance gives
   rnum hi ≤ rnum lo (CONJUNCT the right one); `rnumLt[lo, hi]` +
   `realLtNotLeThm` gives ¬(rnum hi ≤ rnum lo); NOTELIM + MP ⟹ F; NOTINTRO
   the DISCH. Out-of-domain (m === n): "realarith-ground" throw.
4. Private `rnumDivFold[m, d]` (d ≥ 1, d | m):
   ⊢ realMul (rnumTm m) (realInv (rnumTm d)) = rnumTm (m/d).
   Route: rnumMul[m/d, d] (rnum(m/d) · rnum d = rnum m) so
   LHS = (rnum(m/d)·rnum d)·inv(rnum d)   [APTERM of SYM rnumMul]
       = rnum(m/d)·(rnum d·inv(rnum d))   [realMulAssoc]
       = rnum(m/d)·rnum 1                 [realMulInvThm + MP with rnumNe[d,0]
                                           — note its hypothesis literally is
                                           ¬(x = &ℝ 0) and &ℝ 0 IS rnumTm[0]]
       = rnum(m/d)                        [realMulOneThm].

### Untrusted AST (mirror Arith.wl's record style)

`parseLinR[t]` → `<|"const" -> Rational, "vars" -> <|key -> Rational, …|>|>`
(exact WL Rationals/Integers, never floats), where key = stripOrigin of the
atom term; also keep a lookup key → original term (for rebuilding). Walk:
- `rnumTm[n]` shapes (destructure `&ℝ(&ℚ(&ℤ suc-stack))`) → constant n.
- `realAdd a b` → record sum.
- `realNeg a` → scale −1.
- `realMul a b` where ONE side parses to a pure constant record (no vars)
  → scale the other side by that constant. BOTH sides constant → constant
  product. NEITHER → the whole realMul term is one opaque atom.
- `realInv c`: if c parses to a pure nonzero constant w → constant 1/w;
  otherwise the whole `realInv c` term is an opaque atom.
- anything else real-typed → opaque atom, coefficient 1.
- not real-typed → throw "realarith-norm".
`buildLinR[record]` → the canonical TERM (signed canonical above; works for
the nonneg case automatically when no negative entries). Integer-totals
check lives here: non-integer total → "realarith-norm".

### The conv pipeline

`realLinNormConv[t]`:
compute `rec = parseLinR[t]`, `tgt = buildLinR[rec]`, then PROVE ⊢ t = tgt
bottom-up by structural recursion returning, for every subterm u, a pair
(record, ⊢ u = buildLinR[record]) — i.e. every recursive result is already
in canonical form, and each node only has to JOIN two canonical forms:
- `realAdd a b`: from ⊢ a = A, ⊢ b = B (canonical), prove ⊢ A + B =
  canonical-merge: a private `mergeCanonical[Arec, Brec]` walking the two
  sorted summand lists head-to-head:
  - different keys: pull the smaller head out front (realAddAssoc/
    realAddComm shuffles; derive ONCE a private
    `swapLemma` ⊢ ∀aS bS rS. aS + (bS + rS) = bS + (aS + rS)
    from comm+assoc, plus the 2-element tail case realAddCommThm).
  - equal keys: fold the two summands into one with `foldVarPair`:
    (c·x) + (d·x) with independent signs. Reduce to scalar arithmetic via
    realMulComm (to x·rnum c shape), SYM realMulDistribThm
    (x·rnum c + x·rnum d = x·(rnum c + rnum d)), then fold the scalar sum
    with the SIGNED ground helper below, then realMulComm back; a resulting
    zero coefficient: x·rnum 0 = rnum 0 by realMulZeroThm, then eliminate
    via realAddComm + realAddZeroThm.
  - constants: `rnumAddSigned` (private): the four sign cases —
    (+c)+(+d) = rnumAdd; (+c)+(−d), c ≥ d: insert rnumAdd[c−d, d] backwards,
    realAddAssoc, realAddNegThm, realAddZeroThm → rnum(c−d); c < d:
    realAddComm then symmetric → −(rnum(d−c)); (−c)+(−d): SYM realNegAddThm
    + rnumAdd inside via APTERM on realNegConst → −(rnum(c+d)).
- `realNeg a`: from ⊢ a = A: push realNeg through A with realNegAddThm
  (spine), realNegNegThm (negative summands), realNegZeroThm; constant via
  the sign flip.
- `realMul a b`, constant side w (say from a; use realMulComm to put the
  constant LEFT first): w as a reduced fraction p/q (signs handled by
  realMulNegLeft/Right pulls):
  - scale B's spine: realMulDistribThm distributes over the right-assoc
    sum; each summand (rnum p · inv(rnum q) folded FIRST to a single
    literal when q | p … in general you CANNOT fold p/q alone — instead
    scale each summand: (p/q)·(c·x): realMulAssoc gives ((p/q literal
    expression)·rnum c)·x; the scalar product (p/q)·c is again a rational —
    keep the SCALAR as an unreduced literal-expression and fold it with
    `scalarFold[r_Rational]`: a private prover
    ⊢ <literal expression for r> = canonical scalar where canonical scalar
    is rnumTm[r] for integer r ≥ 0, realNeg(rnumTm[−r]) for integer r < 0,
    and for non-integer r the shape realMul (rnumTm num) (realInv (rnumTm
    den)) (reduced, positive den; sign outside) — with the fold lemmas:
    rnumMul, rnumDivFold, realMulAssoc/Comm, realMulNegLeft/Right,
    realNegNegThm. Document the exact scalar-canonical shape you implement;
    the only HARD requirement is: when the FINAL total coefficient of a
    summand is an integer, the finished summand must be exactly
    `realMul (rnumTm c) x` / `realNeg (realMul (rnumTm c) x)`.
  - w == 0: result is rnum 0 via realMulZeroThm (+ comm), regardless of b.
- `rnumTm[n]` / atom term: base cases (REFL; wrap atom as 0 + 1·x:
  SYM realMulOneThm? NO — 1·x must be realMul (rnumTm 1) x: use
  realMulOneThm at x with realMulComm: x = x·1 = 1·x, then add the zero
  constant: x' = rnum 0 + x' via realAddCommThm + realAddZeroThm SYM).
The recursion produces ⊢ t = buildLinR[parseLinR[t]] by construction;
assert (WL-level) that the final term === tgt and throw "realarith-norm"
(internal-error marked) if not — cheap sanity net.

`realAtomNormConv[atomTm]`:
1. Destructure REL ∈ {realLe, realLt} with sides s, t (else throw).
2. ls = parseLinR[s], lt = parseLinR[t]; M = LCM of denominators of ALL
   coefficients+constants in both records (M ≥ 1, an Integer).
3. If M > 1: th1 = SYM of (specAll[realLe/LtMulCancelThm, {rnumTm M, s, t}]
   MP rnumPos[M]) — ⊢ (s REL t) = (M·s REL M·t). Else skip (REFL chain).
4. From the ×M records (all integer entries now): collect the NEGATIVE
   entries of M·ls and of M·lt; build the balance record N = (negative
   part of M·ls as positives) + (negative part of M·lt as positives);
   B = buildLinR[N]. If N is empty skip; else
   th2 = SYM of specAll[realLe/LtAddCancelThm, {M·s-term, M·t-term, B}] —
   ⊢ (M·s REL M·t) = ((M·s)+B REL (M·t)+B).
5. eqL = realLinNormConv[(M·s)+B], eqR = realLinNormConv[(M·t)+B] (both
   guaranteed nonneg canonical by construction — assert no realNeg in the
   results); th3 = MKCOMB[APTERM[relConst, eqL], eqR].
6. Return TRANS[th1, TRANS[th2, th3]] (with REFLs where steps were skipped).

### Tests (append to `tests/real_arith_tests.wl`, ~25 asserts)

Use distinct var names that cannot collide with internal binders. For each:
check the conv theorem's concl is mkEq[input, expected] via aconv (build
expected with the local builders), and hyp empty.
- `realLinNormConv`: rnum-only sums (2+3); single var x (→ 0 + 1·x);
  x + x (→ 0 + 2·x); y + x (sorting); (rnum 2 · x) + (rnum 3 · x) + rnum 1;
  neg x + x (→ 0, i.e. bare rnum 0 constant); rnum 2 · (x + y);
  neg(x + neg y) (→ 0 + (−1·x… signs!) — wait: −x + y sorts as keys do;
  expected: 0 + (neg(1·x) + 1·y) or per your key order); x/2 + x/2
  (rational intermediates, integer total → 0 + 1·x);
  realAbs z as opaque atom: rnum 2 · realAbs z + realAbs z (→ 0 + 3·|z|);
  throw on x/2 alone (non-integer total) and on a num-typed term.
- `realAtomNormConv`: (x ≤ y) → (0+1·x ≤ 0+1·y); strict version;
  (x + neg y < rnum 3) → (0+1·x < 3+1·y); x/2 ≤ y → (0+1·x ≤ 0+2·y);
  (rnum 2·x + neg(rnum 3·y) ≤ rnum 1 + neg x) → (0+3·x ≤ 1+3·y);
  EQMP round-trip sanity: EQMP[conv result, ASSUME[input]] yields the
  canonical atom with the input as hypothesis.
- New lemmas: realLeAddCancelThm / realLtAddCancelThm instantiated at rnum
  literals + EQMP both directions; rnumNe[2,3] concl; rnumDivFold is
  private — test indirectly through x/2 + x/2 above.

## WL / project pitfalls (these WILL bite you — read twice)

1. **No `_` in any identifier**, including Module locals. camelCase.
2. **WL comments close at the first `*)`** — never write `*)` in prose.
3. **Private-context symbols do not cross files** — but Stage 1 privates in
   THIS file are fine. `HOL`Stdlib`Real`'s privates remain off-limits;
   public `*Const[]`/`*Thm` only.
4. **HOL variable identity is (name string, type)**; internal binders and
   helper variables need distinctive names. The atoms/vars in conv INPUTS
   are caller-supplied — never build internal scaffolding vars named like
   plain `x/y/z`.
5. **holError is HoldRest** — tag/msg/extra must be LITERAL String/String/
   Association AT THE CALL SITE (a variable for msg or payload will NOT
   match and nothing is thrown — Stage 1's groundError comment).
6. **Run scripts as `wolframscript -file foo.wls`** (sandbox: can't anyway).
7. **Tests**: harness asserts + aconv against built expected terms; no deep
   MatchQ patterns.
8. mkVar/mkConst/mkComb/mkAbs only — no raw comb/abs.
9. **Debug with narrow probes**, never whole-term dumps.
10. **No `Return` inside `Do`/`For`/`While`** — use result flags or
    Throw/Catch (this bit brief-002).
11. WL `Rational`/`Integer` exact arithmetic only — never floats; `LCM`,
    `Numerator`, `Denominator` are the tools.
12. Recursion on sorted summand LISTS: WL has no TCO — fine for tens of
    summands, do not engineer for thousands.

## Verification

Sandbox cannot run wolframscript: deliver statically-checked code (balanced
brackets, no `_` idents, every lemma name grep-verified — report file:line).
Reviewer runs `tests/dev.wls auto/RealArith.wl real_arith` then the cold
Strict suite.

## Hard rules

- No `git commit`/branch/push/config. Leave changes in the working tree.
- No files outside Scope; if you think you must, STOP and report.
- **Stop-loss**: same step failing twice for the same reason → STOP, report.
- Minimal diff; no reformatting or renames outside the task.

## Report format (your final message)

1. What changed — per file, line ranges, one-line why.
2. The exact canonical scalar shape you implemented for non-integer
   intermediate coefficients (so the reviewer can extend tests).
3. Name verification table (lemma → file:line).
4. Open questions / uncertainties (empty if none).
