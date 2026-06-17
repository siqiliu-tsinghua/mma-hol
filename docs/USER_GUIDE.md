# mma-hol — User Guide

A practical guide to loading the prover, proving your own theorems, and finding your way
around the library. For the project's motivation and design, see the
[README](../README.md); for architecture and proof history, see
[`docs/dev/PLAN.md`](dev/PLAN.md).

> **Conventions.** Public API symbols live in `HOL`*` contexts (`HOL`Terms``, `HOL`Kernel``,
> `HOL`Bool``, `HOL`Stdlib`Real``, …). After loading (below) those contexts are on
> `$ContextPath`, so you can use short names (`mkVar`, `prove`, `formatThm`). Kernel internals
> live in `HOL`Kernel`Private`` and are deliberately out of reach — see the README on
> encapsulation.

---

## 1. Loading the library

The fastest way is to restore the prebuilt snapshot `bootstrap.mx` (Stable mode). In a
notebook or a `wolframscript` session, from the repository root:

```wolfram
$HOLEncapsulationMode = "Stable";          (* set BEFORE loading the snapshot *)
Get["bootstrap.mx"];

(* DumpSave does not restore $ContextPath; re-add the public HOL contexts: *)
$ContextPath = Join[
  Select[Contexts[], StringMatchQ[#, "HOL`*"] && ! StringContainsQ[#, "Private`"] &],
  $ContextPath];
```

If `bootstrap.mx` is missing or stale, rebuild it (≈10 min):

```bash
wolframscript -file tests/build_snapshot.wls
```

The double-click notebook `demos/examples.nb` does this load in its first cell. For a
*from-source* load (no snapshot) see `tests/run_all.wls`, which `Get`s every `.wl` file in
dependency order — slower (~10–15 min) but it is the authoritative Strict-mode build.

## 2. Your first theorem

A theorem is a value of an opaque type that *only the kernel can construct*. You obtain one
either by applying inference rules directly, or by running a tactic. `formatThm` renders it.

```wolfram
formatThm[TRUTH]                                   (* ⊢ T *)
```

### Parsing terms

`parseTerm` turns a string into a typed term (Hindley–Milner inference). ASCII operators:
`==>` (⇒), `/\` (∧), `\/` (∨), `~` (¬), `!` (∀), `?` (∃), `=`, `@` (Hilbert choice),
`\x. body` (λ).

```wolfram
parseTerm["!x. x = x"]
parseTerm["p /\ q ==> p"]
```

### Proving with automation

```wolfram
formatThm[propTaut[parseTerm["p ==> p"]]]          (* ⊢ p ⇒ p *)
formatThm[propTaut[parseTerm["p \/ ~p"]]]          (* ⊢ p ∨ ¬p *)
```

`propTaut` decides propositional tautologies. Other decision procedures (all returning
kernel-checked theorems): `MESON[lemmas]` (first-order), `SIMP[eqs]` / `asmSimp[eqs]`
(rewriting), `SET[]` (finite set algebra), `arithProve` (linear ℕ), `realArithProve` (linear ℝ).

### Proving with tactics

`prove[goalTerm, tactic]` applies a tactic to the goal `⊢ goalTerm` and returns the theorem,
or throws if subgoals remain.

```wolfram
formatThm[prove[parseTerm["T"], acceptTac[TRUTH]]]
```

Tactics compose with the combinators `THEN`, `THENL`, `ORELSE`, `REPEAT`, `TRY`. Basic
tactics include `genTac`, `conjTac`, `dischTac`, `existsTac`, `rewriteTac[eqs]`,
`acceptTac[thm]`, and the automation tactics `MESON`, `SIMP`, `REALARITH`. A worked
multi-step example (proving `p ∧ q` from the assumption `p ∧ q`):

```wolfram
With[{pq = parseTerm["p /\ q"]},
  formatThm @ prove[pq,
    THENL[conjTac, {
      acceptTac[CONJUNCT1[ASSUME[pq]]],
      acceptTac[CONJUNCT2[ASSUME[pq]]]}]]]
```

## 3. The trusted kernel

Everything reduces to ten primitive rules over simply-typed λ-calculus:

`REFL` · `TRANS` · `MKCOMB` · `ABS` · `BETA` · `ASSUME` · `EQMP` · `DEDUCTANTISYM` · `INST` ·
`INSTTYPE`

plus the term/type constructors `mkType`, `mkConst`, `mkEq` and the definition/axiom
extension API (`newConstant`, `newDefinition`, `newBasicTypeDefinition`; `newAxiom` is
withdrawn after the three standard axioms — η, choice, infinity — are installed). Accessors:
`concl[th]`, `hyp[th]`, `isThm[th]`.

Terms are built with `mkVar[name, ty]`, `mkConst[name, ty]`, `mkComb[f, x]`, `mkAbs[v, body]`
(these type-check and α-normalize; raw `comb`/`abs` are kernel-internal). Types: `mkVarType`,
`tyFun`, `mkType`. α-equivalence is `aconv` (not `===`).

Derived rules and conversions sit just above the kernel: `SYM`, `BETACONV`, `GEN`/`SPEC`,
`CONJ`/`CONJUNCT1`/`CONJUNCT2`, `MP`/`DISCH`, `EXISTS`/`CHOOSE`, `EXCLUDEDMIDDLE`, the
conversion combinators (`DEPTHCONV`, `THENC`, `REWRCONV`), etc.

## 4. The standard library

Loaded modules and what they provide (each module's exports carry `::usage` strings —
evaluate e.g. `?HOL`Stdlib`Real`dedekindCompleteThm`):

| Module | Contents |
|---|---|
| `Pair` `Sum` `Option` `Set` | products, sums, options, sets-as-predicates |
| `Num` | ℕ from the infinity axiom: Peano, `+ * ^`, `≤ <`, induction, division |
| `List` `Finite` | finite lists; the `FINITE` predicate, `CARD` |
| `FTA` | gcd / primes / unique factorization |
| `Int` `Rat` | ℤ (ordered integral domain), ℚ (densely ordered field) |
| `Real` | ℝ via Dedekind cuts — a **complete ordered field** |

The real-analysis spine (all in `stdlib/Real/`, names you can display with `formatThm`):

```wolfram
formatThm[HOL`Stdlib`Real`dedekindCompleteThm]            (* least upper bound property *)
formatThm[HOL`Stdlib`Real`bwSequentialThm]                (* Bolzano–Weierstrass *)
formatThm[HOL`Stdlib`Real`compactnessPrincipleThm]        (* Heine–Borel, closed interval *)
formatThm[HOL`Stdlib`Real`compactIffSequentialCompactThm] (* compact ⟺ seq. compact *)
formatThm[HOL`Stdlib`Real`connectedIffIntervalSetThm]     (* connected ⟺ interval *)
```

Other capstones: `monoConvergesIncThm` (monotone convergence), `cauchyConvergesThm` (Cauchy
completeness), `compactIffClosedBoundedThm` (Heine–Borel for general sets), and the
intermediate value theorem among the `connected*` corollaries.

## 5. Developing your own proofs

If you are adding to the library:

- **Write a file** `stdlib/MyThing.wl` as a `BeginPackage["HOL`Stdlib`MyThing`", {imports}]` /
  `EndPackage[]` package; export theorems with `::usage` strings; keep helpers in the
  `` `Private` `` subcontext.
- **Iterate fast**: keep the new file *out* of `tests/build_snapshot.wls`'s load list and use
  ```bash
  wolframscript -file tests/dev.wls stdlib/MyThing.wl mytest
  ```
  which restores the snapshot, loads only your file on top, and runs `tests/*mytest*_tests.wl`
  (≈0.1 s per iteration).
- **Graduate** a finished file: add it to the load lists in `run_all.wls`,
  `run_all_stable.wls`, and `build_snapshot.wls`, then rebuild the snapshot.
- **Gate**: the authoritative check is the cold Strict run `wolframscript -file
  tests/run_all.wls` (and `run_all_stable.wls` for the Stable mode). A green run must show
  `passed: N  failed: 0` with `N` ≥ the previous baseline + your new assertions.

The existing `tests/*_tests.wl` files are the best worked examples of every API — read the
one next to the module you are using.

## 6. The two encapsulation modes (recap)

- **Strict** (default) — kernel state symbols are `Module` gensyms with no stable name; the
  trust boundary is enforced by construction. Cannot be serialized, so it is used for the
  authoritative `run_all` gate, not for the snapshot.
- **Stable** — kernel state symbols have fixed names so `bootstrap.mx` survives a cold
  restart; the boundary is held by convention + a CI lint. Use this for the fast dev loop and
  for the `Get["bootstrap.mx"]` load above.

Set `$HOLEncapsulationMode` **before** the kernel loads. See the [README](../README.md#two-encapsulation-modes-strict-and-stable)
for the full trade-off.
