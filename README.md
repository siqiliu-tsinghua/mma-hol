# mma-hol

*[中文版 / Chinese](README.zh-CN.md)*

A kernel-minimal, **LCF-style higher-order logic theorem prover written in the Wolfram
Language**, modeled on [HOL Light](https://github.com/jrh13/hol-light). Its standard library
builds the real numbers from Dedekind cuts and proves a spine of classical real-analysis
theorems — monotone convergence, Cauchy completeness, Bolzano–Weierstrass, Heine–Borel, and
the connectedness characterization of intervals — entirely from a 10-rule trusted kernel,
with **zero `sorry`/axioms beyond the three standard HOL axioms**.

Status: **complete** — the full suite passes `3126/0` (cold, in both encapsulation modes).

---

## What this project is really about

This is, first and foremost, **an experiment in encapsulation.** The motivating question:

> Can the Wolfram Language's `Module` / `Unique` (gensym) machinery be used to build a
> `private`-like trust boundary — the kind C++ or Java give you with access modifiers —
> around a body of code, in a language that has no native notion of private members?

A theorem prover is the ideal stress test for that question, because correctness depends on
exactly one thing: that **no code outside the kernel can fabricate a value of the theorem
type.** If the encapsulation holds, the worst a bug in the (large, untrusted) library or
automation layer can do is *fail to prove a true theorem* — it can never produce a false one.
That is the LCF discipline, and it makes the encapsulation question concrete and falsifiable.

### How the encapsulation works

All mutable kernel state — the theorem constructor `thmTag`, the constant/arity tables, the
axiom and definition registries — lives in the private context `` HOL`Kernel`Private` ``. A single
installer (`defineKernel`) defines the 10 primitive inference rules and the extension API as
closures over those symbols. Outside code is handed only the *public* surface (`REFL`,
`TRANS`, `ABS`, `mkConst`, `newDefinition`, …); it is never given a name it can use to forge
a `thmTag[...]` directly.

### The honest caveat

This is **not** a hard security boundary. The Wolfram Language exposes its symbol table:
``Names["HOL`Kernel`Private`*"]``, `Symbol`, and context enumeration can still *find* the
internal symbols and poke at them at runtime. So a determined caller can reach in.

What the encapsulation buys is **auditability, not enforcement**: well-behaved code *cannot
accidentally* couple to kernel internals (there is no stable public name to grab), so any
breach of the trust boundary must be deliberate and is therefore greppable. It lowers the cost
of auditing a large codebase from "read everything" to "check for the handful of explicit
private-name references." For a learning/research project, that turned out to be the right
and achievable bar.

## Why LCF + HOL Light

The LCF architecture is what makes the encapsulation question *worth* asking. Because the
soundness of the entire system reduces to the integrity of one small kernel, the WL-`Module`
trust boundary has a precise job to do, and "did it work?" has a precise answer. HOL Light is
the canonical minimal LCF prover (10 primitive rules over simply-typed λ-calculus plus three
axioms), so it is the natural blueprint: small enough to re-implement faithfully, expressive
enough to develop real mathematics on top.

A pleasant consequence: the soundness story is **independent of who wrote the untrusted
layers.** The library and automation in this repo were developed with heavy AI assistance
(see [Provenance](#provenance)); that does not weaken the correctness guarantee one bit,
because every theorem is still rechecked by the same 10 kernel rules.

## Two encapsulation modes: Strict and Stable

The kernel ships in two modes, selected by `` Global`$HOLEncapsulationMode` ``:

| | **Strict** (default, CI) | **Stable** (dev / persistence) |
|---|---|---|
| Kernel state symbols | `Module`-local gensyms (`thmTag$4271`, …) — no stable name | fixed names (``HOL`Kernel`Private`thmTag``) |
| Boundary | enforced by construction — outside code has no name to reference | convention + a CI lint that flags any ``HOL`Kernel`Private`*`` reference outside `Kernel.wl` |
| `DumpSave` snapshot survives a cold restart? | no (gensyms are not stable across serialization) | **yes** |
| Used for | the authoritative correctness gate; the actual encapsulation demonstration | the `bootstrap.mx` snapshot + the fast dev loop |

The two modes share **one** `Kernel.wl` body through the `defineKernel` installer, and CI runs
the full test suite in both — so they can never silently diverge. The trade-off is exactly the
one the experiment is about: Strict gives you real, unnameable privacy but cannot be
serialized; Stable gives you a fast restorable snapshot at the cost of downgrading the boundary
to a linted convention.

## The standard library

The number tower is built bottom-up and entirely inside the kernel: `Pair`, `Sum`, `Option`,
`Set`, `Num` (ℕ from an infinity axiom), `List`, `Finite`, `Int` (ℤ as a Grothendieck
quotient), `Rat` (ℚ as reduced fractions), and `Real`.

**ℝ is constructed via Dedekind cuts** — a single lower set `L : ℚ → bool` — rather than HOL
Light's Cauchy/"nearly-additive function" construction. This is a deliberate, beginner-friendly
choice: the Dedekind construction is the one in most analysis textbooks, the cut *is* the real
number (kernel equality is real equality, no setoid quotient), and the order is literally set
inclusion. ℝ is then proven to be a complete ordered field, and a small linear-arithmetic
decision procedure (`REAL_ARITH`, a Fourier–Motzkin oracle with a Farkas-certificate kernel
verifier) is built on top.

The analysis spine in `stdlib/Real/` (all proofs via the supremum principle — no Lindelöf or
countability machinery):

- **Sequences** (`Seq`): `tendsto` with a real ε, the limit calculus, the monotone convergence
  theorem, subsequences, and **Cauchy completeness**.
- **Compactness** (`Compact`, `CompactSet`): **Bolzano–Weierstrass**; closed-interval
  **Heine–Borel** (via "the set of partially-coverable points has a supremum = the right
  endpoint"); and, for general real sets, the open-cover predicate `isCompact` with the full
  equivalence **`isCompact ⟺ isClosed ∧ setBounded ⟺ isSequentiallyCompact`**.
- **Connectedness** (`Connected`): **connected ⟺ interval** — the order-topological heart of
  the intermediate value theorem. (The library stops at point-set topology: there is no
  continuous-function layer, so the *function-form* IVT, `f(a)<0<f(b) ⇒ ∃c. f(c)=0`, is out
  of scope — but the [`demos/`](demos/) folder builds exactly that layer as a showcase and
  derives the function-form IVT and the extreme value theorem from it.)
- **Topology** (`Topology`): open/closed sets, complements, relative (subspace) closedness.

Interested readers can follow these routes directly in the source — each file is one
dependency-ordered closure of definitions and lemmas with explicit exports. A couple of the
HOL-specific design notes worth highlighting:

- **Open covers without dependent index types.** HOL has no `∀{ι : Type}` quantifier, so a
  cover cannot be a family `U : ι → Set ℝ`. Instead a cover is encoded as a *set of open sets*
  `C : (ℝ → bool) → bool`, and the polymorphic closed-interval compactness theorem is reused by
  instantiating its index type at `ℝ → bool` through a "clamp" family `λV. if C V then V else ∅`.
- **Real multiplication** is defined by a binary sign split (`COND` on `0 ≤ x` / `0 ≤ y`) over a
  non-negative core, which keeps the associativity/distributivity case analysis manageable
  (8 cases, not the 27 a naive zero/positive/negative ternary split produces).

## Repository layout

```
Types.wl Terms.wl Kernel.wl Bootstrap.wl   — the term/type layer + the trusted kernel
Bool.wl Equal.wl Drule.wl Tactics.wl       — derived rules, conversions, the tactic engine
Parser.wl Printer.wl                       — string ⇄ term (no ToExpression; boundary intact)
auto/                                      — MESON, SIMP, SET, ARITH, REAL_ARITH
stdlib/                                    — Pair, Sum, Option, Set, Num, List, Finite, FTA, Int, Rat
stdlib/Real/                               — the ℝ construction + the analysis spine
tests/                                     — runners + per-module *_tests.wl
docs/dev/                                  — design doc (PLAN.md), proof history (PROGRESS.md), dev notes
```

## Running it

Requires `wolframscript` (Wolfram Engine / Mathematica 14.x).

```bash
# Authoritative cold check (Strict mode, ~10–15 min): every file loaded from source.
wolframscript -file tests/run_all.wls

# Fast subset (Stable mode, ~3 s): restores the bootstrap.mx snapshot.
wolframscript -file tests/run_fast.wls real

# Rebuild the snapshot after changing a core file (~10 min).
wolframscript -file tests/build_snapshot.wls
```

Two interactive notebooks in [`demos/`](demos/) let you explore the prover by hand
(double-click to open in Mathematica / the free Wolfram Player): `examples.nb` is a guided
tour of the kernel, the automation, and the marquee library theorems; `continuous.nb` builds
a small continuous-function layer on top of the topology and derives boundedness, the extreme
value theorem, and the function-form intermediate value theorem on a closed interval. See
[`demos/README.md`](demos/README.md) for details, and [`docs/USER_GUIDE.md`](docs/USER_GUIDE.md)
for the API and how to develop your own proofs.

## Provenance

This project was **developed end-to-end by Claude Opus** (Anthropic) in an agentic workflow.
In the later real-analysis stages the proof *routes* were guided by a private, not-yet-released
Lean 4 project (`tautology`, a 0-`sorry` re-development of the same real-analysis tower), and a
portion of the translation from those blueprints into Wolfram Language proofs was delegated to
OpenAI's Codex CLI under a "write the spec here, verify every result against the kernel here"
discipline. As noted above, the AI authorship of the untrusted layers does not affect
soundness — every theorem is rechecked by the kernel.

## License

[MIT](LICENSE) — do essentially anything with it, just keep the copyright notice. A
[`CITATION.cff`](CITATION.cff) is provided if you would like to cite the project, and
[`CONTRIBUTING.md`](CONTRIBUTING.md) describes the one rule that matters (don't breach the
kernel trust boundary).
