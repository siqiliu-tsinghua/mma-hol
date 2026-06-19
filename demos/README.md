# Demos

Runnable, kernel-checked examples of the prover. Everything here is a *showcase* — it
is **not** part of the trusted kernel or the standard library, but every theorem it
displays is still built and rechecked by the same 10 primitive rules.

Open a `.nb` in Mathematica / the free [Wolfram Player](https://www.wolfram.com/player/)
(double-click) and evaluate the cells top to bottom with **Shift+Enter**. The first cell
loads the prebuilt snapshot `bootstrap.mx` from the repo root; if it is missing, run
`wolframscript -file tests/build_snapshot.wls` there first.

| File | What it shows |
|---|---|
| `examples.nb` | A guided tour: the trusted kernel (`⊢ T`), propositional automation (`propTaut`), a tactic proof built live, the marquee standard-library theorems (Dedekind completeness, Bolzano–Weierstrass, Heine–Borel, connected ⟺ interval), `REAL_ARITH` proving the midpoint inequality automatically — and the same prover *refusing* a false statement. |
| `continuous.nb` | **Continuous functions on a closed interval.** A small layer that is deliberately *outside* the real-number theory (it is the next chapter in a typical analysis course): a continuous map is defined topologically (`continuous f ⇔ the preimage of every open set is open`), and from the point-set topology already in the library we derive that a continuous image of a compact set is compact and of a connected set is connected — hence on `[a,b]` a continuous function is **bounded**, **attains its maximum** (the extreme value theorem), and **hits every intermediate value** (the function-form IVT). |

## How they are built

Each `.nb` is committed, but it is *generated* from a plain script so the example code
can be reviewed and re-verified as ordinary source:

```bash
wolframscript -file demos/build_examples_nb.wls      # regenerates examples.nb
wolframscript -file demos/build_continuous_nb.wls    # regenerates continuous.nb
```

The continuity development itself lives in `demos/Continuous.wl` — a package loaded *on top
of* the snapshot. To iterate on it, restore `bootstrap.mx` and `Get` the file directly
(the same pattern the generator's first cell uses). It is not part of the test suite.

For the API and how to develop your own proofs, see [`../docs/USER_GUIDE.md`](../docs/USER_GUIDE.md).
