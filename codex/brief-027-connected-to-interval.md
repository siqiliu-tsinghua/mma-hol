# Brief 027 — M8.3 Connectedness: connected ⇒ interval (append to Real/Connected.wl)

## Goal

Append the FIRST hard direction to `stdlib/Real/Connected.wl`: a connected subset
of ℝ is an interval set. Two new pieces: the subspace `trace` set
(`trace S V = λx. S x ∧ V x`) with `openInTraceThm` (the trace of an open set is
open-in S), then the capstone **`intervalSetOfConnectedThm`** ⊢ ∀S. isConnected S
⇒ isIntervalSet S, proven by contradiction (if some between-point y∉S, split S by
the two open rays around y into a separation, contradicting connectedness).
Append ~4 asserts to `tests/real_connected_tests.wl`. Self-verify with dev.wls,
iterate to green; graded delivery. (The OTHER direction interval ⇒ connected / IVT
is brief-028 — NOT in scope here.)

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealConnectedness/Connected.lean` `intervalSet_of_connected`
(lines 183–238); the trace helper is `RealTopology/Subspace.lean` `Trace` (line 49)
+ `openIn_trace` (line 95). Read those. The proof is plain predicates + the brief-026
order lemmas — no records.

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- Connected.wl is FRONTIER (committed brief-026, NOT in bootstrap.mx). dev loop:
  `wolframscript -file tests/dev.wls stdlib/Real/Connected.wl real_connected`
  (SeqAux/Compact are graduated — do NOT name them). Append to the END of
  Connected.wl (before `End[]; EndPackage[]`) + `::usage` lines in its usage block.
- **Available in Connected.wl itself (brief-026, this file — reachable by bare name):**
  `openInDefThm`/`openInConst`/`openInTm[S,U]`/`unfoldOpenIn[S,U]`; `openInSubsetThm`;
  `setNonemptyDefThm`/`Tm`/`unfold`; `setDisjointDefThm`/…; `coversByTwoDefThm`/…;
  `isSeparationDefThm`/`isSeparationTm[S,U,V]`/`unfoldIsSeparation`; `isConnectedDefThm`/
  `unfoldIsConnected`; `betweenDefThm`/`betweenTm[x,y,z]`/`unfoldBetween`;
  `isIntervalSetDefThm`/`isIntervalSetTm[S]`/`unfoldIsIntervalSet`;
  `openLowerRayDefThm`/`openLowerRayConst`/`openLowerRayTm[cut]`/`unfoldOpenLowerRay`
  (+ openUpperRay); `openLowerRayIsOpenThm`/`openUpperRayIsOpenThm`; `ltOrGtOfNeThm`
  (⊢ ∀x y. ¬(x=y) ⇒ realLt x y ∨ realLt y x). **GREP Connected.wl to confirm the
  EXACT exported names/arities before use** (brief-026 chose them; match precisely).
- **Snapshot (VERIFIED):** `isOpenConst[]`/`isOpenTm`/`unfoldIsOpen` (Compact);
  `realLeAntisymThm` (⊢ ∀x y. realLe x y ⇒ realLe y x ⇒ x=y), `realLtNotLeThm`
  (⊢ ∀x y. realLt x y = ¬(realLe y x)), `realNotLeLtThm` (⊢ ∀x y. ¬(realLe x y) =
  realLt y x), `realLtTransThm`; `HOL`Auto`RealArith`realArithProve` (LINEAR; proves
  `¬(realLt t y ∧ realLt y t)` and the like). Bool: EXCLUDEDMIDDLE/DISJCASES/CHOOSE/
  EXISTS/CONJ/CONJUNCT1/2/CONTR/CCONTR/NOTINTRO/SPEC/GEN/MP/DISCH/ASSUME; PropTaut
  `propTaut` (public). A set is `real→bool`; `S x` = `mkComb[S,x]`; bool iff = `=`.

## Scope

- MODIFY: `stdlib/Real/Connected.wl` (append + `::usage`),
  `tests/real_connected_tests.wl` (append). No other files, NO runner lists. MUST
  NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/docs/
  codex(except report). No newAxiom, no new files.

## Definitions (pin)

```
traceDefThm: ⊢ trace = (λS V. (λx. (S x) ∧ (V x)))
```
Export `traceConst[]`/`traceTm[S,V]` (= the set `λx. S x ∧ V x`)/`unfoldTrace[S,V]`
(+ a `traceMemThm`-style applied form `∀S V x. (trace S V) x = (S x ∧ V x)` — the
β-reduced membership, since you need it at points). `trace : (real→bool)→(real→bool)
→(real→bool)`. Confirm `trace` is FREE (grep `::usage`).

## Deliverable theorems

1. `openInTraceThm` ⊢ ∀S V. isOpen V ⇒ openIn S (trace S V).
   (unfold openIn at (S, trace S V): need ∃W. isOpen W ∧ ∀x. (trace S V) x = (S x ∧ W x).
   Witness W := V (the SAME open set). isOpen V = hyp. ∀x. (trace S V) x = (S x ∧ V x):
   from traceMemThm. EXISTS W:=V. Fold back via SYM unfoldOpenIn. GEN S V, DISCH.)

2. `intervalSetOfConnectedThm` ⊢ ∀S. isConnected S ⇒ isIntervalSet S.
   Module sketch (mirror the blueprint, distinctive binders `xCn yCn zCn tCn` and
   the separation sets `uSet`/`vSet`):
   - unfold isIntervalSet; GEN S; DISCH `isConnected S` (hConn); GEN x y z; DISCH
     `S x` (hx), `S z` (hz), `between x y z` (hBetw). hBetw via unfoldBetween →
     `realLe x y ∧ realLe y z`; CONJUNCT → hxy (x≤y), hyz (y≤z).
   - EXCLUDEDMIDDLE on `S y` (the term `mkComb[S, y]`): DISJCASES.
     - TRUE branch (ASSUME `S y`): that IS the goal `S y`.
     - FALSE branch (hNotSy = ASSUME `¬(S y)`):
       - `x≠y`: NOTINTRO — assume x=y, EQMP into hx gives S y, contra hNotSy. (or:
         from x=y rewrite hx:S x to S y.) Similarly `y≠z`.
       - `¬(realLe y x)`: NOTINTRO assume y≤x; `realLeAntisymThm` MP hxy MP (y≤x) →
         x=y, contra `x≠y`. ⇒ `x<y` via `realLtNotLeThm` SPEC (x,y) (= realLt x y =
         ¬(realLe y x)) EQMP-backward on the `¬(y≤x)`. Symmetric: `¬(realLe z y)` →
         `y<z` via realLtNotLeThm SPEC (y,z) on `¬(z≤y)` (antisym hyz + z≤y → y=z, contra).
       - `uSet := traceTm[S, openLowerRayTm[y]]` (= λt. S t ∧ t<y);
         `vSet := traceTm[S, openUpperRayTm[y]]` (= λt. S t ∧ y<t).
       - Build `isSeparation S uSet vSet` (assemble the 6-conjunction, fold via SYM
         unfoldIsSeparation):
         · openIn S uSet = `openInTraceThm` SPEC (S, openLowerRay y) MP
           (`openLowerRayIsOpenThm` SPEC y). openIn S vSet similarly (openUpperRay).
         · setNonempty uSet = EXISTS xCn:=x of `uSet x` = `(S x ∧ x<y)`: CONJ hx
           (x<y from openLowerRay unfold at x + the `x<y` fact); use traceMemThm SYM to
           fold `S x ∧ x<y` into `uSet x`. setNonempty vSet: witness z, `S z ∧ y<z`.
         · coversByTwo S uSet vSet = ∀t. (S t) = ((uSet t) ∨ (vSet t)). For each t,
           prove the bool eq by propTaut-style or DEDUCTANTISYM of the two implications:
           (→) hSt:S t; `t≠y` (t=y ⇒ S y contra); `ltOrGtOfNeThm` SPEC (t,y) MP (t≠y) →
           t<y ∨ y<t; DISJCASES → uSet t (CONJ hSt (t<y), fold) or vSet t. (←) uSet t ∨
           vSet t → S t: each side's CONJUNCT1 (via traceMem) is S t. Combine the two
           implications into the bool equation (use the `=`-from-iff idiom: build
           `(S t) = (uSet t ∨ vSet t)` — easiest via propTaut once you have both
           directions as theorems, or `IMP_ANTISYM`-style; grep Bool for the
           iff↔eq rule, e.g. `EQ_IMP`/deductAntisym).
         · setDisjoint uSet vSet = ∀t. ¬(uSet t ∧ vSet t): assume uSet t ∧ vSet t;
           traceMem gives t<y (from uSet t) and y<t (from vSet t); `realArithProve`
           `¬(realLt t y ∧ realLt y t)` (linear) applied, OR realLtTransThm → t<t then
           realLtIrrefl. NOTINTRO.
       - `hConn` SPEC uSet, SPEC vSet, MP the separation → `F`; `CONTR[mkComb[S,y], that]`
         → `S y`. (FALSE branch concludes `S y`.)
     - DISJCASES[em, trueBranch (ASSUME S y), falseBranch] → `S y`.
   - GEN/DISCH wrap to the full statement.

## Stop-loss / graded delivery

Tier 1 (must): `trace` def + builders + `traceMemThm` + `openInTraceThm`. Tier 2:
`intervalSetOfConnectedThm`. If Tier 2 stalls (same failure twice), deliver Tier 1
green + STOP with a precise report (which sub-goal, exact thrown payload). The
hardest sub-parts are the coversByTwo bool-equation assembly and the
setDisjoint/`¬(t<y ∧ y<t)` — if one fights you, report exactly where. A loadable
subset (Tier 1 + the def) is acceptable.

## Tests (append ~4 asserts)

- `openInTraceThm` concl shape; `intervalSetOfConnectedThm` concl shape
  (`isConnected S ⇒ isIntervalSet S` at a fresh set var, aconv on built expected,
  empty hyps after DISCH). `traceMemThm` body shape. aconv against builders; no
  deep MatchQ. **NO `testExit[]`.**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. **Public-symbol shadow** —
`trace` must be FREE (grep `::usage`); reuse brief-026/Compact publics, don't
redefine `openIn`/`isOpen`/`openLowerRay`. A bare `foo=…` resolving to an imported
symbol overwrites it ([[wl-public-symbol-shadow-collision]]). 4. HOL var identity=
(name,type): distinctive binders (`tCn`, `uSet`, `vSet`); the FALSE-branch witnesses
must not collide. 5. holError HoldRest. 6. dev.wls verifier (below). 7. aconv tests,
no deep MatchQ, no testExit. 8. mkVar/mkConst/mkComb/mkAbs only. 9. **Narrow probes**
— localize a load throw by per-theorem isThm, don't dump terms. 10. No Return in
Do/For/While. 11. realArithProve is LINEAR — the disjoint `¬(t<y ∧ y<t)` only; the
≤/< reshuffles use realLeAntisym/realLtNotLe; the bool reshapes use propTaut. 12. A
set is `real→bool`; `S t` = `mkComb[S,t]`; iff = kernel `=`. 13. β: `(trace S V) t`
and `(openLowerRay y) t` are redexes — reduce with traceMem/unfoldOpenLowerRay (or
`compactBetaClean`-style DEPTHCONV BETACONV) so terms aconv-match (this kind of
β-redex-vs-normal mismatch broke a CHOOSE in brief-024 — keep ∃-bodies β-normal).

## Verification (MANDATORY — you run wolframscript)

Full machine access. ONE frontier file:

```
wolframscript -file tests/dev.wls stdlib/Real/Connected.wl real_connected
```

Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste the
final `passed: N  failed: 0` line VERBATIM. Do NOT run build_snapshot/
extend_snapshot, do NOT modify bootstrap.mx, do NOT run run_all, no other command,
nothing outside the repo, no network. Same failure twice → deliver the loadable
subset + report. If dev.wls reports a stale snapshot for some OTHER file, STOP and
report.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls
  command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did
  not reach it, say so explicitly and report where it stopped — do NOT claim green
  without the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused symbol → file:line; `trace` confirmed free).
3. How you assembled the coversByTwo bool equation and discharged setDisjoint.
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped.
6. Open questions (empty if none).
