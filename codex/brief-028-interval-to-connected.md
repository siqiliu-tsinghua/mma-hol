# Brief 028 — M8.3 Connectedness capstone: interval ⇒ connected + IVT (append to Real/Connected.wl)

## Goal

Append the SECOND (hard) direction + the equivalence + corollaries to
`stdlib/Real/Connected.wl`, finishing M8.3:
- `notSeparationOfIntervalOrderedPointsThm` — the sup-based core: an interval set
  with a separation (S,U,V), a∈U, b∈V, a<b is impossible;
- `connectedOfIntervalSetThm` ⊢ ∀S. isIntervalSet S ⇒ isConnected S;
- `connectedIffIntervalSetThm` ⊢ ∀S. isConnected S = isIntervalSet S;
- the `connected_*` corollaries (universal / singleton / open+closed interval /
  four rays), each = connectedOfIntervalSet applied to the brief-026 intervalSet_*.
This is the IVT capstone (connected ⟺ interval). Append ~6 asserts to
`tests/real_connected_tests.wl`. Self-verify with dev.wls; graded delivery.

## Blueprint (in-repo — mirror 1:1)

`tautology-ref/Tautology/RealConnectedness/Connected.lean`:
`not_separation_of_interval_ordered_points` (334–446), `connected_of_intervalSet`
(448–470), `connected_iff_intervalSet` (472–478), `connected_*` (480–520). Read
those. The abstract `C.exists_lub`/`le_lub_of_mem`/`lub_le_of_upper`/
`exists_lt_of_lt_lub` map onto OUR `realSup` API (below).

## Context pointers

- `CLAUDE.md` (Conventions + capture hygiene) first.
- Connected.wl FRONTIER; dev loop `wolframscript -file tests/dev.wls
  stdlib/Real/Connected.wl real_connected`. Append before `End[]; EndPackage[]`
  + `::usage` lines.
- **In Connected.wl (briefs 026/027 — reachable):** `openInSubsetThm`
  (⊢ ∀S U. openIn S U ⇒ ∀x. U x ⇒ S x), `unfoldOpenIn[S,U]` (⊢ openIn S U =
  ∃V. isOpen V ∧ ∀x. U x = (S x ∧ V x)), `unfoldIsSeparation[S,U,V]`,
  `unfoldIsConnected[S]`, `unfoldCoversByTwo`/`unfoldSetNonempty`/`unfoldSetDisjoint`,
  `isIntervalSetTm`/`unfoldIsIntervalSet[S]` (⊢ = ∀x y z. S x ⇒ S z ⇒ between x y z ⇒ S y),
  `betweenTm[x,y,z]`/`unfoldBetween`, `isConnectedTm`/`isSeparationTm`,
  `intervalSetOfConnectedThm` (brief-027), `existsRightBetweenThm`
  (⊢ ∀x y z. x<y ⇒ x<z ⇒ ∃d. x<d ∧ d≤y ∧ d<z), `ltOrGtOfNeThm`, `isSeparationSymmThm`,
  the `intervalSet{Universal,Singleton,OpenInterval,ClosedInterval,OpenLowerRay,
  OpenUpperRay,ClosedLowerRay,ClosedUpperRay}Thm`. Helpers: `connectedSpecAll[th,{…}]`,
  `connectedSetApp[S,x]`(= S x), `connectedConjTm`/`connectedDisjTm`,
  `connectedAndConst[]`, `connectedRealTy`/`connectedSetTy`,
  `connectedOpenLowerSet`/`OpenUpperSet`/the universal/singleton/interval set
  builders (grep — brief-026 named them e.g. `universalSet`/`singletonSet`/
  `openIntervalSet…`; CONFIRM by grep). `openIntervalMemThm`/`unfoldOpenInterval`,
  `isOpenTm`/`unfoldIsOpen` (from Compact).
- **OUR realSup API (snapshot, Complete.wl — VERIFIED):**
  - `realSupTm[A]` (= realSup A), `realSupConst[]`.
  - `realSupUpperThm` ⊢ ∀S. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒ ∀a. S a ⇒
    realLe a (realSup S). [= le_lub_of_mem: members ≤ sup]
  - `realSupLeastThm` ⊢ ∀S v. (∃a. S a) ⇒ (∃u. ∀a. S a ⇒ realLe a u) ⇒
    (∀a. S a ⇒ realLe a v) ⇒ realLe (realSup S) v. [= lub_le_of_upper: sup ≤ any UB]
  - `realLeReflThm`, `realLeTransThm`, `realLeAntisymThm`, `realLtImpLeThm`,
    `realLeLtTransThm`, `realLtLeTransThm`, `realLtTransThm`, `realLtIrreflThm`
    (⊢ ∀x. ¬(realLt x x)), `realLtNotLeThm` (⊢ ∀x y. realLt x y = ¬(realLe y x)),
    `realNotLeLtThm` (⊢ ∀x y. ¬(realLe x y) = realLt y x). `realLeTm`/`realLtTm`.
  - Bool/Equal/Kernel: EXCLUDEDMIDDLE/DISJCASES/CHOOSE/EXISTS/CONJ/CONJUNCT1/2/
    DISJ1[thp,q]/DISJ2[thq,p]/CONTR/CCONTR/NOTINTRO/NOTELIM/SPEC/GEN/MP/DISCH/ASSUME/
    DEDUCTANTISYM/MKCOMB/APTERM/EQMP/TRANS/REFL/SYM/BETACONV.

## Scope

- MODIFY: `stdlib/Real/Connected.wl` (append + `::usage`),
  `tests/real_connected_tests.wl` (append). No other files, NO runner lists. MUST
  NOT touch Kernel/Types/Terms/Bootstrap/bootstrap.mx/Compact/Seq/SeqAux/docs/
  codex(except report). No newAxiom, no new files.

## Deliverable theorems

### 1. `notSeparationOfIntervalOrderedPointsThm`
⊢ ∀S U V a b. isIntervalSet S ⇒ isSeparation S U V ⇒ U a ⇒ V b ⇒ realLt a b ⇒ F.
(Hyps as DISCHes; conclusion F.) Module sketch — mirror the blueprint:
- From `unfoldIsSeparation` on (isSeparation S U V) get the 6 conjuncts: hOpU
  (openIn S U), hOpV (openIn S V), hNeU, hNeV, hCov (coversByTwo S U V = ∀t. S t =
  (U t ∨ V t)), hDisj (setDisjoint U V = ∀t. ¬(U t ∧ V t)).
- haS = openInSubsetThm S U hOpU SPEC a MP (U a) → S a; hbS similarly → S b.
- **A := `λtA. (S tA) ∧ ((realLe a tA) ∧ ((realLe tA b) ∧ (U tA)))`** (distinctive
  binder `tA`). `aMemEqAt[tT]` := BETACONV of `A tT` → `(S t ∧ (a≤t ∧ (t≤b ∧ U t)))`.
  Membership intro/elim via aMemEqAt + CONJ/CONJUNCT.
- `aMemA` (A a): CONJ haS (CONJ (realLeRefl a) (CONJ (realLtImpLe a<b) (U a))) → fold to `A a`.
  `hNeA` := `∃t. A t` (EXISTS a aMemA). `hUpperB` := `∀t. A t ⇒ realLe t b`
  (GEN t, DISCH A t, extract `t≤b` = the 2nd-of-3rd conjunct). `hBddA` := `∃u. ∀t. A t ⇒ t≤u`
  (EXISTS b hUpperB). s := `realSupTm[A]`.
- `haLeS` := realSupUpperThm A MP hNeA MP hBddA SPEC a MP aMemA → realLe a s.
- `hsLeB` := realSupLeastThm A b MP hNeA MP hBddA MP hUpperB → realLe s b.
- `hsS` := isIntervalSet S unfolded, SPEC (a,s,b), MP haS, MP hbS, MP (between a s b
  = CONJ haLeS hsLeB folded via betweenTm) → S s.
- `hCov` SPEC s, EQMP → `(S s) = (U s ∨ V s)`; EQMP (with hsS) → `U s ∨ V s`. DISJCASES:
  - **s∈U branch** (hsU : U s): EXCLUDEDMIDDLE on `mkEq[s,b]`:
    - s=b: rewrite hsU (APTERM cong) → U b; hDisj SPEC b applied to CONJ (U b)(V b) → F.
    - s≠b: ¬(b≤s) (else antisym(hsLeB,b≤s)→s=b contra); `hsLtB` (s<b) via realLtNotLeThm
      SPEC (s,b) on ¬(b≤s). CHOOSE U0 from hOpU's `∃V. isOpen V ∧ ∀x. U x = (S x ∧ V x)`
      (unfoldOpenIn) → isOpen U0 + the iff; `hsU0` := (iff at s, U s).right → U0 s.
      unfoldIsOpen U0 SPEC s MP hsU0 → ∃l r. l<s ∧ s<r ∧ ∀y. openInterval l r y ⇒ U0 y.
      CHOOSE l, r, split. `existsRightBetweenThm` SPEC (s, b, r) MP hsLtB MP (s<r) →
      ∃d. s<d ∧ d≤b ∧ d<r. CHOOSE d. ha_d (a≤d) := realLeTrans haLeS (realLtImpLe s<d).
      hdS (S d) := interval SPEC (a,d,b) MP haS MP hbS MP (between a d b = a≤d ∧ d≤b).
      hdU0 (U0 d) := the `∀y. openInterval l r y ⇒ U0 y` at d, MP (openInterval l r d =
      l<d ∧ d<r: l<d via realLtTrans(l<s, s<d), d<r from existsRightBetween). hdU (U d)
      := (iff at d).mpr (CONJ hdS hdU0). hdA (A d): CONJ hdS (CONJ ha_d (CONJ d≤b (U d)))
      → fold A d. hdLeS (d≤s) := realSupUpperThm … SPEC d MP hdA. Then `s<d` (existsRightBetween)
      + `d≤s` ⇒ via realLeLtTrans / realLtNotLe → F. (realLtNotLeThm: s<d = ¬(d≤s);
      MP NOTELIM that, hdLeS → F.)
  - **s∈V branch** (hsV : V s): CHOOSE V0 from hOpV (unfoldOpenIn) → isOpen V0 + iff;
    hsV0 (V0 s); unfoldIsOpen V0 SPEC s MP hsV0 → ∃l r. l<s ∧ s<r ∧ ∀y. openInterval l r y
    ⇒ V0 y. CHOOSE l, r, split; hLtS := l<s. **exists_lt_of_lt_lub** (the one derived
    step — see RECIPE): from `l < s` (= realLt l s, s = realSup A) derive
    `∃d. A d ∧ realLt l d`. CHOOSE d. hdA (A d) = the left part; hd_l_lt_d (l<d).
    hd_le_s (d≤s) := realSupUpperThm SPEC d MP hdA. hd_lt_r (d<r) := realLeLtTrans
    hd_le_s (s<r). hdV0 (V0 d) := the `∀y. openInterval l r y ⇒ V0 y` at d, MP
    (openInterval l r d = l<d ∧ d<r). hdV (V d) := (V0-iff at d).mpr (CONJ hdA.S hdV0).
    hdU (U d) := hdA's U-conjunct (the 4th). hDisj SPEC d applied to CONJ (U d)(V d) → F.
- The DISJCASES gives F; GEN/DISCH the five → the statement.

**RECIPE — exists_lt_of_lt_lub** (`realLt l s ⇒ ∃d. A d ∧ realLt l d`, s=realSup A):
CCONTR: ASSUME `¬(∃d. A d ∧ realLt l d)`. Build `hUBl := ∀d. A d ⇒ realLe d l`:
GEN d, DISCH (A d); EXCLUDEDMIDDLE on `realLt l d`: if `l<d`, EXISTS d of
`A d ∧ l<d` (CONJ (A d)(l<d)) contradicts the ASSUMEd ¬∃ (MP NOTELIM … → F, CONTR →
realLe d l); if `¬(l<d)`, realLtNotLeThm SPEC (l,d) gives `realLt l d = ¬(realLe d l)`,
so `¬(realLt l d)` EQMP'd → `realLe d l`. Then `realSupLeastThm A l MP hNeA MP hBddA MP
hUBl → realLe s l`; with `l<s`: realLeLtTrans (s≤l)(l<s) → s<s, realLtIrrefl → F; CCONTR
closes to `∃d. A d ∧ l<d`.

### 2. `connectedOfIntervalSetThm` ⊢ ∀S. isIntervalSet S ⇒ isConnected S.
unfoldIsConnected; GEN S, DISCH (isIntervalSet S); GEN U V, DISCH (isSeparation S U V);
from it hNeU (∃a. U a) CHOOSE a, hNeV (∃b. V b) CHOOSE b; `a≠b` (else U a=U b → U b ∧
V b → hDisj → F); ltOrGtOfNeThm SPEC (a,b) MP (a≠b) → a<b ∨ b<a. DISJCASES: a<b →
notSeparationOfIntervalOrderedPointsThm S U V a b (MP chain) → F; b<a →
notSeparation… with `isSeparationSymmThm` (S V U) + (V b)(U a)(b<a) → F. So
¬(isSeparation S U V) (NOTINTRO / the F discharges to ¬). Fold isConnected.

### 3. `connectedIffIntervalSetThm` ⊢ ∀S. isConnected S = isIntervalSet S.
DEDUCTANTISYM[ intervalSetOfConnectedThm-as-implication , connectedOfIntervalSetThm-as-
implication ] per S (or build via the two SPEC'd implications). GEN S.

### 4. corollaries (each trivial): `connectedUniversalThm`,
`connectedSingletonThm` (∀a), `connectedOpenIntervalThm`/`connectedClosedIntervalThm`
(∀l r), `connected{OpenLower,OpenUpper,ClosedLower,ClosedUpper}RayThm` (∀cut) — each
= `connectedOfIntervalSetThm` SPEC'd at the set, MP the corresponding brief-026
`intervalSet…Thm`.

## Stop-loss / graded delivery

Tier 1: (1) `notSeparationOfIntervalOrderedPointsThm` (the hard sup lemma). Tier 2:
(2) `connectedOfIntervalSetThm` + (3) `connectedIffIntervalSetThm`. Tier 3: (4) the
corollaries. If Tier 1 stalls (same failure twice — most likely in the
exists_lt_of_lt_lub recipe or an openIn/openInterval β-redex aconv mismatch), STOP
with a PRECISE report (which sub-goal, exact thrown payload, the term shapes you
compared) — do NOT thrash. **A loadable subset (even just the def scaffolding +
where you got to) is acceptable; report exactly where Tier 1 broke so it can be
finished by hand.**

## Tests (append ~6 asserts)

- `connectedOfIntervalSetThm` concl shape (`isIntervalSet S ⇒ isConnected S`),
  `connectedIffIntervalSetThm` concl shape, `notSeparationOfIntervalOrderedPointsThm`
  concl shape (the 5-hyp ⇒ F), and 2-3 corollary concl shapes. aconv on built
  expected; isThm + no-hyps probes. No deep MatchQ. **NO `testExit[]`.**

## WL / project pitfalls (read twice)

1. No `_` idents. 2. comments close at first `*)`. 3. Public-symbol shadow — all
new names FREE (grep `::usage`): `notSeparationOfIntervalOrderedPointsThm`,
`connectedOfIntervalSetThm`, `connectedIffIntervalSetThm`, `connected*Thm`. 4. HOL
var identity=(name,type): the set A's binder `tA`, the CHOOSE witnesses (U0, V0, l, r,
d, a, b, s) ALL distinctive — a leaked witness → ABS/CHOOSE "free in body-hyps"
(this kind of thing has bitten before). 5. holError HoldRest. 6. dev.wls verifier.
7. aconv tests, no deep MatchQ, no testExit. 8. mkVar/mkConst/mkComb/mkAbs only.
9. **Narrow probes** — this is a long proof; localize a load throw by per-theorem
isThm + a single shape check, NEVER dump terms. 10. No Return in Do/For/While. 11.
realArithProve is LINEAR (not used much here — the order steps are realLe*/realLt*
lemmas + realLtIrrefl). 12. set = real→bool; `S x` = mkComb[S,x]; iff = kernel `=`.
13. **β-redex hygiene** — `A t` (a λ applied), `(openInterval l r) y`, the openIn iff
body are redexes; reduce with BETACONV / the `*MemThm`/`unfold*` so ∃-bodies and CHOOSE
targets are β-NORMAL and aconv-match (a β-redex-vs-normal mismatch broke a CHOOSE in
brief-024 and a DISJ in brief-027). 14. **realSup hyps order** — realSupUpper/Least
both need (∃a.S a) THEN (∃u.∀a.S a⇒a≤u) as the first two MPs, in that order.

## Verification (MANDATORY — you run wolframscript)

```
wolframscript -file tests/dev.wls stdlib/Real/Connected.wl real_connected
```
Loop edit → run → read failure → fix until the tail prints `failed: 0`; paste the
final `passed: N  failed: 0` line VERBATIM. Do NOT run build_snapshot/extend_snapshot,
do NOT modify bootstrap.mx, do NOT run run_all, no other command, nothing outside the
repo, no network. Same failure twice → deliver the loadable subset + report exactly
where it broke. If dev.wls reports a stale snapshot for some OTHER file, STOP and report.

## Hard rules

- No git commit/branch/push/config; leave changes in the working tree.
- Nothing outside Scope; if stuck, STOP and report.
- Stop-loss: same failure twice → STOP, deliver loadable subset + report.
- Minimal diff. Touch nothing outside the repo, no network, only the one dev.wls command.
- **You MUST paste the real `passed: N  failed: 0` from dev.wls. If your run did not
  reach it, say so explicitly and report where it stopped — do NOT claim green without
  the verbatim count line.**

## Report format

1. Per-file changes, line ranges + one-line why.
2. Name-verification table (each reused symbol → file:line; each NEW name confirmed free).
3. How you mapped exists_lub/le_lub_of_mem/lub_le_of_upper/exists_lt_of_lt_lub onto
   realSupUpper/realSupLeast, and how the exists_lt_of_lt_lub recipe went.
4. The exact final `passed: N  failed: 0` from your dev.wls run (verbatim).
5. Which tier fully proven vs stopped (and EXACTLY where, if stopped).
6. Open questions (empty if none).
