# TODO — divergences from HOL Light worth tracking

Audit pass against `fusion.ml` / `equal.ml` / `drule.ml` / `bool.ml` / `meson.ml`.

**Status 2026-06-17: audit pass CLOSED — no open action items.** stdlib (M8 ℝ theory)
complete + graduated. All soundness / expressiveness / robustness divergences below are
resolved or reviewed-and-accepted.

## Resolved

- **A** MESON ancestor-stack pollution under k>1 starts — ✓ DONE (`expandOne`/`expandSiblings` split).
- **B** MESON `@` tag-stripping vs user var names — ✓ DONE 2026-06-17: `mkVar` now rejects any
  name containing `@` (reserved for MESON clause renaming, which uses raw `var[name@N]`).
  Regression in `tests/terms_tests.wl`.
- **C** `REWRCONV` first-order-match-only — ✓ DONE (Miller higher-order pattern match).
- **E** `REWRITERULE` loop / non-productivity detection — ✓ DONE (`fixpointConvRule` + cycle break).
- **F** `CHOOSE` freshness errors leaking to kernel — ✓ DONE (up-front body-hyp check).
- **G** `SUBCONV`/`onceDepthConv` fresh-name ignores inner-conversion frees — ✓ DONE (`absConvWithRetry`).

## Reviewed and accepted (no change)

- **D** `INST`/`INSTTYPE` free-var collapse under type instantiation — REVIEWED 2026-06-17,
  ACCEPTED as correct. The "collapse" only fires when two pre-distinct hypotheses become the
  *same term* after `instType` (e.g. `P(x:α)` and `P(x:β)` under α=β=γ), so `normHyps` dedups
  them to one — sound and expected, matching HOL Light's hypotheses-as-a-set semantics. The
  real capture concern (the cited `Clash`/`variant`) is about bound vars in `INST`, already
  prevented structurally by de-Bruijn `bvar`. A kernel hot-path guard for a correct behavior
  is not worth the cost; "rename to keep distinct" would be unsound. Owner decision.

## Monitor only (non-actionable performance notes)

- **H** `propTaut` is O(2^n) on free bool vars — matches HOL Light `TAUT`; fine for ≤3-var
  schema lemmas. Watch if SIMP starts auto-proving larger boolean side-conditions.
- **I** MESON preprocessing builds raw `comb[...]` (Skolem terms) bypassing `mkComb` — safe:
  constants/types pre-registered, replay re-runs through the kernel. Risk only if such terms
  escape a non-replay path.
