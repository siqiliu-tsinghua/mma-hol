# Codex Task Brief Template (mma-hol)

Copy this template to `codex/brief-NNN-<slug>.md`, fill every section, then run:

```
cdx exec -C /Users/fft/Developments/mma-hol -s workspace-write \
  "Read codex/brief-NNN-<slug>.md and execute it exactly. Follow its Hard rules." \
  > /tmp/cdx_brief_NNN.log 2>&1
```

Claude verifies afterwards (git diff scope check + cold Strict run_all).

---

## Goal

One paragraph. What must be true when you are done.

## Context pointers

- Read `CLAUDE.md` (operational notes; especially the **Conventions** section) before writing any code.
- Key files for this task: <list with one-line roles>.
- This is an LCF-style HOL prover in Wolfram Language. You cannot create a
  false theorem from outside the kernel — but you can fail to prove a true
  one. Acceptance is therefore mechanical: the test suite decides.

## Scope

- Files you MAY modify: <explicit list>.
- Files you MUST NOT touch: `Kernel.wl`, `Types.wl`, `Terms.wl`,
  `Bootstrap.wl` (trust boundary — NEVER, even for comments), `bootstrap.mx`
  (rebuilt by scripts, never hand-edited), `CLAUDE.md`, `PLAN.md`,
  `PROGRESS.md`, anything under `codex/` except appending to your own report.
- Do NOT add new axioms or call `newAxiom` under any circumstances.

## Deliverable

Bullet list of concrete artifacts (code, tests, doc line updates).

## WL / project pitfalls (these WILL bite you — read twice)

1. **No `_` in any identifier**, including Module locals: `x_eq` parses as
   `Pattern[x, Blank[eq]]` and silently breaks evaluation. Use camelCase.
2. **WL comments close at the first `*)`** — never write `*)` (e.g. `(a*)`,
   `(SUC k*)`) inside comment prose; the error then points far below.
3. **Private-context symbols do not cross files.** A helper in one file's
   `` `Private` `` is unreachable by bare name elsewhere; an unbound symbol
   stays UNEVALUATED and only fails much later ("not a theorem" /
   "mkComb type mismatch"). When a rule application returns unevaluated,
   suspect a wrong-context symbol first.
4. **HOL variable identity is (name string, type)** — `mkVar["q", ty]` in two
   places is ONE variable. `mkAbs` binds by name. Internal binders and
   per-branch witnesses need distinctive names (`qW`, `aB1`), never bare
   `x/q/r/p/s` that a caller's term might carry.
5. **Errors** are `HOL`Error`holError[tag, msg, payload]` which Throws a
   `Failure["HOLError", …]` with `holErrorTag`. Tests assert on the payload
   tag. Never use `Message` + `$Failed`.
6. **Run scripts as `wolframscript -file foo.wls`** — a bare
   `wolframscript foo.wls` drops into an interactive REPL and hangs forever.
7. **Tests** use `tests/harness.wl` (`HOLTest`assertEq/assertTrue/
   assertThrows/runTests`). Avoid deeply-nested `MatchQ` literal term
   patterns — use position extraction + shallow asserts, or build the
   expected term and compare with `aconv`.
8. Term construction above the kernel goes through `mkVar`/`mkConst`/
   `mkComb`/`mkAbs` — never raw `comb[...]`/`abs[...]` literals.
9. **Debug with narrow probes** (`Head[th]`, `hyp[th]`, one sub-slot), never
   print whole term trees.

## Verification (run each, in order; record exact output)

Typical sequence after editing a library file that is part of the snapshot:

1. `wolframscript -file tests/build_snapshot.wls` — cold rebuild of
   `bootstrap.mx` (~7 min). Must end without a thrown Failure.
2. `wolframscript -file tests/run_fast.wls` — full fast regression on the new
   snapshot. Expect `failed: 0`.
3. Any task-specific test file: `wolframscript -file tests/run_fast.wls <pattern>`.

If `wolframscript` is unavailable in your sandbox, say so explicitly in the
report and deliver code unverified — do NOT fake verification output.

## Hard rules

- Do NOT `git commit`, branch, push, or touch git config. Leave all changes
  in the working tree.
- Do NOT modify files outside Scope. If you believe you must, STOP and write
  that in the report instead.
- **Stop-loss**: if the same step fails twice for the same reason, STOP and
  write a report describing the failure instead of iterating further.
- Keep the diff minimal: no drive-by reformatting, no comment "improvements",
  no renames outside the task.

## Report format (your final message)

1. What changed — per file, with line ranges and a one-line why.
2. Verification — each command run, with the exact pass/fail counts.
3. Open questions / anything you are unsure about (empty if none).
