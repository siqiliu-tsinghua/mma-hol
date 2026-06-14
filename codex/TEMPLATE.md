# Codex Task Brief Template (mma-hol)

Copy this template to `codex/brief-NNN-<slug>.md`, fill every section, then run:

```
cdx exec -C /Users/fft/Developments/mma-hol -s danger-full-access \
  "Read codex/brief-NNN-<slug>.md and execute it exactly. Follow its Hard rules." \
  > /tmp/cdx_brief_NNN.log 2>&1
```

`-s danger-full-access` lets Codex run `wolframscript` on the real machine
(the sandbox blocks the WolframKernel). Codex MUST self-verify with
`tests/dev.wls` and iterate to green BEFORE delivering (see Verification).
Claude still does the authoritative gate afterwards (git diff scope check +
cold Strict run_all).

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
   expected term and compare with `aconv`. **NEVER call `HOLTest`testExit[]`
   in a test file** — the runners call it once centrally; a per-file
   testExit `Exit[]`s the process and silently truncates a cold `run_all`
   (it stays invisible under your `dev.wls` run because that runs your file
   LAST). End test files with the last `runTests[...]`, nothing after.
8. Term construction above the kernel goes through `mkVar`/`mkConst`/
   `mkComb`/`mkAbs` — never raw `comb[...]`/`abs[...]` literals.
9. **Debug with narrow probes** (`Head[th]`, `hyp[th]`, one sub-slot), never
   print whole term trees.
10. **No `Return` inside `Do`/`For`/`While`** — it exits only the loop, NOT
    the surrounding Module; code after the loop still runs. Use a result
    flag (`out = Null; While[out === Null && …]`) or `Throw`/`Catch`.
11. **`holError` is HoldRest** — msg and payload must be a LITERAL String /
    Association at the call site. A computed msg (`name <> "…"`) or a
    payload passed through a variable matches no DownValue: nothing is
    thrown and the call returns unevaluated (bit brief-005). Put variables
    INSIDE a literal `<|"k" -> v|>` wrapper instead.

## Verification (MANDATORY — you run `wolframscript`; iterate to green)

You are dispatched with `-s danger-full-access`, so `wolframscript` works on
this machine. You MUST verify before delivering — do not hand back unverified
code.

For a FRONTIER file (new file not yet in `bootstrap.mx` — the usual case;
the brief's Scope says so), the ONLY command you run is:

```
wolframscript -file tests/dev.wls <the/frontier/file.wl> <test-pattern>
```

e.g. `wolframscript -file tests/dev.wls stdlib/Real/Seq.wl real_seq`. It
restores the snapshot, loads your frontier file on top, and runs the matching
`tests/*_tests.wl`. **Loop: edit → run dev.wls → read the failure → fix →
re-run, until the tail prints `failed: 0`.** Paste that final
`passed: N  failed: 0` line into your report verbatim.

Reading failures: a thrown `Throw::nocatch` at load = a proof/term bug in a
theorem (localize by which tests stopped running); `Syntax::sntx` with a line
number = a bracket/quote typo (fix at that line); `failed: K` with `FAIL`
lines = assertion mismatches (usually a test or an aconv expected-term issue).

**You may ONLY run that one `dev.wls` command for verification.** Do NOT run
`tests/build_snapshot.wls` or `tests/extend_snapshot.wls`, do NOT modify
`bootstrap.mx` (dev.wls only reads it), do NOT run `run_all.wls` (that is
Claude's authoritative gate). If `dev.wls` reports the base snapshot is stale
(an upstream non-frontier file changed), STOP and report — do not rebuild.

If you hit the stop-loss (same failure twice), deliver the loadable subset
(whatever theorems DO make `dev.wls` green with the rest commented out or
omitted) and report precisely where you stopped — never fake a green count.

## Hard rules

- Do NOT `git commit`, branch, push, or touch git config. Leave all changes
  in the working tree.
- Do NOT modify files outside Scope. If you believe you must, STOP and write
  that in the report instead.
- You run with full machine access. Touch NOTHING outside this repo. No
  network. The only commands you run are file edits within Scope and the one
  `wolframscript -file tests/dev.wls …` verification command. No other
  `wolframscript`, no snapshot rebuilds, no `bootstrap.mx` writes.
- **Stop-loss**: if the same step fails twice for the same reason, STOP and
  write a report describing the failure instead of iterating further.
- Keep the diff minimal: no drive-by reformatting, no comment "improvements",
  no renames outside the task.

## Report format (your final message)

1. What changed — per file, with line ranges and a one-line why.
2. Verification — each command run, with the exact pass/fail counts.
3. Open questions / anything you are unsure about (empty if none).
