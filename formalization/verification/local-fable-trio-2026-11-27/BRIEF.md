# Lane rules — local Fable-trio continuation, 27 November 2026

Read this whole file before doing anything. The working directory for every command is the Lean
package root of the **2026-11-25 worktree**:

`/home/other/storage/projects/palace2/projects/inverse/logic-lineages-papers-formalization-2026-11-25/formalization`

(below: `ROOT`). Do not work in the older checkout `…/logic-lineages-papers/formalization`; it is two
days behind. This round's home is `verification/local-fable-trio-2026-11-27/` (below: `HOME`).

## What the project is

Lean 4 (pinned `v4.32.0-rc1`, pinned Mathlib) formalization of papers 16–20. The comparison register is
**161 checked / 6 pending**; all six pending statements are Paper 16
(`16-persistent-marking-termination-ordering/`, two levels up from `ROOT`):
`lem:arithmetic-accessibility`, `thm:upper`, `lem:realization` (wording decision, not proof work),
`lem:tower-cofinality`, `thm:height`, `thm:main`.

The current plan of record is `verification/paper16-remaining-targets-2026-11-25/TARGETS.md` — read it.
It names the Lean target for each pending statement and the ordered proof checkpoints. The state of the
three accessibility lanes a Codex coordinator ran on 25–26 November is in
`verification/local-fable-continuation-2026-11-25/2026-11-26/` (`HANDOFF.md`, `native-window-v2-rebase.md`,
`beta-guard-address-handoff.md`, `codex-lambda-prefix-handoff.md`). The ordinal side was last worked in
`verification/local-fable-pair-2026-11-23-round6/` (`HANDOFF.md`, `opusA/CALIBRATION-INDUCTION-NOTE.md`).

## Parties

- **root** — Claude Fable 5.2 in the user's Claude Code session. Owns the round's records, the gate
  queue order when lanes collide, and an assembly/gating lane.
- **Fable A** — ordinal calibration lane.
- **Fable B** — internal accessibility lane.

Each lane writes only its own new Lean modules, and its own directory `HOME/<lane>/`.
**Nobody in this round runs Git** (no add, commit, checkout, stash, worktree — nothing), and nobody edits
`AGENTS.md`, `README.md`, `TARGETS.json`, `CURRENT-COMPARISON-TARGETS.json`, anything under
`verification/` outside `HOME`, the manuscripts, the toolchain/pins, or `scripts/`. The worktree carries
uncommitted work by the Codex coordinator (five modified tracked `.lean` files, ~70 untracked modules):
leave all of it exactly as it is.

## Hard rules

1. **Compiler.** The only way to run Lean is
   `bash verification/local-fable-trio-2026-11-27/gate.sh mathlib MODULE [MODULE...]`
   run from `ROOT` (it wraps `python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048`
   and waits politely when the single machine-wide compiler lock is busy or free memory is under the
   floor). Never call `lean`, `lake`, or `check.py` directly; never run two gates at once from one lane.
   Three lanes share one compiler, and three unrelated CPU jobs are running on this 4-core machine, so
   **a gate is expensive**: a cold import closure is 1,500–3,300 modules. Read neighbouring proofs and
   get the draft right on paper before gating; batch several new modules into one gate call. A gate on a
   module compiles its uncached local imports first; cached modules print `CACHE_HIT`. Receipts land in
   `build-reports/<id>.json` with a log per module. If the gate reports a wait timeout, just run it again
   later; completed dependency rows are kept.
   Run long gates in the background and keep thinking/drafting meanwhile.
2. **Never edit an existing `.lean` file you did not create in this round.** Accepted modules are
   hash-pinned; changing one invalidates the cache of everything importing it. New work goes in new
   modules. If an existing statement is unusable, write a new module beside it and say why.
3. **Never delete anything.** No `rm`, no `mv` over an existing file, no `git clean`. A failed draft stays
   on disk: copy it to `HOME/drafts/<lane>/` with a one-line note before overwriting your own working
   module, or keep it under a new name. A hook will stop any deleting command and ask the user — treat
   that as a stop sign, do not rephrase the command to get past it.
4. **Freeze the target before the proof.** If the statement you are proving is not already an existing
   `def … : Prop` in a Targets module, first write a `…Targets.lean` module (definitions only) and a
   short `HOME/<lane>/<KEY>-SOURCE-MAP.md` saying which paper statement / TARGETS.md checkpoint it
   serves, what is assumed, and what is *not* claimed. Record its sha256 in your ledger. After that the
   Targets file does not change; if it must, keep the old one, use a new name, and say why.
   Prefer proving statements that already exist as frozen targets.
5. **Do not weaken a claim to fit a limit.** No `sorry`, no `axiom`, no `native_decide`, no extra
   hypotheses that assume the conclusion. Standard axioms only (`propext`, `Classical.choice`,
   `Quot.sound`); end each proof module with `#print axioms <theorem>` so the gate log shows them.
   If a route fails, say so plainly; a recorded stop with the exact reason is a valid result. If you find
   that a frozen target is false or mis-stated, write a short report in your lane directory and move to
   another target — do not repair someone else's target in place.
6. **Stay inside `ROOT`** (and read-only in the manuscript directory). No network, no installs, no
   dependency updates, no writes elsewhere. Scratch files go under `HOME/<lane>/`.
7. **Resources.** The gate caps RSS at 1536 MiB *including file-backed olean maps*. A stop after ~2 s CPU
   is import footprint, not proof search: make heavy suppliers private `import` (not `public import`) and
   keep Targets modules on the lightest public imports. A stop after many seconds with large anonymous
   RSS is elaboration: the usual cause is `omega`/`simp` over big terms — move arithmetic into a lemma
   over abstract naturals/ordinals and apply it.

## House style that compiles (saves hours)

- Files start with `module`, then imports, then `@[expose] public section` (Targets) or
  `public section` (proofs). Exported `rfl`/`decide` facts need `@[expose]`.
- Paper 16 object-calculus proofs: `Derivation body Γ φ` natural deduction; eigenvariables through
  continuation lemmas with `(β) (j : α → β) (Δ)`; suppliers such as `programCases`,
  `programCompositionCases`, `compositionRecover`, `zeroSuccessorCases`, `optionGraphCases`,
  `valueUnique`, `outputTransport`, `headTransport`, `natInduction`, `renameInto`; one
  `…Rename`/`…Subst` syntax lemma per formula family. Untyped `have`s using these fail to infer
  `body`/`Γ` — always give the type. `attribute [local irreducible] programGraph` keeps terms small.
- Copy the import list and `open` block from the nearest accepted neighbour rather than guessing
  names; grep for a lemma before assuming it exists (use `command grep`, plain `grep` here skips
  git-ignored files). Mathlib names for this pin differ from memory often enough
  (`add_le_add_right` argument order, `lt_or_le`, no `norm_num` in some closures) that checking the
  spelling in an accepted neighbour is faster than a failed gate.
- Modules under `LogicLineages/NativeModule/` are module-system copies of legacy files; a module-system
  file cannot import a legacy (non-`module`) root, so import the `NativeModule` twin when one exists.

## Ledger and hand-back

Keep `HOME/<lane>/LEDGER.md` current as you go (append-only): targets chosen or frozen (path + sha256),
gate receipts (id, modules, pass/fail), failed routes with the reason, and at the end a "state and next"
paragraph. Root reads the ledger and the files, not your memory. When a target passes its gate, write
`HOME/<lane>/<KEY>-EVIDENCE.json` with: module names, sha256 of each new source file, the passing receipt
id, and the `#print axioms` lines copied from the gate log.

Report honestly: what passed the gate, what is drafted but ungated, what failed and why. Your final
message to root should be short: theorems gated (names + receipt ids), drafts not gated, blockers, and
what you would do next.
