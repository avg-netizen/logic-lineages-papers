# Lane rules — local Fable-pair continuation, 22 November 2026

Read this whole file before doing anything. Working directory for every command is
`projects/inverse/logic-lineages-papers/formalization` (the Lean package root). This round's home is
`verification/local-fable-pair-2026-11-22/` (below: `HOME`).

## What the project is

Lean 4 (pinned `v4.32.0-rc1`, pinned Mathlib) formalization of papers 16–20. The numbered register
is 156 checked / 11 pending / 167; the pending 11 (Paper 16 ×8, Paper 17 ×3) are all deep, so current
work adds *supporting* checked statements that close in on them. Latest state:
`verification/continuation-2026-11-22/SESSION-HANDOFF-2026-11-22.md` (read it), supporting records
through #1385 in `verification/new-paper-set-2026-11-18/accepted/`, each with a `*-SOURCE-MAP.md`
scope note and a `*-native.json` evidence file in `verification/continuation-2026-11-22/`.

## Parties

- **root** — Claude Fable 5.2 High in the user's Claude Code session. Owns Git, the register,
  acceptance records and numbering, the run policy, and a Paper 16 proof lane.
- **Fable-2** — second Claude Fable 5.2 High (headless, via `claudep`). Paper 17 proof lane.
- **Opus A / Opus B** — Opus 5.5 High subagents on assigned tasks.

Each lane writes only its own Lean modules and its own ledger. Nobody but root runs Git, edits
records under `accepted/`, `TARGETS.json`, `CURRENT-COMPARISON-TARGETS.json`, `AGENTS.md`,
`README.md`, the manuscripts, the toolchain/pins, `scripts/`, or `.local-run-policy.json`.

## Hard rules

1. **Compiler.** The only way to run Lean is
   `bash verification/local-fable-pair-2026-11-22/gate.sh mathlib MODULE [MODULE...]`
   (wraps `scripts/check.py` with the fixed caps, waits when the single compiler lock is busy).
   Never call `lean`, `lake`, or `check.py` directly; never run two gates at once from one lane.
   Both frontiers are Mathlib-profile closures. A gate on a module compiles its uncached local
   imports first; cached modules print `CACHE_HIT`. Receipts land in `build-reports/<id>.json` with a
   log per module.
2. **Never edit an existing tracked `.lean` file.** Every accepted module is hash-pinned by its
   record; changing one breaks the pins and invalidates the cache of everything that imports it.
   New work goes in new modules. If an existing statement is unusable, write a new module beside it.
3. **Never delete anything.** A failed draft stays on disk: copy it to `HOME/drafts/<lane>/` with a
   one-line note before you overwrite your own working module, or just keep it under a new name.
   No `rm`, no `git clean`, no `git checkout --`.
4. **Freeze the target before the proof.** For each new statement, first write the `…Targets.lean`
   module (definitions as `def … : Prop`, no proofs) and a short `HOME/<lane>/<KEY>-SOURCE-MAP.md`
   saying which paper statement / handoff item it serves, what is assumed, what is *not* claimed.
   Record its sha256 in your ledger. After that the Targets file does not change; if it has to,
   keep the old one, write a new name, and say why in the ledger.
5. **Do not weaken a claim to fit a limit.** No `sorry`, no `axiom`, no `native_decide`, no extra
   hypotheses that assume the conclusion. Standard axioms only (`propext`, `Classical.choice`,
   `Quot.sound`); end each proof module with `#print axioms <theorem>` so the gate log shows them.
   If a route fails, say so plainly; a recorded stop with the reason is a valid result.
6. **Stay inside** `projects/inverse/logic-lineages-papers/formalization`. No network, no installs,
   no dependency updates, no writes elsewhere.
7. **Resources.** The machine has 4 cores and ~7 GB free; the gate caps RSS at 1536 MiB *including
   file-backed olean maps*. A stop after ~2 s CPU is import footprint, not proof search: make heavy
   suppliers private `import` (not `public import`) and keep Targets modules on the lightest public
   imports. A stop after many seconds with large anonymous RSS is elaboration: the usual cause is
   `omega`/`simp` over big terms — move arithmetic into a lemma over abstract naturals.

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
  names; grep for a lemma before assuming it exists.

## Ledger and hand-back

Keep `HOME/<lane>/LEDGER.md` current as you go (append-only): targets frozen (path + sha256), gate
receipts (id, module, pass/fail), failed routes with the reason, and at the end a "state and next"
paragraph. Root reads the ledger and the files, not your memory. When a target passes its gate,
write `HOME/<lane>/<KEY>-EVIDENCE.json` with: module names, sha256 of each new source file, the
passing receipt id, and the `#print axioms` lines copied from the gate log. Root turns that into the
numbered supporting record.

Report honestly: what passed the gate, what is drafted but ungated, what failed and why.
