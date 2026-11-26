# Local three-party continuation, 18 November 2026

User release (about 19:40 UTC, local palace2 session): "please fetch the logic
lineages papers repo; latest work is on a branch that I would like you to
continue. please continue formalization with two sol 6.2 high agents (and
yourself)." Checkout: formalization/new-paper-set-2026-11-18 at
ff2e5a5b88771cd93e01332dce8dc39480a960f8. The owner cutoff in
verification/new-paper-set-2026-11-18/PLAN.md stands: 2026-11-19T18:00:00Z
(enforced by .local-run-policy.json; the 14 November local pause is archived
here as PRIOR-LOCAL-RUN-POLICY-2026-11-14.json).

Register at start: 122 checked, 45 pending / 167 (CURRENT-COMPARISON-TARGETS.json).
Read verification/new-paper-set-2026-11-18/PLAN.md and STATUS.md, then the
newest handoff, plan, scope-review and source-map files of your paper before
trusting any summary. All standards of AGENTS.md and PLAN.md are unchanged:
frozen source-exact comparator first, native gate, standard-only axiom audit
(propext, Classical.choice, Quot.sound), recursive source-matched evidence,
independent review before acceptance. No sorry/admit, new axiom, oracle,
native_decide, unsafe, weakened endpoint or hidden supplier. Preserve accepted
and frozen sources and every failed draft byte-for-byte. A false or blocked
target is a result: preserve the precise obstruction and pick a paid supplier.

## Parties and ownership

Root (Claude, this session): coordination, independent final reviews, accepted/
records, CURRENT-COMPARISON-TARGETS.json, STATUS.md, README/AGENTS, the checker,
policy, cache warmer, Git. Root also works lane C.

- Lane A (Sol 6.2 high): paper16. New Lean files only under
  LogicLineages/PersistentMarking; records under
  verification/new-paper-set-2026-11-18/paper16 and this directory's A/.
  17 pending: thm:main, lem:structural-interpretation, lem:operator,
  thm:adequacy, thm:decide, thm:rpo, lem:arithmetic-accessibility,
  lem:window-locality, lem:tuple-simulation, lem:positive-simulation, thm:upper,
  lem:carrier, lem:indexed-carrier, lem:realization, thm:iteration,
  lem:tower-cofinality, thm:height. Frontier at checkout: the twelve
  MarkedConstructor builder contracts (target preflight passed; Head, Occurrence,
  Tuple, Select, FAbs proofs in progress) toward lem:structural-interpretation
  and lem:operator.
- Lane B (Sol 6.2 high): paper19. New Lean files only under
  LogicLineages/ControlSensitivityCurrent; records under
  verification/new-paper-set-2026-11-18/paper19 and this directory's B/.
  15 pending: thm:compiler, cor:ground-equivalence, thm:control-hardness,
  prop:counter-bound, prop:actual-attainment, lem:absolute,
  thm:decision-equivalence, lem:one-unit, thm:unit-elimination, lem:affine-head,
  lem:carriers, lem:reserve, lem:chain, thm:ground-construction, thm:head-graph.
  Frontier at checkout: RawDerivedComposition (derived aggregate/wrapper/rename
  shared-DAG operations) toward thm:compiler.
- Lane C (root): papers 17, 18, 20 (PermittedControl, StandardControlCurrent,
  CartierObserverCurrent); 13 pending. Lanes A and B treat these trees as
  read-only imports.

A lane may choose the order of its pending statements; prefer the statement
whose suppliers are already checked. Whole numbered-statement promotion needs a
fresh complete gate and root review; supporting packets are recorded as such.

## Native compiler

Exactly one Lean process at a time on this host (13 GB RAM, 4 cores, shared).
Run gates ONLY through the wrapper, from any directory:

    verification/local-two-sol-2026-11-18/gate.sh core MODULE...      # paper16
    verification/local-two-sol-2026-11-18/gate.sh mathlib MODULE...   # papers 17-20

It calls the unchanged scripts/check.py with the two established profiles
(--core-profile; --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048), waits
when the shared lock is busy and makes the cache warmer yield. Do not call
lean or lake directly, do not run two gates at once, do not change caps.

Cache: scripts/check.py reuses a module's .olean when its source hash, the
bytes of every imported object, the compiler and the resource profile all
match a recorded successful native receipt (CACHE_HIT lines). The 18 November
work was compiled on another machine, so this host began with no objects for
papers 16-20; warm.py is replaying the existing sources in the background
(logs/warm.log). Consequences: (1) keep one profile per tree, since a profile
change is a cache miss; (2) put new proofs in NEW leaf modules rather than
editing a widely imported module, since an edit recompiles every dependant;
(3) split long proofs into small modules so a failure costs one module;
(4) a first gate over an unwarmed closure simply compiles it once.

## Working protocol

No nested agents and no Git commands. Do not edit files outside your lane
ownership. Work continuously through successive packets; do not stop to ask
for permission between packets. After each packet append a dated entry to your
lane ledger (A/LEDGER.md or B/LEDGER.md): frozen target, files, native receipt
ids, evidence files and hashes, what is and is not proved, next target. Mark a
packet READY-FOR-ROOT-REVIEW when its exact gate, axiom audit and evidence are
complete; root reviews, records acceptance and commits. Continue with the next
packet meanwhile. End your turn only when a numbered statement's complete gate
is ready, when you are blocked on something only root can resolve, or after
roughly three hours of work; the final message must state what is ready for
review, what is draft, and the exact next step. Root resumes the same session.
