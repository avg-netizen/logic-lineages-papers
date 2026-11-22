# Current workflow: construct proofs and let Lean validate them

The user clarified: we do not need to check proof validity manually before
compilation; that is Lean's job. This supersedes earlier duplicate proof-body
pre-review and second full native/artifact replay requirements for new work.
Preserve all existing accepted source, proofs, failed editions and evidence.

The former review Sol now authors substantive missing lemmas and helps repair
actual Lean failures. It owns NumberedWindowInternalSparseCoverScratchOpen*:
the real C option output at the source heads/types and seed, its zero/successor
projection to physical scratch vertices, and common-option output equality at
two seeds. Astra owns callback selection/reinstallation and the sole compiler
queue; the other Sol continues Paper17. No new agent or Fable005 call is needed.

Compile the exact target declarations and audit their axiom dependencies once
through the existing native queue. Use compiler diagnostics to repair failures.
Keep required source/cache identity checks in that compiler invocation. Do not
add a second full closure/object/ZIP audit or manual proof-body approval.

A concise check of formal statement against the paper remains useful on
materially new or changed claims: quantifier/guard scope, extra assumptions,
actual original programs/domains, and which result follows. Lean checks the
supplied proposition, not its correspondence to informal source prose.
This check must not become a separate proof-validity or historical-audit campaign.

Already source-prescoped and native-passed new results may be recorded without
waiting for duplicate review. Records must state the evidence actually used:
source-scope check and exact native/axiom gate, rather than falsely claiming a
second independent artifact replay. Existing numbered-scope qualifications,
resource limits and current provider-source authorization are preserved.
