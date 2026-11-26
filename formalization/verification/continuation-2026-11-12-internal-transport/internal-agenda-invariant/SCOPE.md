# Internal agenda admissibility and operational preservation

The definitions and targets in `FROZEN.json` were fixed before the proofs.
They use formulas of the existing internal calculus, not native `AgendaTyped`
and not a metatheoretic universal as a replacement for an internal invariant.

- `Job` existentially records actual encoded role/type/raw/context coordinates,
  original-window decoder acceptance, an actual weight observation, and the
  fixed global branching bound `weight + 2 ≤ B`.
- `Frame` existentially records a literal visit (tag 0) or return (tag 1) frame,
  with the same admissible parent job. Return counts remain literal metadata.
- `Agenda` universally quantifies actual bounded numeric-list lookups and
  requires each resulting frame to satisfy `Frame`.

The concrete proof chain establishes singleton initialization, return-tail
preservation, and actual visit replacement preservation. Visit preservation
constructs the child's original-window parameter identity from actual raw and
annotated expansion, rather than assuming it. Actual child acceptance and
strict weight decrease then establish the bounded child job. The literal
`tagVisits` map is handled by original internal list-code induction; arbitrary
append uses actual bounded lookup splitting. No child acceptance, same-window,
visit-preservation, or native correctness supplier remains in the final theorem.

The coordinator's bounded build `1794503342351918631-5` checked the final
`OriginalHereditaryInternalAgendaVisitProof.actualVisitPreservation` and its
job-expansion dependencies, and the consuming exact actual-completion alias.
Earlier gates checked the internal binder, structural, tag-map and append laws.
The checker limits and allowed axiom policy were unchanged.

## Explicit scope limit

This invariant constrains pending work, not the semantic contents of the result
stack. Operational completion does not by itself identify the evaluator's
returned value with the intended recursively defined observation. A full
result-content/return-boundary invariant and its integration remain separate.
No final source lambda-computability, ordinary/quotient source-edge closure,
representative coherence, or whole remaining paper statement is claimed here.
