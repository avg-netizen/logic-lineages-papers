# Checked original bounded result-fold calibration

Six exact supporting targets are checked against the unchanged original
result-stack AST. Its complete bounded fold now agrees on every natural
input with an independent well-founded semantic fold on the original term
payload. The actual bounded run has live status, empty work and exactly one
result containing that fold value.

Checked results:

- The semantic fold's original application/leaf recursion equation.
- Exact complete iteration calibration, preserving the entire encoded state.
- Sufficient work-weight fuel and terminal fixed points for arbitrary states.
- Full semantic configuration preservation by transitions and iteration.
- Successful single-visit completion over any background result stack.
- Exact all-input bounded run and fold calibration for arbitrary guard,
  leaf and four-input combine programs.

The fold opens only an original application whose whole-root guard returns
exactly one. Finish pops argument then function, but passes combine the
original domain, codomain, function output and argument output in that order.
Computed outputs are unrestricted and contribute nothing to the exact
`2 * originalPayload + 1` fuel bound. No packed-code bound is assumed.

All six exact aliases and 24 supporting theorem entries passed their actual
axiom audits, using only `propext`, `Classical.choice` and `Quot.sound`.
The focused import closure has **837 source-matched local modules**, including
**8 component Lean files**. All **40** frozen, prerequisite, correspondence
and paper pins match. Peak successful component RSS was **1,044,840 KiB**,
below the unchanged **1,536 MiB** cap. Existing matching supplier receipts
were reused; no fresh whole-closure or full-root build is claimed.

Independent specification review and successful native preflight preceded
proof authorship. One proof-only repair discharged the dependent-if versus
ordinary-if equation after unfolding the semantic definition. No frozen
statement, program AST, original source or premise changed. The failed
candidate, immutable receipts and logs remain local. All owned compiler
processes are reaped and the sole slot was released to the coordinator.

**Still pending separately:** original representative-specific calibration,
internal result-stack composition and recursive constructor closure,
representative application congruence, context-uniform integration and the
complete paper06 accessibility proof. External natural-number calibration
does not infer any internal derivability rule.

No numbered source statement is promoted. The global register and root
imports are unchanged. No Git publication or remote-CI action was performed
by this component. See `VALIDATION.md` for the exact consumer API and checks.
