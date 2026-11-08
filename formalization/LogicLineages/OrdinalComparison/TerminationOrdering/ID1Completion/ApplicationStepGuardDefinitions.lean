module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecDefinitions
@[expose] public section
/-! Exact semantic algorithm identities for original function-side application.

The source rule is paper06, lines 537–549; the least-code quotient and arithmetic
edge interpretation are described at lines 551–556. This family does not replace
any checker, encoder, decoder, calculus, or certificate format. It names no new
program: the targets refer directly to the existing definitions imported above.

All natural step-certificate codes are retained, including paths containing an
invalid position code. The source and argument keep their original universe
guards. The target keeps the ordinary packed decoder, without a new universe
filter. The result type must belong to S explicitly, or by subtype closure.

These are external semantic identities, not internal Derivation terms,
CertifiedApplicationLift, representative congruence, or the full ID1 theorem.
-/
