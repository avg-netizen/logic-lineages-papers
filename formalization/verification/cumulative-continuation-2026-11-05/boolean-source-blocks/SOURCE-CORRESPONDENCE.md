# Boolean closure of homogeneous BASE blocks

This supporting BASE fragment keeps the existing actual SourceFormula grammar,
evaluation, bijective numeric codec, and literal homogeneous-prefix recognizer.
It closes the recognized fragment under original negation and conjunction,
thereby also expressing disjunction through the existing De Morgan syntax.
For example, ordinary negated existential blocks become accepted without
pretending that the old literal forall parser already accepted them.

The algorithm stops at an existential node unless the existing homogeneous
recognizer accepts that entire node. It does not recursively pass a rejected
binder. Both leading exists/not-exists and not-exists/not-exists mixed patterns
are explicitly rejected in the frozen boundary proposition. This is not general
quantifier alternation, equivalence-normalized syntax recognition, QE or full
first-order BASE. No source-register promotion is claimed.

Six exact targets require typed acceptance domain, actual truth at finite
ambient values (missing entries zero), literal numeric calibration, the actual
primitive-recursive numeric decision, all-natural-code truth/domain, and the
fragment boundary. Boolean truth/false answers are both characterized; there is
no supplied decision oracle or caller-provided semantic premise.
