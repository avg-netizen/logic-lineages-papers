# Paper 16: application respects the function's class (measured exchange)

Serves the function-side closure on classes used in `lem:arithmetic-accessibility`
("Q R_S Q' gives Qx R_S Q'x"; "all statements respect the finite equivalence quotient").

Frozen `NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationTargets.lean`
(sha256 `1cb10ccfc3c3ec7afe52888fbc1aef9a95967f3171ae7b0642cb8cea20f79c6b`),
`ExactFullyMeasuredClassApplication`: on the chosen combined restricted programs with the measured
guarded paired exchange at function and application level, if f and g have the same successful
function-level packed least x and their applications to the same argument have successful leasts m and
m', then the application of g has least m.

Proof: #1421 `exact_FullyMeasuredLeastRepresentativeApplication` at f and at g puts both m and m' on the
application of x; `valueUnique` and `outputTransport` on the packed least program finish.

Held, not derived: both type guards, the argument window, and all four least calls. No measure
hypothesis and no edge between f and g. Not claimed: existence of the application leasts; the same
statement for the unmeasured exchange the route currently installs (false in general without a measure
premise, see #1400); argument-side statements; anything about reduction steps.
