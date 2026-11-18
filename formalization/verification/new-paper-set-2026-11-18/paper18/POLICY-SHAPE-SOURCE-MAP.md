# Supporting arbitrary computable-policy literal macro programs

Motivation: current18 source-applications.tex fixes a computable admissible
policy for finite sums/repetitions before literal zero-history assignment.
This packet pays that actual policy execution boundary only; full source
assignment recursion and numbered source claims are not included.

Policy.shape site n has Shape(n+1). Macro code receives n as the policy
index, and literal calibration consumes exactly n+1 original operand codes.
All seven MacroSite constructors have explicit numeric tags and a required
encode/decode equation. Unknown tags totalize to optionalBoxTail.

shapeCode is postorder: leaf=false; join concatenates left/right scripts
then true. The total step consumes the next operand on leaf, preserving its
entire code, and on join pops right/left and constructs literal node4(left,
right). Underflow and missing operands fail; finish requires exhausted input
and exactly one result, rejecting all other final states. No operand syntax,
name or value is inspected, normalized or reassociated. FramedExpansion
proves exact typed syntax and leftover operands/stack for EVERY Shape.

RawPrograms requires actual primitive recursion for total step/run/finish/
expandCode, not just structural termination. Effective p is the concrete
joint Computable numeric function selector p, returning the actual coded
shape selected by the given p and decoded macro tag/arity. No assignment
success, shape-normalization or semantic oracle is assumed. PolicyPrograms
requires actual jointly Computable macro/repetition composition for that
fixed selector; no higher-order universal index evaluator is claimed.

LiteralCalibration is exact full AST code equality with AdmissibleSum.expand
and AdmissibleAssignment.repeated for every actual policy, independently
of whether it is effective. Zero repetition explicitly yields source zero.
The effective hypothesis is used only for genuine program assertions.

Remaining: replace default calls throughout literal partial/box/abstraction
programs and prove joint total computation/calibration of original source
assignment, then reassemble equality on actual admissible domains. Default
association is not interchangeable with arbitrary association by value
alone because literal size and partials observe the original tree.
