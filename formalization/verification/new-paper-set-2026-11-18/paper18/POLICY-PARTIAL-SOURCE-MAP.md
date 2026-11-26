# Literal arbitrary-policy partial compiler: supporting scope

Current18 source-applications fixes an arbitrary computable admissible policy.
The actual source syntax is `Source.AdmissiblePartial.run`, not an association-
normalized or default-policy replacement. The new numeric `PolicyPartial.run`
uses exactly the existing raw ordinal-expression codes and whole-head-free test.

Frozen comparator contains all of:
1. Actual coordinate syntax for activeAdd and activeExp with unchanged nested
   positiveRepeat2 as first operand. Three operands remain left-to-right; policy
   both outer activeAdd/activeExp shape indices are 2 (arity 3); the nested
   positiveRepeat shape index is 1 (arity 2).
2. Literal typed calibration for every context/type/grade/expression, including
   every `none` result and every coordinate of a successful actual source vector.
   Whole-head-free precedence includes otherwise inactive constructor cases.
3. Genuine joint all-raw-input Computable coordinate, vector merge and recursive
   run under ONLY `PolicyShape.Effective p`, not PR of the selector.

The vector merge traverses all level+2 coordinates in order using actual policy
macro codes and existing getD-zero convention. Malformed natural codes are
handled totally by the same tag/child scheme as the previous literal compiler.
Recursive grades are unchanged: add i/i, exp i+1/i requiring i>0, collapse1/0
requiring i=0. Collapse is the original fixed collapse/headClosure syntax and
positive plain additions, not a policy macro or normalized expression.

The checked ComputableRecursion supplier will be instantiated with real child
states and strict child code rank. Assembly success/recursion equation must be
proved internally; no numeric evaluation oracle or PR policy assumption.
The only existing proofs in definitions are structural termination obligations.

Supporting compiler only. This packet does not claim source abstraction,
assignment, equality, or any numbered arbitrary-policy frontend theorem.
