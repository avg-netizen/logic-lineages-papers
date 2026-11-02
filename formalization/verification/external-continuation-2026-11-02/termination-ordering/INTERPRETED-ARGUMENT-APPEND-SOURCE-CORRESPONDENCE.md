# Literal argument append and its interpreted extras

Paper 06, original-spine application and fixed-point equations (lines 161–174 and 244–275), append every remaining argument simultaneously to a marked state's existing extras. This component supplies the missing append algebra for that exact representation, not a new evaluator or a source correctness theorem.

1. AppendConfinement derives the unchanged source Frame type/head projections for actual appendArguments from the two original argument lists. No free-variable or normality premise is added.
2. OrderedPackedAppend equates the actual packArguments / evaluateArguments / buildArguments representation of that appended syntax to concatenation of the two actual interpreted packed lists. Every occurrence, order and duplicate is retained. The appended confinement proof is immaterial evidence; its existence is independently paid by the first target. The constructor family and typed environment remain arbitrary.
3. DownclosureAppend proves sequential downward-closure append is exactly append of concatenated full packed lists, including empty lists. No cancellation, meet preservation, extra restriction, or implicit currying is used.

These are structural suppliers for a later literal applyOriginalWith correctness proof. They do not establish that proof, arbitrary-family source structural semantics, or any whole numbered statement.
