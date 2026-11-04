# Original finite marking: structural calibration and primitive recursion

Paper06, lines 537–546, includes marking from an ordinary head to any finite
label and uses marked arguments in the Mul rule. The immutable implementation
is `NumberedRewriteReduction.finiteMark`; its packed interface is
`NumberedMarkCertificate.markTarget`. The source manuscript SHA256 is
`bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.

The three targets in `NumberedFiniteMarkPrimrecTargets` state exact structural
calibration for every typed term and primitive recursion of the raw and packed
operations. The latter results fix only the explicit finite signature, arity
and context; the natural label and source remain joint inputs, including the
empty signature. The calibration itself permits an arbitrary symbol type.

`finiteMarkCode` propagates through every initial lambda. At the first ordinary
head it retains the original head, result and base list, inserts the requested
label, and supplies empty extra types and arguments. Variables, applications,
bottom and numbered heads fail. Label zero is included. This is the original
partial marking used by replacement witnesses, including marking below binders.

The proof uses the accepted immediate-child list and strictly decreasing
`codeNumber` rank to establish primitive recursion on every raw code. Exact
typed calibration and the accepted packed reconstruction lemma then establish
primitive recursion of the actual `markTarget` under its genuine presentation.
All correctness and effectivity suppliers are proved; the target adds no
oracle or correctness premise.

The definitions and targets were compiled and frozen before candidate proof
authoring in `ROOT-EFFECTIVITY-FREEZE.json`, using bounded comparator receipt
`1793763176589684697-2`. Their SHA256 values are respectively
`34db76c92eb9c1558c6b6a27b80f41caa453d200a724c3a527f039550fe83f51`
and `fa3df21b4d58073dc2e2d2c341b5d4c066500c1013a0c110eae1194b8bfc4a03`.
This supporting component discharges marking effectivity; it leaves the
paper's full arithmetic representation and accessibility obligations separate.
