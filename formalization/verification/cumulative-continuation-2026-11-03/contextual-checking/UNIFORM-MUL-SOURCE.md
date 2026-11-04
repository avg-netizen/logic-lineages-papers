# Context-uniform unguarded original Mul-selector checking

The four targets concern the original Mul branch of
`NumberedNumericRoot.selectorTest`, whose typed decision is
`NumberedMulCertificate.mulCertificateTest`. In the original `stepTest`, focus
under lambdas changes `holeGamma`; its certificate decoder must therefore
compute uniformly in that varying context. The relevant source is paper06's
all-Mul auxiliary reduction and arithmetic relation discussion, lines 537–556,
with manuscript SHA256
`bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.

The raw root test retains the original positive source label, ordinary target,
result-type equality, head equivalence and target head window. It extracts
both base argument spines strictly and passes their ordered type/code pairs
to the calibrated raw multiset test. Source extra types and arguments remain
in the source and are not included in the base-list comparison. Calibration
equals the original typed test for every actual packed source, target and
certificate, without window closure or endpoint-membership assumptions.

`mulTest` decodes the original numeric certificate in the supplied context and
then evaluates that raw root test. Its exact calibration is
`decodeCertificate.any (mulCertificateTest ... q r)` for every context, typed
endpoint pair and certificate natural. This is the unguarded selector leaf:
it adds no `decodeUniverse` or source-universe condition. Primitive recursion
varies the symbol/type windows, context, both raw endpoint codes and numeric
certificate jointly. Signature size and arity are explicit fixed parameters.

Definitions and targets were compiled and frozen before candidate proof
authoring in `CONTEXTUAL-EFFECTIVITY-FREEZE.json`, comparator receipt
`1793765185672810400-2`. Their respective SHA256 values are
`2460b91fc89e3ee6c81853aa7ff8f13f280e842a7dca375a1f49449e1b00d06d`
and `728123e3daec45a88fccb884a438e679563920f53d895aa668987ddb422ed3f2`.
The component supplies the actual Mul branch at `focus.holeGamma`; complete
selector, step, edge/path checking and arithmetic formula representation
remain separately calibrated obligations.
