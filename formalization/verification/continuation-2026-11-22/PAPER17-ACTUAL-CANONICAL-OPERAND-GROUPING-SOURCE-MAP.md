# Paper 17: original signed operand grouping in first-occurrence byte order

Printed anchor: `arithmetic.tex`, `thm:arithmetic` high-stratum arithmetic
comparison: the original signed counts and values are grouped by literal
operand before the greatest-class reduction. This packet supplies a
determinate ordering for that original grouping; it is not a replacement
ordering theorem for the whole compiler.

- `ActualCanonicalOperandGroupingTargets`: reverse/dedup/reverse keeps
  first source occurrences; each surviving syntactic key receives the sum
  over the complete original ordered list. Retain a key iff its total is
  nonzero. Raw keys are exactly `LowerOperandCode`, including constructor
  tag, original rank, and original iterate/ordinal bytes. `groupCheckedRaw`
  deliberately takes the result of checking original occurrences as an
  explicit Boolean; it is not a new executable reader or a proof that
  arbitrary bytes encode an admitted field.
- `EncodingProof`: injectivity of all three original operand constructors
  and the actual signed weighted pair on typed encodings, using raw note
  decode-on-encode. No injectivity or source-validity claim for arbitrary
  external tagged data.
- `TapeProof`: the executable grouping agrees literally with encoding the
  canonical typed tape; distinct retained keys, each with its true complete
  signed coefficient and exactly the old nonzero support. Relative order
  is imposed by the first occurrences, not by any claim about
  `Finset.toList`.
- `ReadProof`: check every original actual `lowerOperandRead` occurrence
  before discarding zeros or cancellations, then use unchanged genuine
  values. Failure is exactly failure of the same actual lifted reads.
  On success the complete canonical read list is a permutation of the
  checked old typed list, with its same original signed value. It is not
  asserted to be literally equal to that list.
- `ChargeProof`: actual grouped Finsupp coefficients and the original
  ranked-column natural charge are invariant under this permutation;
  the proof uses the existing actual count/value support definitions,
  with no assumption that a merely available coordinate is charged.

Gate: `LogicLineages.PermittedControl.ActualCanonicalOperandGroupingStatementChecks`.
Five exact named aliases, author-side source-only. No primitive-recursive
bound, stable-tie syntax equality, new zero successor, or order-independent
replacement/branch replay is asserted. In particular, two true equal-rank
anchors may yield different literal transferred intervals after reordering.
