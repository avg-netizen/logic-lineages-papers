# Paper 17: effective LongField comparisons and low-strip boundary

**Status: prospective, unproved route from static inspection.** No code or
new native evidence in this packet. No amendment to record 704 or the short
preprocessing freeze. This is not the printed arithmetic theorem or a
blanket quantifier-elimination claim.

## Explicit witness extraction, without choice

The existing LongField proof constructs each existential witness explicitly.
Append strengthened lemmas using those witness expressions as bound
hypotheses; the existential result alone cannot imply correctness at a new
specific bound. Preserve the current owner proof and target. In the table
below (P=(l_p,m_p)), (Q=(l_q,m_q)) label entry fields with respective outer
iterate exponents (a,b), and (m_p'=m_p+omega(b-a)),
(m_q'=m_q+omega(a-b)), using truncated exponent differences.
Let (d_p=l_p-m_p'), (d_q=l_q-m_q'). Write
`peel(P,c)` for the existing `peelTail B lp mp c`, and
`gap(Q',P')` for the existing semantic `gapInputTail` on those
oriented peeled intervals with final argument zero.

| Fields in source order | Distinct branch, x < y | Equal-input branch |
|---|---|---|
| iterate m, iterate n | 0 | 0 |
| iterate m, entry Q | peel(Q,m) | peel(Q,m+1) |
| entry P, iterate n | max(peel(P,0), peel(P,n−a)) | peel(P,n+1) |
| entry P, entry Q | max of peel(P,b−a), peel(Q,a−b), inverseTableTail(lp,mp',mq',dq,B), gap(Q',P') | max of the two peeled tails, both oriented gap tails, equalGapCertificateTailCode(mp',mq',dp,B) |

Prove each strengthened statement with the corresponding local argument
from `FieldComparisonProof.lean`; in particular keep the orientation of
the inverse table and equality certificate. Reverse the distinct branch by
swapping the fields and reversing the comparison, retaining the parameter
field at the now-smaller coordinate. The all-large wrapper must include
both original short preprocessing tails, the selected normalized comparison
bound, and any order-specific guard. Retain the original actual-value
semantics when substituting the normalized fields.

## Exact raw effectivity

- Make an explicit raw code for the normal monomial `ω*c` (zero when
  `c=0`, otherwise a single node with exponent code of one, positive
  coefficient and zero remainder). Calibrate its literal and ordinal
  meanings using normal-form uniqueness and the existing
  `omegaMultiple_repr`/`peeled_repr`. Do not treat ordinal multiplication
  as an executable oracle.
- Use `ordinalAddCodeEffective` and `ordinalSubCodeEffective` from
  `OrdinalEndpointProgramsProof`, and
  `ordinal_add_note_code`, `ordinal_sub_note_code`, `normal_norm_code`
  from `ThresholdNoteCodeProof` to build and calibrate the peeled endpoints,
  differences, norm bounds and partner interval. These are static supplier
  identifications, not newly checked compositions.
- `normal_encoded_gap_tail` and `inverseTableTailCode_correct` from
  `ThresholdTailBridgeProof` bridge the encoded and semantic tails.
  `gapInputTailEffective` supplies a computable gap bound; for Primrec,
  compose the elementary max/add/mul raw-norm expression already used in
  `ThresholdNumericProgramsProof`. That module also supplies
  `inverseTableTailCode_primrec`. Use
  `equalGapCertificateTailEffective` for the equal-gap tail.
- For the form itself, return a tagged fixed answer or tagged table sign and
  parameter field code. Use `rawComparisonPrimitiveRecursive` and
  `rawComparisonOrdinalCorrect` for gap order,
  `equalGapCertificateSignEffective` for the sign, and raw ordinal
  addition for the selected partner endpoint `mp'+dq`. Calibrate against
  the actual form constructors and use `FormWellFormed` for parameter
  properness. A proper parameter need not be long. This is a syntactic
  compiler: it does not evaluate the selected lower-input field or vary
  its raw argument independently.

## Mixed low/high strips are not covered

The bound above concerns only the all-large branch. The rest of the
arithmetic proof (arithmetic.tex, “Residues, finite strips, and one-variable
projection”) enumerates every admissible below-cutoff value of one
coordinate, substitutes that same value into every occurrence, keeps true
definedness flags and domain guards, and leaves all other coordinates
unbounded. This is a finite family of potentially infinite strips, not a
finite cube. It needs a separate exact closed-evaluation supplier and
smaller-dimensional recursion; a cutoff based only on comparison bounds
does not pay either obligation.

`fixedEntryProgram` and `entrySearchWith` are partial; correctness of
successful hits and on-tail domain do not decidably report low-input
misses. A concrete future route is to use `terminalSearchWith` and the
normal-code termination in `EncodedEvaluatorProof` to obtain the first
finite state, then scan the actual exact entry predicate through that state
*inclusively*. Encoded finite states are absorbing. Thus a positive target
not seen by the terminal state is a genuine miss, while a zero target can
first be hit there. The proof must connect `canonicalInitialCodeCorrect`,
encoded-state calibration and the actual `FirstEntry` predicate, retain
true source guards and handle all relevant closed fields; an arbitrary
fallback for partial search would not suffice. No such new evaluator or
strip theorem is proved here.
