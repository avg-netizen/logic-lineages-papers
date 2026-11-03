# Literal signed-shift collection and domain rebasing

Subject label: `SignedShiftCollection4`. Source: `08-multivariate-collapse-comparison/paper.tex`, proof of `thm:snyatkov`, lines 171–185, especially equal-shift collection at 171–174, greatest surviving shift at 174–178, and original-domain safety at 179. Source SHA-256: `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This bounded exact-target draft follows the verified `FixedSeedControlResidue` checkpoint `baa913603f944a8f81f4025af11a36a28ac5d30b` (174 checked; Space version 78). No accepted supplier is edited.

The source starts with a finite integer combination of actual integer translates, `S(x) = sum_b a_b f(x+b)`. This component pays only the finite input-data operations preceding the growth/sign calculation: preserve the original domain, combine equal signed shifts, remove zero blocks, and compute the largest surviving signed shift with its actual coefficient. All finite input rows and all integer coefficients/shifts are quantified; there is no fixed size or magnitude bound and no effectiveness premise. The eventual sign-separation theorem, its exact delta, and the quantified Snyatkov/BASE decision supplier remain separate and PENDING. No numbered whole theorem is promoted.

## Literal integer input and original-domain offset

`Row := List (Int × Int)` stores each original `(coefficient, shift)` occurrence. Both coordinates really are integers. In particular, negative shifts are not omitted, interpreted as naturals, or replaced with an unordered encoding.

`domainOffset row = (row.map (fun a => (-a.2).toNat)).foldl max 0` computes `D` from **every original occurrence before collection**. Zero-coefficient occurrences and all occurrences in a block that later cancels still contribute to the original domain constraint. The empty-row value is exactly zero. For example, a zero-coefficient occurrence at shift `-7` still forces `D ≥ 7`; cancelling coefficients at that shift cannot remove the requirement. Such examples describe the literal definition, not additional accepted checks.

`OriginalDomainAndRebasing` proves the exact least-offset characterization: for every natural `d`, `D ≤ d` if and only if `d+b ≥ 0` for every original occurrence. It also proves nonnegativity of every original argument `x+D+b` for every natural `x`, the equality `(x + rebaseKey row b : Int) = x+D+b`, and reconstruction of every original signed shift. This is the original expression's domain, not only the surviving support's domain.

The key is `rebaseKey row b := (D+b).toNat`. On original shifts, the nonnegativity just proved makes this literal translation, with no truncation loss. Its inverse is explicitly `originalShift row k := (k : Int)-D`. Equality, weak order, and strict order of original shifts are all equivalent to equality, weak order, and strict order of their keys. Thus a maximum key corresponds to the actual largest signed shift. No order property of `Encodable.encode Int` is used. The total extension of `rebaseKey` to integers absent from the row may truncate and is **not** claimed globally injective.

This least-offset characterization preserves exactly the domain contribution `max(0,-min b)` in the source's later displayed delta for a nonempty original row. No delta is defined here. In particular, this component does not replace the source's exact `max(0,-min b,A+1-B)` with a larger bound. The later component must retain that exact maximum and separately establish the growth inequalities.

## Reuse of the literal accepted collector

`rebaseRow` maps every original occurrence to `(coefficient, rebaseKey row shift)`, with unchanged coefficient. `collected row` is **exactly** `CommonHeadCollectedRow.collect (rebaseRow row)`. The accepted collector takes deduplicated natural keys, computes each key's signed coefficient sum, and filters zero coefficient blocks. Its definitions and proofs remain unchanged. This is not a new unspecified collection relation, a chosen representative list, or an oracle-supplied normalization.

The separate definition `coefficient row b` is the literal sum of original coefficients whose integer shift equals `b`. `ExactCollectionAndSupport` requires:

1. Exact weighted equality for every evaluator `Int → Int`, using `originalShift` to interpret the collected keys.
2. Exact equality for every evaluator `Nat → Int` at every safely rebased input `x+D`: the collected evaluator receives `x+key`, and the original evaluator receives `(x+D+b).toNat`. The domain target proves that this conversion is exact on every original occurrence.
3. Pairwise distinct collected keys and, for every output block, a nonzero coefficient equal to the **original signed-shift** coefficient sum, plus original-occurrence provenance and its exact rebase key.
4. Complete support: an original signed block coefficient is nonzero if and only if a collected key interprets to that signed shift, for every integer shift. The row is empty after collection exactly when every signed block sum is zero.
5. The collected absolute coefficient mass is at most the original occurrence mass.

The accepted narrow supplier `CommonHeadCollectedRowAlgebraProof.lean` already proves `Proof.exactWeightedCollection` and `Proof.literalCollectedSupport` for the actual natural-key collector. It imports only its targets and elementary list sum/dedup/pairwise support. The new algebra candidate transports those results through the proved signed rebase and proves the remaining signed block/completeness statements by finite list algebra. It must not import the broad actual ordinal dominance proof or assume the desired signed block identity.

## Actual greatest survivor

`greatestKey row` is the finite `foldl max 0` of the actual collected keys. `greatestShift row` applies the explicit inverse, and `leadingCoefficient row` is the actual original signed block sum at that shift.

`ActualGreatestSurvivingShift` has the essential premise `collected row ≠ []`. It proves that the computed `(leadingCoefficient, greatestKey)` is an actual collected member, its coefficient is nonzero, every collected key is at most this key, an original occurrence has the computed signed shift, and every nonzero original signed block is at most this signed shift. No largest *original* shift is substituted after cancellation. A larger original shift whose coefficients cancel is allowed and does not become the leader. Empty and all-cancelled rows have total numerical defaults but no assertion that these defaults are surviving shifts.

## Uniform effectiveness of the actual algorithms

`UniformPrimitiveRecursiveData` requires actual `Primrec`/`Primrec₂` proofs for `domainOffset`, `rebaseKey`, `originalShift`, `rebaseRow`, `collected`, `coefficient`, `greatestKey`, `greatestShift`, and `leadingCoefficient`, under the existing standard public integer, pair and list coding. No encoded integer order is used as signed order, and no primitive-recursion hypothesis is passed in.

The narrow accepted supplier `LayeredComparison/IntegerAlgorithmsProof.lean` provides actual integer cast, negation, addition, multiplication, absolute value and sign primitive-recursion theorems. In particular, a local proof of `Primrec Int.toNat` can use its exact equality to `if Int.sign z = -1 then 0 else Int.natAbs z`, checked by integer constructor cases. No change to that accepted supplier is authorized.

`Mathlib.Computability.Primrec.List` provides list map, folds, recursion, filter, and ordinary coding operations. The current collector has no accepted primitive-recursion theorem, so the programs candidate must prove effectiveness of its **literal** implementation. Natural membership is a finite equality test (or index/length comparison), dedup is a finite fold/recursion with that test, signed sums use the accepted actual addition operation, and the zero filter is finite equality. These are bounded scans of the input data, not searches for mathematical witnesses. Actual primitive recursion of the whole rebased collector follows by composition, rather than replacing the collector with an extensionally unspecified routine. Greatest-key computation is the displayed finite maximum fold.

## Four exact targets and prospective candidates

1. `OriginalDomainAndRebasing` / `original_domain_and_rebasing`: exact original offset, all-input domain safety, reconstruction, and order preservation.
2. `ExactCollectionAndSupport` / `exact_collection_and_support`: the two evaluator identities, signed coefficient sums and complete literal support, zero cancellation, distinctness, and mass bound.
3. `ActualGreatestSurvivingShift` / `actual_greatest_surviving_shift`: the computed actual leading block and largest signed survivor under nonempty support.
4. `UniformPrimitiveRecursiveData` / `uniform_primitive_recursive_data`: effectiveness of the displayed algorithms themselves, without supplied programs or oracles.

Prospective candidate files, all ABSENT during this draft:

- `LogicLineages/OrdinalComparison/SignedShiftCollectionDomainProof.lean`: original domain and signed/natural rebase arithmetic, using finite maximum/list facts.
- `LogicLineages/OrdinalComparison/SignedShiftCollectionAlgebraProof.lean`: signed transport of the accepted elementary collector results, complete support, and mass.
- `LogicLineages/OrdinalComparison/SignedShiftCollectionGreatestProof.lean`: actual finite maximum membership and signed leading block.
- `LogicLineages/OrdinalComparison/SignedShiftCollectionProgramsProof.lean`: primitive recursion of the actual finite algorithms using the accepted integer primitives and standard list operations.
- `LogicLineages/OrdinalComparison/SignedShiftCollectionProof.lean`: thin import/export aggregation of the four obligations.

Definitions import only the accepted collector definitions. Targets add only the standard primitive-recursion/list interface and import no candidate. Accepted axiom closures may use only `propext`, `Classical.choice`, and `Quot.sound`. No proof of Phi sign separation, unboundedness, the delta inequalities, published quantified arithmetic decidability, or a whole balanced comparison statement is claimed or assumed here.

This is an exact-target draft for parent/root scope review. No comparator or prospective freeze has run. Candidates must stay absent until root approval, comparator acceptance and prospective freeze. This step performs no proof/candidate authoring, compiler invocation, accepted/frozen-file edit or Git operation.
