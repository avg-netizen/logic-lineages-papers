# Exact signed fixed-translate separation for the actual Phi

Subject label: `SignedPhiSeparation4`. Source: `08-multivariate-collapse-comparison/paper.tex`, proof of `thm:snyatkov`, lines 171–185. The literal control is defined at lines 94–100, and its required growth inequality is at lines 102–117. Source SHA-256: `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This target draft follows root's verified `SignedShiftCollection4` checkpoint 42, commit `778ed582`. It edits no accepted supplier.

This component pays the actual finite shifted-sign calculation for the already defined `Phi n = fastControl 5 (n+100)`. It quantifies every finite `List (Int × Int)` of original coefficient/shift occurrences, without a bound on length or integer magnitude. Duplicate shifts, zero coefficients, cancellation at any shift, an empty row, and complete cancellation are all retained in the semantics. There is no supplied growth function, assumed separation theorem, chosen extremum, or arithmetic decision oracle. The published quantified Snyatkov theorem and the BASE decision supplier remain PENDING; no numbered whole theorem is promoted.

## Original semantics, domain, and the exact source delta

`Row` is exactly `SignedShiftCollection.Row`. The actual original sum is

`value row t = (row.map (fun a => a.1 * (Phi (((t : Int) + a.2).toNat) : Int))).sum`.

It is a total natural-input function because `Int.toNat` supplies an off-domain extension. This extension is not used to weaken the original domain: `ExactSourceShiftAndArguments` proves nonnegativity and the exact integer value of the argument at **every original occurrence** when `t = x + delta row`, for **every natural x**. It also identifies the argument with `x + (delta-D) + rebaseKey row b`, so collection is evaluated at the original argument, not at a truncated replacement. `originalArguments` and `shiftedArguments` preserve occurrence order and multiplicity, including the arguments of zero-coefficient and subsequently cancelled occurrences.

The existing `SignedShiftCollection.domainOffset` is reused unchanged as `D`. The first target explicitly repeats its exact least-offset characterization:

`D ≤ d ↔ ∀ a ∈ row, 0 ≤ (d : Int) + a.2`, for every natural `d`.

For a nonempty original row with least original signed shift `m`, this is exactly `D = max(0,-m)`. No new minimum algorithm is introduced. The proof target separately requires the exact integer identity, whenever the collection is nonempty:

`(delta row : Int) = max (D : Int) ((A : Int) + 1 - B)`.

Together these are precisely the displayed source formula `max(0,-min ORIGINAL shift,A+1-B)`. This is the permitted least-offset/integer-max formulation of that formula, not a merely sufficient inequality. The literal definition is `max D ((A+1-B).toNat)`; the cast identity explicitly proves that natural truncation has not enlarged or altered the integer maximum. In particular, the domain bound still sees an occurrence at a negative shift even if its coefficient is zero or its entire block cancels. A cancelled original shift greater than the surviving leader also remains an occurrence but does not determine `B`.

The original empty row has `D=0` by its accepted definition. Every empty **collection**, including a nonempty row that completely cancels, instead takes the expressly defined branch `delta=D`. No minimum or leading-survivor assertion is made for this case. Its actual shifted value is zero in the second target.

## Exact A and actual leading block

`collected row`, `greatestKey row`, `greatestShift row` and `leadingCoefficient row` are the accepted literal algorithms, unchanged. Write their signed greatest surviving shift as `B` and their actual leading block coefficient as `a_B`. The accepted nonempty-support theorem proves this block is present, nonzero, and greatest, with original-occurrence provenance.

`lowerRow row` is **exactly** `(collected row).filter (fun a => decide (a.2 < greatestKey row))`. `lowerMass row` is the sum of the absolute integer coefficients of this strict lower row. Accepted order preservation and complete collected support identify this number with the source's `A = sum_{b<B} |a_b|`. It excludes the leading block and uses the combined block coefficients, not individual original coefficients. It is not the full collected mass, original occurrence mass, or a larger bounding substitute.

`ExactEvaluationAndCancellation` requires literal equality between the original shifted sum and the actual collected `Phi` evaluation. It then proves the all-cancelled value is zero. Under nonempty support it gives the exact split into the actual leading term and the `lowerRow` remainder. This fixes both the evaluator and the row; there is no new arbitrary-function premise.

## Narrow growth proof route

The inspected accepted `ControlHierarchyGrowthProof.lean` exports `fullFastControlHierarchyGrowth`. Its final conjunct is exactly `(A+2)*Phi z ≤ Phi(z+1)` for natural `A≤z`. The inspected `Control.lean` exports `Phi_strictMono` and `self_lt_Phi`; these provide monotonicity and positivity. Do not replace these by the different constants in `CommonHeadLargeRowNumericalProof`, or import that broad dominance development as a supplier.

For nonempty support, the exact delta yields `z = (x+delta+B-1).toNat ≥ x+A`, with exact integer reconstruction. The leading argument is `z+1`; every strict lower surviving argument is at most `z`. Elementary finite-list absolute-value bounds give an absolute remainder bound `A*Phi z`. A positive integer leading coefficient is at least one, and a negative one has magnitude at least one. The accepted growth inequality then yields `S(x+delta) ≥ 2*Phi z > Phi x` or `S(x+delta) ≤ -2*Phi z < -Phi x`, respectively. Those inequalities, for every natural x, are the third target. All-cancelled rows have the zero result rather than a fictitious leading sign.

The strict comparison with `Phi x` implies the expected corresponding unboundedness using `x < Phi x`; this slice does not introduce a separate registered unboundedness or sign-classifier target. It does not claim the full published arithmetic decision procedure.

## Uniform effectiveness of these actual algorithms

The fourth target includes the accepted nine-part `SignedShiftCollection.Targets.UniformPrimitiveRecursiveData` itself, paying the original-domain offset, rebasing, literal collection, greatest key/shift, and leading coefficient. It additionally requires primitive recursion of `lowerRow`, exact `lowerMass`, exact `delta`, the original argument and value functions, `shiftedInput`, `rebasedInput`, both original/shifted argument lists, and the composite actual shifted value.

The programs candidate can reuse `SignedShiftCollection.Proof.uniformPrimitiveRecursiveData` and its named component theorems from `SignedShiftCollectionProgramsProof.lean`, `LogicLineages.OrdinalComparison.Phi_primrec` from `ControlComputability.lean`, and the accepted integer primitives in `LayeredComparison/IntegerAlgorithmsProof.lean`. Natural-key filtering, sums, zero/empty tests, comparison, maximum, subtraction, and map composition are finite primitive-recursive operations under the standard integer/pair/list coding. No concrete huge `Phi` value need be evaluated. This proves uniform effectiveness of the displayed data and evaluation maps, not decidability of quantified arithmetic.

## Four exact targets and prospective candidate files

1. `ExactSourceShiftAndArguments` / `exact_source_shift_and_arguments`: the exact original least domain, exact integer-max delta, all-cancelled branch, and every original argument at every natural shifted input.
2. `ExactEvaluationAndCancellation` / `exact_evaluation_and_cancellation`: original/collected equality, all-cancelled zero, and exact leading/lower decomposition.
3. `ActualSignedPhiSeparation` / `actual_signed_phi_separation`: the two strict inequalities against the actual `Phi x`, according to the actual leading coefficient's sign.
4. `UniformPrimitiveRecursiveData` / `uniform_primitive_recursive_data`: primitive recursion of all the displayed finite data and actual evaluation/argument maps.

Prospective candidate files, all ABSENT during this target draft:

- `LogicLineages/OrdinalComparison/SignedPhiSeparationDomainProof.lean`: exact delta cast, least-domain reuse, and all-original argument identities.
- `LogicLineages/OrdinalComparison/SignedPhiSeparationEvaluationProof.lean`: exact accepted-collection transport, cancellation, and leading/lower decomposition.
- `LogicLineages/OrdinalComparison/SignedPhiSeparationGrowthProof.lean`: finite remainder bound and actual strict signed separation using the narrow accepted growth theorem.
- `LogicLineages/OrdinalComparison/SignedPhiSeparationProgramsProof.lean`: primitive recursion of the literal finite data and actual Phi evaluation/maps.
- `LogicLineages/OrdinalComparison/SignedPhiSeparationProof.lean`: thin aggregate of those four obligations.

Definitions and targets import no candidate proof. The prospective statement checks bind only these four exact target aliases. Only `propext`, `Classical.choice`, and `Quot.sound` may appear in accepted axiom closures. No `sorry`, `admit`, added axiom, `native_decide`, evaluator oracle, weakened source domain, enlarged A/delta, or whole-theorem promotion is permitted.

This is a draft for root review, not a comparator receipt or freeze. Candidates must remain absent until root exact-target approval, comparator acceptance and prospective freeze. This step invokes no compiler, authors no candidate, edits no accepted/frozen supplier, and performs no Git operation.
