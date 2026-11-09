# Exact encoded stage program

The frozen R004 target computes `stage D maximum r |>.map encodeBranch` on
all numeric inputs. Source values and guard truth never occur as program
inputs. No Primcodable/Encodable instance for semantic Formula is needed:
formula constructors are computed directly at their actual numeric codes.

The guarded source program composes the already accepted total
`FullWordGuardCompletion.compile` with original-name row renaming, literal
sign encodings, exact disjunction/conjunction code folds and actual tails.
`AlgorithmGuardProgramsProof` supplies those exact encoded guard and cutoff
computability claims. Its first native run passed the narrow bounded list
fold/map supplier and refreshed every accepted guard-program dependency;
proof-only encoding/Bool/import repairs are centrally queued. The generic
fold proof is the existing bounded-fold recipe, reproduced narrowly to avoid
the broad comparison-assembly source closure.

`AlgorithmBaseProgramsProof` (uncompiled candidate) gives primitive recursive
original-row normalization, zero filtering, active/linear extraction,
actual head/dropLast projections and original leader/preimage constructors.
Last-letter projection uses the literal reverse/head option equation; it
does not evaluate source functions. Remaining finite residual construction,
class/label enumeration, tails and actual branch encoding are composed from
these finite source-data operations, with the checked pair compiler the only
non-primitive-recursive supplier.

The following R005 numeric stack will operate on `EncodedState` directly.
Guard conjunction codes are combined as `6*pair left right+4`; no formula
decoder or guard consistency test is needed. The finite run is calibrated by
fuel induction to `encodeState (run ...)`. Actual all-input termination,
proved from the intrinsic current-row histogram, then removes the total
notation fallback from leastFuel and permits genuine Computable minimization.
These construction details are the proof path, not accepted results.
