# GeometricState2: nonvacuous full geometric pole equivalence

Approved direction GEOMETRIC-DESCENT-STAGING-REVIEW. Uses the actual algebraic
closure of the actual full source splitting field and the actual rationalMap
extension. supportedSimple inspects ACTUAL canonical denominator pole orders
in that algebraically closed field, not only roots visible in the finite field.
Every positive pole must equal the image of an actual complete source root;
every pole order is <=1. No splitting or partial-fraction premise is supplied.

Two targets: independent K-state iff canonical properness plus this genuine
geometric support/simple condition; independent base F2-state iff base properness
plus the condition on its actual extension. All d, zero fractions and empty root
sets included. Unrelated irreducible denominator factors cannot vanish from the
condition, since the inspection field is algebraically closed.

Proof must use checked actual canonical denominator extension, actual splitting
in the closure, full root-product/mapped root multiplicities and true polynomial
divisibility reflection through the injective field map. Base equivalence must
pay properness transport. No root-vector oracle or new caller premise.

New AlgebraicClosure import is cached but requires ordinary unchanged-cap
TARGET-ONLY preflight after scope approval and queue grant, before deep proofs.
A resource failure must be preserved, not bypassed with higher caps.
This pays geometry only; no full observer/cardinality/effectivity promotion.
