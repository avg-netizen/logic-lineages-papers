# Outer fuel and actual source-HB gap audit

Read-only review after the fresh core-MP source packet,13 November2026.
No source HB2/HB3 or numbered completion is claimed.

* `SixSol20261112/Fuel/Definitions.lean`: actual verifier is a bounded OR of
  `isOne(core(index,t,context,formula,cert))`, not merely core at the outer bound.
* `Fuel/Targets.lean`: NativeSaturation is an external natural-number theorem.
  Existing internal OpenStep/OpenIncrement/OpenMonotonicity only preserve
  OUTER acceptance; they do not extract the core witness or prove core monotonicity.
* `SixSol20261113/LiteralCoreMP/Targets.lean`: core MP requires SAME actual core
  fuel for both input core acceptances. Internal extraction from two outer
  acceptances can yield DIFFERENT core fuels. Raising both outer bounds does not
  equalize these inner fuels. Native calibration of an existential axiomProgram
  cannot supply an internal core/axiom-leaf fuel-monotonicity theorem.
* `GorbowPublishedDCBDefinitions.lean`: prD is PrS(rho->sigma).
  `SourceBaseCompletion/SelectedVerifierTargets.lean` requires original internal
  hb2 and hb3 for the same presentation. Raw MP on sigma->tau and sigma alone
  does not match rho->(sigma->tau),rho->sigma. A certified propositional
  distribution-tautology/certificate transformation remains necessary too.

The smallest independent honest next packet is the proposed generic actual
Fuel.verifier internal extraction AND injection at a bound: acceptance iff an
internally existential t with additive-gap order t<=fuel makes the SAME exact
core AST return1. Arbitrary q0, no core Boolean/monotonicity/calibration premise;
isOne pays the Boolean normalization. This is not outer MP closure. Later work
still needs a genuinely monotone literal axiom/core supplier or a heterogeneous-
fuel certificate construction, plus rho transport and the separate HB3 route.

Definitions/Targets/Preflight only have been proposed; no proofs yet.

## Constructive next route reviewed at20:17 UTC

Do not infer internal monotonicity for the old existential axiom leaf from its
native calibration. Instead, the separately frozen SaturatedAxiomLeaf packet
wraps the old three-input axiom program in the already explicit bounded-search
Fuel.verifier. The lifted core ignores context/formula and takes index,fuel,line;
the wrapper supplies literal zeros for unused fields. Its native all-vector
calibration must be proved from actual external axiom-evaluator monotonicity,
while its internal monotonicity is proved independently from the literal
saturated AST for arbitrary input programs. A future rebuilt source tuple must
use that actual wrapper. Dispatcher acceptance transport, successful iterator
and core fuel transport, common-bound combination, and source implication
construction remain additional obligations. No old tuple identification is
licensed by this route.
