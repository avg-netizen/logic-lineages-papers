module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecTargets
@[expose] public section
/-! Original application endpoint-leaf representability.

The function and calibration relation are the unchanged endpointValue and
EndpointCalibrated from InternalApplicationStepPeel. No replacement decoder,
checker, packed representation, universe predicate or calculus is introduced.
Inputs are [domain,codomain,function,target,argument]. Source and argument
use the original decodeUniverse; target uses ordinary decodePackedNumber.
Domain and codomain use decodeType. Their successful outputs must satisfy
both arrow-type equalities, argument-domain equality and literal tau membership
in S. Every failed decoder or guard returns zero. S is arbitrary.

This component establishes external primitive-recursive representability and
existence of a calibrated Program 5 for each fixed signature, window and Gamma.
The witness may be obtained through the original allPrimitiveFunctions theorem.
It supplies no exposed decoder AST, internal endpoint acceptance derivation,
original typed invariant, representative congruence or CertifiedApplicationLift.
-/
