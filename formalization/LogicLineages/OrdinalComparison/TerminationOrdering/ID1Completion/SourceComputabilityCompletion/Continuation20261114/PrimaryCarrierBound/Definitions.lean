module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
/-- Actual carrier union, expressed internally without constructing or
normalizing a new list, replacing the original pool, or changing its length. -/
def inCarrier {alpha : Type} (initial pool candidate : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) initial candidate ⊔ graph2 contains (numeral 1) pool candidate
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound
