module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixValueTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual uniform prefix executions have a unique entire produced row even
at incomparable symbolic counts. No admission or length premise is supplied. -/
def ActualProducedAgreement : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (tagged first second left right : OTerm alpha),
 Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged first left)) →
 Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged second right)) →
 Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn left right))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixValueTargets
