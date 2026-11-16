module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTypedDecoderInternalAcceptance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The actual variable branch of original source Fields coverage. All metadata
other than the observed original context length remains arbitrary. Neither raw
validity nor the index bound is supplied: both must be derived internally from
the actual constructor and actual typed acceptance. No window/image/native
calibration premise is present, including for n = 0 and empty contexts. -/
def InternalVariableFields : Prop := ∀ (n : Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (typ raw index gamma count types heads labels tupleBound : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)) →
  Nonempty (Derivation body Delta (TermAccepted H typ raw gamma)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) →
  Nonempty (Derivation body Delta
    (OriginalEnumerationFields.Targets.accepted n raw count types heads labels tupleBound))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.Targets
