module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalTypedDecoderInternalAcceptance
open OriginalRawSyntaxTransportInternalVariableSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem decoder (H : Program 1) (typ raw index gamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)))
    (ht : Nonempty (Derivation body Delta (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Delta (OriginalVariableDecoder.graph (suc z) typ index gamma)) := by
  have he := OriginalTypedDecoderInternalAcceptanceLeafProof.variableIff H raw index typ gamma
    (variableConstructorPair raw index hc)
  exact ⟨Derivation.implicationElimination (Classical.choice (andLeft he)) (Classical.choice ht)⟩

theorem fieldsFromIndex (n : Nat) (raw index count types heads labels tupleBound : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)))
    (hi : Nonempty (Derivation body Delta (InternalLessThan.strictLess index count))) :
    Nonempty (Derivation body Delta
      (OriginalEnumerationFields.Targets.accepted n raw count types heads labels tupleBound)) :=
  (OriginalEnumerationFields.LeafProof.internalVariable n body alpha Delta raw count types heads labels tupleBound index hc).mpr
    (andIntro (OriginalEnumerationValidity.LeafProof.variableValid n raw index hc) hi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AcceptanceProof
