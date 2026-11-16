module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.IndexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.VariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalUniverseDecoderInternalAcceptance
open InternalApplicationStepPeelSupportProof (andLeft andRight)

theorem atConstructor (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw index typ gamma context count types heads labels tupleBound : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)))
    (ha : Nonempty (Derivation body Delta (TermAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.accepted n raw count types heads labels tupleBound)) := by
  have hi := OriginalUniverseDecoderTransportLeafAcceptanceProof.variableIff H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) raw index typ gamma context hc
  have hp := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice ha)
  have hb := OriginalVariableFieldsCoverage.IndexProof.bound typ index gamma count
    ⟨Derivation.conjunctionRight hp⟩ hl
  exact OriginalVariableFieldsCoverage.AcceptanceProof.fieldsFromIndex n raw index count types heads labels tupleBound hc hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.VariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.VariableProof
