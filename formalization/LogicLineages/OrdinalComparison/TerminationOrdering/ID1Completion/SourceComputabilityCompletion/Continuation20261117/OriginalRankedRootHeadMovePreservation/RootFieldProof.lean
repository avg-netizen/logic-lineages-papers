module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootAllowedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootFieldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ordinaryFields (raw head base : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base))) :
    Nonempty (Derivation body Delta (graph1 (leftOf (.projection 0)) (numeral 4) raw)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) head raw)) ∧
    Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) base raw)) := by
  have ht := ordinaryTag (.projection 0) raw head base ![raw] (projectionValue 0 ![raw]) hc
  have hh := ordinaryHead (.projection 0) raw head base ![raw] (projectionValue 0 ![raw]) hc
  have hhead := branchNumeralIntro 4 5 (leftOf (.projection 0))
    (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf (.projection 0)))) head ![raw] ht hh
  exact ⟨ht,hhead,andLeft (andRight (OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof.ordinaryFields raw z head base hc))⟩

theorem numberedFields (raw label head recorded base extraTypes extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras]))) :
    Nonempty (Derivation body Delta (graph1 (leftOf (.projection 0)) (numeral 5) raw)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) head raw)) ∧
    Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) base raw)) := by
  have ht := numberedTag (.projection 0) raw label head recorded base extraTypes extras ![raw] (projectionValue 0 ![raw]) hc
  have hh := numberedHead (.projection 0) raw label head recorded base extraTypes extras ![raw] (projectionValue 0 ![raw]) hc
  have hhead := branchNumeralIntro 5 5 (leftOf (.projection 0))
    (leftOf (rightOf (.projection 0))) (leftOf (rightOf (rightOf (.projection 0)))) head ![raw] ht hh
  exact ⟨ht,hhead,andLeft (andRight (OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof.numberedFields raw label head recorded base extraTypes extras hc))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootFieldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootFieldProof
