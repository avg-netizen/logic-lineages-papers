module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalFoldLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalParametersLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParameters
open OriginalStructuralNodeSizeInternalFoldLeafProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem leafParameters (rank : Bool) (raw out d k other otherK : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z raw)))
    (h : Nonempty (Derivation body Delta (graph3 OriginalStructuralNodeSizeInternalMachineCompletion.fold out d k raw))) :
    Nonempty (Derivation body Delta
      (graph3 OriginalStructuralNodeSizeInternalMachineCompletion.fold out other (if rank then otherK else k) raw)) := by
  have hl := leafForward d k raw out ha h
  have he := valueUnique (constant 3 1) out (suc z) ![d,k,raw] hl (constantValue 1 ![d,k,raw])
  obtain ⟨he⟩ := he
  exact leafBackward other (if rank then otherK else k) raw out ha
    (outputTransport (constant 3 1) (suc z) out ![other,if rank then otherK else k,raw]
      ⟨symm he⟩ (constantValue 1 ![other,if rank then otherK else k,raw]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalParametersLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalParametersLeafProof
