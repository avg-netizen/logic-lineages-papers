module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalParametersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRawParametersProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open OriginalStructuralNodeSizeInternalMachineCompletion (fold)
open OriginalStructuralNodeSizeInternalLeafProof (rawFromFold)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawToFold (input out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw out input))) :
    Nonempty (Derivation body Delta (graph3 fold out z z input)) := by
  apply programCases fold (Fin.cons z (Fin.cons z (Fin.cons input Fin.elim0))) _
  intro beta j Theta produced hj hp
  simp only [graph3Rename,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hp
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hraw := rawFromFold (input.relabel j) produced hp
  exact outputTransport fold produced (out.relabel j) ![z,z,input.relabel j]
    (valueUnique OriginalStructuralNodeSize.raw produced (out.relabel j) ![input.relabel j] hraw hr') hp

/-- Genuine internal parameter independence is used here before comparing a
lambda child's shifted cutoff with the public raw zero-cutoff interface. -/
theorem rawAtParameters (input out d k : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw out input))) :
    Nonempty (Derivation body Delta (graph3 fold out d k input)) :=
  OriginalRawSyntaxTransportInternalParametersBindingProof.atRawApply fold true input out z z d k
    (OriginalStructuralNodeSizeInternalParametersProof.allRawParameters true input) (rawToFold input out hr)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRawParametersProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRawParametersProof
