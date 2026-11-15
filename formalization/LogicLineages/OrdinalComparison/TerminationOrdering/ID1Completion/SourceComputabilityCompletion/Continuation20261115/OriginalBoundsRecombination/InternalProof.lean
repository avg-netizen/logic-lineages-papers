module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalVariableSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
attribute [local irreducible] programGraph

theorem internalNil : Targets.InternalNil := by
  intro body alpha Delta
  exact InternalRawListRecursionProof.nilValue (OriginalRawSyntaxTransport.constant 0 0) merge
    (numeral 0) Fin.elim0 (constantValue 0 Fin.elim0)

theorem internalCons : Targets.InternalCons := by
  intro body alpha Delta raw head tail tailValue out hc hr
  constructor
  · intro ho
    apply programCases merge (Fin.cons head (Fin.cons tailValue Fin.elim0)) _
    intro beta j Theta value hj hv
    rw [graph2Rename]
    simp only [consTermRename,emptyRename] at hv
    have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
    rw [graph2Rename] at hcj
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    rw [graph1Rename] at hrj
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph1Rename] at hoj
    have hval := InternalRawListRecursionProof.consValue (OriginalRawSyntaxTransport.constant 0 0) merge
      (raw.relabel j) (head.relabel j) (tail.relabel j) (tailValue.relabel j) value Fin.elim0 hcj hrj hv
    obtain ⟨he⟩ := valueUnique collect (out.relabel j) value (Fin.cons (raw.relabel j) Fin.elim0) hoj hval
    exact outputTransport merge value (out.relabel j) (Fin.cons (head.relabel j) (Fin.cons (tailValue.relabel j) Fin.elim0)) ⟨symm he⟩ hv
  · intro hs
    exact InternalRawListRecursionProof.consValue (OriginalRawSyntaxTransport.constant 0 0) merge
      raw head tail tailValue out Fin.elim0 hc hr hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.InternalProof
