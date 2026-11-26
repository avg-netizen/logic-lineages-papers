module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTotalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalRecursionClosureProof
open InternalPositiveUnfoldingSupportProof SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Normalize the input tuple while the original Program remains a symbolic
parameter, before specializing to the concrete traversal AST. -/
theorem totalThree (positive : Positive (Fin 1)) (p : Program 3) (alpha : Type)
    (Delta : List (Formula alpha)) (d k raw : OTerm alpha) :
    Nonempty (Derivation positive Delta (existsOne
      (graph3 p (.var (.inr 0)) (d.relabel Sum.inl) (k.relabel Sum.inl) (raw.relabel Sum.inl)))) := by
  obtain ⟨h⟩ := (actualOriginalPrograms positive 3 p).1 alpha
    (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0)))
  simpa only [graph3,programGraph,InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] using
    (show Nonempty (Derivation positive Delta _) from ⟨weakenClosed h Delta⟩)

/-- Structural Program closure supplies an actual derivation for the original
finite traversal AST. No native evaluation or successful execution is a premise. -/
theorem actualRawSyntaxInternalTotality : ActualRawSyntaxInternalTotality := by
  intro positive mode alpha Delta d k raw
  exact totalThree positive (fold mode) alpha Delta d k raw

/-- Original graph functionality applies at every positive body and symbolic
input, including malformed raw codes and arbitrary logical contexts. -/
theorem actualRawSyntaxInternalFunctionality : ActualRawSyntaxInternalFunctionality := by
  intro positive mode alpha Delta out out' d k raw
  obtain ⟨h⟩ := (actualOriginalPrograms positive 3 (fold mode)).2 alpha out out'
    (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0)))
  exact ⟨weakenClosed h Delta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTotalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTotalProof
