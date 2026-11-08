module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftInductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalPathChecker InternalApplicationPathLift InternalApplicationPathLiftSyntaxProof
open InternalApplicationPathLiftSupportProof InternalApplicationPathLiftCoreProof InternalApplicationPathLiftInductionProof
open InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualInternalReflexivePathLift :
    InternalApplicationPathLiftTargets.ActualInternalReflexivePathLift := by
  intro body edge vertex invariant hInvariant hEdge α Gamma ps x y code out other mapped hi
  exact rowApply edge vertex invariant ps x y code out other mapped
    (allRows edge vertex invariant hInvariant hEdge ps code) hi

/-- Positive acceptance supplies a genuine cons internally. The tail is
reflexive, so the previously proved list-code induction suffices. -/
theorem actualInternalPositivePathLift :
    InternalApplicationPathLiftTargets.ActualInternalPositivePathLift := by
  intro body edge vertex invariant hInvariant hEdge α Gamma ps x y code out other mapped hi
  have hpositive : Nonempty (Derivation body Gamma (positiveGraph edge x y code)) := by
    obtain ⟨hi⟩ := hi
    exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hi)⟩
  apply positiveConsCases edge x y code _ hpositive
  intro β j Delta raw tail hj hc
  rw [positiveRename]
  have hi' := renameInto hi j Delta hj
  rw [inputsRename] at hi'
  have hr := allRows (Gamma := Delta) edge vertex invariant hInvariant hEdge
    (fun i => (ps i).relabel j) tail
  exact consLift edge vertex invariant hInvariant hEdge true (fun i => (ps i).relabel j)
    (x.relabel j) (y.relabel j) (code.relabel j) (out.relabel j) (other.relabel j)
    (mapped.relabel j) raw tail hr hc hi'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftProof
