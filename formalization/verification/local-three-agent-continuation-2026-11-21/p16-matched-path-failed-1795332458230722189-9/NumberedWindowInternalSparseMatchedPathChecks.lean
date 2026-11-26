module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedPathTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedPathInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedPathChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof (forward)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (headCases)
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation)
open NumberedWindowInternalSparseFormationRepresentativeSyntaxProof (formationRename)
open NumberedWindowInternalSparseMatchedCallsTargets (pulled)
open NumberedWindowInternalSparseMatchedCallsBindingProof (pulledRename)
open NumberedWindowInternalSparseMatchedPathTargets
attribute [local irreducible] ID1Completion.InternalControlGraph.programGraph

theorem exact_MatchedFinish : ExactMatchedFinish := NumberedWindowInternalSparseMatchedPathInductionProof.finishMatching

theorem exact_MatchedPath : ExactMatchedPath := by
  intro C X W s raw law body α Γ ctx dom cod arg fn next cert value positive later
  let H := formation W ctx dom cod arg ⊓ (positive ⊓ later)
  let Δ := H :: Γ
  have h : Derivation body Δ H := Derivation.hypothesis List.mem_cons_self
  let least := packedLeastProgram C X W s
  have whole := forward raw least ctx (rawCons dom cod) fn cert next
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
  have out : Nonempty (Derivation body Δ (pulled C X W s raw ctx cod (auxiliaryTerm dom cod fn arg) value)) := by
    apply headCases raw least ctx (rawCons dom cod) fn cert next _ whole
    intro β j Θ head tail middle keep row
    rw [pulledRename,auxiliaryRename]
    rw [rawConsRename] at row
    have typing := renameInto ⟨Derivation.conjunctionLeft h⟩ j Θ keep
    rw [formationRename] at typing
    have val := renameInto ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩ j Θ keep
    simp only [later,leastRename,auxiliaryRename] at val
    obtain ⟨typing⟩ := typing
    obtain ⟨val⟩ := val
    obtain ⟨row⟩ := row
    have stepTail := Derivation.conjunctionRight row
    obtain ⟨finish⟩ := exact_MatchedFinish C X W s raw law body β Θ (ctx.relabel j) (dom.relabel j)
      (cod.relabel j) (arg.relabel j) middle (next.relabel j) tail (value.relabel j)
    have suffix := Derivation.implicationElimination finish
      (Derivation.conjunctionIntroduction typing (Derivation.conjunctionIntroduction (Derivation.conjunctionRight stepTail) val))
    obtain ⟨advance⟩ := law body β Θ (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) (fn.relabel j)
      middle head (value.relabel j)
    exact ⟨Derivation.implicationElimination advance (Derivation.conjunctionIntroduction typing
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft stepTail) suffix))⟩
  obtain ⟨out⟩ := out
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_MatchedFinish
#print axioms exact_MatchedPath
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedPathChecks
