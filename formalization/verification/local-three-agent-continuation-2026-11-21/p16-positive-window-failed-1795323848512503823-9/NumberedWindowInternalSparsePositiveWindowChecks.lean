module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof (forward)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (headCases)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePositiveWindowTargets
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseAdvanceWindowChecks (exact_SuccessfulAdvanceWindowsFromRetained)

theorem exact_FinishWindow : ExactFinishWindow :=
  NumberedWindowInternalSparsePositiveWindowInductionProof.finishWindow

theorem exact_PositiveWindows : ExactPositiveWindows := by
  intro raw least W law body α Γ ctx ty source cert target
  let P := positiveAt raw least ctx ty source cert target
  let Δ := P :: Γ
  have p : Derivation body Δ P := Derivation.hypothesis List.mem_cons_self
  have accepted := forward raw least ctx ty source cert target ⟨p⟩
  have both : Nonempty (Derivation body Δ (windowAt W ctx ty source ⊓ windowAt W ctx ty target)) := by
    apply headCases raw least ctx ty source cert target _ accepted
    intro β j Θ head tail next _ row
    rw [conjunctionRename,windowRename,windowRename]
    obtain ⟨data⟩ := row
    have stepAndTail := Derivation.conjunctionRight data
    obtain ⟨step⟩ := law body β Θ (ctx.relabel j) (ty.relabel j) (source.relabel j) head next
    have atHead := Derivation.implicationElimination step (Derivation.conjunctionLeft stepAndTail)
    obtain ⟨rest⟩ := exact_FinishWindow raw least W law body β Θ (ctx.relabel j) (ty.relabel j) next tail (target.relabel j)
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft atHead)
      (Derivation.implicationElimination rest (Derivation.conjunctionIntroduction
        (Derivation.conjunctionRight atHead) (Derivation.conjunctionRight stepAndTail)))⟩
  obtain ⟨r⟩ := both
  exact ⟨Derivation.implicationIntroduction r⟩

theorem exact_PhysicalPositiveWindowsFromRetained : ExactPhysicalPositiveWindowsFromRetained := by
  intro retained C X W root other syntaxProg s
  exact exact_PositiveWindows (typedRaw5 root other W syntaxProg) (packedLeastProgram C X W s) W
    (exact_SuccessfulAdvanceWindowsFromRetained retained C X W root other syntaxProg s)

#print axioms exact_FinishWindow
#print axioms exact_PositiveWindows
#print axioms exact_PhysicalPositiveWindowsFromRetained
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowChecks
