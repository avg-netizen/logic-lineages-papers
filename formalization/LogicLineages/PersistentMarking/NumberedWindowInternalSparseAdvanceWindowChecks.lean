module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc hopCertified)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof (obtainCalls)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseCoverOccurrenceChecks (exact_PackedLeastOccurrenceFromPass)
open NumberedWindowInternalSparsePackedLeastOpenChecks (exact_OpenPackedLeastPoolOccurrence)
open NumberedWindowInternalSparseFilterInclusionChecks (exact_DirectedPassInclusion)
open NumberedWindowInternalSparseRoundWindowChecks (exact_SelectedWindowFromRetained)
open NumberedWindowInternalSparseAdvanceWindowTargets

private theorem rawGuards (root other W : Program 3) (syntaxProg : Program 1)
    {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (ctx ty q w r : OTerm α)
    (d : Derivation body Γ (ID1Completion.InternalControlGraph.programGraph (typedRaw5 root other W syntaxProg)
      (suc NumberedWindowInternalSparsePathEnvelopeTargets.z) ![ctx,ty,q,w,r])) :
    Nonempty (Derivation body Γ (windowAt W ctx ty q ⊓ windowAt W ctx ty r)) := by
  obtain ⟨rule⟩ := NumberedWindowInternalSparseTypedRawOpenProof.graph body root other W syntaxProg α Γ ctx ty q w r
  exact ⟨Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft rule) d)⟩

theorem exact_CertifiedAdvanceCovers : ExactCertifiedAdvanceCovers := by
  intro C X W root other syntaxProg s body α Γ ctx ty current hop target q w r
  let raw := typedRaw5 root other W syntaxProg
  let least := packedLeastProgram C X W s
  let A := selectedGraph raw least (suc target) ctx ty (suc current) hop ⊓ hopCertified hop target q w r
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have selectors := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))
  obtain ⟨calls⟩ := obtainCalls raw least ctx ty current hop target q w r ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft selectors⟩ ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight selectors)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight selectors)⟩
  have terms := Derivation.conjunctionRight calls
  obtain ⟨guards⟩ := rawGuards root other W syntaxProg ctx ty q w r (Derivation.conjunctionLeft terms)
  have minima := Derivation.conjunctionRight terms
  have cover := exact_PackedLeastOccurrenceFromPass exact_OpenPackedLeastPoolOccurrence exact_DirectedPassInclusion
    C X W s body α Δ ctx ty
  obtain ⟨source⟩ := cover q current
  obtain ⟨dest⟩ := cover r target
  have both := Derivation.conjunctionIntroduction
    (Derivation.implicationElimination source (Derivation.conjunctionLeft minima))
    (Derivation.implicationElimination dest (Derivation.conjunctionRight minima))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction calls
    (Derivation.conjunctionIntroduction guards both))⟩

theorem exact_SuccessfulAdvanceWindowsFromRetained : ExactSuccessfulAdvanceWindowsFromRetained := by
  intro retained C X W root other syntaxProg s body α Γ ctx ty current hop target
  let raw := typedRaw5 root other W syntaxProg
  let least := packedLeastProgram C X W s
  let A := selectedGraph raw least (suc target) ctx ty (suc current) hop
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨invert⟩ := exact_OpenSuccessfulAdvanceCalls body raw least α ctx ty current hop target
  have supplied := closedApply ⟨Derivation.conjunctionLeft invert⟩ ⟨h⟩
  have result : Nonempty (Derivation body Δ (windowAt W ctx ty current ⊓ windowAt W ctx ty target)) := by
    apply reportCases raw least ctx ty current hop target _ supplied
    intro β j Θ q w r _ facts
    rw [conjunctionRename,windowRename,windowRename]
    obtain ⟨row⟩ := facts
    have terms := Derivation.conjunctionRight row
    obtain ⟨g⟩ := rawGuards root other W syntaxProg (ctx.relabel j) (ty.relabel j) q w r
      (Derivation.conjunctionLeft terms)
    have minima := Derivation.conjunctionRight terms
    have selected := exact_SelectedWindowFromRetained retained C X W s body β Θ (ctx.relabel j) (ty.relabel j)
    obtain ⟨fromRule⟩ := selected q (current.relabel j)
    obtain ⟨toRule⟩ := selected r (target.relabel j)
    exact ⟨Derivation.conjunctionIntroduction
      (Derivation.implicationElimination fromRule
        (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft g) (Derivation.conjunctionLeft minima)))
      (Derivation.implicationElimination toRule
        (Derivation.conjunctionIntroduction (Derivation.conjunctionRight g) (Derivation.conjunctionRight minima)))⟩
  obtain ⟨d⟩ := result
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_CertifiedAdvanceCovers
#print axioms exact_SuccessfulAdvanceWindowsFromRetained
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowChecks
