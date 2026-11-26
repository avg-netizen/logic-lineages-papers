module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename casesLeast)
open NumberedWindowInternalCoverCombinedRestrictedRawHopTargets (thinRawAt)
open NumberedWindowInternalCoverCombinedRestrictedSingletonBindingProof
  (thinRawRename thinProvidedRename introduceThinProvided)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

private theorem finishRight (ctx cod src wr dst left : OTerm α)
    (accepted : Nonempty (Derivation body Γ (thinRawAt raw ctx cod src wr dst)))
    (first : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod src left)))
    (last : Nonempty (Derivation body Γ (hasLeast C X W s ctx cod dst))) :
    Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr dst)) := by
  apply casesLeast C X W s ctx cod dst _ last
  intro β j Δ right keep toLast
  rw [thinProvidedRename]
  have a := renameInto accepted j Δ keep
  rw [thinRawRename] at a
  have l := renameInto first j Δ keep
  rw [leastRename] at l
  obtain ⟨a⟩ := a
  obtain ⟨l⟩ := l
  obtain ⟨r⟩ := toLast
  have outputs := Derivation.conjunctionIntroduction l r
  obtain ⟨positive⟩ := NumberedWindowInternalSparseAddressSingletonCoreProof.fromCalls raw
    (packedLeastProgram C X W s) _ _ _ _ _ _ _ ⟨Derivation.conjunctionIntroduction a outputs⟩
  exact introduceThinProvided C X W s raw _ _ _ _ _ _ _ ⟨Derivation.conjunctionIntroduction outputs positive⟩

private theorem finish (ctx cod src wr dst : OTerm α)
    (accepted : Nonempty (Derivation body Γ (thinRawAt raw ctx cod src wr dst)))
    (first : Nonempty (Derivation body Γ (hasLeast C X W s ctx cod src)))
    (last : Nonempty (Derivation body Γ (hasLeast C X W s ctx cod dst))) :
    Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr dst)) := by
  apply casesLeast C X W s ctx cod src _ first
  intro β j Δ left keep leftResult
  rw [thinProvidedRename]
  have a := renameInto accepted j Δ keep
  rw [thinRawRename] at a
  have r := renameInto last j Δ keep
  rw [hasRename] at r
  exact finishRight C X W s raw _ _ _ _ _ left a leftResult r

theorem exact_OpenCoverThinSingletonFromAvailableLeast : ExactOpenCoverThinSingletonFromAvailableLeast := by
  intro C X W s raw body α Γ ctx ty src wr dst accepted srcLeast dstLeast
  exact finish C X W s raw ctx ty src wr dst accepted srcLeast dstLeast

#print axioms exact_OpenCoverThinSingletonFromAvailableLeast

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonCoreProof
