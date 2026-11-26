module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionPointProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionFamilyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb suc z)
open ID1Completion.InternalStrongInduction (below lift)
open ID1Completion.InternalStrongInductionProof (actualStrongInductionInstance)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow)
open NumberedWindowInternalCoverOwnEarlierTargets
open NumberedWindowInternalCoverOwnEarlierSyntaxProof (ownMotiveAt)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedStepProof (exact_OpenCoverCombinedRestrictedBoundedStep)
open NumberedWindowInternalCoverCombinedRestrictedInductionBindingProof (combinedOwnMotiveLift)
open NumberedWindowInternalCoverCombinedRestrictedInductionPointProof (allOwnFromBelow)
open NumberedWindowInternalCoverCombinedRestrictedInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem ownFamilyOfPointStep (P : Programs) (s : Settings) (raw : OTerm α)
    (work : PointOwnStep P s body) : Nonempty (Derivation body Γ (ownAt P.V P.W P.cover s raw)) := by
  let theta : Formula (α ⊕ Fin 1) := ownMotive P.V P.W P.cover s
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H : Formula (α ⊕ Fin 1) := below (lift theta) key
  let D : List (Formula (α ⊕ Fin 1)) := H :: Γ.map weaken
  let A : Formula (α ⊕ Fin 1) := unary P.V (suc z) key
  have small : Nonempty (Derivation body (A :: D) (ownBelow P.V P.W P.cover s key)) := by
    have given : Derivation body (A :: D) H :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    change Derivation body (A :: D) (below (lift (ownMotive P.V P.W P.cover s)) key) at given
    rw [combinedOwnMotiveLift] at given
    exact ⟨given⟩
  have known : Nonempty (Derivation body (A :: D) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have inductionStep : Nonempty (Derivation body D theta) := by
    obtain ⟨family⟩ := allOwnFromBelow P s key work small known
    exact ⟨Derivation.implicationIntroduction family⟩
  have accepted := actualStrongInductionInstance body α Γ theta raw inductionStep
  change Nonempty (Derivation body Γ (instantiate (ownMotive P.V P.W P.cover s) (emb raw))) at accepted
  rw [ownMotiveAt] at accepted
  exact accepted

theorem exact_OpenCoverCombinedRestrictedOwnFamily : ExactOpenCoverCombinedRestrictedOwnFamily := by
  intro V TV M M0 B T s body α Γ raw
  let P := combinedPrograms s V TV M M0 B T
  have work : PointOwnStep P s body :=
    fun β Δ q p vertices ctx result row =>
      exact_OpenCoverCombinedRestrictedBoundedStep V TV M M0 B T s body β Δ q p vertices ctx result row
  exact ownFamilyOfPointStep P s raw work

#print axioms ownFamilyOfPointStep
#print axioms exact_OpenCoverCombinedRestrictedOwnFamily

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionFamilyProof
