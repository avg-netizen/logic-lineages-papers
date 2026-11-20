module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipBottomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipFreeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipChecks
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRulesProof
  (actualOriginalAccessibilityIntroduction actualOriginalCarrierExtraction)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicMembershipTargets
open NumberedWindowInternalAtomicMembershipBottomProof (bottomMember bottomSuccessors)
open NumberedWindowInternalAtomicMembershipFreeProof (freeSuccessors)

theorem exact_RefinedAtomicSuccessors : ExactRefinedAtomicSuccessors :=
  ⟨bottomSuccessors,freeSuccessors⟩

theorem exact_RefinedAtomicMembership : ExactRefinedAtomicMembership := by
  constructor
  · intro i j r d context α Γ x c t
    dsimp only
    intro shape
    exact ⟨bottomMember i j r d context α Γ x c t shape,
      actualOriginalCarrierExtraction (data i j (refined i r) d) false context α Γ x⟩
  · intro i j r d context α Γ x c t n
    dsimp only
    intro shape
    let S := data i j (refined i r) d
    exact ⟨fun valid => actualOriginalAccessibilityIntroduction S false context α Γ x valid
        (freeSuccessors i j r d context α Γ x c t n shape),
      actualOriginalCarrierExtraction S false context α Γ x⟩

#print axioms exact_RefinedAtomicSuccessors
#print axioms exact_RefinedAtomicMembership
end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipChecks
