module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafHeadNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListDomainProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalCoverArgumentGuardTargets (acceptedHeads)
open NumberedWindowInternalCoverArgumentGuardNumericProof (exact_CoverArgumentGuardNumeric)
open NumberedWindowInternalCoverMixedLeafArgumentTargets (mixedLeafHead)
open NumberedWindowInternalCoverMixedLeafHeadNumericProof (exact_CoverMixedLeafHeadNumeric)
open NumberedWindowInternalCoverRestrictedMixedListTargets

theorem exact_CoverMixedArgumentDomain : ExactCoverMixedArgumentDomain := by
  intro s a
  unfold run
  rw [exact_CoverArgumentGuardNumeric]
  have gate : acceptedHeads (mixedLeafHead s) a = true ↔ OriginalMixedArguments s a := by
    unfold acceptedHeads OriginalMixedArguments
    cases eq : unpack a with
    | none => simp [eq]
    | some xs =>
      simp only [Option.any_some,List.all_eq_true]
      constructor
      · intro h
        exact ⟨xs,rfl,fun q hq =>
          (exact_CoverMixedLeafHeadNumeric s q).mp (by
            change evaluate (mixedLeafHead s) (q ::ᵥ nil) = 1
            exact beq_iff_eq.mp (h q hq))⟩
      · rintro ⟨ys,read,h⟩
        have same := Option.some.inj read
        subst ys
        intro q hq
        have yes := (exact_CoverMixedLeafHeadNumeric s q).mpr (h q hq)
        change (evaluate (mixedLeafHead s) (q ::ᵥ nil) == 1) = true
        exact beq_iff_eq.mpr yes
  cases test : acceptedHeads (mixedLeafHead s) a <;> simp_all

#print axioms exact_CoverMixedArgumentDomain

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListDomainProof
