import LogicLineages.PersistentMarking.NumberedWindowAddressClassRankTargets
import LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMapChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalApplicationChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedNormProof
import LogicLineages.PersistentMarking.OrdinalRankMapEqualityProof

namespace LogicLineages.PersistentMarking.NumberedWindowAddressClassRankProof
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass NumberedWindowExternalIDOperators
open NumberedWindowCanonicalAddressMap NumberedWindowCanonicalAddressMapChecks NumberedWindowGuardedNormTargets
open NumberedWindowGuardedNormProof NumberedWindowAddressClassRankTargets OrdinalRankMapEqualityProof

theorem exact_ActualAddressClassRankEquality : ActualAddressClassRankEquality := by
  intro S K Γ τ hk q hClass hAddress
  have forwards {q t : Class S K (finiteC Γ) τ} (edge : ClassBelow S K Γ τ t q) :
      AddressBelow S K (classAddress hk t) (classAddress hk q) :=
    (exact_ActualClassAddressSuccessors S K Γ τ hk q (classAddress hk t)).mpr ⟨t, rfl, edge⟩
  have lifts (q : Class S K (finiteC Γ) τ) (n : Nat) (edge : AddressBelow S K n (classAddress hk q)) :
      ∃ t, ClassBelow S K Γ τ t q ∧ classAddress hk t = n := by
    obtain ⟨t, literal, descendant⟩ := (exact_ActualClassAddressSuccessors S K Γ τ hk q n).mp edge
    exact ⟨t, descendant, literal⟩
  exact exact_RankEqualityFromSuccessorLifting (ClassBelow S K Γ τ) (AddressBelow S K)
    (classAddress hk) forwards lifts q hClass hAddress

theorem exact_ActualClassStageNormAtAddress : ActualClassStageNormAtAddress := by
  intro S K Γ τ hk q
  let classWF : WellFounded (ClassBelow S K Γ τ) :=
    NumberedWindowExternalWellFoundedChecks.exact_ActualPositiveRelationWellFounded S K Γ τ hk
  let classAcc := classWF.apply q
  obtain ⟨coded, guard, _⟩ := exact_ActualClassAddressSpecification S K Γ τ hk q
  have membership : Least (scalarStep S K) (classAddress hk q) :=
    (NumberedWindowExternalApplicationChecks.exact_ScalarClassAccessibility
      S K Γ τ hk q (classCode hk q) coded).mpr classAcc
  have addressAcc : Acc (AddressBelow S K) (classAddress hk q) :=
    ((NumberedWindowExternalIDOperatorChecks.exact_ActualGuardedAccessibilitySemantics S K
      (classAddress hk q)).1.mp membership).2
  have norm := exact_ActualScalarOrdinalNorm S K (classAddress hk q) addressAcc guard
  have equality := exact_ActualAddressClassRankEquality S K Γ τ hk q classAcc addressAcc
  exact ⟨classAcc, equality.symm ▸ norm⟩

#print axioms exact_ActualAddressClassRankEquality
#print axioms exact_ActualClassStageNormAtAddress

end LogicLineages.PersistentMarking.NumberedWindowAddressClassRankProof
