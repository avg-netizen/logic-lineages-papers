module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalDirectCoreReinstallTargets (HeldThree)
open NumberedWindowInternalDirectCoreReinstallProof (exact_Reinstall)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedListNumericProof (exact_NumericJRaw)
open NumberedWindowInternalDirectTypedListInstallTargets

theorem exact_ReinstallTypedList : ExactReinstallTypedList := by
  intro xs s i r count si positives counted
  have h : HeldThree xs s i (jRaw i) r := by
    refine ⟨si,?_,positives⟩
    intro raw
    change evaluate (jRaw i) (raw ::ᵥ nil) =
      (NumberedWindowDirectAlgorithm.typedList (checks xs s).scalar raw).toNat
    exact exact_NumericJRaw i (checks xs s).scalar si raw
  exact exact_Reinstall xs s i (jRaw i) r count h counted

#print axioms exact_ReinstallTypedList
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallProof
