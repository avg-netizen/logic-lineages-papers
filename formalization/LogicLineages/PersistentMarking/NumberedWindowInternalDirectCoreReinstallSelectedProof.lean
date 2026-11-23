module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallSelectedProof
open NumberedWindowInternalAccessibilityChecks (exact_ConcreteInternalAccessibility)
open NumberedWindowInternalDirectCoreReinstallTargets
open NumberedWindowInternalDirectCoreReinstallProof (exact_Reinstall)

theorem exact_SelectedReinstall : ExactSelectedReinstall := by
  intro xs s count hf
  obtain ⟨i,j,r,dOld,held,_,_⟩ := exact_ConcreteInternalAccessibility xs s
  have h : HeldThree xs s i j r := ⟨held.1,held.2.1,held.2.2.1⟩
  exact ⟨i,j,r,h,exact_Reinstall xs s i j r count h hf⟩

#print axioms exact_SelectedReinstall
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallSelectedProof
