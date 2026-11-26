module
public import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberSharedProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalCalculus InternalAcceptance
open InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open NumberedWindowPositiveFiberPrograms NumberedWindowPositiveFiberOpenTargets

theorem exact_OpenSharedTest : OpenSharedTest :=
  NumberedWindowPositiveFiberSharedProof.openSharedTest

theorem exact_OpenFiberRules : OpenFiberRules := by
  intro ctx ty r body α Γ q w v
  constructor
  · intro h
    obtain ⟨outer⟩ := conjunctionRecover (agree ctx) (conjunction (agree ty) r) ![q,w,v] h
    obtain ⟨inner⟩ := conjunctionRecover (agree ty) r ![q,w,v] ⟨Derivation.conjunctionRight outer⟩
    exact ⟨(exact_OpenSharedTest ctx body α Γ q w v).mp ⟨Derivation.conjunctionLeft outer⟩,
      (exact_OpenSharedTest ty body α Γ q w v).mp ⟨Derivation.conjunctionLeft inner⟩,
      ⟨Derivation.conjunctionRight inner⟩⟩
  · rintro ⟨hc,ht,hr⟩
    exact conjunctionAccept (agree ctx) (conjunction (agree ty) r) ![q,w,v]
      ((exact_OpenSharedTest ctx body α Γ q w v).mpr hc)
      (conjunctionAccept (agree ty) r ![q,w,v] ((exact_OpenSharedTest ty body α Γ q w v).mpr ht) hr)

#print axioms exact_OpenSharedTest
#print axioms exact_OpenFiberRules
end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberOpenChecks
