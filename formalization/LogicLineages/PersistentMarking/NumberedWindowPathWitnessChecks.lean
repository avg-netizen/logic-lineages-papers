import LogicLineages.PersistentMarking.NumberedWindowPathWitnessRawProof
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassWalkSound
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassWalkComplete

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessChecks
open NumberedWindowPathWitnessTargets

theorem exact_CertifiedFiniteRawPath : ExactCertifiedFiniteRawPath :=
  NumberedWindowPathWitnessRawProof.exactPath

theorem exact_ActualClassCodeFibers : ExactActualClassCodeFibers :=
  NumberedWindowPathWitnessClassCode.fibers

theorem exact_CertifiedNumericClassEdge : ExactCertifiedNumericClassEdge :=
  NumberedWindowPathWitnessClassEdge.exactEdge

theorem exact_CertifiedPositiveNumericClassPath : ExactCertifiedPositiveNumericClassPath := by
  intro S K Γ τ src dst hk
  exact ⟨fun ⟨es,h⟩ => NumberedWindowPathWitnessClassWalkSound.sound hk h,
    fun ⟨_,_,hs,hd,h⟩ => NumberedWindowPathWitnessClassWalkComplete.complete hk hs hd h⟩

#print axioms exact_CertifiedFiniteRawPath
#print axioms exact_ActualClassCodeFibers
#print axioms exact_CertifiedNumericClassEdge
#print axioms exact_CertifiedPositiveNumericClassPath

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessChecks
