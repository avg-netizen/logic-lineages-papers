module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequenceWindowProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceChecks
open NumberedWindowPrimarySequenceTargets

theorem exact_TypedElementarySound : TypedElementarySound :=
  NumberedWindowPrimarySequenceElementarySound.both

theorem exact_TypedPrimarySequences : ExactTypedPrimarySequences := by
  intro S K C τ Q R
  exact ⟨NumberedWindowPrimarySequenceComplete.term,
    fun ⟨p⟩ => NumberedWindowPrimarySequenceSound.term p⟩

theorem exact_TypedOrderedSequences : ExactTypedOrderedSequences := by
  intro S K C types qs rs
  exact ⟨NumberedWindowPrimarySequenceComplete.args,
    fun ⟨p⟩ => NumberedWindowPrimarySequenceSound.args p⟩

theorem exact_ActualSequenceWindowPropagation : ActualSequenceWindowPropagation :=
  NumberedWindowPrimarySequenceWindowProof.propagation

theorem exact_AdmittedPrimarySequences : ExactAdmittedPrimarySequences :=
  NumberedWindowPrimarySequenceWindowProof.admitted

#print axioms exact_TypedElementarySound
#print axioms exact_TypedPrimarySequences
#print axioms exact_TypedOrderedSequences
#print axioms exact_ActualSequenceWindowPropagation
#print axioms exact_AdmittedPrimarySequences

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceChecks
