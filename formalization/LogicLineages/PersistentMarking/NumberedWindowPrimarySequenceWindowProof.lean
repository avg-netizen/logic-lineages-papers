import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceComplete
import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceSound
import LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryProof

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceWindowProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimarySequence
open NumberedWindowPrimarySequenceTargets

private theorem supply {S K C τ Q R} (trace : TypedExchangeTrace S K C τ Q R)
    (hk : DecisionSourceUniverse.Closed K) : InWindow S K C τ Q →
      (∀ T, T ∈ typedVertices trace → InWindow S K C τ T) ∧
      ∃ a : AdmittedExchangeTrace S K C τ Q R, admittedVertices a = typedVertices trace := by
  induction trace with
  | refl _ =>
    intro h
    refine ⟨?_,⟨.refl h,rfl⟩⟩
    intro T ht
    simp only [typedVertices,List.mem_singleton] at ht
    exact ht.symm ▸ h
  | next edge tail ih =>
    intro h
    have hNext := (NumberedWindowPreservationPrimaryProof.primary hk
      (NumberedWindowPrimarySequenceElementarySound.term edge)).mp h
    obtain ⟨all,a,e⟩ := ih hNext
    refine ⟨?_,⟨.next ⟨edge.1,h,hNext⟩ a,?_⟩⟩
    · intro T ht
      simp only [typedVertices,List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact h
      · exact all T ht
    · simp only [admittedVertices,typedVertices,e]

theorem propagation : ActualSequenceWindowPropagation := by
  intro S K C τ Q R p hk h
  exact supply p hk h

theorem admitted : ExactAdmittedPrimarySequences := by
  intro S K C τ Q R hk hq
  constructor
  · intro hp
    obtain ⟨p⟩ := NumberedWindowPrimarySequenceComplete.term hp
    obtain ⟨_,a,_⟩ := supply p hk hq
    exact ⟨a⟩
  · rintro ⟨p⟩
    exact NumberedWindowPrimarySequenceSound.admitted p

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceWindowProof
