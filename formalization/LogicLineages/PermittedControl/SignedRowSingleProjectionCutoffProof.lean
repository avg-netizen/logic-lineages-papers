module

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowSingleProjection

theorem cutoffCaseSplit (cutoff : Nat) (holds : Nat → Prop) (low high : Prop)
    (below : (∃ z, z < cutoff ∧ holds z) ↔ low)
    (above : high ↔ ∃ z, cutoff ≤ z ∧ holds z) :
    (∃ z, holds z) ↔ low ∨ high := by
  constructor
  · rintro ⟨z,truth⟩
    rcases Nat.lt_or_ge z cutoff with small | large
    · exact Or.inl (below.mp ⟨z,small,truth⟩)
    · exact Or.inr (above.mpr ⟨z,large,truth⟩)
  · rintro (small | large)
    · obtain ⟨z,_,truth⟩ := below.mpr small
      exact ⟨z,truth⟩
    · obtain ⟨z,_,truth⟩ := above.mp large
      exact ⟨z,truth⟩

end LogicLineages.PermittedControl.SignedRowSingleProjection
