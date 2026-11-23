module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWindowSubstitutionTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionBottomProof
open NumberedWindowSyntax NumberedWindowExternalWindowSubstitutionTargets

private theorem getMem (values : NArgs) (i : Nat) (a : NTerm) (h : values.get i = some a) :
    a ∈ values.toList := by
  cases values with
  | nil => cases h
  | cons first rest =>
    cases i with
    | zero =>
      have e : first = a := Option.some.inj h
      subst a
      exact List.mem_cons_self
    | succ i => exact List.mem_cons_of_mem _ (getMem rest i a h)
termination_by i

private theorem shiftBottom (a : NTerm) (d : Nat) (ρ : Ty) (h : shift d 0 a = .bottom ρ) :
    a = .bottom ρ := by
  cases a with
  | bottom σ => exact h
  | bound σ i => simp only [shift, Nat.not_lt_zero, if_false] at h; cases h
  | _ => cases h

/-- Only a replacement from a bound slot can introduce a bottom at
the original nonbottom root. -/
theorem imageBottom (values : NArgs) (d : Nat) (q : NTerm) (ρ : Ty)
    (hn : q ≠ .bottom q.type) (h : substitute values d q = .bottom ρ) :
    HasBottomValue values := by
  cases q with
  | bottom σ => exact (hn rfl).elim
  | bound σ i =>
    by_cases hi : i < d
    · simp only [substitute, hi, if_true] at h
      cases h
    · cases hg : values.get (i - d) with
      | none =>
        simp only [substitute, hi, if_false, hg] at h
        cases h
      | some a =>
        simp only [substitute, hi, if_false, hg] at h
        have hm := getMem values (i - d) a hg
        have he := shiftBottom a d ρ h
        exact ⟨ρ, he ▸ hm⟩
  | _ => cases h

end LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionBottomProof
