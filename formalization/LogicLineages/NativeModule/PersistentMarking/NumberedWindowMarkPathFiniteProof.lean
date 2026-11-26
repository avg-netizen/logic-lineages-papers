module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowMarkPathTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowMarkPathFiniteProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPreservationTargets
open NumberedWindowClosing NumberedWindowTraceAlgebra NumberedWindowMarkPathTargets

theorem typedAtLabel {C f τ k bs es} (h : Typed C (.numbered f τ k bs es) τ) (l : Nat) :
    Typed C (.numbered f τ l bs es) τ := by
  cases h with
  | numbered hb he => exact .numbered hb he

theorem typedChain (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (f : Head) (τ : Ty) (bs es : NArgs) (k l : Nat) (hle : l ≤ k)
    (ht : ∀ j, Typed C (.numbered f τ j bs es) τ) :
    ∃ path : TypedTrace S K C τ (.numbered f τ k bs es) (.numbered f τ l bs es),
      onlyRaw path ∧ rawLength path = k-l := by
  induction k generalizing l with
  | zero =>
    have e : l = 0 := Nat.eq_zero_of_le_zero hle
    subst l
    exact ⟨.done (ht 0),True.intro,rfl⟩
  | succ k ih =>
    by_cases e : l = k+1
    · subst l
      exact ⟨.done (ht _),True.intro,by simp only [rawLength,Nat.sub_self]⟩
    · have hl : l ≤ k := by omega
      obtain ⟨tail,hRaw,hLength⟩ := ih l hl
      refine ⟨.raw (ht (k+1)) (ht k) .lower tail,hRaw,?_⟩
      simp only [rawLength,hLength]
      omega

theorem finite : FiniteLoweringChain := by
  intro S K C τ f bs es k l hk hw hl
  obtain ⟨path,hRaw,hLength⟩ :=
    typedChain S K C f τ bs es k l hl (typedAtLabel hw.1)
  exact ⟨path,hRaw,hLength,
    NumberedWindowPreservationChecks.exact_AllTypedTraceIntermediates
      S K C τ _ _ hk hw path⟩

end LogicLineages.PersistentMarking.NumberedWindowMarkPathFiniteProof
