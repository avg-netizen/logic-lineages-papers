import LogicLineages.PersistentMarking.NumberedWindowFrameTargets

namespace LogicLineages.PersistentMarking.NumberedWindowClosingInventoryProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing
open NameBridge (Name)

mutual
theorem term (name : Name) (d : Nat) (q : NTerm) :
    (closeAt name d q).type = q.type ∧
      support (closeAt name d q) = support q ∧ heads (closeAt name d q) = heads q := by
  cases q with
  | free σ x =>
    by_cases h : (σ,x) = name <;> simp [closeAt,h,NTerm.type,support,heads]
  | bound σ i => exact ⟨rfl,rfl,rfl⟩
  | lam σ q =>
    obtain ⟨ht,hs,hh⟩ := term name (d+1) q
    exact ⟨by simp only [closeAt,NTerm.type,ht],by simp only [closeAt,support,ht,hs],hh⟩
  | bottom σ => exact ⟨rfl,rfl,rfl⟩
  | ordinary f bs =>
    obtain ⟨hs,hh⟩ := args name d bs
    exact ⟨rfl,by simp only [closeAt,support,hs],by simp only [closeAt,heads,hh]⟩
  | numbered f τ k bs es =>
    obtain ⟨hbs,hbh⟩ := args name d bs
    obtain ⟨hes,heh⟩ := args name d es
    exact ⟨rfl,by simp only [closeAt,support,hbs,hes],by simp only [closeAt,heads,hbh,heh]⟩
  | auxApp σ τ q a =>
    obtain ⟨_,hqs,hqh⟩ := term name d q
    obtain ⟨_,has,hah⟩ := term name d a
    exact ⟨rfl,by simp only [closeAt,support,hqs,has],by simp only [closeAt,heads,hqh,hah]⟩
termination_by sizeOf q

theorem args (name : Name) (d : Nat) (As : NArgs) :
    argsSupport (closeArgsAt name d As) = argsSupport As ∧
      argsHeads (closeArgsAt name d As) = argsHeads As := by
  cases As with
  | nil => exact ⟨rfl,rfl⟩
  | cons q qs =>
    obtain ⟨_,hqs,hqh⟩ := term name d q
    obtain ⟨hss,hsh⟩ := args name d qs
    exact ⟨by simp only [closeArgsAt,argsSupport,hqs,hss],
      by simp only [closeArgsAt,argsHeads,hqh,hsh]⟩
termination_by sizeOf As
end

theorem annotation (name : Name) (d : Nat) (q : NTerm) : (closeAt name d q).type = q.type :=
  (term name d q).1

end LogicLineages.PersistentMarking.NumberedWindowClosingInventoryProof
