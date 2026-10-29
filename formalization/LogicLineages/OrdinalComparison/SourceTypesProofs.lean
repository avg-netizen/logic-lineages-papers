module
public import LogicLineages.OrdinalComparison.SourceTypeTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source

theorem groundArityLevel : Targets.GroundArityLevel := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      change max (0 + 1) ((Ty.curriedGround (k + 1)).level) = 1
      rw [ih]
      rfl

theorem Ty.mem_subtypes_self (σ : Ty) : σ ∈ σ.subtypes := by
  cases σ <;> simp [Ty.subtypes]

theorem typeSubexpressionClosure : Targets.TypeSubexpressionClosure := by
  intro σ
  induction σ with
  | ground =>
      intro τ hτ υ hυ
      have hτ' : τ = Ty.ground := by simpa only [Ty.subtypes, List.mem_singleton] using hτ
      subst τ
      exact hυ
  | arrow σ₁ σ₂ ih₁ ih₂ =>
      intro τ hτ υ hυ
      simp only [Ty.subtypes, List.mem_cons, List.mem_append] at hτ
      rcases hτ with rfl | hτ | hτ
      · exact hυ
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (ih₁ τ hτ υ hυ))))
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (ih₂ τ hτ υ hυ))))

#print axioms groundArityLevel
#print axioms typeSubexpressionClosure

end LogicLineages.OrdinalComparison.Source
