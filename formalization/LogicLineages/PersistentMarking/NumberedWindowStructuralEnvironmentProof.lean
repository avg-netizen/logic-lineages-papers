import LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowPreservationBoundProof

namespace LogicLineages.PersistentMarking.NumberedWindowStructuralEnvironmentProof
open NumberedWindowSyntax NumberedWindowArithmeticLeastClass
open NumberedWindowStructuralComputabilityTargets
open NumberedWindowPreservationBoundProof (Compatible)
open NumberedWindowBindingBaseProof (shiftZero)

theorem compatible {S K Γ hk C values} (h : Environment S K Γ hk C values) :
    Compatible S K values 0 C (finiteC Γ) := by
  intro i τ hi hType
  obtain ⟨hw, _⟩ := h i τ hi hType
  exact hw

private theorem boundFirst (a : NTerm) (values : NArgs) (σ : Ty) :
    substitute (.cons a values) 0 (.bound σ 0) = a := by
  simp only [substitute, Nat.not_lt_zero, if_false, Nat.sub_zero, NArgs.get, shiftZero]

private theorem boundLater (a : NTerm) (values : NArgs) (τ : Ty) (i : Nat) :
    substitute (.cons a values) 0 (.bound τ (i + 1)) = substitute values 0 (.bound τ i) := by
  cases hGet : values.get i with
  | some a' => simp only [substitute, Nat.not_lt_zero, if_false, Nat.sub_zero, NArgs.get, hGet]
  | none =>
    simp only [substitute, Nat.not_lt_zero, if_false, Nat.sub_zero, NArgs.get, hGet, NArgs.length]
    congr 1
    omega

/-- Extending the input context at the nearest binder adds the actual
new value and leaves the images of all older bound positions unchanged. -/
theorem extend {S K Γ hk C values σ a} (h : Environment S K Γ hk C values)
    (ha : TypedComputable S K Γ hk σ a) : Environment S K Γ hk (C.push σ) (.cons a values) := by
  intro i τ hi ht
  cases i with
  | zero =>
    have he : σ = τ := Option.some.inj hi
    subst τ
    rw [boundFirst]
    exact ha
  | succ i =>
    rw [boundLater]
    exact h i τ hi ht

end LogicLineages.PersistentMarking.NumberedWindowStructuralEnvironmentProof
