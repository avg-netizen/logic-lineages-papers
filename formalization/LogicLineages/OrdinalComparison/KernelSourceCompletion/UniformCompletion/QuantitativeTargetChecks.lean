module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeTargets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.TargetChecks

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeTargetChecks

example : Targets.ShiftedSourceBudgetOrder =
  (∀ t a b : Nat, a ≤ Phi t → ∀ i : Nat,
    (Phi^[i+1]) t-b ≤ (Phi^[i+1]) (t+1)-a) := rfl

example : Targets.BroadSourceBlock =
  (∀ n c t : Nat, c+n+2 ≤ Phi t →
    sourceValue (n+2) c t =
      sourceValue (n+1) c (sourceValue (n+2) (c+n+2) t) ∧
    sourceCount (n+2) c t =
      sourceCount (n+1) c (sourceValue (n+2) (c+n+2) t) +
        sourceCount (n+2) (c+n+2) t) := rfl

example : Targets.CubicUnsignedSeparation =
  (∀ c e R t : Nat, 16 ≤ t → 9000*(c+e+R+1) ≤ Phi t →
    (Phi^[R]) (sourceValue 3 e t) < sourceValue 3 c (t+1) ∧
    (c < e → (Phi^[R]) (sourceValue 3 e t) < sourceValue 3 c t)) := rfl

example : Targets.UnsignedSeparation =
  (∀ d c e R t : Nat, 3 ≤ d →
    degreeThreshold d ≤ t ∧ degreeConstant d*(c+e+R+1) ≤ Phi t →
    (Phi^[R]) (sourceValue d e t) < sourceValue d c (t+1) ∧
    (c < e → (Phi^[R]) (sourceValue d e t) < sourceValue d c t)) := by
  simp only [Targets.UnsignedSeparation,region,Int.natAbs_zero,Nat.add_zero]

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeTargetChecks
