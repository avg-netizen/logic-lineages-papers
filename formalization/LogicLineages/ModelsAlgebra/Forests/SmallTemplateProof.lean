module

public import LogicLineages.ModelsAlgebra.Forests.SmallTemplateTargets
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Pi
public import Lean.Elab.Tactic.Omega

/-! Exhaustive finite combinatorics for n≤m≤3. Each case is checked by ordinary
kernel reduction (`decide`), never native evaluation or an added axiom. All
finite families and all possible label functions remain quantified. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.SmallTemplateProof

private instance decidableLaminar (n : Nat) (family : Finset (Finset (Fin n))) :
    Decidable (IsLaminarLeafFamily family) := by
  unfold IsLaminarLeafFamily ClusterCompatible
  infer_instance

private instance decidableLabeling (m n : Nat) (family : Finset (Finset (Fin n))) :
    Decidable (∃ f : Fin n → Fin m, Function.Injective f ∧
      ∀ B ∈ family, B.image f ∈ combFamily m) := by
  infer_instance

theorem smallLaminarCombLabeling : Targets.SmallLaminarCombLabeling := by
  intro m n hnm
  change n.val ≤ m.val at hnm
  fin_cases m <;> fin_cases n <;> dsimp only at hnm ⊢
  all_goals try omega
  all_goals decide +kernel

end LogicLineages.ModelsAlgebra.Forests.SmallTemplateProof
