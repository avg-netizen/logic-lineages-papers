module
public import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetTargets
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSyntaxChargeBudget
open MixedSameRankResidue

private theorem powThreePrimitive : Primrec (fun n : Nat => (3 : Nat) ^ n) := by
  let step := fun (_ : Nat) (last : Nat) => last * 3
  have update : Primrec₂ step :=
    (Primrec.nat_mul.comp (Primrec.snd : Primrec (Prod.snd : Nat × Nat → Nat))
      (Primrec.const 3)).to₂
  apply (Primrec.nat_rec₁ (1 : Nat) update).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.rec 1 step n * 3 = 3 ^ (n+1)
      rw [ih,Nat.pow_succ]

theorem budgetCodeExact : BudgetCodeExact := by
  have length : Primrec (fun a : Nat × List WeightedCode => a.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have pow : Primrec (fun a : Nat × List WeightedCode => (3 : Nat) ^ a.1) :=
    powThreePrimitive.comp Primrec.fst
  refine ⟨(Primrec.nat_mul.comp length pow).to₂,?_⟩
  intro r terms
  simp only [syntaxBudgetCode,syntaxBudget,List.length_map]

end LogicLineages.PermittedControl.ActualSyntaxChargeBudget
