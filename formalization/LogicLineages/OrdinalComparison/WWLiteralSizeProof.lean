module
public import LogicLineages.OrdinalComparison.WWLiteralSizeTargets
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem nodes_pos {ι : Type} (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι) :
    0 < ordinalLiteralNodes t := by
  cases t <;> simp [ordinalLiteralNodes] <;> omega

private theorem weight_pos {ι : Type} (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι) :
    0 < ordinalLiteralWeight t := by
  cases t <;> simp [ordinalLiteralWeight] <;> omega

private theorem partialSize_le_weight {Γ : List Ty} {σ : Ty}
    (t : OrdinalExpression (σ :: Γ)) : ordinalPartialSize t ≤ ordinalLiteralWeight t := by
  induction t <;> rw [ordinalPartialSize] <;> split
  all_goals first | exact weight_pos _ | (simp_all [ordinalLiteralWeight]; omega)

private theorem weight_add_one_le_pow {ι : Type} (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι) :
    ordinalLiteralWeight t + 1 ≤ 2 ^ ordinalLiteralNodes t := by
  induction t with
  | var c => simp [ordinalLiteralWeight, ordinalLiteralNodes]
  | zero => simp [ordinalLiteralWeight, ordinalLiteralNodes]
  | one => simp [ordinalLiteralWeight, ordinalLiteralNodes]
  | omega => simp [ordinalLiteralWeight, ordinalLiteralNodes]
  | add f g hf hg | collapse f g hf hg =>
    have ha : 2 ≤ 2 ^ ordinalLiteralNodes f := by
      have := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) (nodes_pos f)
      simpa using this
    have hb : 2 ≤ 2 ^ ordinalLiteralNodes g := by
      have := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) (nodes_pos g)
      simpa using this
    simp only [ordinalLiteralWeight, ordinalLiteralNodes, pow_succ, pow_add]
    nlinarith
  | emul f g hf hg =>
    have ha : 2 ≤ 2 ^ ordinalLiteralNodes f := by
      have := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) (nodes_pos f)
      simpa using this
    have hb : 2 ≤ 2 ^ ordinalLiteralNodes g := by
      have := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) (nodes_pos g)
      simpa using this
    simp only [ordinalLiteralWeight, ordinalLiteralNodes, pow_succ, pow_add]
    nlinarith

theorem actualLiteralPartialSizeBound : Targets.ActualLiteralPartialSizeBound := by
  intro Γ σ t
  exact ⟨partialSize_le_weight t, by have := weight_add_one_le_pow t; omega⟩

theorem actualLiteralMultiplierBound : Targets.ActualLiteralMultiplierBound := by
  intro Γ σ h
  apply Nat.mul_le_mul_left
  induction h with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    have ht := actualLiteralPartialSizeBound Γ σ t
    omega

end LogicLineages.OrdinalComparison.Source
