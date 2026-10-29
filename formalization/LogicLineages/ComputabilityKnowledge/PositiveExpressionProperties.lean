module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialGap

@[expose] public section

/-! Direct consequences of the fixed paper02 syntax: every evaluation is
positive, and applying the finite collision compiler to depth-one source
equations gives terms of depth at most two. These do not discharge MRDP. -/
namespace LogicLineages.ComputabilityKnowledge.PositiveExpressionProperties

open PositiveExpression
open Comparators.ExponentialGap

theorem eval_positive {ι : Type} (ρ : ι → PosNat) (e : Expr ι) :
    0 < e.eval ρ := by
  induction e with
  | one => exact Nat.zero_lt_one
  | var i => exact (ρ i).property
  | add a b ha hb => exact Nat.add_pos_left ha _
  | emul a b ha hb =>
    exact Nat.mul_pos (Nat.two_pow_pos _) hb

theorem pair_depth {ι : Type} (a b : Expr ι)
    (ha : a.depth ≤ 1) (hb : b.depth ≤ 1) :
    (leftPair a b).depth ≤ 2 ∧ (rightPair a b).depth ≤ 2 := by
  simp only [leftPair, rightPair, Expr.depth]
  omega

theorem system_depth {ι : Type} (equations : List (Expr ι × Expr ι))
    (h : ∀ pair ∈ equations, pair.1.depth ≤ 1 ∧ pair.2.depth ≤ 1) :
    (systemLeft equations).depth ≤ 2 ∧ (systemRight equations).depth ≤ 2 := by
  revert h
  induction equations with
  | nil =>
    intro _
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | cons pair rest ih =>
    intro h
    obtain ⟨a,b⟩ := pair
    have hab := h (a,b) (List.Mem.head rest)
    have hr : ∀ pair ∈ rest, pair.1.depth ≤ 1 ∧ pair.2.depth ≤ 1 :=
      fun pair hp => h pair (List.Mem.tail (a,b) hp)
    obtain ⟨hl,hright⟩ := ih hr
    obtain ⟨hpl,hpr⟩ := pair_depth a b hab.1 hab.2
    change max (leftPair a b).depth (systemLeft rest).depth ≤ 2 ∧
      max (rightPair a b).depth (systemRight rest).depth ≤ 2
    omega

end LogicLineages.ComputabilityKnowledge.PositiveExpressionProperties
