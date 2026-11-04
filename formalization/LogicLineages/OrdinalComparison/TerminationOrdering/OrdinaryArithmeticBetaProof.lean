module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaProof

open FirstOrder Language OrdinaryArithmetic OrdinaryArithmeticBetaTargets

@[simp] theorem realize_zero {α : Type} (v : α → Nat) : zeroTerm.realize v = 0 := rfl
@[simp] theorem realize_succ {α : Type} (t : Term α) (v : α → Nat) :
    (succTerm t).realize v = Nat.succ (t.realize v) := rfl
@[simp] theorem realize_add {α : Type} (s t : Term α) (v : α → Nat) :
    (addTerm s t).realize v = s.realize v + t.realize v := rfl
@[simp] theorem realize_mul {α : Type} (s t : Term α) (v : α → Nat) :
    (mulTerm s t).realize v = s.realize v * t.realize v := rfl

theorem bodyTruth {α : Type} (a b i r : Term α) (v : α → Nat) (xs : Fin 2 → Nat) :
    (betaBody a b i r).Realize v xs ↔
      a.realize v = xs 0 * ((i.realize v + 1) * b.realize v + 1) + r.realize v ∧
      r.realize v + Nat.succ (xs 1) = ((i.realize v + 1) * b.realize v + 1) := by
  simp [betaBody, Nat.succ_eq_add_one]

theorem betaTermTruth : BetaTermTruth := by
  intro α a b i r v
  rw [betaFormula, BoundedFormula.realize_exs]
  constructor
  · rintro ⟨xs, hx⟩
    obtain ⟨ha, hr⟩ := (bodyTruth a b i r v xs).mp hx
    have hlt : r.realize v < (i.realize v + 1) * b.realize v + 1 := by omega
    rw [ha]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]
  · intro h
    let m := (i.realize v + 1) * b.realize v + 1
    have hm : 0 < m := Nat.succ_pos _
    have hr : r.realize v < m := by
      rw [← h]
      exact Nat.mod_lt _ hm
    refine ⟨![a.realize v / m, m - (r.realize v + 1)], ?_⟩
    apply (bodyTruth a b i r v _).mpr
    constructor
    · change a.realize v = (a.realize v / m) * m + r.realize v
      have hd := Nat.mod_add_div (a.realize v) m
      have h' : a.realize v % m = r.realize v := h
      rw [h'] at hd
      simpa only [Nat.mul_comm, Nat.add_comm] using hd.symm
    · change r.realize v + (m - (r.realize v + 1) + 1) = m
      omega

theorem actualBetaTruth : ActualBetaTruth := by
  intro n i r
  simpa [betaGraph, Nat.beta] using
    (betaTermTruth (.var 0) (.var 1) (.var 2) (.var 3)
      ![n.unpair.1, n.unpair.2, i, r])

theorem finiteSequenceWitness : FiniteSequenceWitness := by
  intro l
  refine ⟨(Nat.unbeta l).unpair.1, (Nat.unbeta l).unpair.2, ?_⟩
  intro i
  apply (actualBetaTruth (Nat.unbeta l) (i : Nat) l[i]).mpr
  exact Nat.beta_unbeta_coe l i

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaProof
