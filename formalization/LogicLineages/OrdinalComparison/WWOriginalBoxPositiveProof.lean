module
public import LogicLineages.OrdinalComparison.WWOriginalBoxPositiveTargets
public import LogicLineages.OrdinalComparison.WWOriginalBoxStepProof
public import LogicLineages.OrdinalComparison.WWOriginalBoxControlProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain

theorem originalBoxPositiveGrade : Targets.OriginalBoxPositiveGrade := by
  intro Γ m n hnm f g hf hg i hi him
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    apply AmbientGrade.emul hi
    · exact originalBoxPositiveGrade Γ m n hnm f g hf hg (i + 1) (by omega) (by omega)
    · apply AmbientGrade.add
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < n + 1)] using hg ⟨i, by omega⟩
  · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
termination_by Γ m n hnm f g hf hg i hi him => n + 1 - i
decreasing_by omega

private theorem tower_bound {Γ : List Ty} {m n : Nat} (hnm : n < m)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (ρ : AdmissibleSubstitution Γ) (A B : Nat)
    (hf : ∀ j, actualOrdinalNorm (expressionValue ρ (f j)) ≤ A)
    (hg : ∀ j, actualOrdinalNorm (expressionValue ρ (g j)) ≤ B)
    (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    actualOrdinalNorm (expressionValue ρ
      (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)) ≤
        (fastControl 0)^[2 * (n + 1 - i)] (A + B + 1) := by
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    have ih := tower_bound hnm f g ρ A B hf hg (i + 1) (by omega) (by omega)
    have hf' : actualOrdinalNorm (expressionValue ρ (ordinalVectorAt f i)) ≤ A := by
      simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
    have hg' : actualOrdinalNorm (expressionValue ρ (ordinalVectorAt g i)) ≤ B := by
      simpa only [ordinalVectorAt, dif_pos (by omega : i < n + 1)] using hg ⟨i, by omega⟩
    let x := (fastControl 0)^[2 * (n + 1 - (i + 1))] (A + B + 1)
    have hsx : A + B ≤ x := (Nat.le_succ _).trans
      (iterate_self_le (fun t => (self_lt_fastControl 0 t).le) _ _)
    have hp := originalBoxStepNorm Γ ρ
      (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) (i + 1))
      (ordinalVectorAt f i) (ordinalVectorAt g i)
    have he : 2 * (n + 1 - i) = 2 + 2 * (n + 1 - (i + 1)) := by omega
    rw [he, Function.iterate_add_apply]
    change _ ≤ 2 ^ (2 ^ x)
    exact hp.trans ((Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) ih)
      (Nat.add_le_add hf' hg')).trans (originalBoxNumericalStep x (A + B) hsx))
  · rename_i hin
    have he : n + 1 - i = 0 := by omega
    rw [he]
    simp only [Nat.mul_zero, Function.iterate_zero, id_eq]
    have hf' := hf ⟨i, by omega⟩
    simp only [ordinalVectorAt, dif_pos (by omega : i < m + 1)]
    omega
termination_by n + 1 - i
decreasing_by omega

theorem originalBoxPositiveNorm : Targets.OriginalBoxPositiveNorm := by
  intro Γ m n hnm f g ρ A B hs hf hg i hi him
  have h := tower_bound hnm f g ρ A B hf hg i hi him
  have hc : 2 * (n + 1 - i) ≤ 2 * n := by omega
  exact h.trans (((iterate_index_mono (fun x => (self_lt_fastControl 0 x).le)
    (A + B + 1)) hc).trans (originalBoxControlEnvelope (A + B) n hs))

end LogicLineages.OrdinalComparison.Source.OriginalDomain
