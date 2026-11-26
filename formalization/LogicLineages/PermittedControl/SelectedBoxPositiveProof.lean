module
public import LogicLineages.PermittedControl.SelectedBoxTargets
public import LogicLineages.PermittedControl.SelectedNormSumsProof
public import LogicLineages.OrdinalComparison.WWOriginalBoxStepProof
public import LogicLineages.OrdinalComparison.WWOriginalBoxControlProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedBoxPositiveProof
open OrdinalComparison Source SelectedSourceDomain

 theorem stepNorm (ctrl : Nat → Nat) (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ)
    (h f g : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ (.emul h (.add f g))) ≤
      2 ^ actualOrdinalNorm (expressionValue ctrl ρ h) *
        (actualOrdinalNorm (expressionValue ctrl ρ f) + actualOrdinalNorm (expressionValue ctrl ρ g)) := by
  have hh := SelectedValueClosureProof.ambient_below ctrl ρ h
  have hp := Source.OriginalDomain.actualNaturalProductUpperNorm _ _
    (SelectedValueClosureProof.two_power_below hh)
    (SelectedValueClosureProof.ambient_below ctrl ρ (.add f g))
  have hs := Source.OriginalDomain.actualNaturalSumNormAdditivity _ _
    (SelectedValueClosureProof.ambient_below ctrl ρ f)
    (SelectedValueClosureProof.ambient_below ctrl ρ g)
  exact hp.trans (by
    change actualOrdinalNorm ((2 : Ordinal)^expressionValue ctrl ρ h) *
      actualOrdinalNorm (ordinalNaturalSum (expressionValue ctrl ρ f) (expressionValue ctrl ρ g)) ≤ _
    rw [hs]
    exact Nat.mul_le_mul_right _ (Source.OriginalDomain.actualBaseTwoForwardNorm _ hh))

theorem positiveGrade (ctrl : Nat → Nat) (Γ : List Ty) (m n : Nat) (hnm : n < m)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (hf : ∀ j, AmbientGrade ctrl Γ j.val (f j)) (hg : ∀ j, AmbientGrade ctrl Γ j.val (g j))
    (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    AmbientGrade ctrl Γ i (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i) := by
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    apply AmbientGrade.emul hi
    · exact positiveGrade ctrl Γ m n hnm f g hf hg (i + 1) (by omega) (by omega)
    · apply AmbientGrade.add
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < n + 1)] using hg ⟨i, by omega⟩
  · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
termination_by n + 1 - i
decreasing_by omega

private theorem tower_bound (ctrl : Nat → Nat) {Γ : List Ty} {m n : Nat} (hnm : n < m)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (ρ : AdmissibleSubstitution ctrl Γ) (A B : Nat)
    (hf : ∀ j, actualOrdinalNorm (expressionValue ctrl ρ (f j)) ≤ A)
    (hg : ∀ j, actualOrdinalNorm (expressionValue ctrl ρ (g j)) ≤ B)
    (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    actualOrdinalNorm (expressionValue ctrl ρ
      (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)) ≤
        (fastControl 0)^[2 * (n + 1 - i)] (A + B + 1) := by
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    have ih := tower_bound ctrl hnm f g ρ A B hf hg (i + 1) (by omega) (by omega)
    have hf' : actualOrdinalNorm (expressionValue ctrl ρ (ordinalVectorAt f i)) ≤ A := by
      simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
    have hg' : actualOrdinalNorm (expressionValue ctrl ρ (ordinalVectorAt g i)) ≤ B := by
      simpa only [ordinalVectorAt, dif_pos (by omega : i < n + 1)] using hg ⟨i, by omega⟩
    let x := (fastControl 0)^[2 * (n + 1 - (i + 1))] (A + B + 1)
    have hsx : A + B ≤ x := (Nat.le_succ _).trans
      (iterate_self_le (fun t => (self_lt_fastControl 0 t).le) _ _)
    have hp := stepNorm ctrl Γ ρ
      (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) (i + 1))
      (ordinalVectorAt f i) (ordinalVectorAt g i)
    have he : 2 * (n + 1 - i) = 2 + 2 * (n + 1 - (i + 1)) := by omega
    rw [he, Function.iterate_add_apply]
    change _ ≤ 2 ^ (2 ^ x)
    exact hp.trans ((Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) ih)
      (Nat.add_le_add hf' hg')).trans (Source.OriginalDomain.originalBoxNumericalStep x (A + B) hsx))
  · rename_i hin
    have he : n + 1 - i = 0 := by omega
    rw [he]
    simp only [Nat.mul_zero, Function.iterate_zero, id_eq]
    have hf' := hf ⟨i, by omega⟩
    simp only [ordinalVectorAt, dif_pos (by omega : i < m + 1)]
    omega
termination_by n + 1 - i
decreasing_by omega

theorem positiveNorm (ctrl : Nat → Nat) (Γ : List Ty) (m n : Nat) (hnm : n < m)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n) (ρ : AdmissibleSubstitution ctrl Γ)
    (A B : Nat) (hs : 0 < A+B)
    (hf : ∀ j, actualOrdinalNorm (expressionValue ctrl ρ (f j)) ≤ A)
    (hg : ∀ j, actualOrdinalNorm (expressionValue ctrl ρ (g j)) ≤ B)
    (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    actualOrdinalNorm (expressionValue ctrl ρ
      (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)) ≤ fastControl 2 (A+B+n) := by
  have h := tower_bound ctrl hnm f g ρ A B hf hg i hi him
  have hc : 2 * (n + 1 - i) ≤ 2 * n := by omega
  exact h.trans (((iterate_index_mono (fun x => (self_lt_fastControl 0 x).le)
    (A + B + 1)) hc).trans (Source.OriginalDomain.originalBoxControlEnvelope (A + B) n hs))

end LogicLineages.PermittedControl.SelectedBoxPositiveProof
