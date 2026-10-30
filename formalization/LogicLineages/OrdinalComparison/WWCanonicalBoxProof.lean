module
public import LogicLineages.OrdinalComparison.WWCanonicalBoxTargets
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem actualOrdinalNumeral : Targets.ActualOrdinalNumeral := by
  constructor
  · intro Γ ρ n
    induction n with
    | zero => rfl
    | succ n ih =>
      cases n with
      | zero => simp [ordinalNumeral, denote]
      | succ n =>
        change ordinalNaturalSum (denote ρ (ordinalNumeral (n + 1))) 1 = ((n + 2 : Nat) : Ordinal)
        rw [ih]
        simpa only [Nat.cast_one] using
          LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof.naturalSum_finite (n + 1) 1
  · intro Γ i n hn
    induction n, hn using Nat.le_induction with
    | base => exact .one i
    | succ n hn ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact .add ih (.one i)

private theorem box_at_positive {Γ : List Ty} {m n : Nat}
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n) (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    ordinalVectorAt (ordinalCanonicalBox f g) i =
      ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i := by
  simp only [ordinalVectorAt, dif_pos (by omega : i < m + 1), ordinalCanonicalBox]
  exact if_neg (by omega)

theorem actualCanonicalBoxEquations : Targets.ActualCanonicalBoxEquations := by
  intro Γ m n hnm f g
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [ordinalCanonicalBox]
    rw [if_neg (by omega : i.val ≠ 0), ordinalBoxPositive, dif_neg (by omega : ¬ i.val ≤ n)]
    simp [ordinalVectorAt, i.isLt]
  · intro i hi hin
    rw [ordinalCanonicalBox]
    rw [if_neg (by omega : i.val ≠ 0), ordinalBoxPositive, dif_pos hin]
    rw [box_at_positive f g (i.val + 1) (by omega) (by omega)]
    simp [ordinalVectorAt, i.isLt]
  · change Term.collapse (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) 1)
      (ordinalBoxScalarTail n (f 0) (g 0)) = _
    rw [box_at_positive f g 1 (by omega) (by omega)]

private theorem box_positive_grade {Γ : List Ty} {m n : Nat} (hnm : n < m)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (hf : ∀ i, GeneratedOrdinalGrade Γ i.val (f i))
    (hg : ∀ i, GeneratedOrdinalGrade Γ i.val (g i))
    (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    GeneratedOrdinalGrade Γ i (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i) := by
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    apply GeneratedOrdinalGrade.emul hi
    · exact box_positive_grade hnm f g hf hg (i + 1) (by omega) (by omega)
    · apply GeneratedOrdinalGrade.add
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < n + 1)] using hg ⟨i, by omega⟩
  · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
termination_by n + 1 - i
decreasing_by omega

theorem actualCanonicalBoxGeneratedGrade : Targets.ActualCanonicalBoxGeneratedGrade := by
  intro Γ m n hnm f g hf hg i
  unfold ordinalCanonicalBox
  split
  · rename_i hi
    rw [hi]
    apply GeneratedOrdinalGrade.collapse
    · exact box_positive_grade hnm f g hf hg 1 (by omega) (by omega)
    · unfold ordinalBoxScalarTail
      split
      · exact .add (hf 0) (hg 0)
      · rename_i hn
        exact .add (hf 0) (.add (hg 0) ((actualOrdinalNumeral).2 Γ 0 n (by omega)))
  · rename_i hi
    exact box_positive_grade hnm f g hf hg i.val (by omega) (by have := i.isLt; omega)

end LogicLineages.OrdinalComparison.Source
