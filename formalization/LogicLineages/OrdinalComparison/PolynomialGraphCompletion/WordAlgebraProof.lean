module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordAlgebraProof

theorem wordValue_append (w v : Word) (t : Nat) :
    wordValue (w ++ v) t = wordValue v (wordValue w t) := by
  induction w generalizing t with
  | nil => rfl
  | cons a w ih => exact ih (letterValue a t)

theorem wordDomain_append (w v : Word) (t : Nat) :
    WordDomain (w ++ v) t ↔ WordDomain w t ∧ WordDomain v (wordValue w t) := by
  induction w generalizing t with
  | nil => simp [WordDomain, wordValue]
  | cons a w ih =>
      simp only [List.cons_append, WordDomain, wordValue, ih, and_assoc]

theorem addUnary_value (r s : UnaryRow) (t : Nat) :
    unaryValue (addUnary r s) t = unaryValue r t + unaryValue s t := by
  simp only [unaryValue, addUnary, List.map_append, List.sum_append]
  omega

theorem addUnary_domain (r s : UnaryRow) (t : Nat)
    (hr : UnaryDomain r t) (hs : UnaryDomain s t) : UnaryDomain (addUnary r s) t := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hr a ha
  · exact hs a ha

theorem addUnary_allowed (D : Nat) (r s : UnaryRow)
    (hr : UnaryAllowed D r) (hs : UnaryAllowed D s) : UnaryAllowed D (addUnary r s) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hr a ha
  · exact hs a ha

theorem prepend_value (w : Word) (r : UnaryRow) (t : Nat) :
    unaryValue (prepend w r) t = unaryValue r (wordValue w t) := by
  simp only [unaryValue, prepend, List.map_map, Function.comp_def, wordValue_append]

theorem prepend_domain (w : Word) (r : UnaryRow) (t : Nat)
    (hw : WordDomain w t) (hr : UnaryDomain r (wordValue w t)) :
    UnaryDomain (prepend w r) t := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact (wordDomain_append w b.2 t).mpr ⟨hw, hr b hb⟩

theorem prepend_allowed (D : Nat) (w : Word) (r : UnaryRow)
    (hw : WordAllowed D w) (hr : UnaryAllowed D r) : UnaryAllowed D (prepend w r) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  intro letter hletter
  rcases List.mem_append.mp hletter with hletter | hletter
  · exact hw letter hletter
  · exact hr b hb letter hletter

theorem letterAllowed_mono {D E : Nat} (hDE : D ≤ E) (a : Letter)
    (ha : LetterAllowed D a) : LetterAllowed E a := by
  by_cases hsmall : a.1 ≤ 2
  · simp only [LetterAllowed, if_pos hsmall]
  · simp only [LetterAllowed, if_neg hsmall] at ha ⊢
    exact ⟨ha.1, ha.2.1, ha.2.2.trans hDE⟩

theorem wordAllowed_mono {D E : Nat} (hDE : D ≤ E) (w : Word)
    (hw : WordAllowed D w) : WordAllowed E w :=
  fun a ha => letterAllowed_mono hDE a (hw a ha)

theorem unaryAllowed_mono {D E : Nat} (hDE : D ≤ E) (r : UnaryRow)
    (hr : UnaryAllowed D r) : UnaryAllowed E r :=
  fun a ha => wordAllowed_mono hDE a.2 (hr a ha)

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordAlgebraProof
