module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmCanonicalProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmResidualProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm
open OuterShiftNormalization KernelSourceCompletion

/-- The runtime head/inner-word projections reconstruct the entire actual
current source word. No head-rank metadata is supplied as a premise. -/
theorem active_item_view (D : Nat) (r : Row) (a : Item) (hD : RowAllowed D r)
    (ha : a ∈ active (canonicalRow r)) :
    a.2.2 = innerWord a ++ [head a] ∧ (head a).1 ≠ 0 ∧
      LetterAllowed D (head a) ∧ WordAllowed D (innerWord a) := by
  have hc := List.mem_filter.mp ha
  have hcanonical := canonical_item r a hc.1
  have hne : a.2.2 ≠ [] := by simpa using hc.2
  have hw := canonical_allowed D r hD a hc.1
  rcases (OuterShiftNormalization.Proof.splitSyntax a.2.2).2.2.1 with he | ⟨A,b,he,hb⟩
  · exact False.elim (hne (hcanonical.2.symm.trans he))
  · have hword : a.2.2 = A++[b] := hcanonical.2.symm.trans he
    have hhead : head a = b := by simp [head,hword,List.getLastD_concat]
    have hinner : innerWord a = A := by simp [innerWord,hword]
    have hbAllowed : LetterAllowed D b := hw b (by simp [hword])
    have hAAllowed : WordAllowed D A := by
      intro c hc
      exact hw c (by rw [hword]; exact List.mem_append.mpr (Or.inl hc))
    exact ⟨by simpa [hhead,hinner] using hword,by simpa [hhead] using hb,
      by simpa [hhead] using hbAllowed,by simpa [hinner] using hAAllowed⟩

theorem counter_head (a : Item) (hc : isCounter a = true) : (head a).1 = 4 := by
  simpa [isCounter] using hc

theorem counter_parameters (D : Nat) (r : Row) (a : Item) (hD : RowAllowed D r)
    (ha : a ∈ active (canonicalRow r)) (hc : isCounter a = true) :
    3 ≤ (head a).2.1 ∧ (head a).2.1 ≤ D ∧
      rank a = (head a).2.1 ∧ counterIndex a+3 = rank a := by
  have hv := active_item_view D r a hD ha
  have hh := counter_head a hc
  have hb : 3 ≤ (head a).2.1 ∧ (head a).2.1 ≤ D := by
    simpa [LetterAllowed,hh] using hv.2.2.1
  have hrank : rank a = (head a).2.1 := by
    unfold rank topRank
    change (if (head a).1 = 4 then (head a).2.1 else 0) = _
    simp [hh]
  refine ⟨hb.1,hb.2,hrank,?_⟩
  unfold counterIndex
  omega

/-- Unused counter-letter payloads do not alter the original source count.
The literal word's entire actual inner argument remains unchanged. -/
theorem counter_item_value (D : Nat) (r : Row) (a : Item) (hD : RowAllowed D r)
    (ha : a ∈ active (canonicalRow r)) (hc : isCounter a = true) (t : Nat) :
    wordValue a.2.2 t =
      sourceCount (counterIndex a+3) (mass a) (wordValue (innerWord a) t) := by
  have hv := active_item_view D r a hD ha
  have hp := counter_parameters D r a hD ha hc
  have hh := counter_head a hc
  have hdegree : (head a).2.1 = counterIndex a+3 := by omega
  rw [hv.1,WordAlgebraProof.wordValue_append]
  change letterValue (head a) (wordValue (innerWord a) t) = _
  simp [letterValue,hh,hdegree,mass]

theorem counter_item_domain (D : Nat) (r : Row) (a : Item) (hD : RowAllowed D r)
    (ha : a ∈ active (canonicalRow r)) (hc : isCounter a = true) (t : Nat) :
    WordDomain a.2.2 t ↔
      WordDomain (counterWord (innerWord a) (counterIndex a) (mass a)) t := by
  have hv := active_item_view D r a hD ha
  have hh := counter_head a hc
  rw [hv.1]
  simp [counterWord,WordAlgebraProof.wordDomain_append,WordDomain,
    LetterDomain,counterLetter,hh,mass]

theorem counter_item_canonical_value (D : Nat) (r : Row) (a : Item)
    (hD : RowAllowed D r) (ha : a ∈ active (canonicalRow r))
    (hc : isCounter a = true) (t : Nat) :
    wordValue a.2.2 t =
      wordValue (counterWord (innerWord a) (counterIndex a) (mass a)) t := by
  rw [counter_item_value D r a hD ha hc t]
  simp [counterWord,WordAlgebraProof.wordValue_append,wordValue,letterValue,counterLetter]

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
