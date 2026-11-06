module
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.Targets
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.SemanticProof
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.InvariantProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
open PolynomialGraphCompletion OuterShiftNormalization CounterWordGuardCompletion
open AdjacentRangeWordGuardCompletion GuardChildMeasureCompletion

/-- Removing unused fields preserves admission and the source semantics even
at inputs outside the source domain. Malformed tags retain the entire letter. -/
theorem canonicalCalibration : Targets.CanonicalCalibration := by
  intro D a
  by_cases h1 : a.1 = 1
  · simp [canonicalHead, h1, IsCanonical, LetterAllowed, rangeRank,
      letterValue, LetterDomain, phiLetter]
  by_cases h2 : a.1 = 2
  · simp [canonicalHead, h1, h2, IsCanonical, LetterAllowed, rangeRank,
      letterValue, LetterDomain, quadraticLetter]
  by_cases h3 : a.1 = 3
  · simp [canonicalHead, h1, h2, h3, IsCanonical, LetterAllowed, rangeRank,
      letterValue, LetterDomain, kernelLetter]
  by_cases h4 : a.1 = 4
  · simp [canonicalHead, h1, h2, h3, h4, IsCanonical, LetterAllowed, rangeRank,
      letterValue, LetterDomain, counterLetter]
  · simp [canonicalHead, h1, h2, h3, h4, IsCanonical]

/-- A literal last-letter decomposition identifies the extracted prefix. -/
theorem viewPrefix_of_core (w A : Word) (a : Letter)
    (h : coreWord w = A ++ [a]) : viewPrefix w = A := by
  simp [viewPrefix, h, List.reverse_append]

/-- The extracted raw head retains all four original fields. -/
theorem rawHead_of_core (w A : Word) (a : Letter)
    (h : coreWord w = A ++ [a]) : rawHead w = a := by
  simp [rawHead, h, List.reverse_append]

theorem viewHead_of_core (w A : Word) (a : Letter)
    (h : coreWord w = A ++ [a]) : viewHead w = canonicalHead a := by
  rw [viewHead, rawHead_of_core w A a h]

theorem preparedWord_of_core (w A : Word) (a : Letter)
    (h : coreWord w = A ++ [a]) :
    preparedWord w = A ++ [canonicalHead a, shiftLetter (outerShift w)] := by
  have hn : coreWord w ≠ [] := by simp [h]
  rw [preparedWord, if_neg hn, viewPrefix_of_core w A a h, viewHead_of_core w A a h]

/-- The default Phi is admitted at every degree, including zero; it is not
inserted into the prepared word in the empty-core case. -/
theorem viewSyntax : Targets.ViewSyntax := by
  intro D w hw
  have hcore := (OuterShiftNormalization.Proof.normalizationSyntax D w hw).1
  rcases (OuterShiftNormalization.Proof.splitSyntax w).2.2.1 with hnil | ⟨A, a, ha, hn⟩
  · simp [viewPrefix, viewHead, rawHead, preparedWord, hnil, canonicalHead,
      WordAllowed, LetterAllowed, IsCanonical, phiLetter, shiftLetter]
  · have hA : WordAllowed D A := by
      intro b hb
      apply hcore b
      rw [ha]
      exact List.mem_append.mpr (Or.inl hb)
    have hAllowed : LetterAllowed D a := by
      apply hcore a
      rw [ha]
      simp
    have hc := canonicalCalibration D a
    rw [viewPrefix_of_core w A a ha, viewHead_of_core w A a ha]
    refine ⟨hA, hc.1.mpr hAllowed, hc.2.1, ?_, ?_, ?_⟩
    · rw [hc.2.2.1]
      exact hn
    · rw [preparedWord_of_core w A a ha]
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hA b hb
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact hc.1.mpr hAllowed
        · have he := List.mem_singleton.mp hb
          subst b
          simp [LetterAllowed, shiftLetter]
    · intro _
      rw [rawHead_of_core w A a ha]
      exact ha

/-- Canonicalizing the last nonshift head preserves the exact domain of the
already normalized word. This is not a converse to source normalization. -/
theorem prepared_normalized (w : Word) (t : Nat) :
    (WordDomain (preparedWord w) t ↔ WordDomain (normalizedWord w) t) ∧
      wordValue (preparedWord w) t = wordValue (normalizedWord w) t := by
  rcases (OuterShiftNormalization.Proof.splitSyntax w).2.2.1 with hnil | ⟨A, a, ha, _⟩
  · simp [preparedWord, normalizedWord, hnil]
  · rw [preparedWord_of_core w A a ha]
    have hc := (canonicalCalibration 0 a).2.2.2.2 (wordValue A t)
    simp [normalizedWord, ha, List.append_assoc, List.cons_append, List.nil_append,
      WordAlgebraProof.wordDomain_append, WordAlgebraProof.wordValue_append,
      WordDomain, wordValue, hc.1, hc.2]

/-- Source domains imply prepared domains without erasing an invalid
intermediate signed shift from the original suffix. -/
theorem viewCorrect : Targets.ViewCorrect := by
  intro D w t _hw hd
  have hn := OuterShiftNormalization.Proof.normalizationCorrect w t hd
  have hp := prepared_normalized w t
  exact ⟨hp.1.mpr hn.2.1, hp.2.trans hn.2.2.1.symm⟩

/-- The original word's checked threshold supplies the original exact domain. -/
theorem viewTailCorrect : Targets.ViewTailCorrect := by
  intro D w t hw ht
  have hd := (WordGuardCompletion.Proof.wordTailCorrect D w t hw ht).1
  exact ⟨hd, viewCorrect D w t hw hd⟩

/-- The head replacement preserves literal counter and range occurrences,
including rank zero; only the earlier shift normalization merges shifts. -/
theorem prepared_normalized_counts (w : Word) :
    counterNodes (preparedWord w) = counterNodes (normalizedWord w) ∧
      ∀ r, rangeNodes r (preparedWord w) = rangeNodes r (normalizedWord w) := by
  rcases (OuterShiftNormalization.Proof.splitSyntax w).2.2.1 with hnil | ⟨A, a, ha, _⟩
  · simp [preparedWord, normalizedWord, hnil]
  · rw [preparedWord_of_core w A a ha]
    have htag := (canonicalCalibration 0 a).2.2.1
    have hrank := (canonicalCalibration 0 a).2.2.2.1
    constructor
    · by_cases h : a.1 = 4 <;>
        simp [normalizedWord, ha, List.append_assoc, counterNodes, List.filter_append,
          List.filter_cons, List.filter_nil, htag, h]
    · intro r
      by_cases h : rangeRank a = r <;>
        simp [normalizedWord, ha, List.append_assoc, rangeNodes, List.filter_append,
          List.filter_cons, List.filter_nil, hrank, h]

/-- The actual finite histogram and counter coordinate are unchanged. -/
theorem viewMeasure : Targets.ViewMeasure := by
  intro D A B hA hB
  have hcA := prepared_normalized_counts A
  have hcB := prepared_normalized_counts B
  calc
    wordMeasure D (preparedWord A, preparedWord B) =
        wordMeasure D (normalizedWord A, normalizedWord B) := by
      apply GuardChildMeasureCompletion.Proof.measure_ext D
      · exact congrArg₂ Nat.add hcA.1 hcB.1
      · intro r _ _
        exact congrArg₂ Nat.add (hcA.2 r) (hcB.2 r)
    _ = wordMeasure D (A, B) :=
      GuardChildMeasureCompletion.Proof.measure_normalized D A B hA hB

end LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
