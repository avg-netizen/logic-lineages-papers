module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.SyntaxProof
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem shiftSumCorrect : Targets.ShiftSumCorrect := by
  intro w
  induction w with
  | nil => intro t _ _; simp [wordValue,shiftSum]
  | cons a w ih =>
      intro t hs hd
      have ha : a.1 = 0 := hs a List.mem_cons_self
      have hw : ShiftOnly w := fun b hb => hs b (List.mem_cons_of_mem a hb)
      have hdom : 0 ≤ (t : Int)+a.2.2.2 := by
        simpa only [LetterDomain,ha,if_true] using hd.1
      have hletter : (letterValue a t : Int) = (t : Int)+a.2.2.2 := by
        simp only [letterValue,ha,if_true]
        omega
      have hrest := ih (letterValue a t) hw hd.2
      change (wordValue w (letterValue a t) : Int) = (t : Int)+(a.2.2.2+shiftSum w)
      omega

theorem normalizationCorrect : Targets.NormalizationCorrect := by
  intro w t hd
  have hs := splitSyntax w
  have hds := (WordAlgebraProof.wordDomain_append (coreWord w) (shiftSuffix w) t).mp
    (Eq.mp (congrArg (fun u => WordDomain u t) hs.1) hd)
  have hv := congrArg (fun u => wordValue u t) hs.1
  rw [WordAlgebraProof.wordValue_append] at hv
  have hsum := shiftSumCorrect (shiftSuffix w) (wordValue (coreWord w) t) hs.2.1 hds.2
  have hsum' : (wordValue w t : Int) = (wordValue (coreWord w) t : Int)+outerShift w := by
    rw [hv]
    exact hsum
  have hshift : 0 ≤ (wordValue (coreWord w) t : Int)+outerShift w := by omega
  have hnorm : WordDomain (normalizedWord w) t :=
    (WordAlgebraProof.wordDomain_append (coreWord w) [shiftLetter (outerShift w)] t).mpr
      ⟨hds.1,hshift,trivial⟩
  have hvalue : wordValue (normalizedWord w) t =
      ((wordValue (coreWord w) t : Int)+outerShift w).toNat := by
    simp only [normalizedWord,WordAlgebraProof.wordValue_append,wordValue,
      letterValue,shiftLetter,if_true]
  refine ⟨hds.1,hnorm,?_,hsum'⟩
  rw [hvalue]
  omega

theorem tailNormalization : Targets.TailNormalization := by
  intro D w t hw ht
  have hd := (WordGuardCompletion.Proof.wordTailCorrect D w t hw ht).1
  have hn := normalizationCorrect w t hd
  exact ⟨hd,hn.2.1,hn.2.2.1⟩

end LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
