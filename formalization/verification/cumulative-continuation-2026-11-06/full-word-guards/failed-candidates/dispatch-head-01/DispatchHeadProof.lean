module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchLocalProof
import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchHeadProof
open PolynomialGraphCompletion CanonicalGuardSelector CounterRangeWordGuardCompletion
open DispatchLocalProof

/-- The same admitted canonical-head classification used by the accepted
selector; only the local proof is reproduced, without altering its source. -/
private theorem canonical_head_cases (D : Nat) (a : Letter)
    (ha : LetterAllowed D a) (hc : IsCanonical a) (hz : a.1 ≠ 0) :
    a = phiLetter ∨ (∃ j, a = quadraticLetter j) ∨
    (∃ n c j, n+3 ≤ D ∧ a = kernelLetter (n+3) c j) ∨
    (∃ n c, n+3 ≤ D ∧ a = counterLetter (n+3) c) := by
  have ht : a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 ∨ a.1 = 4 := by
    unfold LetterAllowed at ha
    split at ha
    · omega
    · rcases ha.1 with h | h <;> omega
  have he : canonicalHead a = a := hc
  rcases ht with h | h | h | h
  · exact Or.inl (by simpa [canonicalHead,h] using he.symm)
  · exact Or.inr (Or.inl ⟨a.2.2.2,by simpa [canonicalHead,h] using he.symm⟩)
  · have hd : 3 ≤ a.2.1 ∧ a.2.1 ≤ D := by
      simpa [LetterAllowed,h] using ha
    have hn : a.2.1-3+3 = a.2.1 := by omega
    refine Or.inr (Or.inr (Or.inl ⟨a.2.1-3,a.2.2.1,a.2.2.2,by omega,?_⟩))
    simpa [canonicalHead,h,hn] using he.symm
  · have hd : 3 ≤ a.2.1 ∧ a.2.1 ≤ D := by
      simpa [LetterAllowed,h] using ha
    have hn : a.2.1-3+3 = a.2.1 := by omega
    refine Or.inr (Or.inr (Or.inr ⟨a.2.1-3,a.2.2.1,by omega,?_⟩))
    simpa [canonicalHead,h,hn] using he.symm

/-- All sixteen canonical nonlinear head pairs use the exact selected child
and exact original local cutoff. Reversal changes comparison orientation,
not the association of either child with its original raw input. -/
theorem headCorrect (D : Nat) (A : Word) (a : Letter) (B : Word) (b : Letter)
    (j k : Int) (hA : WordAllowed D A) (ha : LetterAllowed D a)
    (hca : IsCanonical a) (hza : a.1 ≠ 0)
    (hB : WordAllowed D B) (hb : LetterAllowed D b)
    (hcb : IsCanonical b) (hzb : b.1 ≠ 0) (x y : Nat)
    (hx : headTail A a B b j k ≤ x) (hy : headTail A a B b j k ≤ y) :
    let q := selectHeads A a B b
    Result (A++[a,shiftLetter j]) (B++[b,shiftLetter k])
      q.2.2.1 q.2.2.2 (headTie a b j k) x y := by
  rcases canonical_head_cases D a ha hca hza with rfl | ⟨i,rfl⟩ |
    ⟨n,c,i,hn,rfl⟩ | ⟨n,c,hn,rfl⟩
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · simpa [headTie,selectHeads,forwardTie,phiLetter] using
        (phiRange D A B phiLetter hA hB hb (by simp [RangeHead,phiLetter]) j k x y
          (by simpa [headTail,selectHeads,forwardTail,phiLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,phiLetter] using hy))
    · simpa [headTie,selectHeads,forwardTie,phiLetter,quadraticLetter] using
        (phiRange D A B (quadraticLetter l) hA hB hb
          (by simp [RangeHead,quadraticLetter]) j k x y
          (by simpa [headTail,selectHeads,forwardTail,phiLetter,quadraticLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,phiLetter,quadraticLetter] using hy))
    · simpa [headTie,selectHeads,forwardTie,phiLetter,kernelLetter] using
        (phiRange D A B (kernelLetter (m+3) e l) hA hB hb
          (by simp [RangeHead,kernelLetter]) j k x y
          (by simpa [headTail,selectHeads,forwardTail,phiLetter,kernelLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,phiLetter,kernelLetter] using hy))
    · have hs := counterRange D B A phiLetter hB hA ha
        (by simp [RangeHead,phiLetter]) m e k j hm y x
        (by simpa [headTail,selectHeads,forwardTail,phiLetter,counterLetter] using hy)
        (by simpa [headTail,selectHeads,forwardTail,phiLetter,counterLetter] using hx)
      simpa [headTie,selectHeads,forwardTie,phiLetter,counterLetter] using
        (reverse_result _ _ _ _ 0 y x (by omega) hs)
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · have hs := phiRange D B A (quadraticLetter i) hB hA ha
        (by simp [RangeHead,quadraticLetter]) k j y x
        (by simpa [headTail,selectHeads,forwardTail,phiLetter,quadraticLetter] using hy)
        (by simpa [headTail,selectHeads,forwardTail,phiLetter,quadraticLetter] using hx)
      simpa [headTie,selectHeads,forwardTie,phiLetter,quadraticLetter] using
        (reverse_result _ _ _ _ _ y x (ComparisonProof.orderInt_bound k j) hs)
    · simpa [headTie,selectHeads,forwardTie,quadraticLetter] using
        (quadratic D A B hA hB i l j k x y
          (by simpa [headTail,selectHeads,forwardTail,quadraticLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,quadraticLetter] using hy))
    · have hs := mixedQuadratic D B A hB hA m e l i k j hm y x
        (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,kernelLetter] using hy)
        (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,kernelLetter] using hx)
      simpa [headTie,selectHeads,forwardTie,quadraticLetter,kernelLetter] using
        (reverse_result _ _ _ _ _ y x
          (ComparisonProof.lexOrder_bound _ _
            (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _)) hs)
    · have hs := counterRange D B A (quadraticLetter i) hB hA ha
        (by simp [RangeHead,quadraticLetter]) m e k j hm y x
        (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,counterLetter] using hy)
        (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,counterLetter] using hx)
      simpa [headTie,selectHeads,forwardTie,quadraticLetter,counterLetter] using
        (reverse_result _ _ _ _ 0 y x (by omega) hs)
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · have hs := phiRange D B A (kernelLetter (n+3) c i) hB hA ha
        (by simp [RangeHead,kernelLetter]) k j y x
        (by simpa [headTail,selectHeads,forwardTail,phiLetter,kernelLetter] using hy)
        (by simpa [headTail,selectHeads,forwardTail,phiLetter,kernelLetter] using hx)
      simpa [headTie,selectHeads,forwardTie,phiLetter,kernelLetter] using
        (reverse_result _ _ _ _ _ y x (ComparisonProof.orderInt_bound k j) hs)
    · simpa [headTie,selectHeads,forwardTie,quadraticLetter,kernelLetter] using
        (mixedQuadratic D A B hA hB n c i l j k hn x y
          (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,kernelLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,kernelLetter] using hy))
    · by_cases heq : n = m
      · subst m
        simpa [headTie,selectHeads,forwardTie,kernelLetter] using
          (equalRank D A B hA hB (n+3) c e i l j k (by omega) hn x y
            (by simpa [headTail,selectHeads,forwardTail,kernelLetter] using hx)
            (by simpa [headTail,selectHeads,forwardTail,kernelLetter] using hy))
      · by_cases hlt : m < n
        · have hsame : n+3 ≠ m+3 := by omega
          have horder : m+3 < n+3 := by omega
          have hsub : n+3-(m+3)-1 = n-m-1 := by omega
          have hrank : m+(n-m-1)+4 = n+3 := by omega
          have hD : m+(n-m-1)+4 ≤ D := by omega
          simpa [headTie,selectHeads,forwardTie,kernelLetter,hsame,horder,hsub,hrank] using
            (mixedKernel D A B hA hB m (n-m-1) c e i l j k hD x y
              (by simpa [headTail,selectHeads,forwardTail,kernelLetter,hsame,horder,hsub] using hx)
              (by simpa [headTail,selectHeads,forwardTail,kernelLetter,hsame,horder,hsub] using hy))
        · have hsame : n+3 ≠ m+3 := by omega
          have horder : ¬ m+3 < n+3 := by omega
          have hsub : m+3-(n+3)-1 = m-n-1 := by omega
          have hrank : n+(m-n-1)+4 = m+3 := by omega
          have hD : n+(m-n-1)+4 ≤ D := by omega
          have hs := mixedKernel D B A hB hA n (m-n-1) e c l i k j hD y x
            (by simpa [headTail,selectHeads,forwardTail,kernelLetter,hsame,horder,hsub] using hy)
            (by simpa [headTail,selectHeads,forwardTail,kernelLetter,hsame,horder,hsub] using hx)
          simpa [headTie,selectHeads,forwardTie,kernelLetter,hsame,horder,hsub,hrank] using
            (reverse_result _ _ _ _ _ y x
              (ComparisonProof.lexOrder_bound _ _
                (ComparisonProof.orderNat_bound _ _)
                (ComparisonProof.lexOrder_bound _ _
                  (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _))) hs)
    · have hs := counterRange D B A (kernelLetter (n+3) c i) hB hA ha
        (by simp [RangeHead,kernelLetter]) m e k j hm y x
        (by simpa [headTail,selectHeads,forwardTail,kernelLetter,counterLetter] using hy)
        (by simpa [headTail,selectHeads,forwardTail,kernelLetter,counterLetter] using hx)
      simpa [headTie,selectHeads,forwardTie,kernelLetter,counterLetter] using
        (reverse_result _ _ _ _ 0 y x (by omega) hs)
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · simpa [headTie,selectHeads,forwardTie,phiLetter,counterLetter] using
        (counterRange D A B phiLetter hA hB hb (by simp [RangeHead,phiLetter])
          n c j k hn x y
          (by simpa [headTail,selectHeads,forwardTail,phiLetter,counterLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,phiLetter,counterLetter] using hy))
    · simpa [headTie,selectHeads,forwardTie,quadraticLetter,counterLetter] using
        (counterRange D A B (quadraticLetter l) hA hB hb
          (by simp [RangeHead,quadraticLetter]) n c j k hn x y
          (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,counterLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,quadraticLetter,counterLetter] using hy))
    · simpa [headTie,selectHeads,forwardTie,kernelLetter,counterLetter] using
        (counterRange D A B (kernelLetter (m+3) e l) hA hB hb
          (by simp [RangeHead,kernelLetter]) n c j k hn x y
          (by simpa [headTail,selectHeads,forwardTail,kernelLetter,counterLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,kernelLetter,counterLetter] using hy))
    · simpa [headTie,selectHeads,forwardTie,counterLetter] using
        (counterCounter D A B hA hB n m c e j k hn hm x y
          (by simpa [headTail,selectHeads,forwardTail,counterLetter] using hx)
          (by simpa [headTail,selectHeads,forwardTail,counterLetter] using hy))

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchHeadProof
