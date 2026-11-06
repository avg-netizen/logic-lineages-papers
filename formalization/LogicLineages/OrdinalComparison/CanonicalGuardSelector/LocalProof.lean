module
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.Targets
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.LeaderProof
public import LogicLineages.OrdinalComparison.RangePhiFactorization.HeadProof
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.KernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
open PolynomialGraphCompletion OuterShiftNormalization CounterWordGuardCompletion
open CounterRangeWordGuardCompletion MixedRangeWordGuardCompletion GuardChildMeasureCompletion

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

private theorem prefix_allowed (D : Nat) (A B : Word)
    (h : WordAllowed D (A++B)) : WordAllowed D A := by
  intro a ha
  exact h a (List.mem_append.mpr (Or.inl ha))

private theorem range_input_allowed (D : Nat) (B : Word) (a : Letter)
    (hB : WordAllowed D B) (ha : LetterAllowed D a) (hr : RangeHead a) :
    WordAllowed D (rangeInputWord B a) := by
  apply RangePhiFactorization.Proof.word_allowed_append D B _ hB
  by_cases h1 : a.1 = 1
  · simp [preimageWord,h1,WordAllowed]
  · have hr' : RangePhiFactorization.RangeHead a := by
      rcases hr with h | h
      · exact False.elim (h1 h)
      · exact h
    rw [preimageWord,if_neg h1]
    exact RangePhiFactorization.Proof.singleton_allowed D _
      (RangePhiFactorization.Proof.predecessorHeadSyntax D a ha hr').1

private theorem head_word_allowed (D : Nat) (A : Word) (a : Letter) (j : Int)
    (hA : WordAllowed D A) (ha : LetterAllowed D a) :
    WordAllowed D (A++[a,shiftLetter j]) := by
  apply RangePhiFactorization.Proof.word_allowed_append D A _ hA
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · have h := List.mem_singleton.mp hb
    subst b
    simp [shiftLetter,LetterAllowed]

/-- Admission follows the same literal child constructor, including reversal. -/
private theorem guard_case_allowed {D code : Nat} {rev : Bool} {next current : WordPair}
    (h : GuardCase D code rev next current) :
    WordAllowed D current.1 → WordAllowed D current.2 →
    WordAllowed D next.1 ∧ WordAllowed D next.2 := by
  induction h with
  | counterCounter A B n m c e j k hn hm =>
      intro hA hB
      exact ⟨RangePhiFactorization.Proof.word_allowed_append D A _
          (prefix_allowed D A _ hA) (CounterWordGuardCompletion.Proof.leaderWord_allowed D n c hn),
        RangePhiFactorization.Proof.word_allowed_append D B _
          (prefix_allowed D B _ hB) (CounterWordGuardCompletion.Proof.leaderWord_allowed D m e hm)⟩
  | counterRange A B a n c j k ha hr hn =>
      intro hA hB
      exact ⟨RangePhiFactorization.Proof.word_allowed_append D A _
          (prefix_allowed D A _ hA) (CounterWordGuardCompletion.Proof.leaderWord_allowed D n c hn),
        range_input_allowed D B a (prefix_allowed D B _ hB) ha hr⟩
  | phiRange A B a j k ha hr =>
      intro hA hB
      exact ⟨prefix_allowed D A _ hA,
        range_input_allowed D B a (prefix_allowed D B _ hB) ha hr⟩
  | quadratic A B j k a b =>
      intro hA hB
      exact ⟨prefix_allowed D A _ hA,prefix_allowed D B _ hB⟩
  | equalRank A B d c e j k a b hd hD =>
      intro hA hB
      exact ⟨prefix_allowed D A _ hA,prefix_allowed D B _ hB⟩
  | mixedKernel A B n m c e j k a b hD =>
      intro hA hB
      exact ⟨MixedRangeWordGuardCompletion.Proof.retainedWord_allowed D A (n+1) m c
          (prefix_allowed D A _ hA) (by omega),prefix_allowed D B _ hB⟩
  | mixedQuadratic A B m c j k a b hD =>
      intro hA hB
      exact ⟨MixedRangeWordGuardCompletion.Proof.retainedWord_allowed D A 0 m c
          (prefix_allowed D A _ hA) (by omega),prefix_allowed D B _ hB⟩
  | reverse h ih =>
      intro hA hB
      have hh := ih hB hA
      exact ⟨hh.2,hh.1⟩

/-- Case numbers and orientation are certified together with the exact child. -/
private theorem select_heads_case (D : Nat) (A : Word) (a : Letter)
    (B : Word) (b : Letter) (j k : Int)
    (ha : LetterAllowed D a) (hca : IsCanonical a) (hza : a.1 ≠ 0)
    (hb : LetterAllowed D b) (hcb : IsCanonical b) (hzb : b.1 ≠ 0) :
    let q := selectHeads A a B b
    GuardCase D q.1 q.2.1 q.2.2 (A++[a,shiftLetter j],B++[b,shiftLetter k]) := by
  rcases canonical_head_cases D a ha hca hza with rfl | ⟨i,rfl⟩ |
    ⟨n,c,i,hn,rfl⟩ | ⟨n,c,hn,rfl⟩
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · simpa [selectHeads,phiLetter] using
        GuardCase.phiRange (D := D) A B phiLetter j k hb (by simp [RangeHead,phiLetter])
    · simpa [selectHeads,phiLetter,quadraticLetter] using
        GuardCase.phiRange (D := D) A B (quadraticLetter l) j k hb
          (by simp [RangeHead,quadraticLetter])
    · simpa [selectHeads,phiLetter,kernelLetter] using
        GuardCase.phiRange (D := D) A B (kernelLetter (m+3) e l) j k hb
          (by simp [RangeHead,kernelLetter])
    · simpa [selectHeads,phiLetter,counterLetter] using
        GuardCase.reverse (GuardCase.counterRange (D := D) B A phiLetter m e k j ha
          (by simp [RangeHead,phiLetter]) hm)
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · simpa [selectHeads,phiLetter,quadraticLetter] using
        GuardCase.reverse (GuardCase.phiRange (D := D) B A (quadraticLetter i) k j ha
          (by simp [RangeHead,quadraticLetter]))
    · simpa [selectHeads,quadraticLetter] using
        GuardCase.quadratic (D := D) A B i l j k
    · simpa [selectHeads,quadraticLetter,kernelLetter] using
        GuardCase.reverse (GuardCase.mixedQuadratic (D := D) B A m e l i k j hm)
    · simpa [selectHeads,quadraticLetter,counterLetter] using
        GuardCase.reverse (GuardCase.counterRange (D := D) B A (quadraticLetter i)
          m e k j ha (by simp [RangeHead,quadraticLetter]) hm)
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · simpa [selectHeads,phiLetter,kernelLetter] using
        GuardCase.reverse (GuardCase.phiRange (D := D) B A (kernelLetter (n+3) c i)
          k j ha (by simp [RangeHead,kernelLetter]))
    · simpa [selectHeads,quadraticLetter,kernelLetter] using
        GuardCase.mixedQuadratic (D := D) A B n c i l j k hn
    · by_cases heq : n = m
      · subst m
        simpa [selectHeads,kernelLetter] using
          GuardCase.equalRank (D := D) A B (n+3) c e i l j k (by omega) hn
      · by_cases hlt : m < n
        · have hsame : n+3 ≠ m+3 := by omega
          have horder : m+3 < n+3 := by omega
          have hsub : n+3-(m+3)-1 = n-m-1 := by omega
          have hrank : m+(n-m-1)+4 = n+3 := by omega
          have hD : m+(n-m-1)+4 ≤ D := by omega
          simpa [selectHeads,kernelLetter,heq,hsame,horder,hsub,hrank] using
            GuardCase.mixedKernel (D := D) A B m (n-m-1) c e i l j k hD
        · have hsame : n+3 ≠ m+3 := by omega
          have horder : ¬ m+3 < n+3 := by omega
          have hsub : m+3-(n+3)-1 = m-n-1 := by omega
          have hrank : n+(m-n-1)+4 = m+3 := by omega
          have hD : n+(m-n-1)+4 ≤ D := by omega
          simpa [selectHeads,kernelLetter,heq,hsame,horder,hsub,hrank] using
            GuardCase.reverse
              (GuardCase.mixedKernel (D := D) B A n (m-n-1) e c l i k j hD)
    · simpa [selectHeads,kernelLetter,counterLetter] using
        GuardCase.reverse (GuardCase.counterRange (D := D) B A (kernelLetter (n+3) c i)
          m e k j ha (by simp [RangeHead,kernelLetter]) hm)
  · rcases canonical_head_cases D b hb hcb hzb with rfl | ⟨l,rfl⟩ |
      ⟨m,e,l,hm,rfl⟩ | ⟨m,e,hm,rfl⟩
    · simpa [selectHeads,phiLetter,counterLetter] using
        GuardCase.counterRange (D := D) A B phiLetter n c j k hb
          (by simp [RangeHead,phiLetter]) hn
    · simpa [selectHeads,quadraticLetter,counterLetter] using
        GuardCase.counterRange (D := D) A B (quadraticLetter l) n c j k hb
          (by simp [RangeHead,quadraticLetter]) hn
    · simpa [selectHeads,kernelLetter,counterLetter] using
        GuardCase.counterRange (D := D) A B (kernelLetter (m+3) e l) n c j k hb
          (by simp [RangeHead,kernelLetter]) hn
    · simpa [selectHeads,counterLetter] using
        GuardCase.counterCounter (D := D) A B n m c e j k hn hm

theorem localSelectionCorrect : Targets.LocalSelectionCorrect := by
  intro D A a B b j k hA ha hca hza hB hb hcb hzb
  have hc := select_heads_case D A a B b j k ha hca hza hb hcb hzb
  exact ⟨hc,guard_case_allowed hc (head_word_allowed D A a j hA ha)
    (head_word_allowed D B b k hB hb)⟩

end LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
