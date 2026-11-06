module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open AdjacentRangeWordGuardCompletion

private theorem coreWord_cons (a : Letter) (w : Word) :
    coreWord (a::w) = if coreWord w = [] ∧ a.1 = 0 then [] else a::coreWord w := by
  simp only [coreWord,splitWord,List.foldr_cons,splitStep]
  split <;> rfl

private theorem shiftSuffix_cons (a : Letter) (w : Word) :
    shiftSuffix (a::w) =
      if coreWord w = [] ∧ a.1 = 0 then a::shiftSuffix w else shiftSuffix w := by
  simp only [shiftSuffix,coreWord,splitWord,List.foldr_cons,splitStep]
  split <;> rfl

private theorem split_decomposition (w : Word) :
    w = coreWord w ++ shiftSuffix w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      by_cases h : coreWord w = [] ∧ a.1 = 0
      · have hw : w = shiftSuffix w := by
          simpa only [h.1,List.nil_append] using ih
        simpa only [coreWord_cons,shiftSuffix_cons,if_pos h,List.nil_append]
          using congrArg (List.cons a) hw
      · simpa only [coreWord_cons,shiftSuffix_cons,if_neg h,List.cons_append]
          using congrArg (List.cons a) ih

private theorem suffix_shiftOnly (w : Word) : ShiftOnly (shiftSuffix w) := by
  induction w with
  | nil =>
      intro a ha
      cases ha
  | cons a w ih =>
      by_cases h : coreWord w = [] ∧ a.1 = 0
      · rw [shiftSuffix_cons,if_pos h]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact h.2
        · exact ih b hb
      · rw [shiftSuffix_cons,if_neg h]
        exact ih

private theorem core_last_nonshift (w : Word) :
    coreWord w = [] ∨ ∃ A a, coreWord w = A++[a] ∧ a.1 ≠ 0 := by
  induction w with
  | nil => exact Or.inl rfl
  | cons a w ih =>
      by_cases h : coreWord w = [] ∧ a.1 = 0
      · exact Or.inl (by rw [coreWord_cons,if_pos h])
      · right
        rw [coreWord_cons,if_neg h]
        rcases ih with hw | ⟨A,b,hA,hb⟩
        · have ha : a.1 ≠ 0 := fun ha => h ⟨hw,ha⟩
          exact ⟨[],a,by simp only [hw,List.nil_append],ha⟩
        · refine ⟨a::A,b,?_,hb⟩
          simp only [hA,List.cons_append]

private theorem core_empty_iff (w : Word) : coreWord w = [] ↔ ShiftOnly w := by
  induction w with
  | nil => simp [coreWord,splitWord,ShiftOnly]
  | cons a w ih =>
      rw [coreWord_cons]
      by_cases h : coreWord w = [] ∧ a.1 = 0
      · rw [if_pos h]
        constructor
        · intro _ b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact h.2
          · exact ih.mp h.1 b hb
        · intro _
          rfl
      · rw [if_neg h]
        constructor
        · intro he
          cases he
        · intro hw
          have ht : ShiftOnly w := fun b hb => hw b (List.mem_cons_of_mem a hb)
          have ha : a.1 = 0 := hw a (by simp)
          exact False.elim (h ⟨ih.mpr ht,ha⟩)

/-- The decomposition preserves the literal letters and identifies the maximal
all-shift suffix, including the empty-word and all-shift cases. -/
theorem splitSyntax : Targets.SplitSyntax := by
  intro w
  exact ⟨split_decomposition w,suffix_shiftOnly w,core_last_nonshift w,core_empty_iff w⟩

/-- Unused fields on a shift never restrict its degree admission. -/
theorem shiftOnly_allowed (D : Nat) (w : Word) (hw : ShiftOnly w) : WordAllowed D w := by
  intro a ha
  simp [LetterAllowed,hw a ha]

private theorem shiftOnly_counterNodes : ∀ w : Word, ShiftOnly w → counterNodes w = 0 := by
  intro w
  induction w with
  | nil =>
      intro _
      rfl
  | cons a w ih =>
      intro hw
      have ha : a.1 = 0 := hw a (by simp)
      have ht : ShiftOnly w := fun b hb => hw b (List.mem_cons_of_mem a hb)
      simpa [counterNodes,ha] using ih ht

private theorem shiftOnly_rangeNodes (r : Nat) :
    ∀ w : Word, ShiftOnly w → rangeNodes (r+1) w = 0 := by
  intro w
  induction w with
  | nil =>
      intro _
      rfl
  | cons a w ih =>
      intro hw
      have ha : a.1 = 0 := hw a (by simp)
      have ht : ShiftOnly w := fun b hb => hw b (List.mem_cons_of_mem a hb)
      have hr : rangeRank a = 0 := by simp [rangeRank,ha]
      have hn : (0 : Nat) ≠ r+1 := by omega
      simpa [rangeNodes,hr,hn] using ih ht

private theorem counterNodes_append (A B : Word) :
    counterNodes (A++B) = counterNodes A+counterNodes B := by
  simp [counterNodes,List.filter_append]

private theorem rangeNodes_append (r : Nat) (A B : Word) :
    rangeNodes r (A++B) = rangeNodes r A+rangeNodes r B := by
  simp [rangeNodes,List.filter_append]

/-- Combining the literal shift suffix leaves all nonlinear occurrence counts
unchanged, and preserves the original degree bound. -/
theorem normalizationSyntax : Targets.NormalizationSyntax := by
  intro D w hw
  have hs := splitSyntax w
  have hC : WordAllowed D (coreWord w) := by
    intro a ha
    apply hw a
    rw [hs.1]
    exact List.mem_append.mpr (Or.inl ha)
  have hS : WordAllowed D (shiftSuffix w) := shiftOnly_allowed D _ hs.2.1
  have hN : WordAllowed D (normalizedWord w) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hC a ha
    · have he := List.mem_singleton.mp ha
      subst a
      simp [LetterAllowed,shiftLetter]
  refine ⟨hC,hS,hN,?_,?_⟩
  · have hOriginal : counterNodes w = counterNodes (coreWord w) := by
      calc
        counterNodes w = counterNodes (coreWord w ++ shiftSuffix w) :=
          congrArg counterNodes hs.1
        _ = counterNodes (coreWord w) := by
          rw [counterNodes_append,shiftOnly_counterNodes _ hs.2.1,Nat.add_zero]
    calc
      counterNodes (normalizedWord w) = counterNodes (coreWord w) := by
        simp [normalizedWord,counterNodes,List.filter_append,shiftLetter]
      _ = counterNodes w := hOriginal.symm
  · intro r
    have hOriginal : rangeNodes (r+1) w = rangeNodes (r+1) (coreWord w) := by
      calc
        rangeNodes (r+1) w = rangeNodes (r+1) (coreWord w ++ shiftSuffix w) :=
          congrArg (rangeNodes (r+1)) hs.1
        _ = rangeNodes (r+1) (coreWord w) := by
          rw [rangeNodes_append,shiftOnly_rangeNodes r _ hs.2.1,Nat.add_zero]
    have hn : (0 : Nat) ≠ r+1 := by omega
    calc
      rangeNodes (r+1) (normalizedWord w) = rangeNodes (r+1) (coreWord w) := by
        simp [normalizedWord,rangeNodes,List.filter_append,rangeRank,shiftLetter,hn]
      _ = rangeNodes (r+1) w := hOriginal.symm

end LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
