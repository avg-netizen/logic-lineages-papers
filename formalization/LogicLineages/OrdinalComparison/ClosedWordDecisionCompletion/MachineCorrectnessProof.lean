module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchAssemblyProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchCodeProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.ConstantLeafProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineFiniteDepthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Machine
attribute [local irreducible] commonTail matrix Code.children children

theorem fuelValue_correct (D fuel floor : Nat) (p : Formula)
    (hD : 3 ≤ D) (hp : Formula.allowed D p) (hcount : (names p).length ≤ fuel) :
    fuelValue D fuel floor (Formula.encode p) = true ↔ SatisfiableAt floor p := by
  induction fuel generalizing floor p with
  | zero =>
    have hn : names p = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hcount)
    simpa only [fuelValue,CodeProof.names_calibration,hn,if_true] using
      ConstantLeafProof.exactConstantEvaluation floor p hn
  | succ fuel ih =>
    by_cases hn : names p = []
    · simpa only [fuelValue,CodeProof.names_calibration,hn,if_true] using
        ConstantLeafProof.exactConstantEvaluation floor p hn
    · simp only [fuelValue,CodeProof.names_calibration,if_neg hn,
        CodeProof.children_calibration,List.any_map,Function.comp_def]
      constructor
      · intro h
        obtain ⟨b,hb,htrue⟩ := List.any_eq_true.mp h
        have hs := BranchProof.actualChildSyntax D floor p hD hp b hb
        have hchildcount : (names b.2).length ≤ fuel := by
          have hlt := hs.2.2.2
          omega
        exact (BranchProof.actualChildEquivalence D floor p hD hp hn).mpr
          ⟨b,hb,(ih b.1 b.2 hs.2.1 hchildcount).mp htrue⟩
      · intro h
        obtain ⟨b,hb,htrue⟩ := (BranchProof.actualChildEquivalence D floor p hD hp hn).mp h
        have hs := BranchProof.actualChildSyntax D floor p hD hp b hb
        have hchildcount : (names b.2).length ≤ fuel := by
          have hlt := hs.2.2.2
          omega
        exact List.any_eq_true.mpr ⟨b,hb,(ih b.1 b.2 hs.2.1 hchildcount).mpr htrue⟩

theorem adequateFuelCorrectness : MachineTargets.AdequateFuelCorrectness := by
  intro D fuel floor p hD hp hcount
  rw [exactFiniteDepth]
  exact fuelValue_correct D fuel floor p hD hp hcount

theorem allowed_mono (D E : Nat) (p : Formula) (hDE : D ≤ E)
    (hp : Formula.allowed D p) : Formula.allowed E p := by
  intro t ht a ha
  have h := hp t ht a ha
  by_cases htag : a.1 ≤ 2
  · simp only [LetterAllowed,htag,if_true]
  · simp only [LetterAllowed,htag,if_false] at h ⊢
    exact ⟨h.1,h.2.1,h.2.2.trans hDE⟩

theorem actualClosedDecision : MachineTargets.ActualClosedDecision := by
  intro D p hp
  unfold solve
  rw [CodeProof.names_calibration]
  have hs := adequateFuelCorrectness (max 3 D) (names p).length 0 p
    (Nat.le_max_left _ _) (allowed_mono D (max 3 D) p (Nat.le_max_right _ _) hp) (Nat.le_refl _)
  apply hs.trans
  constructor
  · rintro ⟨ν,hfloor,hdomains,htrue⟩
    exact ⟨ν,hdomains,htrue⟩
  · rintro ⟨ν,hdomains,htrue⟩
    exact ⟨ν,fun _ _ => Nat.zero_le _,hdomains,htrue⟩

#print axioms fuelValue_correct
#print axioms adequateFuelCorrectness
#print axioms allowed_mono
#print axioms actualClosedDecision

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineProof
