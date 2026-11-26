module
public import LogicLineages.StandardControlCurrent.OrderedGuardsTargets
public import LogicLineages.StandardControlCurrent.UniformSeparationProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedGuardsProof
open OrdinalComparison PolynomialGraphCompletion

theorem letterCalibration (D : Nat) (a : Letter) (ha : LetterAllowed D a) (t : Nat) :
    (OrderedGuards.LetterDomain a t ↔ LetterDomain a t) ∧
    (OrderedGuards.LetterDomain a t → OrderedGuards.letterValue a t = letterValue a t) := by
  by_cases h0 : a.1 = 0
  · simp [OrderedGuards.LetterDomain,LetterDomain,OrderedGuards.letterValue,letterValue,h0]
  by_cases h1 : a.1 = 1
  · simp [OrderedGuards.LetterDomain,LetterDomain,OrderedGuards.letterValue,letterValue,h0,h1]
  by_cases h2 : a.1 = 2
  · simp [OrderedGuards.LetterDomain,LetterDomain,OrderedGuards.letterValue,letterValue,h0,h1,h2]
  have hn : ¬ a.1 ≤ 2 := by omega
  have hd : 3 ≤ a.2.1 := (by simpa only [LetterAllowed,if_neg hn] using ha :
    (a.1 = 3 ∨ a.1 = 4) ∧ 3 ≤ a.2.1 ∧ a.2.1 ≤ D).2.1
  by_cases h3 : a.1 = 3
  · simp only [OrderedGuards.LetterDomain,LetterDomain,OrderedGuards.letterValue,letterValue,
      if_neg h0,if_neg h1,if_neg h2,if_pos h3]
    constructor
    · constructor
      · rintro ⟨hc,hpos⟩
        exact ⟨hc,by simpa only [((UniformSeparationProof.calibration _ _ _ (by omega) hc).2.2 a.2.2.2).1] using hpos⟩
      · rintro ⟨hc,hpos⟩
        exact ⟨hc,by simpa only [((UniformSeparationProof.calibration _ _ _ (by omega) hc).2.2 a.2.2.2).1] using hpos⟩
    · intro h
      exact ((UniformSeparationProof.calibration _ _ _ (by omega) h.1).2.2 a.2.2.2).2.symm
  · simp only [OrderedGuards.LetterDomain,LetterDomain,OrderedGuards.letterValue,letterValue,
      if_neg h0,if_neg h1,if_neg h2,if_neg h3]
    exact ⟨Iff.rfl,fun h => (UniformSeparationProof.calibration _ _ _ (by omega) h.2).1.symm⟩

theorem wordCalibration : OrderedGuardsTargets.WordCalibration := by
  intro D w
  induction w with
  | nil => intro _ t; exact ⟨Iff.rfl,fun _ => rfl⟩
  | cons a w ih =>
    intro hw t
    have ha : LetterAllowed D a := hw a (by simp)
    have ht : WordAllowed D w := fun b hb => hw b (by simp [hb])
    have hl := letterCalibration D a ha t
    constructor
    · constructor
      · rintro ⟨h,hrest⟩
        refine ⟨hl.1.mp h,?_⟩
        rw [← hl.2 h]
        exact (ih ht _).1.mp hrest
      · rintro ⟨h,hrest⟩
        have hnew := hl.1.mpr h
        refine ⟨hnew,?_⟩
        rw [← hl.2 hnew] at hrest
        exact (ih ht _).1.mpr hrest
    · rintro ⟨h,hrest⟩
      change OrderedGuards.wordValue w (OrderedGuards.letterValue a t) = wordValue w (letterValue a t)
      rw [(ih ht _).2 hrest,hl.2 h]
end LogicLineages.StandardControlCurrent.OrderedGuardsProof
