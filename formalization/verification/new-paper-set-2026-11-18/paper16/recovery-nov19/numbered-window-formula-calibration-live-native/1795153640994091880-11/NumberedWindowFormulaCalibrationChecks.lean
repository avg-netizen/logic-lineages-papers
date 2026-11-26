module
public import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation PositiveArithmeticOperators
open PositiveArithmeticTransforms (tagNumber)
open NumberedWindowFormulaCalibrationTargets NumberedWindowInternalPresentationTargets
open NumberedWindowPresentationClauses
open NumberedWindowInternalPresentationChecks

private theorem one (b : Bool) : b.toNat = 1 ↔ b = true := by cases b <;> decide

theorem exact_InterpretsEvaluatingPrograms : InterpretsEvaluatingPrograms := by
  intro f i j r d h context P
  obtain ⟨hi, hj, hr, hd⟩ := h
  have ci (x) : DomainHolds i x ↔ f.scalar x = true := by
    unfold DomainHolds
    rw [hi, one]
  have cj (x) : DomainHolds j x ↔ f.multiset x = true := by
    unfold DomainHolds
    rw [hj, one]
  have cr (x y) : CertificateHolds r x y ↔ ∃ c, f.positive x c y = true := by
    unfold CertificateHolds
    simp only [hr, one]
  have cd (x y) : CertificateHolds d x y ↔ ∃ c, f.direct x c y = true := by
    unfold CertificateHolds
    simp only [hd, one]
  have branches (x : Nat) := exact_TaggedSemantics i j r d context P x
  simp only [ci, cj, cr, cd, tagNumber, Bool.false_eq_true, if_false, if_true] at branches
  constructor
  · intro z
    constructor
    · intro hz
      obtain ⟨⟨b,x⟩, heq, _⟩ := TaggedArithmeticOperatorsProof.tagPartition z
      cases b
      · subst z
        exact Or.inl ⟨x,rfl,(branches x).1.mp hz⟩
      · subst z
        exact Or.inr ⟨x,rfl,(branches x).2.mp hz⟩
    · rintro (⟨x,rfl,hx⟩ | ⟨x,rfl,hx⟩)
      · exact (branches x).1.mpr hx
      · exact (branches x).2.mpr hx
  · simpa only [terms, ci, tagNumber, Bool.false_eq_true, if_false] using
      exact_AllTermsSemantics i j r d context P

#print axioms exact_InterpretsEvaluatingPrograms
end LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
