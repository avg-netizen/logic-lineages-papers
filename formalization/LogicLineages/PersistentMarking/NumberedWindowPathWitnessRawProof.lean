import LogicLineages.PersistentMarking.NumberedWindowPathWitnessTargets
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessChecks

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessRawProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowLiteralEquality NumberedWindowTypingBits
open NumberedWindowRawWitnessBits NumberedWindowRawWitnessLaws
open NumberedWindowArithmeticLeastClass
open NumberedWindowPathWitnessBits NumberedWindowPathWitnessTargets

theorem sound (S : Signature) (K Γ : List Ty) (τ : Ty) :
    ∀ es Q R, rawPathBit S K Γ τ Q es R = true → WindowPath S K (finiteC Γ) τ Q R := by
  intro es
  induction es with
  | nil =>
    intro Q R h
    change (termEq Q R && finiteWindowBit S K Γ τ Q) = true at h
    obtain ⟨e,hw⟩ := Bool.and_eq_true_iff.mp h
    have hQR := (termEqTrue Q R).mp e
    subst R
    exact .refl ((NumberedWindowTypingBitsChecks.exact_FiniteWindowBit S K Γ τ Q).mp hw)
  | cons e es ih =>
    intro Q R h
    change (finiteWindowWitnessBit S K Γ τ e.witness Q e.target &&
      rawPathBit S K Γ τ e.target es R) = true at h
    obtain ⟨he,ht⟩ := Bool.and_eq_true_iff.mp h
    have hs := (NumberedWindowRawWitnessChecks.exact_CertifiedFiniteWindowStep
      S K Γ τ Q e.target).mp ⟨e.witness,he⟩
    exact .next hs (ih _ _ ht)

theorem complete {S K Γ τ Q R} (h : WindowPath S K (finiteC Γ) τ Q R) :
    ∃ es, rawPathBit S K Γ τ Q es R = true := by
  induction h with
  | @refl Q hw =>
    refine ⟨[],?_⟩
    change (termEq Q Q && finiteWindowBit S K Γ τ Q) = true
    exact Bool.and_eq_true_iff.mpr
      ⟨termRefl Q,(NumberedWindowTypingBitsChecks.exact_FiniteWindowBit S K Γ τ Q).mpr hw⟩
  | @next Q M R hs _ ih =>
    obtain ⟨w,hw⟩ := (NumberedWindowRawWitnessChecks.exact_CertifiedFiniteWindowStep
      S K Γ τ Q M).mpr hs
    obtain ⟨es,he⟩ := ih
    refine ⟨⟨M,w⟩ :: es,?_⟩
    exact Bool.and_eq_true_iff.mpr ⟨hw,he⟩

theorem exactPath : ExactCertifiedFiniteRawPath := by
  intro S K Γ τ Q R
  exact ⟨fun ⟨es,he⟩ => sound S K Γ τ es Q R he, complete⟩

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessRawProof
