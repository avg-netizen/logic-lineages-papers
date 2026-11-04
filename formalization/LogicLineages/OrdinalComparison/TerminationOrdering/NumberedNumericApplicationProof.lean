module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedNumericCarrier
open NumberedLeastCodeRepresentative NumberedQuotientApplication NumberedNumericApplication
open NumberedNumericApplicationSupportProof

theorem canonicalApplicationSound : NumberedNumericApplicationTargets.ActualCanonicalApplicationSound := by
  intro n arity symbols S hc Gamma sigma tau x y z h
  cases hf : decodeUniverse n arity symbols S Gamma x with
  | none => simp [canonicalApplication,hf] at h
  | some f =>
    cases ha : decodeUniverse n arity symbols S Gamma y with
    | none => simp [canonicalApplication,hf,ha] at h
    | some a =>
      rcases f with ⟨fty,f⟩
      rcases a with ⟨aty,a⟩
      by_cases ht : fty = .arrow sigma tau
      · subst fty
        by_cases hu : aty=sigma
        · subst aty
          by_cases he : representativeCode symbols S ⟨.arrow sigma tau,f⟩=x ∧ representativeCode symbols S ⟨sigma,a⟩=y
          · have hfG := ((NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma x ⟨.arrow sigma tau,f⟩).mp hf).2
            have haG := ((NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma y ⟨sigma,a⟩).mp ha).2
            have hz : representativeCode symbols S (applicationPacked f a)=z := by
              simpa [canonicalApplication,hf,ha,he.1,he.2] using h
            refine ⟨f,a,hfG,haG,he.1,he.2,hz,?_⟩
            exact (NumberedTypedCarrierProof.typedCanonicalCarrier n arity symbols S hc Gamma tau z).mpr
              ⟨applicationPacked f a,NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity symbols S hc Gamma sigma tau f a hfG haG,rfl,hz⟩
          · simp [canonicalApplication,hf,ha,he] at h
        · simp [canonicalApplication,hf,ha,hu] at h
      · simp [canonicalApplication,hf,ha,ht] at h

theorem canonicalApplicationCalibration : NumberedNumericApplicationTargets.ActualCanonicalApplicationCalibration := by
  intro n arity symbols S hc Gamma sigma tau f a hf ha
  obtain ⟨g,hg,hdg,heg⟩ := decodedRepresentative n arity symbols S hc Gamma (.arrow sigma tau) f hf
  obtain ⟨b,hb,hdb,heb⟩ := decodedRepresentative n arity symbols S hc Gamma sigma a ha
  have he := evaluateOnDecoded n arity symbols S Gamma sigma tau _ _ g b hdg hdb heg heb
  have happ := NumberedQuotientApplicationProof.representativeApplicationCongruence n arity symbols S hc Gamma sigma tau g f b a hg hf hb ha heg heb
  exact he.trans (congrArg some happ)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationProof
