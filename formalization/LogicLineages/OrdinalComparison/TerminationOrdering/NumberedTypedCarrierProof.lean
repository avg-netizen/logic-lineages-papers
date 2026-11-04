module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierProof
open Source NumberedTypedCarrier NumberedNumericCarrier NumberedLeastCodeRepresentative

theorem typedRepresentativeAttained : NumberedTypedCarrierTargets.ActualTypedRepresentativeAttained := by
  intro n arity symbols S hc Gamma q hq
  obtain ⟨r,hqr,hnum⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained n arity symbols S hc Gamma q hq
  have ht := NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma q r
    (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma q r hqr)
  have hr := (NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S Gamma q r hqr).mp hq
  exact ⟨r,hqr,ht.symm,hr,hnum⟩

theorem typedCanonicalCarrier : NumberedTypedCarrierTargets.ActualTypedCanonicalCarrier := by
  intro n arity symbols S hc Gamma tau value
  constructor
  · intro h
    cases hd : decodeUniverse n arity symbols S Gamma value with
    | none => simp [typedCanonicalCarrierTest,hd] at h
    | some q =>
      have hp := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value q).mp hd
      have hb : q.1=tau ∧ representativeCode symbols S q=value := by
        simpa [typedCanonicalCarrierTest,hd] using h
      exact ⟨q,hp.2,hb⟩
  · rintro ⟨q,hq,ht,he⟩
    obtain ⟨r,hqr,hrt,hr,hatt⟩ := typedRepresentativeAttained n arity symbols S hc Gamma q hq
    have hnum : packedNumber r=value := hatt.symm.trans he
    have hre : representativeCode symbols S r=value :=
      ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q r hq hr).mpr hqr).symm.trans he
    have hd := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value r).mpr ⟨hnum,hr⟩
    have hrtype : r.1=tau := hrt.trans ht
    simp [typedCanonicalCarrierTest,hd,hrtype,hre]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierProof
