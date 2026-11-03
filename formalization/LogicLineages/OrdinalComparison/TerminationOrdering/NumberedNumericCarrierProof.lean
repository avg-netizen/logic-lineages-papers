module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier

theorem universeTestCorrect : NumberedNumericCarrierTargets.ActualUniverseTest := by
  intro Symbol inst arity symbols S Gamma tau q
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => argumentsUniverseTest symbols S args=true ↔
      auxArgumentTypesAllowed (fun tau => tau∈S) args ∧ auxArgumentsAllowed (HeadInWindow arity symbols S) args)
  all_goals simp_all [universeTest,argumentsUniverseTest,InUniverse,auxTypesAllowed,auxHeadsAllowed,
    auxArgumentTypesAllowed,auxArgumentsAllowed,and_assoc,and_left_comm,and_comm]

theorem argumentsUniverseTestCorrect : NumberedNumericCarrierTargets.ActualArgumentsUniverseTest := by
  intro Symbol inst arity symbols S Gamma types args
  induction types with
  | nil => cases args; simp [argumentsUniverseTest,auxArgumentTypesAllowed,auxArgumentsAllowed]
  | cons sigma types ih => cases args with
    | cons q rest =>
      have hq : universeTest symbols S q=true ↔ InUniverse symbols S q := universeTestCorrect Symbol inst arity symbols S Gamma sigma q
      simp [argumentsUniverseTest,hq,ih rest,InUniverse,auxArgumentTypesAllowed,auxArgumentsAllowed,and_assoc,and_left_comm,and_comm]

theorem numericUniverseDecode : NumberedNumericCarrierTargets.ActualNumericUniverseDecode := by
  intro n arity symbols S Gamma value q
  simp only [decodeUniverse,Option.filter_eq_some_iff]
  constructor
  · rintro ⟨hd,hg⟩
    exact ⟨NumberedNumericDecodingProof.packedNumericSound n arity Gamma value q hd,
      (universeTestCorrect (Fin n) inferInstance arity symbols S Gamma q.1 q.2).mp hg⟩
  · rintro ⟨he,hg⟩
    refine ⟨?_,(universeTestCorrect (Fin n) inferInstance arity symbols S Gamma q.1 q.2).mpr hg⟩
    rw [← he]
    exact NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma q

theorem rawCarrierTestCorrect : NumberedNumericCarrierTargets.ActualRawCarrierTest := by
  intro n arity symbols S Gamma value
  constructor
  · intro h
    cases hd : decodeUniverse n arity symbols S Gamma value with
    | none => simp [rawCarrierTest,hd] at h
    | some q =>
      have hp := (numericUniverseDecode n arity symbols S Gamma value q).mp hd
      exact ⟨q,hp.2,hp.1⟩
  · rintro ⟨q,hq,he⟩
    have hd := (numericUniverseDecode n arity symbols S Gamma value q).mpr ⟨he,hq⟩
    simp [rawCarrierTest,hd]

theorem canonicalCarrierTestCorrect : NumberedNumericCarrierTargets.ActualCanonicalCarrierTest := by
  intro n arity symbols S hc Gamma value
  constructor
  · intro h
    cases hd : decodeUniverse n arity symbols S Gamma value with
    | none => simp [canonicalCarrierTest,hd] at h
    | some q =>
      have hp := (numericUniverseDecode n arity symbols S Gamma value q).mp hd
      exact ⟨q,hp.2,by simpa [canonicalCarrierTest,hd] using h⟩
  · rintro ⟨q,hq,he⟩
    obtain ⟨r,hqr,hatt⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained n arity symbols S hc Gamma q hq
    have hr := (NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S Gamma q r hqr).mp hq
    have hnum : packedNumber r=value := hatt.symm.trans he
    have hre : representativeCode symbols S r=value :=
      ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q r hq hr).mpr hqr).symm.trans he
    have hd := (numericUniverseDecode n arity symbols S Gamma value r).mpr ⟨hnum,hr⟩
    simp [canonicalCarrierTest,hd,hre]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierProof
