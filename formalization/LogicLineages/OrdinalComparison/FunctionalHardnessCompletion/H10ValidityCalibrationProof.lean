module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.Proof
open LogicLineages.ComputabilityKnowledge.PolynomialCircuit

theorem variablesValidity : Targets.VariablesValidity := by
  intro n vs
  simp [variablesValid]

theorem termsValidity : Targets.TermsValidity := by
  intro n ms
  simp [termsValid, variablesValid]

theorem inputValidity : Targets.InputValidity := by
  intro xs
  simp [validInput, Option.any_eq_true, termsValid, variablesValid, Code.WellFormed]

private theorem terms_roundtrip (ms : Monomials) : decodeTerms (encodeTerms ms) = some ms := by
  induction ms with
  | nil => simp [encodeTerms, decodeTerms]
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    cases z <;> simp [encodeTerms, decodeTerms, ih]

theorem canonicalValidity : Targets.CanonicalValidity := by
  intro p
  simp [validInput, LogicLineages.ComputabilityKnowledge.PolynomialCircuit.decode,
    LogicLineages.ComputabilityKnowledge.PolynomialCircuit.encode, terms_roundtrip,
    termsValid, variablesValid, Code.WellFormed]

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.Proof
