module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordValueProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordFormulaProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordCodeCalibrationProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordNumericProgramsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.StatementChecks

theorem letter_exact : Targets.LetterCorrect := Proof.letterCorrect
theorem letter_domain_exact : Targets.LetterDomainCorrect := Proof.letterDomainCorrect
theorem word_exact : Targets.WordCorrect := Proof.wordCorrect
theorem word_domain_exact : Targets.WordDomainCorrect := Proof.wordDomainCorrect
theorem letter_programs : Targets.LetterPrograms := Proof.letterPrograms
theorem word_programs : Targets.WordPrograms := Proof.wordPrograms
theorem row_substitution_exact : Targets.RowSubstitution := Proof.rowSubstitution
theorem formula_substitution_exact : Targets.FormulaSubstitution := Proof.formulaSubstitution
theorem support_exact : Targets.ExactSupport := Proof.exactSupport
theorem literal_code_exact : Targets.LiteralCodeCalibration := Proof.literalCodeCalibration
theorem numeric_programs : Targets.NumericPrograms := Proof.Numeric.numericPrograms

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.StatementChecks
