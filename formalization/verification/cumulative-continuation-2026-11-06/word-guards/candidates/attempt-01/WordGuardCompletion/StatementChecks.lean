module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordGuardCompletion.StatementChecks

theorem fixed_letterTailCorrect : Targets.LetterTailCorrect := Proof.letterTailCorrect
theorem fixed_wordTailCorrect : Targets.WordTailCorrect := Proof.wordTailCorrect
theorem fixed_wordReachCorrect : Targets.WordReachCorrect := Proof.wordReachCorrect
theorem fixed_composedDomainCorrect : Targets.ComposedDomainCorrect := Proof.composedDomainCorrect
theorem fixed_tailPrograms : Targets.TailPrograms := Proof.tailPrograms

#print axioms fixed_letterTailCorrect
#print axioms fixed_wordTailCorrect
#print axioms fixed_wordReachCorrect
#print axioms fixed_composedDomainCorrect
#print axioms fixed_tailPrograms

end LogicLineages.OrdinalComparison.WordGuardCompletion.StatementChecks
