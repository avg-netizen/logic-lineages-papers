import LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalProof
namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalChecks
open NumberedWindowArithmeticLexicalTargets NumberedWindowArithmeticLexicalProof
theorem exact_LiteralLexicalRequirements : LiteralLexicalRequirements := ⟨fun C q => term q C,fun C qs => args qs C⟩
theorem exact_ExactFiniteTypedChecker : ExactFiniteTypedChecker := finiteTyped
#print axioms exact_LiteralLexicalRequirements
#print axioms exact_ExactFiniteTypedChecker
end LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalChecks
