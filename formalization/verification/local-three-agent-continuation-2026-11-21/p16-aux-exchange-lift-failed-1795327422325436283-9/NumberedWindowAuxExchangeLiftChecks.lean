module

public import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTypingProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (rowAuxPair)
open NumberedWindowAuxExchangeLiftTargets
open NumberedWindowAuxExchangeLiftTypingProof
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowScalarAlgorithm (admitted edge)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

theorem exact_AuxTermSyntax : ExactAuxTermSyntax := syntaxAux

theorem exact_AuxTermTyping : ExactAuxTermTyping := typingAux

theorem exact_AuxWindowAdmission : ExactAuxWindowAdmission := admissionAux

theorem exact_AuxExchangeLift : ExactAuxExchangeLift := by
  intro hp dom cod fn fn' arg domValid codValid argValid related
  simp only [bits,Bool.and_eq_true,and_assoc] at related
  have nested : (row hp (auxRaw dom cod fn arg) (auxRaw dom cod fn' arg)).1 = true := by
    rw [rowAuxPair]
    simp [related.2.2]
  simp [bits,syntaxAux,domValid,codValid,argValid,related.1,related.2.1,nested]

theorem exact_AuxWindowEdgeLift : ExactAuxWindowEdgeLift := by
  intro s ctx dom cod fn fn' arg domValid codValid domAllowed codAllowed argAdmitted fnEdge
  simp only [edge,Bool.and_eq_true,and_assoc] at fnEdge
  have argValid : (syntaxBits arg).1 = true := by
    simp only [admitted,NumberedWindowLexicalAlgorithm.typed,Bool.and_eq_true,and_assoc]
      at argAdmitted
    exact argAdmitted.1
  have related := exact_AuxExchangeLift s.equivalentHeads dom cod fn fn' arg
    domValid codValid argValid fnEdge.1
  simp [-List.contains_eq_mem,edge,related,admissionAux,domValid,codValid,domAllowed,codAllowed,argAdmitted,
    fnEdge.2.1,fnEdge.2.2]

end LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks

#print axioms LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks.exact_AuxTermSyntax
#print axioms LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks.exact_AuxTermTyping
#print axioms LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks.exact_AuxWindowAdmission
#print axioms LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks.exact_AuxExchangeLift
#print axioms LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftChecks.exact_AuxWindowEdgeLift
