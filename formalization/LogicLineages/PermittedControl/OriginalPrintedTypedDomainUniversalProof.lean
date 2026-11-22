module
public import LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversalTargets
import LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversalDomainProof
import LogicLineages.PermittedControl.OriginalPrintedTypedExistentialProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversal
open OriginalPrintedTypedExistential (exactOriginalPrintedTypedExistential solveOriginal)

theorem exactOriginalTypedDomainUniversal : ExactOriginalTypedDomainUniversal := by
  intro f B paid known gates p topo plain positive
  have result := exactOriginalPrintedTypedExistential f B paid known gates p topo plain (!positive)
  have trueAsFalse :
      solveUniversal f B known gates p positive = true ↔ solveOriginal f B known gates p (!positive) = false := by
    change (!(solveOriginal f B known gates p (!positive))) = true ↔ _
    cases solveOriginal f B known gates p (!positive) <;> decide
  have falseAsTrue :
      solveUniversal f B known gates p positive = false ↔ solveOriginal f B known gates p (!positive) = true := by
    change (!(solveOriginal f B known gates p (!positive))) = false ↔ _
    cases solveOriginal f B known gates p (!positive) <;> decide
  exact ⟨trueAsFalse.trans (result.2.trans (exactDefinedDomainCounterexample f gates p positive)),
    falseAsTrue.trans result.1⟩

theorem exactOriginalTypedTotalUniversal : ExactOriginalTypedTotalUniversal := by
  intro f B paid known gates p topo plain total polarity
  refine (exactOriginalTypedDomainUniversal f B paid known gates p topo plain polarity).1.trans ?_
  exact ⟨fun all base => all base (total base),fun all base _ => all base⟩

end LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversal
