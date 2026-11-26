module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetTargets
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_actualZeroEdgeAlphabet :
    ActualZeroEdgeAlphabet.FullActualZeroEdgeAlphabet :=
  ActualZeroEdgeAlphabet.fullActualZeroEdgeAlphabet

#print axioms fixed_actualZeroEdgeAlphabet

end LogicLineages.PermittedControl.StatementChecks
