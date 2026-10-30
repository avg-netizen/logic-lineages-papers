module

public import LogicLineages.ModelsAlgebra.Differential.FiniteJet
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_finiteJetClosedAndEqualsGenerated : Targets.finiteJetClosedAndEqualsGenerated :=
  FiniteJet.closed_and_equals_generated
theorem fixed_independentFiniteJetIsomorphism : Targets.independentFiniteJetIsomorphism :=
  FiniteJet.independent_isomorphism

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
