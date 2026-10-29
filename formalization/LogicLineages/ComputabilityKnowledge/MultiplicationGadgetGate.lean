module

public import LogicLineages.ComputabilityKnowledge.MultiplicationGadgetProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem multiplication_gadget : Comparators.MultiplicationGadget.Target :=
  MultiplicationGadgetProof.sevenEquationMultiplication

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
