module
public import LogicLineages.OrdinalComparison.KernelConcreteCountConventionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelConcreteCountConvention.Targets
/-- Exactly degree two, retained mass one and original input four. -/
def ExactCompanionCount : Prop := CompanionData 4
/-- A complete-count discrepancy at this diagnostic instance only.
No rank-at-least-three source lemma or intended wording is refuted. -/
def ExactWholeCountDiscrepancy : Prop := CountDiscrepancy 4
end LogicLineages.OrdinalComparison.KernelConcreteCountConvention.Targets
