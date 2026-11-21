module
public import LogicLineages.CartierObserverCurrent.FullTransientTargets
public import LogicLineages.CartierObserverCurrent.FullResidueObserverTargets
import LogicLineages.CartierObserverCurrent.FullTransientStatementChecks
import LogicLineages.CartierObserverCurrent.FullResidueObserverStatementChecks
public meta import LogicLineages.Audit

public section
universe u v
namespace LogicLineages.CartierObserverCurrent.MainTheorem.Residue

/-- Item 3 of current20 thm:main: lem:binary-transient and thm:residue-observer. -/
theorem residueObserver :
    FullTransient.Targets.BinaryTransient.{u, v} ∧
    FullResidueObserver.Targets.CompleteResidueObserver :=
  ⟨FullTransient.StatementChecks.fixed_binaryTransient.{u, v},
    FullResidueObserver.StatementChecks.fixed_completeResidueObserver⟩

#audit_namespace LogicLineages.CartierObserverCurrent.MainTheorem.Residue
end LogicLineages.CartierObserverCurrent.MainTheorem.Residue
