module
public import LogicLineages.CartierObserverCurrent.MainTheoremTargets
import LogicLineages.CartierObserverCurrent.MainTheoremCountProof
import LogicLineages.CartierObserverCurrent.MainTheoremObserverProof
import LogicLineages.CartierObserverCurrent.MainTheoremResidueProof
import LogicLineages.CartierObserverCurrent.MainTheoremBoundaryProof
import LogicLineages.CartierObserverCurrent.ActualPeriodStatementChecks
public meta import LogicLineages.Audit

public section
universe u v
namespace LogicLineages.CartierObserverCurrent.MainTheorem

/-- Current20 thm:main: the four printed items. -/
theorem completeMain : Targets.CompleteMain.{u, v} :=
  ⟨Count.countTransfer, Observer.binaryObserver.{u}, Residue.residueObserver.{u, v},
    Boundary.boundary.1, Boundary.boundary.2.1, Boundary.boundary.2.2.1, Boundary.boundary.2.2.2,
    ActualPeriod.StatementChecks.fixed_completeActualPeriod⟩

#audit_namespace LogicLineages.CartierObserverCurrent.MainTheorem
end LogicLineages.CartierObserverCurrent.MainTheorem
