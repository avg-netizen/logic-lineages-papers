module
public import LogicLineages.CartierObserverCurrent.FullBudgetTransferTargets
public import LogicLineages.CartierObserverCurrent.FullBinaryMatrixTargets
public import LogicLineages.CartierObserverCurrent.FullSelectedCoefficientTargets
public import LogicLineages.CartierObserverCurrent.FullObservabilityTargets
public import LogicLineages.OrdinalComparison.BinarySourceTargets
public import LogicLineages.CartierObserverCurrent.FullTransientTargets
public import LogicLineages.CartierObserverCurrent.FullResidueObserverTargets
public import LogicLineages.CartierObserverCurrent.LinkedBoundaryParityTargets
public import LogicLineages.CartierObserverCurrent.MainTheoremBoundaryTargets
public import LogicLineages.CartierObserverCurrent.ActualPeriodTargets

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.MainTheorem.Targets

/-! Current20 thm:main (paper.tex 85-112). The theorem prints four items
about "the constructions below"; the closing section of the paper names the
numbered statements that supply each of them. Every item here is the
conjunction of the already frozen comparators of those statements, with two
additions that make the printed specialisations literal: the observability
clause at the actual source denominator A_d (item 2) and the first
omega^omega block of the actual descent from omega^(omega+1)+(v-4) (item 4). -/

/-- Item 1: thm:transfer. Complete count of one omega^d deletion with retained
mass c under budgets at least the current total norm and congruent to S>=c
modulo Q_d, both numerically and behind an actual retained prefix. -/
def CountTransfer : Prop := FullBudgetTransfer.Targets.CompleteTransfer

/-- Item 2: lem:matrix, thm:observer, lem:observable. Two explicit matrices on
the space of dimension d(d+1)/2 compute p_d(n) mod 2 exactly, and distinct
proper numerators of the actual source denominator are separated by a
continuation of length at most ceil(log2(d(d+1)/2)). -/
def BinaryObserver : Prop :=
  FullBinaryMatrix.Targets.CompleteStateUpdate ∧
  FullSelectedCoefficient.Targets.CompleteSelectedCoefficient ∧
  FullObservability.Targets.CompleteObservability.{u} ∧
  LogicLineages.OrdinalComparison.Targets.ActualSourceBinaryObservability.{u}

/-- Item 3: lem:binary-transient, thm:residue-observer. After the explicit
transient every binary word reaches simple poles; the residue profile is a
finite space closed under both selectors with the printed pole updates and
scalar output, and observes every remaining continuation. -/
def ResidueObserver : Prop :=
  FullTransient.Targets.BinaryTransient.{u, v} ∧
  FullResidueObserver.Targets.CompleteResidueObserver

/-- Item 4: lem:entry, prop:omega-block, equation (delta), thm:actual-period.
The explicit first-block parity of the actual descent, and on the same
linked parameters the exact tuple period and the divisibility of every
eventual period of the complete differential Cartier state. -/
def LinkedPeriod : Prop :=
  FullThetaEntry.Targets.CompleteEntry ∧
  FullOmegaBlock.Targets.CompleteOmegaBlock ∧
  LinkedBoundaryParity.Targets.ActualBoundaryParity ∧
  LinkedFirstBlock ∧
  ActualPeriod.Targets.CompleteActualPeriod

def CompleteMain : Prop :=
  CountTransfer ∧ BinaryObserver.{u} ∧ ResidueObserver.{u, v} ∧ LinkedPeriod

end LogicLineages.CartierObserverCurrent.MainTheorem.Targets
