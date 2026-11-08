module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibration
open InternalApplicationValidityStack

/-- The external structured execution of the EXISTING transition. This is not
an alternative Program AST, an internal derivability rule, or a fuel oracle. -/
def stateIterate (node leaf : Nat → Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state => stateStep node leaf (stateIterate node leaf count state)

/-- The only canonical terminal states: rejected, or live with no pending work.
Both are fixed points of the existing transition for every node/leaf pair. -/
def terminal (state : State) : Prop :=
  state = failedState ∨ state = (⟨1, []⟩ : State)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibration
