import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowAddressApplication

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalApplicationScalarTargets
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowScalarAlgorithm (scalar)
open NumberedWindowAddressApplication (graph)

/-- The original accepting graph on its same three arbitrary raw codes.
Scalar admission of the actual returned value is asserted only for
the literal original fixed signature/window under its original Closed
condition. No arbitrary Settings or changed accepted graph. -/
def ExactFixedOriginalApplicationScalar : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ q u y : Nat,
      graph (fixed S K) q u y = true →
      scalar (fixed S K) q = true ∧ scalar (fixed S K) u = true ∧
        scalar (fixed S K) y = true

end LogicLineages.PersistentMarking.NumberedWindowOriginalApplicationScalarTargets
