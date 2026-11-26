import LogicLineages.PersistentMarking.NumberedWindowNumericalMatching
import LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteCheckersTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchTargets
namespace LogicLineages.PersistentMarking.NumberedWindowOriginalNumeralMatchTargets
open NumberedWindowNumericalMatching NumberedWindowArithmeticScalarTargets
def OriginalNumericalMatching : Prop :=
  ∀ (S : Spine.Signature) (K : List Spine.Ty), DecisionSourceUniverse.Closed K →
    Matching (NumberedWindowConcreteCheckers.positive S.entries (fixed S K)) (NumberedWindowAddressApplication.graph (fixed S K))
end LogicLineages.PersistentMarking.NumberedWindowOriginalNumeralMatchTargets
