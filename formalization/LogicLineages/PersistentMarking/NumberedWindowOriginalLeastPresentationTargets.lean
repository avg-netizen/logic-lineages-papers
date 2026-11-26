import LogicLineages.PersistentMarking.NumberedWindowOriginalPresentationTargets
import LogicLineages.PersistentMarking.NumberedWindowPresentationLeast
namespace LogicLineages.PersistentMarking.NumberedWindowOriginalLeastPresentationTargets
open NumberedWindowPresentationClauses NumberedWindowPresentationLeast NumberedWindowPresentationCheckers
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowExternalIDOperators

def OriginalLeastAndAllTerms : Prop :=
  ∀ (S : Spine.Signature) K, DecisionSourceUniverse.Closed K →
    (∀ z, least (checks S.entries (fixed S K)) z ↔ Least (taggedStep S K) z) ∧
      terms (checks S.entries (fixed S K)) (least (checks S.entries (fixed S K)))
end LogicLineages.PersistentMarking.NumberedWindowOriginalLeastPresentationTargets
