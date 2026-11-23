module

public import LogicLineages.PersistentMarking.NumberedWindowPresentationCheckers
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDOperators

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalPresentationTargets
open NumberedWindowPresentationClauses NumberedWindowPresentationCheckers
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticAllContextTargets (AdmittedAddress)
open NumberedWindowExternalIDOperators (taggedStep tagScalar)

def ActualOperatorAndTerms : Prop :=
  ∀ (S : Spine.Signature) K, DecisionSourceUniverse.Closed K → ∀ (P : Nat → Prop),
    (∀ z, tagged (checks S.entries (fixed S K)) P z ↔ taggedStep S K P z) ∧
    (terms (checks S.entries (fixed S K)) P ↔
      ∀ x, AdmittedAddress S K x → P (tagScalar x))

end LogicLineages.PersistentMarking.NumberedWindowOriginalPresentationTargets
