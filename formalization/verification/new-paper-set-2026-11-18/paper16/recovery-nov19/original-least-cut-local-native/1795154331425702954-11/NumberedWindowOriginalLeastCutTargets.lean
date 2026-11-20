import LogicLineages.PersistentMarking.NumberedWindowOriginalLeastPresentationTargets
namespace LogicLineages.PersistentMarking.NumberedWindowOriginalLeastCutTargets
open NumberedWindowPresentationClauses NumberedWindowPresentationLeast NumberedWindowPresentationCheckers
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowExternalIDOperators
open NumberedWindowArithmeticAllContextTargets (AdmittedAddress)

def AdmittedScalarSentence (S : Spine.Signature) (K : List Spine.Ty) : Prop :=
  ∀ x, AdmittedAddress S K x → Least (taggedStep S K) (tagScalar x)

def LeastAndSentenceComparison : Prop :=
  ∀ (S : Spine.Signature) K, DecisionSourceUniverse.Closed K →
    (∀ z, least (checks S.entries (fixed S K)) z ↔ Least (taggedStep S K) z) ∧
    (terms (checks S.entries (fixed S K)) (least (checks S.entries (fixed S K))) ↔
      AdmittedScalarSentence S K)

def AllAdmittedInTaggedLeast : Prop :=
  ∀ S K, DecisionSourceUniverse.Closed K → AdmittedScalarSentence S K

def OriginalCut : Prop :=
  LeastAndSentenceComparison → AllAdmittedInTaggedLeast →
    NumberedWindowOriginalLeastPresentationTargets.OriginalLeastAndAllTerms

end LogicLineages.PersistentMarking.NumberedWindowOriginalLeastCutTargets
