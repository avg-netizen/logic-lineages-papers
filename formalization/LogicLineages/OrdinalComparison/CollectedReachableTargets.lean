module
public import LogicLineages.OrdinalComparison.CollectedReachableDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedReachableTagDomain : Prop :=
  ∀ F : CollectedPositiveNF, CollectedPositiveValid F → 1≤collectedOneInputThreshold F ∧
    ∀ (rho : NONote) (A : CollectedPositiveNF), (rho,A)∈collectedReachableTags F →
      Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero ∧
      CollectedPositiveValid A ∧ collectedPositiveSupport A=true ∧
      collectedAtomThreshold rho A≤collectedOneInputThreshold F

def CollectedAtomInputRegime : Prop :=
  ∀ (rho : NONote) (c b : Nat) (tags : CollectedPositiveTags),
    Order.IsSuccLimit rho.1.repr → rho.1.repr<epsilonZero →
    CollectedPositiveValid (.mk c b tags) → collectedPositiveSupport (.mk c b tags)=true →
    ∀ x : Nat, collectedAtomThreshold rho (.mk c b tags)≤x →
      let t := actualOrdinalNorm (actualCollectedTagInput rho (.mk c b tags) x)
      (tags=.nil → x≤t ∧ t<Phi x) ∧ (tags≠.nil → ControlRoot t ∧ Phi x<t) ∧ CommonBandOrRoot x t

end LogicLineages.OrdinalComparison.Targets
