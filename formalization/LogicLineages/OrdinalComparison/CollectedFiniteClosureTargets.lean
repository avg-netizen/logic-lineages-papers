module
public import LogicLineages.OrdinalComparison.CollectedFiniteClosureDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedFiniteClosureDomain : Prop :=
  ∀ forms : List CollectedPositiveNF, (∀ A∈forms, CollectedPositiveValid A) →
    CollectedPositiveNF.mk 0 0 .nil∈collectedFiniteClosure forms ∧
    (∀ A∈forms, A∈collectedFiniteClosure forms) ∧
    (∀ A∈collectedFiniteClosure forms, CollectedPositiveValid A) ∧
    ∀ (c b : Nat) (tags : CollectedPositiveTags),
      CollectedPositiveNF.mk c b tags∈collectedFiniteClosure forms →
      ∀ (rho : NONote) (A : CollectedPositiveNF), (rho,A)∈collectedDirectTags tags →
        A∈collectedFiniteClosure forms

def CollectedDirectChildHeight : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags) (rho : NONote) (A : CollectedPositiveNF),
    (rho,A)∈collectedDirectTags tags →
      collectedPositiveHeight A<collectedPositiveHeight (.mk c b tags)

def CollectedDirectTagReachable : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags) (rho : NONote) (A : CollectedPositiveNF),
    (rho,A)∈collectedDirectTags tags → (rho,A)∈collectedReachableTags (.mk c b tags)

end LogicLineages.OrdinalComparison.Targets
