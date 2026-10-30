module
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupSocleCorrectionRepresentative : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (S : AddSubgroup G) (x : G),
    x ∈ S → p • x ∈ pStep p (pStep p S) →
    ∃ y : G, y ∈ pStep p S ∧ p • y = p • x ∧ x - y ∈ pSocle p S

def groupSocleCorrectionEquality : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (S : AddSubgroup G) (a b : pSocle p S),
    (QuotientAddGroup.mk' (successorSocleSubgroup p S)) a =
      (QuotientAddGroup.mk' (successorSocleSubgroup p S)) b ↔
      (a : G) - b ∈ pStep p S

end LogicLineages.ModelsAlgebra.PGroups.Targets
