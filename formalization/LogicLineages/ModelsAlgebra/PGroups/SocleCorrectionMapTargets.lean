module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupSocleCorrectionEvaluation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G)
    (x : socleCorrectionDomain G p B S) (a : pSocle p S),
    (a : G) - x ∈ pStep p S →
    socleCorrectionClass G p B S x = (QuotientAddGroup.mk' (successorSocleSubgroup p S)) a

def groupSocleCorrectionHomKernel : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G),
    ∃ f : socleCorrectionDomain G p B S →+ UlmLayer p S,
      (∀ x, f x = socleCorrectionClass G p B S x) ∧
      f.ker = (pStep p S).comap (socleCorrectionDomain G p B S).subtype

end LogicLineages.ModelsAlgebra.PGroups.Targets
