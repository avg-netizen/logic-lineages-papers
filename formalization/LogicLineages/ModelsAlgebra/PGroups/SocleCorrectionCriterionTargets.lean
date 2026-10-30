module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupSocleCorrectionNonsurjective : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G),
    ¬Function.Surjective (socleCorrectionClass G p B S) ↔
      ∃ a : pSocle p S, (a:G) ∉ pStep p S ∧ ∀ b : B, (a:G) + b ∉ pStep p S

end LogicLineages.ModelsAlgebra.PGroups.Targets
