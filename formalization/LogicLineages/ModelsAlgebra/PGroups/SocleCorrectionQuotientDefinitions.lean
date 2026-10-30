module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

abbrev SocleCorrectionQuotient (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G) :=
  socleCorrectionDomain G p B S ⧸ (pStep p S).comap (socleCorrectionDomain G p B S).subtype

noncomputable instance socleCorrectionQuotientZModModule (G : Type u) [AddCommGroup G]
    (p : ℕ) (B S : AddSubgroup G) : Module (ZMod p) (SocleCorrectionQuotient G p B S) :=
  QuotientAddGroup.zmodModule fun x => by
    change p • (x:G) ∈ pStep p S
    exact ⟨(x:G),x.property.1.2,rfl⟩

end LogicLineages.ModelsAlgebra.PGroups
