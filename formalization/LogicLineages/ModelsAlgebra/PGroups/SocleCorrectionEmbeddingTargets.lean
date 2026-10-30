module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupSocleCorrectionKernelImage : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G),
    ((pStep p S).comap (socleCorrectionDomain G p B S).subtype).map
      (socleCorrectionDomain G p B S).subtype = B ⊓ pStep p S

def groupSocleCorrectionEmbedding : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G),
    ∃ e : (socleCorrectionDomain G p B S ⧸
        (pStep p S).comap (socleCorrectionDomain G p B S).subtype) →+ UlmLayer p S,
      Function.Injective e ∧ ∀ x,
        e ((QuotientAddGroup.mk' ((pStep p S).comap (socleCorrectionDomain G p B S).subtype)) x) =
          socleCorrectionClass G p B S x

end LogicLineages.ModelsAlgebra.PGroups.Targets
