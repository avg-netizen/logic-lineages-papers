module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionBasics
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

def socleCorrectionDomain (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G) : AddSubgroup G :=
  (B ⊓ S) ⊓ (pStep p (pStep p S)).comap (nsmulAddMonoidHom p)

noncomputable def socleCorrectionRepresentative (G : Type u) [AddCommGroup G]
    (p : ℕ) (B S : AddSubgroup G) (x : socleCorrectionDomain G p B S) : pSocle p S := by
  let h := socle_correction_representative G p S x x.property.1.2 x.property.2
  exact ⟨(x:G) - Classical.choose h, (Classical.choose_spec h).2.2⟩

noncomputable def socleCorrectionClass (G : Type u) [AddCommGroup G]
    (p : ℕ) (B S : AddSubgroup G) (x : socleCorrectionDomain G p B S) : UlmLayer p S :=
  (QuotientAddGroup.mk' (successorSocleSubgroup p S)) (socleCorrectionRepresentative G p B S x)

end LogicLineages.ModelsAlgebra.PGroups
