module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
def socleEndomorphism (D : Type) [AddCommGroup D] (p : ℕ) (f : D →+ D) :
    pSocle p (⊤:AddSubgroup D) →+ pSocle p (⊤:AddSubgroup D) :=
  (f.comp (pSocle p (⊤:AddSubgroup D)).subtype).codRestrict _ (fun x => by
    change f (x:D) ∈ pSocle p (⊤:AddSubgroup D)
    refine ⟨AddSubgroup.mem_top _,?_⟩
    change p • f (x:D) = 0
    have hx : p • (x:D) = 0 := x.property.2
    rw [←map_nsmul,hx,map_zero])
end LogicLineages.ModelsAlgebra.PGroups
