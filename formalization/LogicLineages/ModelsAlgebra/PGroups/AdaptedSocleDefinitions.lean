module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

variable {G : Type} [AddCommGroup G]

/-- Canonical scalar action from the actual annihilation equation, not an
independent module hypothesis. No existing Ulm module definition is changed. -/
noncomputable instance actualSocleModule (p : ℕ) (S : AddSubgroup G) :
    Module (ZMod p) (pSocle p S) :=
  AddCommGroup.zmodModule fun x => Subtype.ext x.property.2

def socleInclusionHom (p : ℕ) (S : AddSubgroup G) : pSocle p S →+ pSocle p (⊤ : AddSubgroup G) where
  toFun x := ⟨x.val, ⟨AddSubgroup.mem_top _, x.property.2⟩⟩
  map_zero' := rfl
  map_add' := fun _ _ => rfl

noncomputable def socleInclusion (p : ℕ) (S : AddSubgroup G) :
    pSocle p S →ₗ[ZMod p] pSocle p (⊤ : AddSubgroup G) :=
  (socleInclusionHom p S).toZModLinearMap p

noncomputable def socleLevel (p : ℕ) (G : Type) [AddCommGroup G] (j : ℕ) :
    Submodule (ZMod p) (pSocle p (⊤ : AddSubgroup G)) :=
  AddSubgroup.toZModSubmodule p ((finiteFiltration p j).comap (pSocle p (⊤ : AddSubgroup G)).subtype)

noncomputable def includedSocleFamily (p : ℕ) (N : ℕ) (I : Fin N → Type)
    (x : ∀ l : Fin N, I l → pSocle p (finiteFiltration p l.val : AddSubgroup G)) :
    (Σ l : Fin N, I l) → pSocle p (⊤ : AddSubgroup G) :=
  fun a => socleInclusion p (finiteFiltration p a.1.val) (x a.1 a.2)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
