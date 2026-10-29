module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteFiltration

@[expose] public section

/-!
# The actual homomorphism induced on Ulm layers

The socle map sends x to the given f(x). Its well-definedness is proved
from actual subgroup images and p-annihilation. Descending it to the
successive-socle quotients constructs a ZMod-linear map for every f.
No injectivity, surjectivity or isomorphism property is built into this
map or taken as an input. Those are the later fixed theorem targets.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

variable {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]

def pSocleMap (p : ℕ) (S : AddSubgroup G) (f : G →+ H) :
    pSocle p S →+ pSocle p (S.map f) where
  toFun x := ⟨f x, ⟨⟨x, x.property.1, rfl⟩, by
    have hx : p • (x : G) = 0 := x.property.2
    change p • f (x : G) = 0
    rw [← map_nsmul, hx, map_zero]⟩⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero f
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add f x y

@[simp] theorem pSocleMap_coe (p : ℕ) (S : AddSubgroup G) (f : G →+ H)
    (x : pSocle p S) : (pSocleMap p S f x : H) = f (x : G) := rfl

theorem pSocleMap_successor (p : ℕ) (S : AddSubgroup G) (f : G →+ H) :
    successorSocleSubgroup p S ≤
      (successorSocleSubgroup p (S.map f)).comap (pSocleMap p S f) := by
  intro x hx
  have hxStep : (x : G) ∈ pStep p S := hx.1
  change f (x : G) ∈ pSocle p (pStep p (S.map f))
  refine ⟨?_, (pSocleMap p S f x).property.2⟩
  rw [← map_pStep p f S]
  exact ⟨x, hxStep, rfl⟩

noncomputable def ulmMap (p : ℕ) (S : AddSubgroup G) (f : G →+ H) :
    UlmLayer p S →ₗ[ZMod p] UlmLayer p (S.map f) :=
  (QuotientAddGroup.map (successorSocleSubgroup p S)
    (successorSocleSubgroup p (S.map f)) (pSocleMap p S f)
    (pSocleMap_successor p S f)).toZModLinearMap p

@[simp] theorem ulmMap_mk (p : ℕ) (S : AddSubgroup G) (f : G →+ H)
    (x : pSocle p S) :
    ulmMap p S f (QuotientAddGroup.mk' (successorSocleSubgroup p S) x) =
      QuotientAddGroup.mk' (successorSocleSubgroup p (S.map f)) (pSocleMap p S f x) := rfl

end LogicLineages.ModelsAlgebra.PGroups
