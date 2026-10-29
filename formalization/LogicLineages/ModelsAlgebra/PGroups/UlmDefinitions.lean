module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationDefinitions
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

/-!
# Actual socles and Ulm layers

The socle is the intersection with the actual kernel of multiplication
by p. The denominator is the next socle viewed inside the current one.
No invariant, isomorphism or quotient-map property is built into these
definitions. The scalar action is constructed from the actual
p-annihilation proof, rather than supplied by a module hypothesis.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

variable {G : Type*} [AddCommGroup G]

def pSocle (p : ℕ) (S : AddSubgroup G) : AddSubgroup G :=
  S ⊓ (nsmulAddMonoidHom p).ker

def successorSocleSubgroup (p : ℕ) (S : AddSubgroup G) : AddSubgroup (pSocle p S) :=
  (pSocle p (pStep p S)).comap (pSocle p S).subtype

abbrev UlmLayer (p : ℕ) (S : AddSubgroup G) :=
  (pSocle p S) ⧸ successorSocleSubgroup p S

noncomputable instance ulmLayerZModModule (p : ℕ) (S : AddSubgroup G) :
    Module (ZMod p) (UlmLayer p S) :=
  QuotientAddGroup.zmodModule fun x => by
    have hx : p • x = (0 : pSocle p S) := by
      apply Subtype.ext
      change p • (x : G) = 0
      exact x.property.2
    rw [hx]
    exact (successorSocleSubgroup p S).zero_mem

end LogicLineages.ModelsAlgebra.PGroups
