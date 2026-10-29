module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationDefinitions

@[expose] public section

/-!
# The finite part of the p-filtration

These are the actual multiplication-by-p images of additive subgroups.
The finite successor calculation is a dependency of paper 01's
transfinite quotient-filtration lemma. No transfinite or Scott-analysis
conclusion is claimed here.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

variable {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Multiplication by p commutes with taking an additive-homomorphic image. -/
theorem map_pStep (p : ℕ) (f : G →+ H) (S : AddSubgroup G) :
    (pStep p S).map f = pStep p (S.map f) := by
  unfold pStep
  rw [AddSubgroup.map_map, AddSubgroup.map_map]
  congr 1
  ext x
  simp

/-- Every finite filtration stage commutes with an actual surjective
additive homomorphism. In the paper the homomorphism is a quotient map. -/
theorem map_finiteFiltration (p : ℕ) (f : G →+ H)
    (hf : Function.Surjective f) (n : ℕ) :
    (finiteFiltration p n : AddSubgroup G).map f =
      (finiteFiltration p n : AddSubgroup H) := by
  induction n with
  | zero => exact AddSubgroup.map_top_of_surjective f hf
  | succ n ih =>
      change (pStep p (finiteFiltration p n : AddSubgroup G)).map f =
        pStep p (finiteFiltration p n : AddSubgroup H)
      rw [map_pStep, ih]

end LogicLineages.ModelsAlgebra.PGroups
