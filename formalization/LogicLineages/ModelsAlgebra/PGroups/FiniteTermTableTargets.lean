module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTermTableDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth
universe u w

def groupDistinctTermMatrix : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n m : ℕ) (t : Fin m → GroupTerm n) (a : Fin n → G),
    (distinctTermMatrix t).Realize a ↔ Function.Injective (fun i => (t i).eval a)

def groupFiniteTermTable : Prop :=
  ∀ (K : Type w) [AddCommGroup K] [Fintype K] (G : Type u) [AddCommGroup G]
    (n : ℕ) (t : K → GroupTerm n) (a : Fin n → G),
    (finiteTermTable K t).Realize a ↔
      ∃ f : K →+ G, Function.Injective f ∧ ∀ x : K, f x = (t x).eval a

end LogicLineages.ModelsAlgebra.PGroups.Targets
