module
public import LogicLineages.ModelsAlgebra.PGroups.BackForthIsomorphismDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
universe u v
def backForthIsomorphism : Prop :=
  ∀ (α : Ordinal.{v}) (G H G' H' : Type u)
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup G'] [AddCommGroup H']
    (e : G ≃+ G') (f : H ≃+ H') (n : ℕ) (a : Fin n → G) (b : Fin n → H),
    BackAndForth α a b ↔ BackAndForth α (fun i => e (a i)) (fun i => f (b i))
end LogicLineages.ModelsAlgebra.PGroups.Targets
