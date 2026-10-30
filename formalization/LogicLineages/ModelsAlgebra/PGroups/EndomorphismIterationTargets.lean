module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismIterationDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupIterationTransitionIdentity : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G) (i : ℕ) (x : G),
    iterationTransition f i i le_rfl x = x

def groupIterationTransitionComposition : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G) (i j k : ℕ)
    (hij : i ≤ j) (hjk : j ≤ k) (x : G),
      iterationTransition f j k hjk (iterationTransition f i j hij x) =
        iterationTransition f i k (hij.trans hjk) x

def groupIterationTransitionInjective : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G), Function.Injective f →
    ∀ (i j : ℕ) (hij : i ≤ j), Function.Injective (iterationTransition f i j hij)

end LogicLineages.ModelsAlgebra.PGroups.Targets
