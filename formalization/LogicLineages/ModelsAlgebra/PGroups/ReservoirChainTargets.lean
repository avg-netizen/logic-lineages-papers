module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChainDefinitions
public import Mathlib.Order.Monotone.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupReservoirMonotone : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C], Monotone (reservoirStage A B C)
def groupReservoirCover : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (x : ReservoirGroup A B C), ∃ i, x ∈ reservoirStage A B C i

def groupReservoirMapInjective : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (i M : ℕ) (j : B →+ C),
    Function.Injective j → Function.Injective (reservoirStageMap A B C i M j)

def groupReservoirMapFixes : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (i M : ℕ) (j : B →+ C)
    (x : reservoirStage A B C i), (∀ n ∈ x.val.2.2.support, n < M) →
      reservoirStageMap A B C i M j x.val = x

def groupReservoirTupleFixing : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (j : B →+ C),
    Function.Injective j → ∀ (i m : ℕ) (d : Fin m → reservoirStage A B C i),
      ∃ f : ReservoirGroup A B C →+ reservoirStage A B C i,
        Function.Injective f ∧ ∀ a, f (d a : ReservoirGroup A B C) = d a

end LogicLineages.ModelsAlgebra.PGroups.Targets
