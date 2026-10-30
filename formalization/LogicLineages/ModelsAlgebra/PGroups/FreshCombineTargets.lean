module
public import LogicLineages.ModelsAlgebra.PGroups.FreshCombineDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupFreshCombineOdd : Prop :=
  ∀ (B C : Type) [AddCommGroup B] [AddCommGroup C] (M : ℕ) (j : B →+ C)
    (x : ℕ →₀ B) (y : ℕ →₀ C) (n : ℕ), freshCombine B C M j (x,y) (reserveOdd M n) = j (x n)

def groupFreshCombineEven : Prop :=
  ∀ (B C : Type) [AddCommGroup B] [AddCommGroup C] (M : ℕ) (j : B →+ C)
    (x : ℕ →₀ B) (y : ℕ →₀ C) (n : ℕ), freshCombine B C M j (x,y) (reserveEven M n) = y n

def groupFreshCombineInjective : Prop :=
  ∀ (B C : Type) [AddCommGroup B] [AddCommGroup C] (M : ℕ) (j : B →+ C),
    Function.Injective j → Function.Injective (freshCombine B C M j)

def groupFreshCombineFixes : Prop :=
  ∀ (B C : Type) [AddCommGroup B] [AddCommGroup C] (M : ℕ) (j : B →+ C) (y : ℕ →₀ C),
    (∀ n ∈ y.support, n < M) → freshCombine B C M j (0,y) = y

end LogicLineages.ModelsAlgebra.PGroups.Targets
