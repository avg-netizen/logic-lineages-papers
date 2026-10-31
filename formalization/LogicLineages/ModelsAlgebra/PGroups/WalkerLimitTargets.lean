module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def walkerLimitFaithful : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence, ∀ n,
    Function.Injective (walkerStageInclusion p parent n)

def walkerLimitCompatible : Prop :=
  ∀ p : ℕ, ∀ parent : WalkerParentSequence, ∀ n m (h : n ≤ m),
    (walkerStageInclusion p parent m).comp (walkerStageMap p parent n m h) =
      walkerStageInclusion p parent n

def walkerLimitDigits : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence,
    ∀ x : WalkerSequentialGroup p parent, ∃ (n : ℕ) (d : Fin n → Fin p),
      walkerStageInclusion p parent n (walkerFiniteDigitSum p parent n d) = x

def walkerLimitCountable : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence,
    Countable (WalkerSequentialGroup p parent)

def walkerLimitGenerators : Prop :=
  ∀ p : ℕ, ∀ parent : WalkerParentSequence, ∀ n (i : Fin n),
    walkerStageInclusion p parent n ((walkerFinitePresentation p parent n).generator i) =
      walkerSequentialGenerator p parent i.val

def walkerLimitRelations : Prop :=
  ∀ p : ℕ, ∀ parent : WalkerParentSequence, ∀ i : ℕ,
    p • walkerSequentialGenerator p parent i =
      (parent i).elim 0 (fun j => walkerSequentialGenerator p parent j.val)

end LogicLineages.ModelsAlgebra.PGroups.Targets
