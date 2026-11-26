module
public import LogicLineages.OrdinalComparison.OmegaBlockTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullOmegaBlock.Targets
open LogicLineages.OrdinalComparison

def NumericalBlock : Prop :=
  ∀ c u m : Nat, c + 3 ≤ u → 1 ≤ m → 16 ≤ Phi u → m ≤ Phi u →
    Nat.ModEq m (actualOmegaCopyCount c u)
      (1 + restrictedPartitionCount (Phi u - c - 1) (Phi (u + 1) - c)) ∧
    0 < actualOmegaCopyCount c u ∧
    actualOmegaCopyState c u (actualOmegaCopyCount c u) < Ordinal.omega0 ∧
    (∀ i : Nat, i < actualOmegaCopyCount c u → Ordinal.omega0 ≤ actualOmegaCopyState c u i) ∧
    c + actualOrdinalNorm (actualOmegaCopyState c u (actualOmegaCopyCount c u)) =
      (Phi^[actualOmegaCopyCount c u]) u

def PrefixBlock : Prop :=
  ∀ k : Ordinal.{0}, k < epsilonZero → actualMinExponentAtLeast k Ordinal.omega0 →
    ∀ u m : Nat, actualOrdinalNorm k + 3 ≤ u → 1 ≤ m → 16 ≤ Phi u → m ≤ Phi u →
      let c := actualOrdinalNorm k
      let a := actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - c)
      let H := actualOmegaCopyCount c u
      Nat.ModEq m H (1 + restrictedPartitionCount (Phi u - c - 1) (Phi (u + 1) - c)) ∧
      (∀ i : Nat, i ≤ H → actualControlledStateAfter Phi (k + a) i = k + actualOmegaCopyState c u i) ∧
      (∃ n : Nat, actualControlledStateAfter Phi (k + a) H = k + (n : Ordinal)) ∧
      (∀ i : Nat, i < H → k + Ordinal.omega0 ≤ actualControlledStateAfter Phi (k + a) i) ∧
      actualOrdinalNorm (actualControlledStateAfter Phi (k + a) H) = (Phi^[H]) u

def CompleteOmegaBlock : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualOmegaBlockFirstStep ∧ NumericalBlock ∧ PrefixBlock
end LogicLineages.CartierObserverCurrent.FullOmegaBlock.Targets
