module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedDescriptorTargets
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- Literal dSigma2 Scott upper bound from the actual source descriptor data. -/
def groupBoundedDescriptorScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [AddCommGroup K] [Fintype K]
    (k N : ℕ), 0 < k → k ≤ N → ∀ (a : Fin (k-1) → ℕ)
    (G : Type) [AddCommGroup G] [Countable G],
    Nonempty (multipleImage G (p ^ k) ≃+ K) →
    Set.Infinite (Set.range (fun x : G => p ^ (k-1) • x)) →
    finiteFiltration p N = (⊥ : AddSubgroup G) →
    (∀ i : Fin (k-1), Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i.val : AddSubgroup G)) = (a i : Cardinal)) →
    (boundedDescriptor K p k N a).AtLevel (2 : Ordinal.{0}) ∧
      DifferenceScottSentence G (boundedDescriptor K p k N a)

/-- Literal Pi2 Scott upper bound for the actual zero-lower case. -/
def groupZeroLowerDescriptorScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [AddCommGroup K] [Fintype K]
    (k N : ℕ), 0 < k → k ≤ N → ∀ (G : Type) [AddCommGroup G] [Countable G],
    Nonempty (multipleImage G (p ^ k) ≃+ K) →
    Set.Infinite (Set.range (fun x : G => p ^ (k-1) • x)) →
    finiteFiltration p N = (⊥ : AddSubgroup G) →
    (∀ i : ℕ, i < k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i : AddSubgroup G)) = 0) →
    Complexity .pi (2 : Ordinal.{0}) (zeroLowerDescriptor K p k N) ∧
      GroupScottSentence G (zeroLowerDescriptor K p k N)

end LogicLineages.ModelsAlgebra.PGroups.Targets
