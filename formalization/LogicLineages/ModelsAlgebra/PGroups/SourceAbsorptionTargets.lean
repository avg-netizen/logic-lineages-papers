module
public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionLogicTargets
public import LogicLineages.ModelsAlgebra.PGroups.SingleReservoirExtractionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth

def groupAbsorptionTupleTransport : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K A T : Type) [AddCommGroup K] [AddCommGroup A] [AddCommGroup T]
    [Countable T] (k : ℕ) (e : K ≃+ A × (ℕ →₀ ZMod (p^k))),
    (∀ t : T, p^k • t = 0) → ∀ (m : ℕ) (a : Fin m → K),
      ∃ f : (K × T) →+ K, Function.Injective f ∧ ∀ j, f (a j,0) = a j

def groupSourceFactorAbsorption : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K A T : Type) [AddCommGroup K] [AddCommGroup A] [AddCommGroup T]
    [Countable K] [Countable T] (k N : ℕ) (e : K ≃+ A × (ℕ →₀ ZMod (p^k))),
    (∀ x : K, p^N • x = 0) → (∀ t : T, p^k • t = 0) →
    (∀ (n : ℕ) (a : Fin n → K) (φ : Formula n), Complexity .sigma (1 : Ordinal.{0}) φ →
      (φ.Realize a ↔ φ.Realize (fun j => (a j,0) : Fin n → K × T))) ∧
    BackAndForth (2 : Ordinal.{0}) (Fin.elim0 : Fin 0 → K × T) (Fin.elim0 : Fin 0 → K)

def groupSourceBoundedAbsorption : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K T : Type) [AddCommGroup K] [AddCommGroup T]
    [Countable K] [Countable T] (N : ℕ) (a : Fin N),
    (∀ x : K, p^N • x = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup K)) = Cardinal.aleph0 →
    (∀ t : T, p^(a.val+1) • t = 0) →
    (∀ (n : ℕ) (a : Fin n → K) (φ : Formula n), Complexity .sigma (1 : Ordinal.{0}) φ →
      (φ.Realize a ↔ φ.Realize (fun j => (a j,0) : Fin n → K × T))) ∧
    BackAndForth (2 : Ordinal.{0}) (Fin.elim0 : Fin 0 → K × T) (Fin.elim0 : Fin 0 → K)

end LogicLineages.ModelsAlgebra.PGroups.Targets
