module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChainDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssemblyTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupReservoirWholeRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A] (ell m : ℕ),
    0 < ell → ell < m →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell - 1) : AddSubgroup A)) = 0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell - 1) :
      AddSubgroup (ReservoirGroup A (ZMod (p^ell)) (ZMod (p^m))))) = Cardinal.aleph0

def groupReservoirStageRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A] (ell m : ℕ),
    0 < ell → ell < m →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell - 1) : AddSubgroup A)) = 0 →
    ∀ i : ℕ, Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell - 1) :
      AddSubgroup (reservoirStage A (ZMod (p^ell)) (ZMod (p^m)) i))) = (i : Cardinal)

def groupReservoirStageNonisomorphism : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A] (ell m : ℕ),
    0 < ell → ell < m →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell - 1) : AddSubgroup A)) = 0 →
    ∀ i : ℕ, ¬ Nonempty (ReservoirGroup A (ZMod (p^ell)) (ZMod (p^m)) ≃+
      reservoirStage A (ZMod (p^ell)) (ZMod (p^m)) i)

end LogicLineages.ModelsAlgebra.PGroups.Targets
