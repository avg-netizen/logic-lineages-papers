module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionLinearTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupSocleCorrectionStrictRank : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) [Fact p.Prime] (B S : AddSubgroup G) [Finite B],
    ¬Function.Surjective (socleCorrectionClass G p B S) ↔
      Module.rank (ZMod p) (SocleCorrectionQuotient G p B S) < Module.rank (ZMod p) (UlmLayer p S)

end LogicLineages.ModelsAlgebra.PGroups.Targets
