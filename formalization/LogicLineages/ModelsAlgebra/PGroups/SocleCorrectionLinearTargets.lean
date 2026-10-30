module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionQuotientDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupSocleCorrectionLinearEmbedding : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B S : AddSubgroup G),
    ∃ e : SocleCorrectionQuotient G p B S →ₗ[ZMod p] UlmLayer p S,
      Function.Injective e ∧ ∀ x,
        e ((QuotientAddGroup.mk' ((pStep p S).comap (socleCorrectionDomain G p B S).subtype)) x) =
          socleCorrectionClass G p B S x

def groupSocleCorrectionFiniteRank : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) [Fact p.Prime] (B S : AddSubgroup G) [Finite B],
    Finite (SocleCorrectionQuotient G p B S) ∧
      Module.rank (ZMod p) (SocleCorrectionQuotient G p B S) < Cardinal.aleph0

def groupSocleCorrectionRankLe : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) [Fact p.Prime] (B S : AddSubgroup G),
    Module.rank (ZMod p) (SocleCorrectionQuotient G p B S) ≤ Module.rank (ZMod p) (UlmLayer p S)

end LogicLineages.ModelsAlgebra.PGroups.Targets
