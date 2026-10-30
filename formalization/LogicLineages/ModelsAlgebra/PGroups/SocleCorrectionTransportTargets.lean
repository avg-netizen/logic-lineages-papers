module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionQuotientDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupSocleCorrectionTransport : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ)
    (B S : AddSubgroup G) (C T : AddSubgroup H) (f : B ≃+ C),
    (∀ b : B, (f b:H) ∈ T ↔ (b:G) ∈ S) →
    (∀ b : B, (f b:H) ∈ pStep p T ↔ (b:G) ∈ pStep p S) →
    (∀ b : B, (f b:H) ∈ pStep p (pStep p T) ↔ (b:G) ∈ pStep p (pStep p S)) →
    Nonempty (SocleCorrectionQuotient G p B S ≃ₗ[ZMod p] SocleCorrectionQuotient H p C T)

def groupSocleCorrectionRankTransport : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ)
    (B S : AddSubgroup G) (C T : AddSubgroup H) (f : B ≃+ C),
    (∀ b : B, (f b:H) ∈ T ↔ (b:G) ∈ S) →
    (∀ b : B, (f b:H) ∈ pStep p T ↔ (b:G) ∈ pStep p S) →
    (∀ b : B, (f b:H) ∈ pStep p (pStep p T) ↔ (b:G) ∈ pStep p (pStep p S)) →
    Module.rank (ZMod p) (SocleCorrectionQuotient G p B S) =
      Module.rank (ZMod p) (SocleCorrectionQuotient H p C T)

end LogicLineages.ModelsAlgebra.PGroups.Targets
