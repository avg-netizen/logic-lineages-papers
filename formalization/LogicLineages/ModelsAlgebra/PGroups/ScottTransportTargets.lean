module

public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FullShiftDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

/-- Genuine iso invariance, not an assertion that arbitrary groups possess
a source normal form. The literal Pi rank supplies checked truth transfer. -/
def groupPiScottIsomorphism : Prop :=
  ∀ (α : Ordinal.{v}) (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (φ : Formula 0), Complexity .pi α φ →
      (GroupScottSentence G φ ↔ GroupScottSentence H φ)

/-- The other lower obstruction for the actual full normal forms, obtained
from their proved exponent/countability/infinitude, not a torsion oracle. -/
def groupFullShiftNoSigmaTwoScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ), (∀ j, ℓ j ≤ k) →
    ∀ (s : ℕ) (r : Fin s → ℕ), 0 < k → ∀ φ : Formula 0,
      Complexity .sigma (2 : Ordinal.{v}) φ → ¬ GroupScottSentence (FullShiftGroup p k t ℓ s r) φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
