module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirRankTargets
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

def groupReservoirNoDifferenceTwoScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A] [Countable A] (ell m : ℕ),
    0 < ell → ell < m →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell-1) : AddSubgroup A)) = 0 →
    ∀ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) →
      ¬ DifferenceScottSentence (ReservoirGroup A (ZMod (p^ell)) (ZMod (p^m))) d

def groupDifferenceScottIsomorphism : Prop :=
  ∀ (α : Ordinal.{v}) (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : DifferenceFormula 0), d.AtLevel α →
      (DifferenceScottSentence G d ↔ DifferenceScottSentence H d)

end LogicLineages.ModelsAlgebra.PGroups.Targets
