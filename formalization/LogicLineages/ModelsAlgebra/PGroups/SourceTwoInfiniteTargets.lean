module
public import LogicLineages.ModelsAlgebra.PGroups.TwoReservoirExtractionTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupSourceTwoInfiniteNoDifferenceScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (N : ℕ)
    (a b : Fin N), a < b → (∀ x : G, p^N • x = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup G)) = Cardinal.aleph0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup G)) = Cardinal.aleph0 →
    ∀ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) → ¬ DifferenceScottSentence G d

def groupRawSourceTwoInfiniteScottBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (N : ℕ)
    (a b : Fin N), a < b → (∀ x : G, p^N • x = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup G)) = Cardinal.aleph0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup G)) = Cardinal.aleph0 →
    (∃ φ : Formula 0, Complexity .pi (3 : Ordinal.{0}) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
    (∀ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) →
      ¬ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d)

end LogicLineages.ModelsAlgebra.PGroups.Targets
