module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.BoundedScottTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupRawFiniteDifferenceScott : Prop :=
  ∀ (K : Type u) [AddCommGroup K] [Fintype K],
    ∃ d : DifferenceFormula 0, d.AtLevel (1 : Ordinal.{0}) ∧
      RawDifferenceScottSentence (RawGroupStructure.ofGroup K) d

def groupRawTrivialPiOneScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Subsingleton G],
    ∃ φ : Formula 0, Complexity .pi (1 : Ordinal.{0}) φ ∧
      RawScottSentence (RawGroupStructure.ofGroup G) φ

def groupRawBoundedPiThreeScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (N : ℕ),
    (∀ x : G, p^N • x = 0) →
    ∃ φ : Formula 0, Complexity .pi (3 : Ordinal.{0}) φ ∧
      RawScottSentence (RawGroupStructure.ofGroup G) φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
