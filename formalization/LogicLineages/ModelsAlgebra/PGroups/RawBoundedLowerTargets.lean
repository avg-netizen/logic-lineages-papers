module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupRawBoundedNoSigmaTwoScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] [Infinite G] (N : ℕ),
    (∀ x : G, p^N • x = 0) → ∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{0}) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
