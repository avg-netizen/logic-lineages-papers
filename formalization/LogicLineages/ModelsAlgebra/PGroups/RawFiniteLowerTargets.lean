module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupRawFiniteNoSigmaOneScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] [Finite G],
    ∀ φ : Formula 0, Complexity .sigma (1 : Ordinal.{0}) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ

def groupRawNontrivialNoPiOneScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] [Nontrivial G],
    ∀ φ : Formula 0, Complexity .pi (1 : Ordinal.{0}) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
