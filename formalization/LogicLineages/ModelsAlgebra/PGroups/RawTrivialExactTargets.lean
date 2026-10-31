module
public import LogicLineages.ModelsAlgebra.PGroups.RawTrivialExactDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def rawTrivialExact : Prop :=
  ∀ (G:Type) [AddCommGroup G] [Subsingleton G],
    (∃φ:Formula 0, Complexity .pi (1:Ordinal.{0}) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
    (∀q:QF 0, ¬ RawScottSentence (RawGroupStructure.ofGroup G) (Formula.qf q))
end LogicLineages.ModelsAlgebra.PGroups.Targets
