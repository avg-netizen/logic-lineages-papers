module
public import LogicLineages.ModelsAlgebra.PGroups.StabilizationSyntaxDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def stabilizationSentenceExact : Prop :=
  ∀ (p N:ℕ), Complexity .pi (2:Ordinal.{0}) (stabilizationSentence p N) ∧
    ∀ (G:Type) [AddCommGroup G],
      (stabilizationSentence p N).Realize (Fin.elim0:Fin 0→G) ↔ StableAt p G (N:Ordinal.{0})
end LogicLineages.ModelsAlgebra.PGroups.Targets
