module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalTagArithmeticSyntaxProof
/-- Unconditional append, including empty prefixes, in the actual original proof calculus. -/
def ActualBetaSequenceExtension : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b n z : OTerm α),
  Nonempty (Derivation body [] (InternalBetaExtension.extension a b n z))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionTargets
