module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingTargets
open Source RecursiveComparison SourceExtendedTargetDropping

/-- Full genuine derivation induction, with no transitivity or dropping oracle. -/
def ActualTargetDropping : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (s t : Packed Symbol arity Gamma),
  SourceExtendedComparison.Weak Symbol arity above Gamma s t → DropMeaning above s t

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingTargets
