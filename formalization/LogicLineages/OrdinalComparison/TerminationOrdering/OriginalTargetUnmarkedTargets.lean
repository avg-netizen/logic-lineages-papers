module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalTargetUnmarkedTargets
open Source RecursiveComparison SourceUnmarked SourceExtendedElimination

/-- INTRINSIC target domain of all five ORIGINAL relations. This is to be
proved from every actual original constructor, not supplied as a premise.
No auxiliary In/marked rule belongs to the original relations. -/
def ActualFiveWayTargetNormality : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma),Weak Symbol arity above Gamma s t → Unmarked Symbol arity Gamma t.2) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma),Strict Symbol arity above Gamma s t → Unmarked Symbol arity Gamma t.2) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),WeakMatch Symbol arity above Gamma ss ts → AllUnmarked ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),StrictMultiset Symbol arity above Gamma ss ts → AllUnmarked ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),ReplacementMatch Symbol arity above Gamma ss ts → AllUnmarked ts)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalTargetUnmarkedTargets
