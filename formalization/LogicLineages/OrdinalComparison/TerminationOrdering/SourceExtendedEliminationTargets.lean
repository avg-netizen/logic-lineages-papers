module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationTargets
open Source RecursiveComparison SourceExtendedElimination

/-- FULL real auxiliary derivation elimination, including all finite DropMore,
Reorder, prefix-Args and prefix-Select clauses. Every smaller-derivation
callback must be discharged by ACTUAL mutual induction before acceptance. -/
def ActualJointElimination : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma),SourceExtendedComparison.Weak Symbol arity above Gamma s t → WeakMeaning above s t) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma),SourceExtendedComparison.Strict Symbol arity above Gamma s t → StrictMeaning above s t) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts → MatchMeaning above ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.StrictMultiset Symbol arity above Gamma ss ts → MultiMeaning above ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),SourceExtendedComparison.ReplacementMatch Symbol arity above Gamma ss ts → ReplacementMeaning above ss ts)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationTargets
