module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePrimaryTargets
open Source NumberedRewriteReduction NumberedRewriteSyntax NumberedPrimaryEquivalence NumberedAuxiliaryCoding OriginalStructuralNodeSize
/-- Actual primary congruence preserves the independent encoding-tree metric.
In particular BASE permutations preserve list-spine overhead as well as term
nodes; no inference from variable rank or Primary.size is made. -/
def PrimaryInvariant : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (q r : Packed Symbol arity Gamma), Primary Symbol arity Gamma q r →
      nodeCount (termCode q.2) = nodeCount (termCode r.2)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePrimaryTargets
