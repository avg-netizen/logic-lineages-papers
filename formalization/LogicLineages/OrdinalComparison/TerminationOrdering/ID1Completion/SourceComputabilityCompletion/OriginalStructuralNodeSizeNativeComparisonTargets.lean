module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeNativeComparisonTargets
open OriginalStructuralNodeSize NumberedAuxiliaryCoding
/-- Native source comparison through the existing codeBounds size algebra,
which excludes list nil/cons overhead. No runtime representative equality. -/
def SourceSizeBound : Prop := ∀ (n : Nat) (q : Code (Fin n)),
  (NumberedSyntaxBoundsPrimrec.codeBounds q).1 ≤ nodeCount q
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeNativeComparisonTargets
