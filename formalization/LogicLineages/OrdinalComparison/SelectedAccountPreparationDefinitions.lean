module
public import LogicLineages.OrdinalComparison.AccountSemanticDeterminacyDefinitions
public import LogicLineages.OrdinalComparison.WWSelectedBinderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation

/-- Actual typed permutation of the selected occurrence; every other name
retains its relative order. Equal types never identify different occurrences. -/
def prepare (left right : List Ty) (σ : Ty)
    (q : OrdinalExpression (left ++ σ :: right)) : OrdinalExpression (σ :: (left ++ right)) :=
  ordinalExpressionRename (SelectedBinder.moveToHead left right σ) q

def prepareSource {τ : Ty} (left right : List Ty) (σ : Ty)
    (t : OriginalTerm (left ++ σ :: right) τ) : OriginalTerm (σ :: (left ++ right)) τ :=
  t.rename (SelectedBinder.moveToHead left right σ)
end LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation
