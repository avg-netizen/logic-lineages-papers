module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation
open BalancedSyntax

/-- One beyond the greatest actual raw name, or zero for empty support.
This is a table width, not the number of support coordinates. -/
def tableSize (support : List Nat) : Nat :=
  support.foldr (fun i rest => max (i + 1) rest) 0

/-- Convert the EXISTING first-occurrence box lookup to an actual finite
raw table. Sparse raw names retain their original indices. Missing raw
coordinates inside the table use the lookup's one default, and the existing
BaseTermPrograms.valuation supplies one beyond the table. Equality with the
lookup on all Nat requires the full word/support length guard. -/
def finiteTable (support word : List Nat) : BalancedEvaluation.Table :=
  (List.range (tableSize support)).map (singleCoreBoxLookup support word)

/-- The actual source box word is represented by an ordinary raw table for
the UNCHANGED BalancedEvaluation.codeValue/codeVariables/joint algorithm.
No basis entry is replaced by an independent parameter. -/
def boxTable (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (word : List Nat) : BalancedEvaluation.Table :=
  finiteTable (BalancedSmallBox.sourceSupport k Γ C E F) word

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation
