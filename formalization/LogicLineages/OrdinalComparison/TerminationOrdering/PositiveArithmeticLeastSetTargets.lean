module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetTargets
open PositiveArithmeticOperators PositiveArithmeticTransforms TaggedArithmeticOperators PositiveArithmeticLeastSet

def ActualSemanticLeastUnfolding : Prop := ∀ (body : Positive (Fin 2)) (context x : Nat),
    x ∈ leastSet body context ↔ realize (fun y => y ∈ leastSet body context) body.formula ![context,x]

def ActualSemanticLeastness : Prop := ∀ (body : Positive (Fin 2)) (context : Nat) (P : Set Nat),
    (∀ x, realize (fun y => y ∈ P) body.formula ![context,x] → x ∈ P) → leastSet body context ⊆ P

def ActualTaggedLeastSlices : Prop := ∀ (scalar multiset : Positive (Fin 2)) (context x : Nat),
    (tagNumber false x ∈ leastSet (combinedOperator scalar multiset) context ↔ x ∈ leastSet scalar context) ∧
    (tagNumber true x ∈ leastSet (combinedOperator scalar multiset) context ↔ x ∈ leastSet multiset context)

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetTargets
