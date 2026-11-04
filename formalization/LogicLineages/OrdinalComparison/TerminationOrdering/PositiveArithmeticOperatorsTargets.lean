module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsTargets
open PositiveArithmeticOperators

def ActualArithmeticEmbeddingTruth : Prop := ∀ (α : Type) (phi : OrdinaryArithmetic.Formula α)
    (P : Nat → Prop) (v : α → Nat), realize P (arithmeticEmbedding.onFormula phi) v ↔ phi.Realize v

def ActualPositiveMonotonicity : Prop := ∀ (α : Type) (phi : Positive α) (P Q : Nat → Prop),
    (∀ x, P x → Q x) → ∀ v : α → Nat, realize P phi.formula v → realize Q phi.formula v

def ActualAccessibilityOperatorTruth : Prop := ∀ (carrier : OrdinaryArithmetic.Formula (Fin 2))
    (edge : OrdinaryArithmetic.Formula (Fin 3)) (P : Nat → Prop) (context x : Nat),
    realize P (accessibilityOperator carrier edge).formula ![context,x] ↔
      carrier.Realize ![context,x] ∧ ∀ y : Nat, edge.Realize ![context,x,y] → P y

def ActualSourcePositiveOperators : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty),
    ∃ scalar multiset : Positive (Fin 2), ∀ (P : Nat → Prop) (context x : Nat),
      (realize P scalar.formula ![context,x] ↔
        OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x ∧
        ∀ y, encodedR n arity Gamma context x y → P y) ∧
      (realize P multiset.formula ![context,x] ↔
        OrdinaryArithmeticCarrier.encodedList n arity Gamma context x ∧
        ∀ y, OrdinaryArithmeticDirect.encodedDirect n arity Gamma context x y → P y)

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsTargets
