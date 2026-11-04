module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsTargets
open PositiveArithmeticOperators PositiveArithmeticTransforms TaggedArithmeticOperators

def ActualTagPartition : Prop := ∀ z : Nat, ∃! p : Bool × Nat, tagNumber p.1 p.2 = z

def ActualTaggedBranchIsolation : Prop := ∀ (scalar multiset : Positive (Fin 2)) (P : Nat → Prop) (context x : Nat),
    (realize P (combinedOperator scalar multiset).formula ![context,tagNumber false x] ↔
      realize (fun y => P (tagNumber false y)) scalar.formula ![context,x]) ∧
    (realize P (combinedOperator scalar multiset).formula ![context,tagNumber true x] ↔
      realize (fun y => P (tagNumber true y)) multiset.formula ![context,x])

def ActualCombinedMonotonicity : Prop := ∀ (scalar multiset : Positive (Fin 2)) (P Q : Nat → Prop),
    (∀ x, P x → Q x) → ∀ context z : Nat,
    realize P (combinedOperator scalar multiset).formula ![context,z] →
      realize Q (combinedOperator scalar multiset).formula ![context,z]

def ActualTaggedSourceOperators : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty),
    ∃ combined : Positive (Fin 2), ∀ (P : Nat → Prop) (context x : Nat),
    (realize P combined.formula ![context,tagNumber false x] ↔
      OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x ∧
      ∀ y, encodedR n arity Gamma context x y → P (tagNumber false y)) ∧
    (realize P combined.formula ![context,tagNumber true x] ↔
      OrdinaryArithmeticCarrier.encodedList n arity Gamma context x ∧
      ∀ y, OrdinaryArithmeticDirect.encodedDirect n arity Gamma context x y → P (tagNumber true y))

end LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsTargets
