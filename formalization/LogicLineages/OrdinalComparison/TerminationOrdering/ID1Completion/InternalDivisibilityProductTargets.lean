module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof
open InternalBezoutCRT (mul add)
open InternalLinearCombination InternalBezoutExistenceTargets
 def ActualDividesProduct : Prop := ∀ (body : Positive (Fin 1)) (α : Type) (d P B : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula (divides d P)).imp
    (arithmeticEmbedding.onFormula (divides d (mul P B)))))
 def ActualProductPositive : Prop := ∀ (body : Positive (Fin 1)) (α : Type) (a b : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (eqn (mul (suc a) (suc b)) (suc (add (mul a (suc b)) b))))
 def ActualCoprimeOne : Prop := ∀ (body : Positive (Fin 1)) (α : Type) (a : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (coprime a (suc z)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductTargets
