module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationArithmeticTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open OrdinaryArithmetic

def ActualMultiplicationRightDistributivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((mulTerm (addTerm s t) u).equal (addTerm (mulTerm s u) (mulTerm t u)))))

def ActualMultiplicationRightCongruence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((s.equal t).imp ((mulTerm s u).equal (mulTerm t u)))))

/-- The nonnegative coefficient identity used to close positive signed linear
combinations under Euclidean remainder. Both hypotheses remain explicit. -/
def ActualLinearCombinationRemainderIdentity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type)
    (a b d q r x y z w : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    (((addTerm (mulTerm x a) (mulTerm y b)).equal
        (addTerm d (addTerm (mulTerm z a) (mulTerm w b)))).imp
      ((a.equal (addTerm (mulTerm q d) r)).imp
        ((addTerm (mulTerm (addTerm (succTerm zeroTerm) (mulTerm q z)) a)
          (mulTerm (mulTerm q w) b)).equal
          (addTerm r (addTerm (mulTerm (mulTerm q x) a) (mulTerm (mulTerm q y) b))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationArithmeticTargets
