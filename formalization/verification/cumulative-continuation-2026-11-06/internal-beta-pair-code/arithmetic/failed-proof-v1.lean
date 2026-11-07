module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalMultiplicationLeftSuccessorProof InternalQuotientGapProof
open InternalBetaPairCode
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def oneMul (t : OTerm α) : Derivation body Gamma (eqn (mul (suc z) t) t) :=
  trans (leftSuccessorMultiplication z t)
    (trans (congAddRight t (multiplicationLeftZero t)) (leftZero t))
def twoMul (t : OTerm α) : Derivation body Gamma (eqn (mul (suc (suc z)) t) (twice t)) :=
  trans (leftSuccessorMultiplication (suc z) t) (congAddRight t (oneMul t))

/-- A finite composition of original associativity/commutativity derivations. -/
def rearrangePair (p x y : OTerm α) : Derivation body Gamma
    (eqn (add (add (add (add p p) (add x y)) (add (add y y) (add y y))) x) (add (add (add (add p p) (add (add x y) (add x y))) (add y y)) y)) :=
  (trans (trans (trans (trans (trans (trans (trans (congAddRight x (trans (congAddRight (add (add y y) (add y y)) (trans (congAddRight (add x y) (trans (congAddRight p (refl p)) (trans (congAddLeft p (refl p)) (refl (add p p))))) (trans (congAddLeft (add p p) (trans (congAddRight y (refl x)) (trans (congAddLeft x (refl y)) (refl (add x y))))) (trans (associativity p p (add x y)) (congAddLeft p (refl (add p (add x y)))))))) (trans (congAddLeft (add p (add p (add x y))) (trans (congAddRight (add y y) (trans (congAddRight y (refl y)) (trans (congAddLeft y (refl y)) (refl (add y y))))) (trans (congAddLeft (add y y) (trans (congAddRight y (refl y)) (trans (congAddLeft y (refl y)) (refl (add y y))))) (trans (associativity y y (add y y)) (congAddLeft y (refl (add y (add y y)))))))) (trans (associativity p (add p (add x y)) (add y (add y (add y y)))) (congAddLeft p (trans (associativity p (add x y) (add y (add y (add y y)))) (congAddLeft p (trans (associativity x y (add y (add y (add y y)))) (congAddLeft x (refl (add y (add y (add y (add y y)))))))))))))) (trans (congAddLeft (add p (add p (add x (add y (add y (add y (add y y))))))) (refl x)) (trans (associativity p (add p (add x (add y (add y (add y (add y y)))))) x) (congAddLeft p (trans (associativity p (add x (add y (add y (add y (add y y))))) x) (congAddLeft p (trans (associativity x (add y (add y (add y (add y y)))) x) (congAddLeft x (trans (associativity y (add y (add y (add y y))) x) (congAddLeft y (trans (associativity y (add y (add y y)) x) (congAddLeft y (trans (associativity y (add y y) x) (congAddLeft y (trans (associativity y y x) (congAddLeft y (refl (add y x)))))))))))))))))) (congAddLeft p (congAddLeft p (congAddLeft x (congAddLeft y (congAddLeft y (congAddLeft y (congAddLeft y (commutativity y x))))))))) (congAddLeft p (congAddLeft p (congAddLeft x (congAddLeft y (congAddLeft y (congAddLeft y (trans (symm (associativity y x y)) (trans (congAddRight y (commutativity y x)) (associativity x y y)))))))))) (congAddLeft p (congAddLeft p (congAddLeft x (congAddLeft y (congAddLeft y (trans (symm (associativity y x (add y y))) (trans (congAddRight (add y y) (commutativity y x)) (associativity x y (add y y)))))))))) (congAddLeft p (congAddLeft p (congAddLeft x (congAddLeft y (trans (symm (associativity y x (add y (add y y)))) (trans (congAddRight (add y (add y y)) (commutativity y x)) (associativity x y (add y (add y y)))))))))) (congAddLeft p (congAddLeft p (congAddLeft x (trans (symm (associativity y x (add y (add y (add y y))))) (trans (congAddRight (add y (add y (add y y))) (commutativity y x)) (associativity x y (add y (add y (add y y)))))))))) (symm (trans (trans (congAddRight y (trans (congAddRight (add y y) (trans (congAddRight (add (add x y) (add x y)) (trans (congAddRight p (refl p)) (trans (congAddLeft p (refl p)) (refl (add p p))))) (trans (congAddLeft (add p p) (trans (congAddRight (add x y) (trans (congAddRight y (refl x)) (trans (congAddLeft x (refl y)) (refl (add x y))))) (trans (congAddLeft (add x y) (trans (congAddRight y (refl x)) (trans (congAddLeft x (refl y)) (refl (add x y))))) (trans (associativity x y (add x y)) (congAddLeft x (refl (add y (add x y)))))))) (trans (associativity p p (add x (add y (add x y)))) (congAddLeft p (refl (add p (add x (add y (add x y)))))))))) (trans (congAddLeft (add p (add p (add x (add y (add x y))))) (trans (congAddRight y (refl y)) (trans (congAddLeft y (refl y)) (refl (add y y))))) (trans (associativity p (add p (add x (add y (add x y)))) (add y y)) (congAddLeft p (trans (associativity p (add x (add y (add x y))) (add y y)) (congAddLeft p (trans (associativity x (add y (add x y)) (add y y)) (congAddLeft x (trans (associativity y (add x y) (add y y)) (congAddLeft y (trans (associativity x y (add y y)) (congAddLeft x (refl (add y (add y y)))))))))))))))) (trans (congAddLeft (add p (add p (add x (add y (add x (add y (add y y))))))) (refl y)) (trans (associativity p (add p (add x (add y (add x (add y (add y y)))))) y) (congAddLeft p (trans (associativity p (add x (add y (add x (add y (add y y))))) y) (congAddLeft p (trans (associativity x (add y (add x (add y (add y y)))) y) (congAddLeft x (trans (associativity y (add x (add y (add y y))) y) (congAddLeft y (trans (associativity x (add y (add y y)) y) (congAddLeft x (trans (associativity y (add y y) y) (congAddLeft y (trans (associativity y y y) (congAddLeft y (refl (add y y)))))))))))))))))) (congAddLeft p (congAddLeft p (congAddLeft x (trans (symm (associativity y x (add y (add y (add y y))))) (trans (congAddRight (add y (add y (add y y))) (commutativity y x)) (associativity x y (add y (add y (add y y))))))))))))

def pairEquation (x y : OTerm α) : Derivation body Gamma
    (eqn (firstCode x y) (add (mul (secondQuotient y) (suc (twice (secondCode x y)))) y)) := by
  let a := twice y
  let s := secondCode x y
  let p := mul a s
  have hl : Derivation body Gamma
      (eqn (firstCode x y) (suc (add (add (add (add p p) s) (add a a)) x))) :=
    trans (congAddRight x (mulSucc (suc (add a a)) s))
      (trans (congAddRight x (congAddRight (suc (add a a)) (leftSuccessorMultiplication (add a a) s)))
        (trans (congAddRight x (congAddRight (suc (add a a)) (congAddRight s (leftDistributivity a a s))))
          (trans (congAddRight x (addSucc (add (add p p) s) (add a a)))
            (leftSuccessor (add (add (add p p) s) (add a a)) x))))
  have hr : Derivation body Gamma
      (eqn (add (mul (secondQuotient y) (suc (twice s))) y)
        (suc (add (add (add (add p p) (add s s)) a) y))) :=
    trans (congAddRight y (mulSucc (suc a) (add s s)))
      (trans (congAddRight y (congAddRight (suc a) (leftSuccessorMultiplication a (add s s))))
        (trans (congAddRight y (congAddRight (suc a) (congAddRight (add s s) (distributivity a s s))))
          (trans (congAddRight y (addSucc (add (add p p) (add s s)) a))
            (leftSuccessor (add (add (add p p) (add s s)) a) y))))
  exact trans hl (trans (congSuc (rearrangePair p x y)) (symm hr))

def rearrangeBound (x y : OTerm α) : Derivation body Gamma
    (eqn (add y (add (add x x) y)) (add (add x y) (add x y))) :=
  (trans (trans (trans (trans (congAddRight (add (add x x) y) (refl y)) (trans (congAddLeft y (trans (congAddRight y (trans (congAddRight x (refl x)) (trans (congAddLeft x (refl x)) (refl (add x x))))) (trans (congAddLeft (add x x) (refl y)) (trans (associativity x x y) (congAddLeft x (refl (add x y))))))) (refl (add y (add x (add x y)))))) (trans (symm (associativity y x (add x y))) (trans (congAddRight (add x y) (commutativity y x)) (associativity x y (add x y))))) (congAddLeft x (trans (symm (associativity y x y)) (trans (congAddRight y (commutativity y x)) (associativity x y y))))) (symm (trans (trans (congAddRight (add x y) (trans (congAddRight y (refl x)) (trans (congAddLeft x (refl y)) (refl (add x y))))) (trans (congAddLeft (add x y) (trans (congAddRight y (refl x)) (trans (congAddLeft x (refl y)) (refl (add x y))))) (trans (associativity x y (add x y)) (congAddLeft x (refl (add y (add x y))))))) (congAddLeft x (trans (symm (associativity y x y)) (trans (congAddRight y (commutativity y x)) (associativity x y y)))))))

def boundEquation (x y : OTerm α) : Derivation body Gamma
    (eqn (add y (suc (add (twice x) y))) (suc (twice (secondCode x y)))) :=
  trans (addSucc y (add (twice x) y)) (congSuc (rearrangeBound x y))

theorem actualPairEquation : InternalBetaPairArithmeticTargets.ActualPairEquation := by
  intro body α Gamma x y
  rw [onEquality]
  exact ⟨pairEquation x y⟩
theorem actualOneMultiplication : InternalBetaPairArithmeticTargets.ActualOneMultiplication := by
  intro body α Gamma t
  rw [onEquality]
  exact ⟨oneMul t⟩
theorem actualTwoMultiplication : InternalBetaPairArithmeticTargets.ActualTwoMultiplication := by
  intro body α Gamma t
  rw [onEquality]
  exact ⟨twoMul t⟩
theorem actualBoundEquation : InternalBetaPairArithmeticTargets.ActualBoundEquation := by
  intro body α Gamma x y
  rw [onEquality]
  exact ⟨boundEquation x y⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticProof
