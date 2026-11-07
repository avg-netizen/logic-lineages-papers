module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationArithmeticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalMultiplicationLeftSuccessorProof InternalQuotientGapProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def multiplicationLeftOne (a : OTerm α) :
    Derivation body Gamma (eqn (mul (suc z) a) a) :=
  trans (leftSuccessorMultiplication z a)
    (trans (congAddRight a (multiplicationLeftZero a)) (leftZero a))

def scaleCombination (q x y a b : OTerm α) :
    Derivation body Gamma (eqn (mul q (add (mul x a) (mul y b)))
      (add (mul (mul q x) a) (mul (mul q y) b))) :=
  trans (distributivity q (mul x a) (mul y b))
    (trans (congAddRight (mul q (mul y b)) (symm (multiplicationAssociativity q x a)))
      (congAddLeft (mul (mul q x) a) (symm (multiplicationAssociativity q y b))))

/-- All manipulations are derivation constructors in the original calculus. -/
def linearCombinationRemainderIdentity (a b d q r x y z' w : OTerm α)
    (hd : Derivation body Gamma
      (eqn (add (mul x a) (mul y b)) (add d (add (mul z' a) (mul w b)))))
    (ha : Derivation body Gamma (eqn a (add (mul q d) r))) :
    Derivation body Gamma
      (eqn (add (mul (add (suc z) (mul q z')) a) (mul (mul q w) b))
        (add r (add (mul (mul q x) a) (mul (mul q y) b)))) := by
  let N := add (mul z' a) (mul w b)
  have hleft : Derivation body Gamma
      (eqn (add (mul (add (suc z) (mul q z')) a) (mul (mul q w) b))
        (add a (mul q N))) :=
    trans (congAddRight (mul (mul q w) b) (leftDistributivity (suc z) (mul q z') a))
      (trans (congAddRight (mul (mul q w) b)
        (congAddRight (mul (mul q z') a) (multiplicationLeftOne a)))
        (trans (associativity a (mul (mul q z') a) (mul (mul q w) b))
          (congAddLeft a (symm (scaleCombination q z' w a b)))))
  have hmiddle : Derivation body Gamma (eqn (add a (mul q N))
      (add r (mul q (add d N)))) :=
    trans (congAddRight (mul q N) ha)
      (trans (congAddRight (mul q N) (commutativity (mul q d) r))
        (trans (associativity r (mul q d) (mul q N))
          (congAddLeft r (symm (distributivity q d N)))))
  exact trans hleft (trans hmiddle
    (trans (congAddLeft r (congMulLeft q (symm hd)))
      (congAddLeft r (scaleCombination q x y a b))))

theorem actualMultiplicationRightDistributivity :
    InternalLinearCombinationArithmeticTargets.ActualMultiplicationRightDistributivity := by
  intro body α s t u
  rw [onEquality]
  exact ⟨leftDistributivity s t u⟩

theorem actualMultiplicationRightCongruence :
    InternalLinearCombinationArithmeticTargets.ActualMultiplicationRightCongruence := by
  intro body α s t u
  change Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula (s.equal t)).imp
    (arithmeticEmbedding.onFormula ((mul s u).equal (mul t u)))))
  rw [onEquality,onEquality]
  exact ⟨Derivation.implicationIntroduction
    (congMulRight u (Derivation.hypothesis List.mem_cons_self))⟩

theorem actualLinearCombinationRemainderIdentity :
    InternalLinearCombinationArithmeticTargets.ActualLinearCombinationRemainderIdentity := by
  intro body α a b d q r x y z' w
  change Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula ((add (mul x a) (mul y b)).equal
      (add d (add (mul z' a) (mul w b))))).imp
      ((arithmeticEmbedding.onFormula (a.equal (add (mul q d) r))).imp
        (arithmeticEmbedding.onFormula
          ((add (mul (add (suc z) (mul q z')) a) (mul (mul q w) b)).equal
            (add r (add (mul (mul q x) a) (mul (mul q y) b))))))))
  rw [onEquality,onEquality,onEquality]
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction
    (linearCombinationRemainderIdentity a b d q r x y z' w
      (Derivation.hypothesis (by simp)) (Derivation.hypothesis List.mem_cons_self)))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationArithmeticProof
