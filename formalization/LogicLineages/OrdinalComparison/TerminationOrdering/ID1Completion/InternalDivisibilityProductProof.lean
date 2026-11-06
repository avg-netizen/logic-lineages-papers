module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalQuotientGapProof
open InternalMultiplicationLeftSuccessorProof InternalOrientedBezoutArithmeticProof
open InternalLinearCombination InternalLinearCombinationSyntaxProof InternalDivisibilityProof
open InternalBetaDivisionSyntaxProof InternalBezoutExistenceTargets InternalBezoutCRTProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem dividesProduct (d P B : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides d P)))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides d (mul P B)))) := by
  apply dividesCases Gamma d P _ h
  intro β j Delta q _ ⟨hq⟩
  rw [dividesRename,mulRelabel]
  apply dividesIntroduction _ _ (mul q (B.relabel j))
  exact ⟨trans (congMulRight (B.relabel j) hq) (productSwap q (d.relabel j) (B.relabel j))⟩
theorem dividesRightProduct (P B : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides B (mul P B)))) :=
  dividesIntroduction B (mul P B) P ⟨refl _⟩
def positiveProduct (a b : OrdinaryArithmetic.Term α) :
    Derivation body Gamma (eqn (mul (suc a) (suc b)) (suc (add (mul a (suc b)) b))) :=
  trans (leftSuccessorMultiplication a (suc b)) (addSucc (mul a (suc b)) b)
theorem coprimeOne (a : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (coprime a (suc z))) :=
  certificateCoprimality a one z one
    ⟨trans (congSuc (multiplicationLeftZero a)) (symm (mulOneRight one))⟩
theorem actualDividesProduct : InternalDivisibilityProductTargets.ActualDividesProduct := by
  intro body α d P B
  obtain ⟨h⟩ := dividesProduct (body := body) (Gamma := [arithmeticEmbedding.onFormula (divides d P)]) d P B
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
theorem actualProductPositive : InternalDivisibilityProductTargets.ActualProductPositive := by
  intro body α a b
  exact ⟨positiveProduct a b⟩
theorem actualCoprimeOne : InternalDivisibilityProductTargets.ActualCoprimeOne := by
  intro body α a
  exact coprimeOne a
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductProof
