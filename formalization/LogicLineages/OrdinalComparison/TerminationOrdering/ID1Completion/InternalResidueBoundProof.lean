module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLeftSuccessorProof
open InternalMultiplicationLawsProof InternalAdditionCancellationProof InternalPositiveUnfoldingSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalCoprimeMultiple InternalCoprimeMultipleStepProof InternalCoprimeMultipleSupportProof
open InternalDivisibilityProductProof InternalBetaModulusCoprimality InternalResidueBoundTargets
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem actualScaleMultiples : ActualScaleMultiples := by
  intro body α Gamma b k n h
  obtain ⟨hp⟩ := boundedDividesProduct (.var (.inr 0)) (suc b) (suc k) n h
  exact ⟨dividesBelowCongruence (.var (.inr 0)) _ _ n (positiveProduct b k) hp⟩

theorem scaleAboveBound (b k : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (ltF k (suc (scalePred b k)))) := by
  apply actualOriginalOrderIntroduction body α Gamma k (suc (scalePred b k)) (mul b (suc k))
  rw [onEquality]
  exact ⟨trans (addSucc k (mul b (suc k))) (congSuc (commutativity k (mul b (suc k))))⟩

theorem modulusAboveScale (B i : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (ltF B (InternalBetaWitness.modulus B i))) := by
  apply actualOriginalOrderIntroduction body α Gamma B (InternalBetaWitness.modulus B i) (mul i B)
  rw [onEquality]
  exact ⟨trans (addSucc B (mul i B))
    (trans (congSuc (commutativity B (mul i B)))
      (congSuc (symm (leftSuccessorMultiplication i B))))⟩

theorem actualResidueBound : ActualResidueBound := by
  intro body α Gamma b k i r hr
  obtain ⟨hr⟩ := hr
  obtain ⟨hk⟩ := scaleAboveBound (body := body) (Gamma := Gamma) b k
  obtain ⟨hB⟩ := modulusAboveScale (body := body) (Gamma := Gamma) (suc (scalePred b k)) i
  obtain ⟨ht⟩ := actualOriginalOrderTransitivity body α r k (suc (scalePred b k))
  have hrB := Derivation.implicationElimination (weakenClosed ht Gamma)
    (Derivation.conjunctionIntroduction hr hk)
  obtain ⟨hu⟩ := actualOriginalOrderTransitivity body α r (suc (scalePred b k))
    (InternalBetaWitness.modulus (suc (scalePred b k)) i)
  exact ⟨Derivation.implicationElimination (weakenClosed hu Gamma)
    (Derivation.conjunctionIntroduction hrB hB)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundProof
