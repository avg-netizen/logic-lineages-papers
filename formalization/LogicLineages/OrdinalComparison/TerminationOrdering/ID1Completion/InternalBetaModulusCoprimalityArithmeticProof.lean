module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityExistenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityDifferenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalAdditionCancellationProof
open InternalOriginalOrderProof InternalBetaDivisionSyntaxProof InternalBetaWitness
open InternalDivisibilityProof InternalBezoutExistenceTargets InternalLinearCombinationSyntaxProof
open InternalProductCoprimalityProof InternalCoprimeMultipleSupportProof
open InternalBetaModulusCoprimalityExistenceProof
open InternalPositiveUnfoldingSupportProof
open InternalQuotientGapProof InternalOriginalOrderSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Literal beta moduli at indices separated by a positive gap differ by that gap times b. -/
def modulusGap (b i w : OrdinaryArithmetic.Term α) :
    Derivation body Gamma (eqn (modulus b (add i (suc w)))
      (add (modulus b i) (mul (suc w) b))) :=
  trans (congSuc (trans (congMulRight b (symm (leftSuccessor i (suc w))))
    (leftDistributivity (suc i) (suc w) b)))
    (symm (leftSuccessor (mul (suc i) b) (mul (suc w) b)))

theorem differenceCoprimality (b i w : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula
      (InternalLinearCombination.divides (suc w) (suc b))))) :
    Nonempty (Derivation body Gamma (coprime (modulus (suc b) i)
      (modulus (suc b) (add i (suc w))))) := by
  apply dividesCases Gamma (suc w) (suc b) _ h
  intro β j Delta q _ he
  simp only [coprimeRename,modulusRename,sucRelabel,addRelabel]
  simp only [sucRelabel] at he
  obtain ⟨he⟩ := he
  let B := suc (b.relabel j)
  let I := i.relabel j
  let W := w.relabel j
  let M := modulus B I
  have hb : Nonempty (Derivation body Delta (coprime B M)) :=
    certificateCoprimality B M (suc I) (suc z)
      ⟨symm (InternalBezoutCRTProof.mulOneLeft M)⟩
  have hd : Nonempty (Derivation body Delta (coprime (suc W) M)) :=
    certificateCoprimality (suc W) M (mul (suc I) q) (suc z)
      ⟨trans (congSuc (trans (multiplicationAssociativity (suc I) q (suc W))
        (congMulLeft (suc I) (symm he)))) (symm (InternalBezoutCRTProof.mulOneLeft M))⟩
  have hmb := coprimeSymmetry B M hb
  have hmd := coprimeSymmetry (suc W) M hd
  obtain ⟨hp⟩ := positiveProductCoprimality (mul (suc I) B) W (b.relabel j) hmd hmb
  obtain ⟨ha⟩ := InternalDivisibilityDifferenceProof.actualCoprimeAdd body β M (mul (suc W) B)
  have hs := Derivation.implicationElimination (weakenClosed ha Delta) hp
  exact ⟨coprimeCongruence M _ _ (symm (modulusGap B I W)) hs⟩

theorem actualDifferenceCoprimality : InternalBetaModulusCoprimalityTargets.ActualDifferenceCoprimality := by
  intro body α b i w
  obtain ⟨h⟩ := differenceCoprimality (body := body)
    (Gamma := [arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc w) (suc b))]) b i w
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityArithmeticProof
