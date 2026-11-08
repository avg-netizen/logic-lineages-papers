module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalBoundedDescentNormalizer InternalBoundedDescentNormalizerTargets
open InternalBoundedDescentNormalizerSupportProof InternalBoundedDescentNormalizerInductionProof
open InternalBoundedDescentNormalizerSyntaxProof
open InternalNumericIteration InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalQuotientComparisonProof InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalBoundedDescentZero : ActualOriginalBoundedDescentZero := by
  intro body R V α Gamma
  exact InternalBoundedDescentNormalizerStepProof.zeroValue R V

theorem actualOriginalBoundedDescentFuelFixedPoint : ActualOriginalBoundedDescentFuelFixedPoint := by
  intro body R V α Gamma out fuel value
  let P := atMost value fuel ⊓ repeatGraph (transition R V) out fuel value
  obtain ⟨hi⟩ := repeatResult (body := body) (Gamma := P :: Gamma) R V fuel value out z
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination
      (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))
      (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)))⟩

theorem actualOriginalBoundedDescentNormalizerBound : ActualOriginalBoundedDescentNormalizerBound := by
  intro body R V α Gamma out input
  let P := normalizerGraph R V out input
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out z hr
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft hi)⟩

theorem actualOriginalBoundedDescentNormalizerFixedPoint : ActualOriginalBoundedDescentNormalizerFixedPoint := by
  intro body R V α Gamma out input
  let P := normalizerGraph R V out input
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out z hr
  obtain ⟨hb⟩ := rightSuccessor (body := body) (Gamma := P :: Gamma) input (suc input)
    ⟨equalToNext (refl input)⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination
      (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hi))) hb)⟩

theorem actualOriginalBoundedDescentNormalizerValidity : ActualOriginalBoundedDescentNormalizerValidity := by
  intro body R V α Gamma out input
  let P := normalizerGraph R V out input
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out z hr
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionRight hi))⟩

theorem actualOriginalBoundedDescentNormalizerLeft : ActualOriginalBoundedDescentNormalizerLeft := by
  intro body R V α Gamma out input typ
  let P := normalizerGraph R V out input
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out typ hr
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerProof
