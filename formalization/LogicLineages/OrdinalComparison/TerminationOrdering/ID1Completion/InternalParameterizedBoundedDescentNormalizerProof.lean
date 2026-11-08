module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedBoundedDescentNormalizer InternalParameterizedBoundedDescentNormalizerTargets
open InternalParameterizedBoundedDescentNormalizerSupportProof InternalParameterizedBoundedDescentNormalizerInductionProof
open InternalParameterizedBoundedDescentNormalizerSyntaxProof
open InternalParameterizedNumericIteration InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalQuotientComparisonProof InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalParameterizedBoundedDescentZero : ActualOriginalParameterizedBoundedDescentZero := by
  intro body R V α Gamma parameter
  exact InternalParameterizedBoundedDescentNormalizerStepProof.zeroValue R V parameter

theorem actualOriginalParameterizedBoundedDescentFuelFixedPoint : ActualOriginalParameterizedBoundedDescentFuelFixedPoint := by
  intro body R V α Gamma out fuel value parameter
  let P := atMost value fuel ⊓ repeatGraph (transition R V) out fuel value parameter
  obtain ⟨hi⟩ := repeatResult (body := body) (Gamma := P :: Gamma) R V fuel value out z parameter
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination
      (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))
      (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)))⟩

theorem actualOriginalParameterizedBoundedDescentNormalizerBound : ActualOriginalParameterizedBoundedDescentNormalizerBound := by
  intro body R V α Gamma out input parameter
  let P := normalizerGraph R V out input parameter
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out z parameter hr
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft hi)⟩

theorem actualOriginalParameterizedBoundedDescentNormalizerFixedPoint : ActualOriginalParameterizedBoundedDescentNormalizerFixedPoint := by
  intro body R V α Gamma out input parameter
  let P := normalizerGraph R V out input parameter
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out z parameter hr
  obtain ⟨hb⟩ := rightSuccessor (body := body) (Gamma := P :: Gamma) input (suc input)
    ⟨equalToNext (refl input)⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination
      (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hi))) hb)⟩

theorem actualOriginalParameterizedBoundedDescentNormalizerValidity : ActualOriginalParameterizedBoundedDescentNormalizerValidity := by
  intro body R V α Gamma out input parameter
  let P := normalizerGraph R V out input parameter
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out z parameter hr
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionRight hi))⟩

theorem actualOriginalParameterizedBoundedDescentNormalizerLeft : ActualOriginalParameterizedBoundedDescentNormalizerLeft := by
  intro body R V α Gamma out input typ parameter
  let P := normalizerGraph R V out input parameter
  have hr := normalizerRecover (body := body) (Gamma := P :: Gamma) R V out input parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatResult R V (suc input) input out typ parameter hr
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hi)))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerProof
