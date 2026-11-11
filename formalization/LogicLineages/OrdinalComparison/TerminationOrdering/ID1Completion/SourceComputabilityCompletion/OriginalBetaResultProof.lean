module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open OriginalBetaResult OriginalBetaResultCalibrationProof OriginalBetaResultPrimitiveProof
open InternalOriginalUniformParameterLeaves InternalOriginalUniformParameterLeavesCodecProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem resultValueAtParameter (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source : Nat) :
    resultValue n arity (List.Vector.ofFn ![source,parameterCode symbols S Gamma table]) =
      rawResult n arity Gamma source := by
  simp only [resultValue, List.Vector.get_ofFn, Matrix.cons_val_zero,
    Matrix.cons_val_one, decodedValueAtParameter]

theorem actualOriginalBetaResultProgram :
    OriginalBetaResultTargets.ActualOriginalBetaResultProgram := by
  intro n arity
  obtain ⟨B, hB⟩ := Proof.allPrimitiveFunctions 2 _
    (actualOriginalBetaResultPrimitive n arity)
  refine ⟨B,hB,?_,?_⟩
  · intro symbols S Gamma table source
    rw [hB]
    exact resultValueAtParameter n arity symbols S Gamma table source
  · intro symbols S Gamma table sigma tau body a
    rw [hB, resultValueAtParameter]
    exact rawTypedBeta n arity Gamma sigma tau body a

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultProof
