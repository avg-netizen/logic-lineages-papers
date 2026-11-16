module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapNative
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.NativeOriginalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem exactOriginal : Targets.NativeOriginal := by
 intro m f g B G target inputs counter
 unfold program
 rw [SwapNative.swapEval]
 have h := CurrentRecursionAccumulator.StatementChecks.exactNativeOriginal (m+1)
  (CurrentRecursionBaseProgram.program f B) (formula f g) (step f g G) (target ::ᵥ inputs)
  (fun k => EffectiveNumeral.calculation target (.recursion f g) (k ::ᵥ inputs))
  (fun k => (SwapNative.swapEval _ k target inputs).trans
   (CurrentCalculationFormulaProgram.StatementChecks.exactNative (m+1) (.recursion f g) target (k ::ᵥ inputs))) counter
 have hs : (fun k => evaluate (step f g G) (k ::ᵥ target ::ᵥ inputs)) =
  (fun k => let previous := evaluate (.recursion f g) (k ::ᵥ inputs)
    CurrentRecursionStepCertificate.number f target k inputs previous (evaluate g (k ::ᵥ previous ::ᵥ inputs))
     (evaluate G ((target+GorbowPRChildTags.stepTag f) ::ᵥ k ::ᵥ previous ::ᵥ inputs))) := by
  funext k
  exact (SwapNative.swapEval _ k target inputs).trans
   (CurrentRecursionStepProgram.StatementChecks.exactNative m f g G target k inputs)
 rw [hs,CurrentRecursionBaseProgram.StatementChecks.exactNative] at h
 exact h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.NativeOriginalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.NativeOriginalProof
