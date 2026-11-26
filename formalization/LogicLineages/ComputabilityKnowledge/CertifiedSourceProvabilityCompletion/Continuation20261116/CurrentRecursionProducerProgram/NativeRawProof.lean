module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapNative
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.NativeRawProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem exactRaw : Targets.NativeRaw := by
 intro m f g B G target inputs counter
 unfold program
 rw [SwapNative.swapEval]
 have h := CurrentRecursionAccumulator.StatementChecks.exactNativeRaw (m+1)
  (CurrentRecursionBaseProgram.program f B) (formula f g) (step f g G) (target ::ᵥ inputs) counter
 have hf : (fun k => evaluate (formula f g) (k ::ᵥ target ::ᵥ inputs)) =
  (fun k => evaluate (CurrentCalculationFormulaProgram.program (.recursion f g)) (target ::ᵥ k ::ᵥ inputs)) := by
  funext k
  exact SwapNative.swapEval _ k target inputs
 have hs : (fun k => evaluate (step f g G) (k ::ᵥ target ::ᵥ inputs)) =
  (fun k => evaluate (CurrentRecursionStepProgram.program f g G) (target ::ᵥ k ::ᵥ inputs)) := by
  funext k
  exact SwapNative.swapEval _ k target inputs
 rw [hf,hs] at h
 exact h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.NativeRawProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.NativeRawProof
