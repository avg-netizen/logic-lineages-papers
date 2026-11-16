module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.CompositionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Proof
open GorbowSyntax GorbowPRProgram GorbowPRChildTags List.Vector
theorem exactNative : Targets.NativeCompiler := by
 intro n q
 induction q with
 | zero => exact CurrentBasicProducerProgram.StatementChecks.exactNative 0 .zero
 | succ => exact CurrentBasicProducerProgram.StatementChecks.exactNative 1 .successor
 | projection i => exact CurrentBasicProducerProgram.StatementChecks.exactNative _ (.projection i)
 | composition f g hf hg => exact CompositionProof.calibration f g hf hg
 | recursion f g hf hg =>
  intro target inputs
  have h := RecursionProof.calibration f g hf hg target inputs.head inputs.tail
  exact Eq.mp (congrArg
   (fun xs => evaluate (compile (.recursion f g)) (target ::ᵥ xs) =
    number (.recursion f g) target xs)
   (List.Vector.cons_head_tail inputs)) h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Proof
