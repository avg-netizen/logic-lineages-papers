module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecurrenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecursionProof
open GorbowSyntax GorbowPRProgram GorbowPRChildTags List.Vector
theorem calibration {m : Nat} (f : Program m) (g : Program (m+2))
 (hf : ∀ target inputs, evaluate (compile f) (target ::ᵥ inputs) = number f target inputs)
 (hg : ∀ target inputs, evaluate (compile g) (target ::ᵥ inputs) = number g target inputs)
 (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (compile (.recursion f g)) (target ::ᵥ counter ::ᵥ inputs) =
 number (.recursion f g) target (counter ::ᵥ inputs) := by
 have h := CurrentRecursionProducerProgram.StatementChecks.exactNativeRaw m f g
  (compile f) (compile g) target inputs counter
 let formula : Nat → Nat := fun k => Encodable.encode (GorbowFormulaPrefixCode.encode
  (EffectiveNumeral.calculation target (.recursion f g) (k ::ᵥ inputs)))
 let step : Nat → Nat := fun k =>
  let previous := evaluate (.recursion f g) (k ::ᵥ inputs)
  CurrentRecursionStepCertificate.number f target k inputs previous
   (evaluate g (k ::ᵥ previous ::ᵥ inputs))
   (number g (target+stepTag f) (k ::ᵥ previous ::ᵥ inputs))
 let base := CurrentRecursionBaseCertificate.number target inputs (evaluate f inputs)
  (number f (target+1) inputs)
 have hformula : ∀ k, evaluate (CurrentCalculationFormulaProgram.program (.recursion f g))
  (target ::ᵥ k ::ᵥ inputs) = formula k := by
  intro k
  exact CurrentCalculationFormulaProgram.StatementChecks.exactNative (m+1) (.recursion f g) target (k ::ᵥ inputs)
 have hstep : ∀ k, evaluate (CurrentRecursionStepProgram.program f g (compile g))
  (target ::ᵥ k ::ᵥ inputs) = step k := by
  intro k
  rw [CurrentRecursionStepProgram.StatementChecks.exactNative,hg]
 have hbase : evaluate (CurrentRecursionBaseProgram.program f (compile f)) (target ::ᵥ inputs) = base := by
  rw [CurrentRecursionBaseProgram.StatementChecks.exactNative,hf]
 have hrec := RecurrenceProof.congruence _ formula _ step _ base hformula hstep hbase counter
 exact h.trans hrec

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecursionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecursionProof
