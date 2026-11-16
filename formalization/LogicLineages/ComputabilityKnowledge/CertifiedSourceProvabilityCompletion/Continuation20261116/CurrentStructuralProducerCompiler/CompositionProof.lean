module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.CompositionProof
open GorbowSyntax GorbowPRProgram GorbowPRChildTags List.Vector
theorem calibration {m n : Nat} (f : Program n) (g : Fin n → Program m)
 (hf : ∀ target inputs, evaluate (compile f) (target ::ᵥ inputs) = number f target inputs)
 (hg : ∀ i target inputs, evaluate (compile (g i)) (target ::ᵥ inputs) = number (g i) target inputs)
 (target : Nat) (inputs : List.Vector Nat m) :
 evaluate (compile (.composition f g)) (target ::ᵥ inputs) = number (.composition f g) target inputs := by
 let values : List.Vector Nat n := List.Vector.ofFn (fun i => evaluate (g i) inputs)
 have h := CurrentCompositionProducerProgram.StatementChecks.exactNative m n f g
  (compile f) (fun i => compile (g i)) target inputs
 have hcodes : (List.Vector.ofFn (fun i => evaluate (compile (g i)) ((target+argumentTag f g i) ::ᵥ inputs))) =
  List.Vector.ofFn (fun i => number (g i) (target+argumentTag f g i) inputs) :=
  congrArg (fun v : Fin n → Nat => List.Vector.ofFn v) (funext (fun i => hg i _ _))
 have hresult := congrArg₂
  (fun (codes : List.Vector Nat n) (fc : Nat) =>
   CurrentCompositionCertificate.number f g target inputs values (evaluate f values) codes fc)
  hcodes (hf (target+1) values)
 exact h.trans hresult

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.CompositionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.CompositionProof
