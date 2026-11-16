module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler
open GorbowSyntax GorbowPRProgram GorbowPRChildTags List.Vector
/-- Actual total compiler on the original five-constructor syntax. Runtime
input zero is the evaluator's target tag, not a supplied certificate. -/
def compile : {n : Nat} → Program n → Program (n+1)
 | _, .zero => CurrentBasicProducerProgram.program .zero
 | _, .succ => CurrentBasicProducerProgram.program .successor
 | _, .projection i => CurrentBasicProducerProgram.program (.projection i)
 | _, .composition f g => CurrentCompositionProducerProgram.program f g (compile f) (fun i => compile (g i))
 | _, .recursion f g => CurrentRecursionProducerProgram.program f g (compile f) (compile g)

/-- Independent structural numeric specification. It never evaluates the
compiler or any producer AST. Only ORIGINAL evaluator programs are evaluated.
Recursion preserves literal decoding/defaults for the original MP operation. -/
def number : {n : Nat} → Program n → Nat → List.Vector Nat n → Nat
 | _, .zero, target, inputs => CurrentBasicProducerProgram.number .zero target inputs
 | _, .succ, target, inputs => CurrentBasicProducerProgram.number .successor target inputs
 | _, .projection i, target, inputs => CurrentBasicProducerProgram.number (.projection i) target inputs
 | _, .composition f g, target, inputs =>
   let values := List.Vector.ofFn (fun i => evaluate (g i) inputs)
   let codes := List.Vector.ofFn (fun i => number (g i) (target+argumentTag f g i) inputs)
   CurrentCompositionCertificate.number f g target inputs values (evaluate f values)
    codes (number f (target+1) values)
 | _, .recursion f g, target, args =>
   let inputs := args.tail
   let baseCode := CurrentRecursionBaseCertificate.number target inputs (evaluate f inputs)
    (number f (target+1) inputs)
   Nat.rec baseCode (fun counter priorCertificate =>
    let previous := evaluate (.recursion f g) (counter ::ᵥ inputs)
    let childInputs := counter ::ᵥ previous ::ᵥ inputs
    let stepCode := CurrentRecursionStepCertificate.number f target counter inputs previous
     (evaluate g childInputs) (number g (target+stepTag f) childInputs)
    let formulaCode := Encodable.encode (GorbowFormulaPrefixCode.encode
     (EffectiveNumeral.calculation target (.recursion f g) ((counter+1) ::ᵥ inputs)))
    GorbowNumericCertificate.certificateNumber
     (GorbowTheoryCertificateOperations.mpLines 0
      ((GorbowNumericCertificate.decodeFormula formulaCode).getD [])
      ((GorbowNumericCertificate.decodeCertificate stepCode).getD [])
      ((GorbowNumericCertificate.decodeCertificate priorCertificate).getD []))) args.head
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler
