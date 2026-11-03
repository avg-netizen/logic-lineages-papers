module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificate
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCopyCertificate NumberedStepContexts NumberedTypedFocus NumberedNumericRoot

structure StepCertificate where
  path : List Position
  replacement : Nat
  root : Nat

def stepTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) {tau : Ty} (q r : AuxTerm (Fin n) arity Gamma tau) (certificate : StepCertificate) : Bool :=
  match focus certificate.path q with
  | none => false
  | some f =>
    match decodePackedNumber n arity f.holeGamma certificate.replacement,decodeSelector n arity f.holeGamma certificate.root with
    | some ⟨sigma,replacement⟩,some selector =>
      if ht : sigma=f.holeType then
        selectorTest n arity symbols S f.holeGamma table ⟨f.holeType,f.value⟩ ⟨sigma,replacement⟩ selector &&
          decide (packedNumber (⟨tau,plug f.context (ht ▸ replacement)⟩ : Packed (Fin n) arity Gamma)=packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma))
      else false
    | _,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificate
