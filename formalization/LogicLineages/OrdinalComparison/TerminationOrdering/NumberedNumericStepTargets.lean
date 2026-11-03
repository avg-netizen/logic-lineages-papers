module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedMultisetNumeric NumberedTypedFocus NumberedStepCertificate NumberedNumericStep

def ActualPathNumericRoundTrip : Prop := ∀ path,decodePath (pathNumber path)=some path
def ActualPathNumericSound : Prop := ∀ value path,decodePath value=some path → pathNumber path=value

def ActualStepCertificateNumericRoundTrip : Prop := ∀ c,decodeStepCertificate (stepCertificateNumber c)=some c
def ActualStepCertificateNumericSound : Prop := ∀ value c,decodeStepCertificate value=some c → stepCertificateNumber c=value

def ActualNumericStepCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source target : Nat),
  (∃ certificate,numericStepTest n arity symbols S Gamma table source target certificate=true) ↔
    ∃ (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),InUniverse symbols S q ∧
      WindowStep (Fin n) arity symbols S (tableAbove table) Gamma tau q r ∧
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)=source ∧ packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)=target

def ActualNumericStepSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (source target certificate : Nat),
  numericStepTest n arity symbols S Gamma table source target certificate=true →
    ∃ (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),InUniverse symbols S q ∧ InUniverse symbols S r ∧
      WindowStep (Fin n) arity symbols S (tableAbove table) Gamma tau q r ∧
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)=source ∧ packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)=target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepTargets
