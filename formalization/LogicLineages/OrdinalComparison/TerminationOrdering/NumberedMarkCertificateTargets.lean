module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedCopyCertificate NumberedMarkCertificate

def ActualTypedMarkCheck : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
  (∃ label,markTarget label q=some r) ↔ PrimitiveMark (Fin n) arity Gamma q r

def ActualLambdaMarkCheck : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (sigma tau : Ty)
    (label : Nat) (q r : AuxTerm (Fin n) arity (sigma::Gamma) tau),
  markTarget label (⟨.arrow sigma tau,.lam q⟩ : Packed (Fin n) arity Gamma)=some ⟨.arrow sigma tau,.lam r⟩ ↔
    finiteMark label q=some r

def ActualNumericMarkCertificate : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (source target : Nat),
  (∃ label,markCertificateTest n arity symbols S Gamma source target label=true) ↔
    ∃ (q r : Packed (Fin n) arity Gamma),InUniverse symbols S q.2 ∧ PrimitiveMark (Fin n) arity Gamma q r ∧
      packedNumber q=source ∧ packedNumber r=target

def ActualNumericMarkSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (above : Fin n → Fin n → Prop) (source target label : Nat),
  markCertificateTest n arity symbols S Gamma source target label=true →
    ∃ (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),InUniverse symbols S q ∧ InUniverse symbols S r ∧
      finiteMark label q=some r ∧ WindowStep (Fin n) arity symbols S above Gamma tau q r ∧
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)=source ∧ packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)=target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateTargets
