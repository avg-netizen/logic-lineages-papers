module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedCopyCertificate

def ActualTypedCopyCheck : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (Gamma : List Ty) (g : Head (Fin n)) (q r : Packed (Fin n) arity Gamma),
  copyTarget arity symbols S table Gamma g q=some r ↔ CopyInstance n arity symbols S table Gamma g q r

def ActualNumericCopyCertificate : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (source target : Nat),
  (∃ certificate,copyCertificateTest n arity symbols S Gamma table source target certificate=true) ↔
    ∃ (g : Head (Fin n)) (q r : Packed (Fin n) arity Gamma),InUniverse symbols S q.2 ∧
      CopyInstance n arity symbols S table Gamma g q r ∧ packedNumber q=source ∧ packedNumber r=target

def ActualNumericCopySound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (source target certificate : Nat),
  copyCertificateTest n arity symbols S Gamma table source target certificate=true →
    ∃ (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),InUniverse symbols S q ∧ InUniverse symbols S r ∧
      WindowStep (Fin n) arity symbols S (tableAbove table) Gamma tau q r ∧
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)=source ∧ packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)=target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateTargets
