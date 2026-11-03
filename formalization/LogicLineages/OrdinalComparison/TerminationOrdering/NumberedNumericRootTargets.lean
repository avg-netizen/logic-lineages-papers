module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedMultisetCertificate NumberedMultisetNumeric NumberedMulCertificate NumberedDirectCertificate NumberedSelectCertificate NumberedRootDecomposition NumberedNumericRoot

def ActualRootSelectorRoundTrip : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (selector : RootSelector n arity Gamma),
  decodeSelector n arity Gamma (selectorNumber selector)=some selector

def ActualTypedRootSelectors : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (q r : Packed (Fin n) arity Gamma),
  (∃ selector,selectorTest n arity symbols S Gamma table q r selector=true) ↔ RootInstance n arity symbols S (tableAbove table) Gamma q r

def ActualNumericRootCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source target : Nat),
  (∃ certificate,numericRootTest n arity symbols S Gamma table source target certificate=true) ↔
    ∃ (q r : Packed (Fin n) arity Gamma),InUniverse symbols S q.2 ∧ RootInstance n arity symbols S (tableAbove table) Gamma q r ∧
      packedNumber q=source ∧ packedNumber r=target

def ActualNumericRootSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (source target certificate : Nat),
  numericRootTest n arity symbols S Gamma table source target certificate=true →
    ∃ (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),InUniverse symbols S q ∧ InUniverse symbols S r ∧
      WindowStep (Fin n) arity symbols S (tableAbove table) Gamma tau q r ∧
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)=source ∧ packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)=target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootTargets
