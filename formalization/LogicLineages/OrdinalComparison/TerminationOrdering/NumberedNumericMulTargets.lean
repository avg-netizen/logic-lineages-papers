module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedMultisetNumeric NumberedMulCertificate NumberedNumericMul

def ActualNumericMulCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (source target : Nat),
  (∃ certificate,numericMulTest n arity symbols S Gamma source target certificate=true) ↔
    ∃ (q r : Packed (Fin n) arity Gamma),InUniverse symbols S q.2 ∧ MulInstance n arity symbols S Gamma q r ∧
      packedNumber q=source ∧ packedNumber r=target

def ActualNumericMulSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (above : Fin n → Fin n → Prop) (source target certificate : Nat),
  numericMulTest n arity symbols S Gamma source target certificate=true →
    ∃ (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),InUniverse symbols S q ∧ InUniverse symbols S r ∧
      WindowStep (Fin n) arity symbols S above Gamma tau q r ∧
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)=source ∧ packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)=target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulTargets
