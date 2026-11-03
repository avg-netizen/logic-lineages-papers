module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMul
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedMultisetNumeric NumberedMulCertificate

def numericMulTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (source target certificate : Nat) : Bool :=
  match decodeUniverse n arity symbols S Gamma source,decodePackedNumber n arity Gamma target,
      decodeCertificate n arity Gamma certificate with
  | some q,some r,some c => mulCertificateTest n arity symbols S Gamma q r c
  | _,_,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMul
