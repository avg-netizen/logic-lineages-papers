module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdge
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedNumericStep NumberedQuotientPaths

def edgeCertificateNumber (source target step : Nat) : Nat := Nat.pair source (Nat.pair target step)

def numericEdgeTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y certificate : Nat) : Bool :=
  let source := (Nat.unpair certificate).1
  let target := (Nat.unpair (Nat.unpair certificate).2).1
  let step := (Nat.unpair (Nat.unpair certificate).2).2
  match decodeUniverse n arity symbols S Gamma source,decodePackedNumber n arity Gamma target with
  | some q,some r => numericStepTest n arity symbols S Gamma table source target step &&
      decide (representativeCode symbols S q=x ∧ representativeCode symbols S r=y)
  | _,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdge
