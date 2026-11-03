module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedNumericStep NumberedQuotientPaths NumberedNumericQuotientEdge

def ActualNumericQuotientEdge : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y : Nat),
  (∃ certificate,numericEdgeTest n arity symbols S Gamma table x y certificate=true) ↔
    QuotientEdge n arity symbols S (tableAbove table) Gamma x y

def ActualNumericEdgeCarrier : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (x y certificate : Nat),
  numericEdgeTest n arity symbols S Gamma table x y certificate=true →
    canonicalCarrierTest n arity symbols S Gamma x=true ∧ canonicalCarrierTest n arity symbols S Gamma y=true

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeTargets
