module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecTargets
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedNumericCarrier NumberedRepresentativePrimrec

/-- The original minimum is bounded without a window-closure or membership premise. -/
def ActualRepresentativeBound : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma),
    representativeCode symbols S q ≤ packedNumber q

/-- Bounded numeric search recovers the unchanged finite-class minimum for every input. -/
def ActualBoundedRepresentativeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma),
    boundedRepresentative symbols S q = representativeCode symbols S q

/-- Joint effectivity in both finite windows and the actual packed term. -/
def ActualRepresentativePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma =>
      representativeCode p.1.1 p.1.2 p.2)

/-- The existing canonical-carrier Boolean is primitive recursive on every natural input. -/
def ActualCanonicalCarrierPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Nat =>
      canonicalCarrierTest n arity p.1.1 p.1.2 Gamma p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecTargets
