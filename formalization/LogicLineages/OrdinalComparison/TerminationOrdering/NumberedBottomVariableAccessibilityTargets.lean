module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableAccessibilityTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedPrimarySubstitution NumberedBottomVariable NumberedLeastCodeRepresentative NumberedQuotientPaths

/-- A transformed numeric successor is lifted from the requested ORIGINAL
representative, through an existential confined source term. The same S and
subtype closure are used on both sides, and genuine self-edges are retained. -/
def ActualPositiveSuccessorInverse : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta)
      (q : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → BottomOrVariable theta → ∀ y : Nat,
    PositivePath (QuotientEdge n arity symbols S above Delta)
      (representativeCode symbols S (substitutePacked theta q)) y →
    ∃ q' : Packed (Fin n) arity Gamma, InUniverse symbols S q'.2 ∧
      representativeCode symbols S (substitutePacked theta q') = y ∧
      PositivePath (QuotientEdge n arity symbols S above Gamma)
        (representativeCode symbols S q) (representativeCode symbols S q')

/-- The converse direction to ranked substitution accessibility reflection,
for the binder-stable bottom-or-variable class only. -/
def ActualAccessibilityPreservation : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta)
      (q : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → BottomOrVariable theta →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S q) →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Delta) source successor)
      (representativeCode symbols S (substitutePacked theta q))

def ActualEdgeAccessibilityPreservation : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta)
      (q : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → BottomOrVariable theta →
    Acc (fun successor source => QuotientEdge n arity symbols S above Gamma source successor)
      (representativeCode symbols S q) →
    Acc (fun successor source => QuotientEdge n arity symbols S above Delta source successor)
      (representativeCode symbols S (substitutePacked theta q))

/-- No sigma-in-S premise is added: the erased binder's type may be arbitrary. -/
def ActualSingleBottomAccessibilityEquivalence : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
      (q : Packed (Fin n) arity (sigma :: Gamma)), InUniverse symbols S q.2 →
    (Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above (sigma :: Gamma)) source successor)
      (representativeCode symbols S q) ↔
     Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S (substitutePacked (singleSubstitution (.bottom sigma)) q)))

def ActualSingleBottomEdgeAccessibilityEquivalence : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
      (q : Packed (Fin n) arity (sigma :: Gamma)), InUniverse symbols S q.2 →
    (Acc (fun successor source => QuotientEdge n arity symbols S above (sigma :: Gamma) source successor)
      (representativeCode symbols S q) ↔
     Acc (fun successor source => QuotientEdge n arity symbols S above Gamma source successor)
      (representativeCode symbols S (substitutePacked (singleSubstitution (.bottom sigma)) q)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableAccessibilityTargets
