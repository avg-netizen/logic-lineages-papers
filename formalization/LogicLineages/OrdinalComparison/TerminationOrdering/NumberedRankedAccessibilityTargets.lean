module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedAccessibilityTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedUniverseBindingTargets NumberedPrimarySubstitution NumberedLeastCodeRepresentative NumberedQuotientPaths

/-- Every numeric positive successor of a confined representative has a confined
packed witness at that exact code. No global code substitution map is assumed. -/
def ActualPositiveSuccessorLift : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → ∀ y : Nat,
    PositivePath (QuotientEdge n arity symbols S above Gamma) (representativeCode symbols S q) y →
    ∃ r : Packed (Fin n) arity Gamma, InUniverse symbols S r.2 ∧ representativeCode symbols S r = y ∧
      PositivePath (QuotientEdge n arity symbols S above Gamma)
        (representativeCode symbols S q) (representativeCode symbols S r)

/-- Exact closure orientation, including genuine self-edges. -/
def ActualPositivePathTransGen : Prop := ∀ (H : Nat → Nat → Prop) (x y : Nat),
    PositivePath H x y ↔ Relation.TransGen (fun successor source => H source successor) y x

def ActualPositivePathAccessibilityEquivalence : Prop := ∀ (H : Nat → Nat → Prop) (x : Nat),
    Acc (fun successor source => PositivePath H source successor) x ↔
    Acc (fun successor source => H source successor) x

/-- Full native accessibility reflection under an arbitrary good substitution,
with precisely the original finite window and confined source. -/
def ActualSubstitutionAccessibilityReflection : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta)
      (q : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 →
    GoodSubstitution (fun t => t ∈ S) (HeadInWindow arity symbols S) theta →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Delta) source successor)
      (representativeCode symbols S (substitutePacked theta q)) →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S q)

def ActualSubstitutionEdgeAccessibilityReflection : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta)
      (q : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 →
    GoodSubstitution (fun t => t ∈ S) (HeadInWindow arity symbols S) theta →
    Acc (fun successor source => QuotientEdge n arity symbols S above Delta source successor)
      (representativeCode symbols S (substitutePacked theta q)) →
    Acc (fun successor source => QuotientEdge n arity symbols S above Gamma source successor)
      (representativeCode symbols S q)

/-- The substitution guard itself has no premise that sigma lies in the window:
it is only asked about variables whose types already satisfy K. -/
def ActualSingleBottomGoodSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (K : Ty → Prop) (H : Source.SourceMarkedSyntax.Head Symbol → Prop) (Gamma : List Ty) (sigma : Ty),
    GoodSubstitution K H (singleSubstitution (AuxTerm.bottom sigma : AuxTerm Symbol arity Gamma sigma))

def ActualSingleBottomAccessibilityReflection : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
      (q : Packed (Fin n) arity (sigma :: Gamma)), InUniverse symbols S q.2 →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S (substitutePacked (singleSubstitution (.bottom sigma)) q)) →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above (sigma :: Gamma)) source successor)
      (representativeCode symbols S q)

def ActualSingleBottomEdgeAccessibilityReflection : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
      (q : Packed (Fin n) arity (sigma :: Gamma)), InUniverse symbols S q.2 →
    Acc (fun successor source => QuotientEdge n arity symbols S above Gamma source successor)
      (representativeCode symbols S (substitutePacked (singleSubstitution (.bottom sigma)) q)) →
    Acc (fun successor source => QuotientEdge n arity symbols S above (sigma :: Gamma) source successor)
      (representativeCode symbols S q)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedAccessibilityTargets
