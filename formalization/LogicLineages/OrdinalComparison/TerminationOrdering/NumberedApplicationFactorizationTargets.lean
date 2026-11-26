module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientApplication

/-- The original least-code representative fixes an original application when
both original typed children are already their own least-code representatives.
The original window, ambient context, type tags and numbering are unchanged. -/
def ActualCanonicalChildrenApplicationFixed : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∀ (Gamma : List Ty) (sigma tau : Ty)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma),
  InUniverse symbols S f → InUniverse symbols S a →
  representativeCode symbols S ⟨.arrow sigma tau, f⟩ = packedNumber ⟨.arrow sigma tau, f⟩ →
  representativeCode symbols S ⟨sigma, a⟩ = packedNumber ⟨sigma, a⟩ →
  representativeCode symbols S (applicationPacked f a) = packedNumber (applicationPacked f a)

/-- Conversely, a least-code original application has least-code children.
This is a native statement about the actual finite primary classes, not an
internal inference rule or a transition/full-fold fixedness identification. -/
def ActualCanonicalApplicationChildrenFixed : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∀ (Gamma : List Ty) (sigma tau : Ty)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma),
  InUniverse symbols S f → InUniverse symbols S a →
  representativeCode symbols S (applicationPacked f a) = packedNumber (applicationPacked f a) →
  representativeCode symbols S ⟨.arrow sigma tau, f⟩ = packedNumber ⟨.arrow sigma tau, f⟩ ∧
  representativeCode symbols S ⟨sigma, a⟩ = packedNumber ⟨sigma, a⟩

/-- Exact numeric factorization of the original representative, using the
actual nested Nat.pair application number and the actual packed child codes.
No replacement representative, observer or new canonicality premise appears. -/
def ActualRepresentativeApplicationFactorization : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∀ (Gamma : List Ty) (sigma tau : Ty)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma),
  InUniverse symbols S f → InUniverse symbols S a →
  representativeCode symbols S (applicationPacked f a) =
    Nat.pair (typeNumber tau)
      (Nat.pair 2 (Nat.pair (typeNumber sigma)
        (Nat.pair (Nat.unpair (representativeCode symbols S ⟨.arrow sigma tau, f⟩)).2
          (Nat.unpair (representativeCode symbols S ⟨sigma, a⟩)).2)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationTargets
