module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorPrimaryMeasuresProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorSignaturesTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability

/-- Native source equivalence only. Child codes are the established native
least-code representatives; this is not an internal arithmetic inverse. -/
def OrdinaryIff : Prop :=
 ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
 SubtypeClosed (fun t => t ∈ S) →
 ∀ (f g : Head (Fin n))
 (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
 (target : AuxArguments (Fin n) arity Gamma (headArguments arity g)),
 InUniverse symbols S (.ordinary f base) → InUniverse symbols S (.ordinary g target) →
 (WindowPrimary (Fin n) arity symbols S Gamma ⟨headResult f,.ordinary f base⟩ ⟨headResult g,.ordinary g target⟩ ↔
  RecursiveComparison.headClass f = RecursiveComparison.headClass g ∧
  headResult f = headResult g ∧ (argumentCodes symbols S base).Perm (argumentCodes symbols S target))

def NumberedIff : Prop :=
 ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
 SubtypeClosed (fun t => t ∈ S) →
 ∀ (k l : Nat) (f g : Head (Fin n)) (tau upsilon : Ty)
 (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
 (target : AuxArguments (Fin n) arity Gamma (headArguments arity g))
 (types otherTypes : List Ty)
 (extras : AuxArguments (Fin n) arity Gamma types)
 (otherExtras : AuxArguments (Fin n) arity Gamma otherTypes),
 InUniverse symbols S (.numbered k f tau base types extras) →
 InUniverse symbols S (.numbered l g upsilon target otherTypes otherExtras) →
 (WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩
   ⟨upsilon,.numbered l g upsilon target otherTypes otherExtras⟩ ↔
  k=l ∧ tau=upsilon ∧ RecursiveComparison.headClass f = RecursiveComparison.headClass g ∧
  (argumentCodes symbols S base).Perm (argumentCodes symbols S target) ∧
  argumentCodes symbols S extras = argumentCodes symbols S otherExtras)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryConstructorSignaturesTargets
