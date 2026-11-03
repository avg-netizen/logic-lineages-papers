module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPaths
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative

def QuotientEdge (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (Gamma : List Ty) (x y : Nat) : Prop :=
  ∃ (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),
    InUniverse symbols S q ∧ WindowStep (Fin n) arity symbols S above Gamma tau q r ∧
    representativeCode symbols S (⟨tau,q⟩ : Packed (Fin n) arity Gamma)=x ∧
    representativeCode symbols S (⟨tau,r⟩ : Packed (Fin n) arity Gamma)=y

inductive CountedPath (H : Nat → Nat → Prop) : Nat → Nat → Nat → Prop where
  | refl (x : Nat) : CountedPath H 0 x x
  | step {x y} : H x y → CountedPath H 1 x y
  | trans {m n x y z} : CountedPath H m x y → CountedPath H n y z → CountedPath H (m+n) x z

inductive PositivePath (H : Nat → Nat → Prop) : Nat → Nat → Prop where
  | step {x y} : H x y → PositivePath H x y
  | trans {x y z} : PositivePath H x y → PositivePath H y z → PositivePath H x z

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPaths
