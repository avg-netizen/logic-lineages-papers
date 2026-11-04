module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaPathsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaPathsTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryShapes
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedQuotientApplication

def ActualPositiveFirstEdge : Prop := ∀ (H : Nat → Nat → Prop) (x y : Nat),
  PositivePath H x y ↔ ∃ z : Nat, H x z ∧ (z = y ∨ PositivePath H z y)

def ActualNonLambdaApplicationPath : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma tau : Ty)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (target : Nat),
    InUniverse symbols S f → InUniverse symbols S a → isLambda f = false →
    PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S (applicationPacked f a)) target →
    target = representativeCode symbols S (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma) ∨
    ∃ g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau), InUniverse symbols S g ∧
      QuotientEdge n arity symbols S above Gamma
        (representativeCode symbols S ⟨.arrow sigma tau,f⟩) (representativeCode symbols S ⟨.arrow sigma tau,g⟩) ∧
      (representativeCode symbols S (applicationPacked g a) = target ∨
       PositivePath (QuotientEdge n arity symbols S above Gamma)
         (representativeCode symbols S (applicationPacked g a)) target)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaPathsTargets
