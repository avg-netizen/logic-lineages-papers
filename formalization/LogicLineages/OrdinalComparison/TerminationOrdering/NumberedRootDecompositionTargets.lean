module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedDirectCertificate NumberedSelectCertificate NumberedMulCertificate NumberedStepContexts NumberedRootDecomposition

def ActualTermRootDecomposition : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (Gamma : List Ty) (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),
  WindowStep (Fin n) arity symbols S above Gamma tau q r ↔ TermDecomposition symbols S above q r

def ActualArgumentRootDecomposition : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (Gamma types : List Ty) (q r : AuxArguments (Fin n) arity Gamma types),
  WindowArgumentStep (Fin n) arity symbols S above Gamma types q r ↔ ArgumentDecomposition symbols S above q r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionTargets
