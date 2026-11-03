module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContextsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContextsTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedStepContexts

def ActualTermContextStep : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (holeGamma : List Ty) (holeType : Ty)
    (q r : AuxTerm (Fin n) arity holeGamma holeType),
  WindowStep (Fin n) arity symbols S above holeGamma holeType q r →
    ∀ (Gamma : List Ty) (tau : Ty) (context : TermContext n arity holeGamma holeType Gamma tau),
      WindowStep (Fin n) arity symbols S above Gamma tau (plug context q) (plug context r)

def ActualArgumentContextStep : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (holeGamma : List Ty) (holeType : Ty)
    (q r : AuxTerm (Fin n) arity holeGamma holeType),
  WindowStep (Fin n) arity symbols S above holeGamma holeType q r →
    ∀ (Gamma types : List Ty) (context : ArgumentContext n arity holeGamma holeType Gamma types),
      WindowArgumentStep (Fin n) arity symbols S above Gamma types (plugArguments context q) (plugArguments context r)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContextsTargets
