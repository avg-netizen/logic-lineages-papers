module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedStepContexts NumberedTypedFocus

def ActualTermFocusReconstruction : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (path : List Position)
    (Gamma : List Ty) (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau) (result : TermFocus n arity Gamma tau),
  focus path q=some result → plug result.context result.value=q

def ActualArgumentFocusReconstruction : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (path : List Position) (index : Nat)
    (Gamma types : List Ty) (args : AuxArguments (Fin n) arity Gamma types) (result : ArgumentFocus n arity Gamma types),
  focusArguments path index args=some result → plugArguments result.context result.value=args

def ActualTermFocusCoverage : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (holeGamma : List Ty) (holeType : Ty)
    (Gamma : List Ty) (tau : Ty) (context : TermContext n arity holeGamma holeType Gamma tau) (q : AuxTerm (Fin n) arity holeGamma holeType),
  ∃ path,focus path (plug context q)=some (⟨holeGamma,holeType,context,q⟩ : TermFocus n arity Gamma tau)

def ActualArgumentFocusCoverage : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (holeGamma : List Ty) (holeType : Ty)
    (Gamma types : List Ty) (context : ArgumentContext n arity holeGamma holeType Gamma types) (q : AuxTerm (Fin n) arity holeGamma holeType),
  ∃ path index,focusArguments path index (plugArguments context q)=some (⟨holeGamma,holeType,context,q⟩ : ArgumentFocus n arity Gamma types)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusTargets
