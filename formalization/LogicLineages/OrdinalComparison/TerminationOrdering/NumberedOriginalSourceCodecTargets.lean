module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecTargets
open Source NumberedRewriteSyntax NumberedOriginalSourceCodec

def ActualProjectionRoundTrip : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (tau : Ty) (s : Term Symbol arity Gamma tau),project (translateOriginal s)=some s

def ActualProjectionSound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau) (s : Term Symbol arity Gamma tau),
    project q=some s → translateOriginal s=q

def ActualArgumentProjectionRoundTrip : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma types : List Ty) (args : OriginalArguments Symbol arity Gamma types),
    projectArguments (translateArguments args)=some args

def ActualProjectionImage : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    (project q).isSome=true ↔ ∃ s : Term Symbol arity Gamma tau,q=translateOriginal s

def ActualNumericRoundTrip : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (tau : Ty) (s : Term (Fin n) arity Gamma tau),
    decodeSourceNumber n arity Gamma tau (sourceNumber s)=some s

def ActualNumericSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (tau : Ty) (value : Nat) (s : Term (Fin n) arity Gamma tau),
    decodeSourceNumber n arity Gamma tau value=some s → sourceNumber s=value

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecTargets
