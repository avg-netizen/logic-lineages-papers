module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTracesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowApplicationTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedWindowTraces

def ActualOpenNumberedBeta : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (sigma tau : Ty)
    (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (a : AuxTerm Symbol arity Gamma sigma),
    WindowStep Symbol arity symbols S above Gamma tau (.app (.lam (openNumbered n f sigma tau base extraTypes extras)) a)
      (.numbered n f tau base (extraTypes++[sigma]) (NumberedRewriteSyntax.appendArguments extras (.cons a .nil)))

def ActualCompleteFunctionContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma types : List Ty) (tau : Ty) (n : Nat)
    (q r : AuxTerm Symbol arity Gamma (arrows types tau)) (args : AuxArguments Symbol arity Gamma types),
    WindowTypedTrace Symbol arity symbols S above Gamma (arrows types tau) n q r →
    WindowTypedTrace Symbol arity symbols S above Gamma tau n
      (NumberedRewriteReduction.applyArguments q args) (NumberedRewriteReduction.applyArguments r args)

def ActualNumberedWholeTuple : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (tau : Ty)
    (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes)
    (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    WindowTypedTrace Symbol arity symbols S above Gamma tau (2*types.length)
      (NumberedRewriteReduction.applyArguments (.numbered (n+types.length) f (arrows types tau) base extraTypes extras) args)
      (.numbered n f tau base (extraTypes++types) (NumberedRewriteSyntax.appendArguments extras args))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowApplicationTargets
