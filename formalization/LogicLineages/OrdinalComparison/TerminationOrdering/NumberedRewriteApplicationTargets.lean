module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

def ActualBindingRetraction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (sigma : NumberedRewriteSyntax.Substitution Symbol arity Delta Gamma),
    (∀ (upsilon : Ty) (v : Variable Gamma upsilon),sigma (rho v)=AuxTerm.var v) →
    ∀ (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    NumberedRewriteSyntax.substitute (NumberedRewriteSyntax.rename q rho) sigma=q

def ActualWeakeningCancellation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (sigma tau : Ty) (q : AuxTerm Symbol arity Gamma tau) (a : AuxTerm Symbol arity Gamma sigma),
    NumberedRewriteSyntax.substitute (NumberedRewriteSyntax.rename q (Renaming.weaken Gamma sigma)) (singleSubstitution a)=q

def ActualOpenNumberedBeta : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (sigma tau : Ty)
    (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (a : AuxTerm Symbol arity Gamma sigma),
    RawStep Symbol arity above Gamma tau (.app (.lam (openNumbered n f sigma tau base extraTypes extras)) a)
      (.numbered n f tau base (extraTypes++[sigma]) (NumberedRewriteSyntax.appendArguments extras (.cons a .nil)))

/-- Literal WHOLE tuple path for a finite-numbered FUNCTIONAL source.
The supplied length is paid exactly in the initial label. No transitivity of
the original comparison or reassociation of original special application. -/
def ActualNumberedWholeTuple : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (tau : Ty)
    (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes)
    (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    RawSteps Symbol arity above Gamma tau
      (NumberedRewriteReduction.applyArguments (.numbered (n+types.length) f (arrows types tau) base extraTypes extras) args)
      (.numbered n f tau base (extraTypes++types) (NumberedRewriteSyntax.appendArguments extras args))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationTargets
