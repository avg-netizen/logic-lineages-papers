module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleDefinitions

@[expose] public section
/-! Genuine original-spine one-way angle simulation. The induction inspects
ORIGINAL q before env acts; an original variable with remaining arguments is
blocked even when its env image is functional. Q is any actual representation
of substituted syntax, not assumed equal to a separately interpreted value.
No source-family append law or unary special-application currying is supplied.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteApplication NumberedOriginalAngle

def ActualGeneralOriginalAngle : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma Delta : List Ty) (sigma : Ty)
    (q : MarkedTerm Symbol arity Gamma sigma) (env : MarkedSubstitution Symbol arity Gamma Delta)
    (types : List Ty) (tau : Ty) (args : Arguments Symbol arity Delta types) (suffix : sigma=arrows types tau)
    (r : MarkedTerm Symbol arity Delta tau),applyOriginalWith q env args suffix=some r →
    ∀ (Q : AuxTerm Symbol arity Delta sigma) (values : AuxArguments Symbol arity Delta types),
    Represents Symbol arity (n+types.length) Delta sigma (substituteTerm q env) Q →
    ArgumentsRepresent Symbol arity (n+types.length) Delta types args values →
    ∃ R,RawSteps Symbol arity above Delta tau
        (NumberedRewriteReduction.applyArguments (transportAux suffix Q) values) R ∧
      Represents Symbol arity n Delta tau r R

def ActualSpecialApplication : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma types : List Ty) (tau : Ty)
    (q : MarkedTerm Symbol arity Gamma (arrows types tau)) (args : Arguments Symbol arity Gamma types)
    (r : MarkedTerm Symbol arity Gamma tau),specialApply q args=some r →
    ∀ (Q : AuxTerm Symbol arity Gamma (arrows types tau)) (values : AuxArguments Symbol arity Gamma types),
    Represents Symbol arity (n+types.length) Gamma (arrows types tau) q Q →
    ArgumentsRepresent Symbol arity (n+types.length) Gamma types args values →
    ∃ R,RawSteps Symbol arity above Gamma tau (NumberedRewriteReduction.applyArguments Q values) R ∧
      Represents Symbol arity n Gamma tau r R

def ActualOrdinaryAngleTranslation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (sigma : Ty)
    (q : Term Symbol arity Gamma sigma) (types : List Ty) (tau : Ty)
    (args : Arguments Symbol arity Gamma types) (suffix : sigma=arrows types tau)
    (r : MarkedTerm Symbol arity Gamma tau),applyOriginalWith (embed q) (fun v => .var v) args suffix=some r →
    ∃ R,RawSteps Symbol arity above Gamma tau
        (NumberedRewriteReduction.applyArguments (transportAux suffix (translateOriginal q))
          (canonicalArguments (n+types.length) args)) R ∧
      Represents Symbol arity n Gamma tau r R

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleTargets
