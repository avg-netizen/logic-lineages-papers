module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening PrefixSourceComposition

/-- Literal full original-spine source-substitution converse with the EXACT
prefix-copy escape. Substitution can expose a consumed original variable;
such an output is paid by actual Sharp, never silently treated as currying. -/
def ActualGuardedSourceComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Xi : List Ty) (f : Head Symbol)
    (base : Arguments Symbol arity Xi (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Xi extraTypes) (sigma tau : Ty) (types : List Ty)
    (q : MarkedTerm Symbol arity Gamma sigma)
    (theta : MarkedSubstitution Symbol arity Gamma Delta) (env : MarkedSubstitution Symbol arity Delta Xi)
    (args : Arguments Symbol arity Xi types),
  (∀ upsilon (v : Variable Gamma upsilon),PrefixImage f base extras (substituteTerm (theta v) env)) →
  SourceExtendedComparison.PrefixCopies f base extras args →
  ∀ (suffix : sigma=arrows types tau) (r : MarkedTerm Symbol arity Xi tau),
  applyOriginalWith (substituteTerm q theta) env args suffix=some r →
    applyOriginalWith q (fun v => substituteTerm (theta v) env) args suffix=some r ∨
      Sharp Symbol arity Xi (.marked f tau base extraTypes extras) r

end LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionTargets
