module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication SourceSharpening SourceSharpeningApplication

/-- Literal full original-spine helper transport under actual pointwise Sharp
environments and a FULL ArgumentsSharp tuple. No assumed application callback,
mask irrelevance, unary currying or arbitrary family append equation. -/
def FullOriginalApplication : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (sigma tau : Ty) (types : List Ty)
    (q u : MarkedTerm Symbol arity Gamma sigma), Sharp Symbol arity Gamma q u →
    ∀ (theta eta : MarkedSubstitution Symbol arity Gamma Delta)
      (argsA argsB : Arguments Symbol arity Delta types),
    (∀ upsilon (v : Variable Gamma upsilon),Sharp Symbol arity Delta (theta v) (eta v)) →
    ArgumentsSharp Symbol arity Delta argsA argsB → (h : sigma=arrows types tau) →
    OutputSharp (applyOriginalWith q theta argsA h) (applyOriginalWith u eta argsB h)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationTargets
