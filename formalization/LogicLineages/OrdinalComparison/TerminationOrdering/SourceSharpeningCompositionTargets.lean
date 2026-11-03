module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningSubstitutionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding SourceSharpening

def Transitivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (tau : Ty) (q u v : MarkedTerm Symbol arity Gamma tau),
  Sharp Symbol arity Gamma q u → Sharp Symbol arity Gamma u v → Sharp Symbol arity Gamma q v

def AdditionalExtras : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types moreTypes : List Ty) (extras : Arguments Symbol arity Gamma types) (more : Arguments Symbol arity Gamma moreTypes),
  Sharp Symbol arity Gamma (.marked f tau base (types++moreTypes) (appendArguments extras more))
    (.marked f tau base types extras)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionTargets
