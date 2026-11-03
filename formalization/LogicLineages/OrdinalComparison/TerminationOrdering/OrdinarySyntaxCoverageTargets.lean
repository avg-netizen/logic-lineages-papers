module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverageDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverageTargets
open Source Source.SourceMarkedSyntax RecursiveComparison SourceUnmarked OrdinarySyntaxCoverage

def ActualHeadReconstruction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (f : Head Symbol) (args : OrdinaryArguments Symbol arity Gamma (headArguments arity f)),
  embed (buildTerm f args)=MarkedTerm.ordinary f (embedArguments args)

/-- Exact syntax coverage, not a normalization or beta-equivalence claim. -/
def ActualUnmarkedCoverage : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty)
    (q : MarkedTerm Symbol arity Gamma tau),
  Unmarked Symbol arity Gamma q ↔ ∃ t : Term Symbol arity Gamma tau,embed t=q

def ActualWeakTargetSourceWitness : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (s t : Packed Symbol arity Gamma),Weak Symbol arity above Gamma s t →
  ∃ source : Term Symbol arity Gamma t.1,embed source=t.2

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverageTargets
