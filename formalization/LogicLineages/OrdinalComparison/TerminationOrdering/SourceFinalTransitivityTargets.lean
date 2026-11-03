module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComposedPrefixSelectionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivityTargets
open Source RecursiveComparison SourceUnmarked

/-- Genuine composition at an ACTUAL ordinary endpoint, with arbitrary
intermediate marked syntax. The sole precedence premise is its actual
transitivity, already part of the paper's selected strict precedence.
No extended-relation transitivity or reduction-pair field is supplied. -/
def ActualUnmarkedFinalComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop),Transitive above →
  ∀ (Gamma : List Ty) (s t u : Packed Symbol arity Gamma),
  SourceExtendedComparison.Weak Symbol arity above Gamma s t →
  SourceExtendedComparison.Weak Symbol arity above Gamma t u →
  Unmarked Symbol arity Gamma u.2 → RecursiveComparison.Weak Symbol arity above Gamma s u

def ActualOriginalEndpointTransitivity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop),Transitive above →
  ∀ (Gamma : List Ty) (s t u : Packed Symbol arity Gamma),
  RecursiveComparison.Weak Symbol arity above Gamma s t →
  RecursiveComparison.Weak Symbol arity above Gamma t u →
  Unmarked Symbol arity Gamma u.2 → RecursiveComparison.Weak Symbol arity above Gamma s u

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivityTargets
