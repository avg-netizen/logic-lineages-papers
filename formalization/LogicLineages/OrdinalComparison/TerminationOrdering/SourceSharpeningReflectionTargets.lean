module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarkedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningInversionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflectionTargets
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked

def UnmarkedIdentity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (tau : Ty) (q u : MarkedTerm Symbol arity Gamma tau),
  Unmarked Symbol arity Gamma u → Sharp Symbol arity Gamma q u → q=u

def MarkabilityReflection : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (tau : Ty) (q u v : MarkedTerm Symbol arity Gamma tau),
  Sharp Symbol arity Gamma q u → strictMark u=some v →
    ∃ r,strictMark q=some r ∧ Sharp Symbol arity Gamma r v

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflectionTargets
