module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparisonDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarkedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparisonTargets
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked

def OriginalEmbedding : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma),RecursiveComparison.Weak Symbol arity above Gamma s t →
    SourceExtendedComparison.Weak Symbol arity above Gamma s t) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma),RecursiveComparison.Strict Symbol arity above Gamma s t →
    SourceExtendedComparison.Strict Symbol arity above Gamma s t) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),RecursiveComparison.WeakMatch Symbol arity above Gamma ss ts →
    SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),RecursiveComparison.StrictMultiset Symbol arity above Gamma ss ts →
    SourceExtendedComparison.StrictMultiset Symbol arity above Gamma ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),RecursiveComparison.ReplacementMatch Symbol arity above Gamma ss ts →
    SourceExtendedComparison.ReplacementMatch Symbol arity above Gamma ss ts)

def OrdinaryEmbedding : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (tau : Ty) (t : Term Symbol arity Gamma tau),Unmarked Symbol arity Gamma (embed t)

def WeakUnmarkedConservativity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (q s t : MarkedTerm Symbol arity Gamma tau),
  Unmarked Symbol arity Gamma t → Sharp Symbol arity Gamma q s →
    SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,s⟩ ⟨tau,t⟩ →
    RecursiveComparison.Weak Symbol arity above Gamma ⟨tau,q⟩ ⟨tau,t⟩

def StrictUnmarkedConservativity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (q s t : MarkedTerm Symbol arity Gamma tau),
  Unmarked Symbol arity Gamma t → Sharp Symbol arity Gamma q s →
    SourceExtendedComparison.Strict Symbol arity above Gamma ⟨tau,s⟩ ⟨tau,t⟩ →
    RecursiveComparison.Strict Symbol arity above Gamma ⟨tau,q⟩ ⟨tau,t⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparisonTargets
