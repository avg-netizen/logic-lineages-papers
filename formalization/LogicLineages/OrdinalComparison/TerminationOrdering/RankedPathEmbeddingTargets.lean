module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEmbeddingTargets
open Source RankedTree RankedPathOrder

def EqualityEmbedding : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (above : Symbol → Symbol → Prop),
  (∀ (s t : Tree Symbol arity Gamma), Equal Symbol arity Gamma s t →
    RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t)) ∧
  (∀ (ss ts : List (Tree Symbol arity Gamma)), EqualMatch Symbol arity Gamma ss ts →
    RecursiveComparison.WeakMatch Symbol arity above Gamma (ss.map pack) (ts.map pack))

def JointStrictEmbedding : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (above : Symbol → Symbol → Prop),
  (∀ (s t : Tree Symbol arity Gamma), Greater Symbol arity Gamma above s t →
    RecursiveComparison.Strict Symbol arity above Gamma (pack s) (pack t)) ∧
  (∀ (s t : Tree Symbol arity Gamma), RankedPathOrder.Weak Symbol arity Gamma above s t →
    RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t)) ∧
  (∀ (ss ts : List (Tree Symbol arity Gamma)), MultisetGreater Symbol arity Gamma above ss ts →
    RecursiveComparison.StrictMultiset Symbol arity above Gamma (ss.map pack) (ts.map pack)) ∧
  (∀ (ss ts : List (Tree Symbol arity Gamma)), Replacement Symbol arity Gamma above ss ts →
    RecursiveComparison.ReplacementMatch Symbol arity above Gamma (ss.map pack) (ts.map pack))

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEmbeddingTargets
