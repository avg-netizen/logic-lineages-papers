module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedMultisetNormalizationTargets
open Source RankedTree RankedPathOrder

def ReplacementMonotone : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (above : Symbol → Symbol → Prop) (removed inserted larger : List (Tree Symbol arity Gamma)),
  (∀ t∈removed,t∈larger) → Replacement Symbol arity Gamma above removed inserted →
    Replacement Symbol arity Gamma above larger inserted

def WeakMatchingNormalization : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (above : Symbol → Symbol → Prop) (ss ts : List (Tree Symbol arity Gamma)),
  List.Forall₂ (RankedPathOrder.Weak Symbol arity Gamma above) ss ts →
    EqualMatch Symbol arity Gamma ss ts ∨ MultisetGreater Symbol arity Gamma above ss ts

def GeneralizedMultisetNormalization : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (above : Symbol → Symbol → Prop) (ss ts kept retained removed inserted : List (Tree Symbol arity Gamma)),
  ss.Perm (kept++removed) → ts.Perm (retained++inserted) → removed≠[] →
  List.Forall₂ (RankedPathOrder.Weak Symbol arity Gamma above) kept retained →
  Replacement Symbol arity Gamma above removed inserted → MultisetGreater Symbol arity Gamma above ss ts

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedMultisetNormalizationTargets
