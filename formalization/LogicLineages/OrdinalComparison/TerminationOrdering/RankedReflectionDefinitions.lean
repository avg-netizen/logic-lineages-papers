module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedMultisetNormalizationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflection
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree RankedPathOrder

def OrdinaryComparison {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) : Prop :=
  ∀ a b : Tree Symbol arity Gamma, s=pack a → t=pack b → RankedPathOrder.Weak Symbol arity Gamma above a b

def MarkedComparison {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) : Prop :=
  ∀ (f : Symbol) (args : Fin (arity f) → Tree Symbol arity Gamma) (b : Tree Symbol arity Gamma),
    s=markedRoot f args → t=pack b → Greater Symbol arity Gamma above (.node f args) b

def StrictComparison {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) : Prop :=
  ∀ a b : Tree Symbol arity Gamma, s=pack a → t=pack b → Greater Symbol arity Gamma above a b

def WeakMatching {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts : List (Packed Symbol arity Gamma)) : Prop :=
  ∀ a b : List (Tree Symbol arity Gamma), ss=a.map pack → ts=b.map pack →
    List.Forall₂ (RankedPathOrder.Weak Symbol arity Gamma above) a b

def StrictMatching {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts : List (Packed Symbol arity Gamma)) : Prop :=
  ∀ a b : List (Tree Symbol arity Gamma), ss=a.map pack → ts=b.map pack →
    MultisetGreater Symbol arity Gamma above a b

def Replacements {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts : List (Packed Symbol arity Gamma)) : Prop :=
  ∀ a b : List (Tree Symbol arity Gamma), ss=a.map pack → ts=b.map pack →
    Replacement Symbol arity Gamma above a b

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflection
