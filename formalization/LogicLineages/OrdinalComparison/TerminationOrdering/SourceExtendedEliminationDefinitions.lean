module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparisonTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflectionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedElimination
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked

/-- A typed packed witness of the ACTUAL already-proved Sharp relation. -/
inductive Refines (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :
    Packed Symbol arity Gamma → Packed Symbol arity Gamma → Prop where
  | mk {tau : Ty} (q s : MarkedTerm Symbol arity Gamma tau) : Sharp Symbol arity Gamma q s →
      Refines Symbol arity Gamma ⟨tau,q⟩ ⟨tau,s⟩

def AllUnmarked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (ps : List (Packed Symbol arity Gamma)) : Prop := ∀ p∈ps,Unmarked Symbol arity Gamma p.2

def WeakMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) : Prop :=
  ∀ q : Packed Symbol arity Gamma,Refines Symbol arity Gamma q s → Unmarked Symbol arity Gamma t.2 →
    RecursiveComparison.Weak Symbol arity above Gamma q t

def StrictMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) : Prop :=
  ∀ q : Packed Symbol arity Gamma,Refines Symbol arity Gamma q s → Unmarked Symbol arity Gamma t.2 →
    RecursiveComparison.Strict Symbol arity above Gamma q t

def MatchMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts : List (Packed Symbol arity Gamma)) : Prop :=
  ∀ qs : List (Packed Symbol arity Gamma),List.Forall₂ (Refines Symbol arity Gamma) qs ss → AllUnmarked ts →
    RecursiveComparison.WeakMatch Symbol arity above Gamma qs ts

def MultiMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts : List (Packed Symbol arity Gamma)) : Prop :=
  ∀ qs : List (Packed Symbol arity Gamma),List.Forall₂ (Refines Symbol arity Gamma) qs ss → AllUnmarked ts →
    RecursiveComparison.StrictMultiset Symbol arity above Gamma qs ts

def ReplacementMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts : List (Packed Symbol arity Gamma)) : Prop :=
  ∀ qs : List (Packed Symbol arity Gamma),List.Forall₂ (Refines Symbol arity Gamma) qs ss → AllUnmarked ts →
    RecursiveComparison.ReplacementMatch Symbol arity above Gamma qs ts

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedElimination
