module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatchingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatchingTargets
open Source Source.SourceOpenedObservations FiniteObservationBits TypedExtraDownsets TypedObservationAccess FiniteOccurrenceMatching

def SplitCalibration : Prop := ∀ (α : Type) (xs kept removed : List α), (kept,removed) ∈ splits xs ↔ xs.Perm (kept++removed)

def OrderedCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (xs : List (Packed I P)) (ys : List (Observation Symbol arity I.context (budget I))), orderedTest (pairBit false) xs ys=true ↔ List.Forall₂ (fun s t => pairBit false s t=true) xs ys

def WeakCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (xs : List (Packed I P)) (ys : List (Observation Symbol arity I.context (budget I))), weakTest (pairBit false) xs ys=true ↔ ∃ matched,ys.Perm matched ∧ List.Forall₂ (fun s t => pairBit false s t=true) xs matched

def ReplacementCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (xs : List (Packed I P)) (ys : List (Observation Symbol arity I.context (budget I))), replacementTest (pairBit true) xs ys=true ↔ ∀ t ∈ ys,∃ s ∈ xs,pairBit true s t=true

def StrictCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (xs : List (Packed I P)) (ys : List (Observation Symbol arity I.context (budget I))), strictTest (pairBit false) (pairBit true) xs ys=true ↔ ∃ kept removed retained inserted,xs.Perm (kept++removed) ∧ ys.Perm (retained++inserted) ∧ removed≠[] ∧ List.Forall₂ (fun s t => pairBit false s t=true) kept retained ∧ (∀ t ∈ inserted,∃ s ∈ removed,pairBit true s t=true)

def PositiveTests : Prop := ∀ (α β : Type) (W S W' S' : α → β → Bool), (∀ s t,W s t ≤ W' s t) → (∀ s t,S s t ≤ S' s t) → ∀ (xs : List α) (ys : List β), weakTest W xs ys ≤ weakTest W' xs ys ∧ strictTest W S xs ys ≤ strictTest W' S' xs ys

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatchingTargets
