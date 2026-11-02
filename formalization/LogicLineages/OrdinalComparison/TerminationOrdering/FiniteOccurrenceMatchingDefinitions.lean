module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccessProof
public import Mathlib.Data.List.Permutation

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatching
open Source Source.SourceOpenedObservations FiniteObservationBits TypedExtraDownsets TypedObservationAccess

/-- All occurrence-preserving permutations and all prefix/suffix cuts, including endpoints. -/
def splits {α : Type} (xs : List α) : List (List α × List α) :=
  xs.permutations.flatMap fun ys => (List.range (ys.length+1)).map fun k => (ys.take k,ys.drop k)

def orderedTest {α β : Type} (W : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | x::xs, y::ys => W x y && orderedTest W xs ys
  | _, _ => false

def weakTest {α β : Type} (W : α → β → Bool) (xs : List α) (ys : List β) : Bool :=
  ys.permutations.any fun zs => orderedTest W xs zs

def replacementTest {α β : Type} (S : α → β → Bool) (removed : List α) (inserted : List β) : Bool :=
  inserted.all fun t => removed.any fun s => S s t

def strictTest {α β : Type} (W S : α → β → Bool) (xs : List α) (ys : List β) : Bool :=
  (splits xs).any fun src => (splits ys).any fun tgt =>
    !src.2.isEmpty && orderedTest W src.1 tgt.1 && replacementTest S src.2 tgt.2

def pairBit {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (strict : Bool) (p : Packed I P) (o : Observation Symbol arity I.context (budget I)) : Bool :=
  readBit strict p.2 o

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatching
