module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNative
open NumberedMultisetNumeric
/-- A literal finite adjacent swap, retaining its exact numeric prefix. -/
structure Move where
 front : List Nat
 first : Nat
 second : Nat
 tail : List Nat

def Move.source (m : Move) : List Nat := m.front ++ m.first :: m.second :: m.tail
def Move.target (m : Move) : List Nat := m.front ++ m.second :: m.first :: m.tail
def Move.certificate (m : Move) : Nat :=
 Nat.pair (numbersNumber m.front) (Nat.pair m.first (Nat.pair m.second (numbersNumber m.tail)))
def Move.prepend (h : Nat) (m : Move) : Move := { m with front := h :: m.front }
/-- Explicit witness chain, rather than an opaque permutation assertion. -/
inductive Trace : List Nat → List Nat → List Move → Prop where
 | nil (xs) : Trace xs xs []
 | cons (m : Move) {ys ms} : Trace m.target ys ms → Trace m.source ys (m :: ms)
def entries (ms : List Move) : List (Nat × Nat) :=
 ms.map (fun m => (numbersNumber m.target,m.certificate))
def pathCode (ms : List Move) : Nat :=
 numbersNumber ((entries ms).map (fun e => Nat.pair e.1 e.2))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNative
