module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowDirectAlgorithm (direct entries Entry)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit)
open NumberedWindowInternalDirectCoreTargets (dCore)

def PositiveFit (r : Program 3) (positive : Nat → Nat → Nat → Bool) : Prop :=
  ∀ dom cert target, evaluate r (dom ::ᵥ cert ::ᵥ target ::ᵥ nil) =
    (positive dom cert target).toNat

/-- One observer, paid on the actual ordered scratch encoding of every list pair. -/
def CountFit (count : Program 2) : Prop :=
  ∀ s t : List Nat, evaluate count (numbersNumber s ::ᵥ numbersNumber t ::ᵥ nil) =
    (decide (s.Perm t)).toNat

def partition (source kept other : Option (List Nat)) : Bool :=
  match source, kept, other with
  | some s, some k, some a => decide (s.Perm (k ++ a))
  | _,_,_ => false

def actualEntries (raw : Nat) : Option (List Entry) := (unpack raw).bind entries

def entryOK (positive : Nat → Nat → Nat → Bool) (removed : List Nat) (e : Entry) : Bool :=
  decide (e.2.1 ∈ removed) && positive e.2.1 e.2.2 e.1

def ExactNumericDCore : Prop :=
  ∀ (scalar : Program 1) (r : Program 3) (count : Program 2)
    (scalarTest : Nat → Bool) (positive : Nat → Nat → Nat → Bool),
    ScalarFit scalar scalarTest → PositiveFit r positive → CountFit count →
    ∀ src cert dst,
      evaluate (dCore scalar r count) (src ::ᵥ cert ::ᵥ dst ::ᵥ nil) =
        (direct scalarTest positive src cert dst).toNat

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
