module
public import LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputs
open ArbitraryHeadSharedWire (Valuation headCode)
open ArbitraryHeadFreshWireAllocation (Wire OriginalConjunction allocate maximum)
open ArbitraryHeadWireList (NormalizedAt Agrees extend)

/-- Each source is already available, and the output is one new name.
This allows any number of gates to share an already available source. -/
def Topological : List Nat → List Wire → Prop
  | _, [] => True
  | known, w :: ws =>
      w.source ∈ known ∧ w.output ∉ known ∧ Topological (w.output :: known) ws

def outputs (wires : List Wire) : List Nat := wires.map Wire.output

def LeavesExternal (wires : List Wire) (base final : Valuation) : Prop :=
  ∀ n : Nat, n ∉ outputs wires → final n = base n

noncomputable def reader (f : Nat → Nat) (w : Wire) (state : Valuation) : Option Nat :=
  ArbitraryFixedHeadCollapse.read f (headCode w.head,state w.source)

/-- Calls the original raw reader at the exact original source name.
Failure stops immediately; on success only the original output is written. -/
noncomputable def run (f : Nat → Nat) (state : Valuation) : List Wire → Option Valuation
  | [] => some state
  | w :: ws =>
      match reader f w state with
      | none => none
      | some value => run f (Function.update state w.output value) ws

def ExactSequentialOutputs : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (wires : List Wire), Topological known wires →
    ∀ base final : Valuation,
      run f base wires = some final ↔ OriginalConjunction f final wires ∧ LeavesExternal wires base final

def ExactFailureAndUniqueOutputs : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (wires : List Wire), Topological known wires →
    ∀ base : Valuation,
      (run f base wires = none ↔
        ¬ ∃ final : Valuation, OriginalConjunction f final wires ∧ LeavesExternal wires base final) ∧
      (run f base wires ≠ none ↔
        ∃! final : Valuation, OriginalConjunction f final wires ∧ LeavesExternal wires base final) ∧
      ∀ final : Valuation, run f base wires = some final → ∀ n ∈ known, final n = base n

/-- Original outputs are discovered first. The second stage adds only
the canonical hidden coordinates, without changing any actual original
wire name (and in fact any name up to the original maximum). -/
def ExactCanonicalHiddenAfterOutputs : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (wires : List Wire), Topological known wires →
    ∀ base final : Valuation,
      (run f base wires = some final ↔ LeavesExternal wires base final ∧
        ∃! lifted : Valuation, NormalizedAt f lifted (allocate wires) ∧ Agrees (allocate wires) final lifted) ∧
      (run f base wires = some final →
        let lifted := extend final (allocate wires)
        NormalizedAt f lifted (allocate wires) ∧ Agrees (allocate wires) final lifted ∧
          ∀ n : Nat, n ≤ maximum wires → lifted n = final n)

def FullArbitraryHeadSequentialOutputs : Prop :=
  ExactSequentialOutputs ∧ ExactFailureAndUniqueOutputs ∧ ExactCanonicalHiddenAfterOutputs

end LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputs
