module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationTargets
public import LogicLineages.PermittedControl.OriginalPrintedCircuitTerminalTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminal
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees)
open OriginalPrintedCircuitSequential (Gate Topological LeavesExternal)
open OriginalPrintedCircuitNormalization (entries normalized Holds)
open OriginalMixedTerminalTest (Test testCeiling)
open OriginalPrintedCircuitTerminal (observe)

/-- This protects all original terminal names and every explicitly known
input, including inputs not referenced by an original gate or the test. -/
def exterior (known : List Nat) (p : Test) : Nat := known.foldr max (testCeiling p)

def ExactPrintedNormalizedTerminal : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (base : Valuation) (p : Test), p.Admitted → ∀ positive : Bool,
      observe f base gates p = .ok positive ↔
        ∃ original lifted : Valuation, LeavesExternal gates base original ∧
          Holds f lifted (normalized (exterior known p) gates) ∧
          Agrees (entries (exterior known p) gates) original lifted ∧
          (∀ n ∈ known, lifted n = base n) ∧ p.atPolarity positive lifted

end LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminal
