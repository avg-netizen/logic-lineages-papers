module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialTargets
public import LogicLineages.PermittedControl.OriginalMixedTerminalTestTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitTerminal
open ArbitraryHeadSharedWire (Valuation)
open OriginalPrintedCircuitSequential (Gate Failure Topological Graphs LeavesExternal run)
open OriginalMixedTerminalTest (Test)

noncomputable def observe (f : Nat → Nat) (base : Valuation) (gates : List Gate)
    (p : Test) : Except Failure Bool :=
  match run f base gates with
  | .error why => .error why
  | .ok final => .ok (p.answer final)

/-- The very same fitted original terminal language observes a successful
full gate run. Only the test polarity varies, not the positive graph. -/
def ExactPrintedCircuitTerminal : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (base : Valuation) (p : Test), p.Admitted →
      (∀ why : Failure, observe f base gates p = .error why ↔ run f base gates = .error why) ∧
      ∀ positive : Bool,
        observe f base gates p = .ok positive ↔
          ∃ final : Valuation, Graphs f final gates ∧ LeavesExternal gates base final ∧
            p.atPolarity positive final

end LogicLineages.PermittedControl.OriginalPrintedCircuitTerminal
