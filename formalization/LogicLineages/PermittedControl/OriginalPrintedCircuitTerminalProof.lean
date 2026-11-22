module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitTerminalTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialProof
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitTerminal
open OriginalPrintedCircuitSequential (run exactPrintedCircuitRun)
open OriginalMixedTerminalTest (exactTerminalTestRead)

theorem exactPrintedCircuitTerminal : ExactPrintedCircuitTerminal := by
  intro f known gates top base p admitted
  constructor
  · intro why
    cases h : run f base gates <;> simp [observe,h]
  · intro positive
    constructor
    · intro h
      cases rr : run f base gates with
      | error why => simp [observe,rr] at h
      | ok final =>
          have answered : p.answer final = positive :=
            Except.ok.inj (by simpa only [observe,rr] using h)
          obtain ⟨graphs,outside⟩ := (exactPrintedCircuitRun f known gates top base final).mp rr
          exact ⟨final,graphs,outside,(exactTerminalTestRead p admitted final positive).mp answered⟩
    · rintro ⟨final,graphs,outside,checked⟩
      have ok := (exactPrintedCircuitRun f known gates top base final).mpr ⟨graphs,outside⟩
      have answered := (exactTerminalTestRead p admitted final positive).mpr checked
      simp only [observe,ok,answered]

end LogicLineages.PermittedControl.OriginalPrintedCircuitTerminal
