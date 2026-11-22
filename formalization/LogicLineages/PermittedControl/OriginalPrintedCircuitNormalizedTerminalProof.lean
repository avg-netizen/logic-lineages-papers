module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminalTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationProtectionProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitTerminalProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialProof
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminal
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees extend)
open OriginalPrintedCircuitNormalization
  (entries exactPrintedProtection exactPrintedNormalizedExtension maxAt maxSeed)
open OriginalPrintedCircuitSequential (exactPrintedCircuitRun exactPrintedCircuitFailureAndUniqueness)
open OriginalPrintedCircuitTerminal (exactPrintedCircuitTerminal)
open OriginalMixedTerminalTest (testCeiling literalTestStable)

theorem exactPrintedNormalizedTerminal : ExactPrintedNormalizedTerminal := by
  intro f known gates top base p hp positive
  let ext := exterior known p
  let aliases := entries ext gates
  have terminal := (exactPrintedCircuitTerminal f known gates top base p hp).2 positive
  have bounds := exactPrintedProtection ext gates
  have same (original lifted : Valuation) (agree : Agrees aliases original lifted) (n : Nat)
      (inside : n ≤ ext) : lifted n = original n :=
    agree n (fun mem => (Nat.not_lt_of_ge (inside.trans bounds.1)) (bounds.2.2 n mem))
  have pass (original lifted : Valuation) (agree : Agrees aliases original lifted) :
      p.atPolarity positive lifted ↔ p.atPolarity positive original := by
    have stable := literalTestStable p original lifted (fun n hn =>
      same original lifted agree n ((maxAt p.names 0 n hn).trans (maxSeed known (testCeiling p))))
    cases positive
    · exact not_congr stable
    · exact stable
  rw [terminal]
  constructor
  · rintro ⟨original,graphs,outside,checked⟩
    let lifted := extend original aliases
    have norm := ((exactPrintedNormalizedExtension f ext gates original).1 lifted).mpr ⟨graphs,rfl⟩
    have ran := (exactPrintedCircuitRun f known gates top base original).mpr ⟨graphs,outside⟩
    have external := (exactPrintedCircuitFailureAndUniqueness f known gates top base).2.2 original ran
    exact ⟨original,lifted,outside,norm.1,norm.2,fun n hn =>
      (same original lifted norm.2 n (maxAt known (testCeiling p) n hn)).trans (external n hn),
      (pass original lifted norm.2).mpr checked⟩
  · rintro ⟨original,lifted,outside,graph,agree,_,checked⟩
    have opened := ((exactPrintedNormalizedExtension f ext gates original).1 lifted).mp ⟨graph,agree⟩
    exact ⟨original,opened.1,outside,(pass original lifted agree).mp checked⟩

end LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminal
