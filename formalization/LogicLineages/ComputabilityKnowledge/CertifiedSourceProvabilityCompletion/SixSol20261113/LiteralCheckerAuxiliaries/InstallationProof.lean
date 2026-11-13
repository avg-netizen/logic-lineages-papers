module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.InstallationProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags
open SixSol20261112

theorem coreInstalled {n : Nat} (p : Program n) (tag : Nat) (q0 : Program 5)
    (ht : (nodes p)[tag]? = some ⟨5,Fuel.verifier q0⟩) :
    (nodes p)[SixSol20261112.HistoryMachine.coreCheckerTag tag q0]? = some ⟨5,q0⟩ := by
  have hacc := Fuel.Equations.functionChild p tag (Fuel.accumulator q0) Fuel.outerArguments ht
  have hbase : (nodes p)[tag+2]? = some ⟨4,Fuel.base q0⟩ := by
    have h := GorbowPRSubtree.Proof.lookupTransport n p (tag+1)
      ⟨5,Fuel.accumulator q0⟩ 1 ⟨4,Fuel.base q0⟩ hacc
      (GorbowPRChildTags.Proof.recursionBase 4 (Fuel.base q0) (Fuel.step q0))
    simpa only [Nat.add_assoc] using h
  have hinner := Fuel.Equations.argumentChild p (tag+2) Fuel.isOne
    (fun _ : Fin 1 => Program.composition q0 Fuel.baseArguments) hbase 0
  exact Fuel.Equations.functionChild p _ q0 Fuel.baseArguments hinner
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.InstallationProof
