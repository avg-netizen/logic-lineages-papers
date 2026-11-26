module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.OccurrenceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.SourceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112

theorem kernelInstalled {n : Nat} (p : Program n) fuelTag
    (v l a : Program 1) (x : Program 3) (bound initial : Program 1) (finalizer : Program 4)
    (ht : (nodes p)[fuelTag]? = some ⟨5,verifier v l a x bound initial finalizer⟩) :
    (nodes p)[SixSol20261112.HistoryMachine.iteratorTag fuelTag (HistoryKernel.kernel v l a x)
      bound initial finalizer + stepTag SixSol20261112.HistoryMachine.iterationBase+1]? =
      some ⟨3,HistoryKernel.kernel v l a x⟩ := by
  have hi := SixSol20261113.HistoryMachine.SourceProof.iteratorInstalled p fuelTag
    (HistoryKernel.kernel v l a x) bound initial finalizer ht
  have hs := Fuel.Equations.recursionStepChild p
    (SixSol20261112.HistoryMachine.iteratorTag fuelTag (HistoryKernel.kernel v l a x) bound initial finalizer)
    SixSol20261112.HistoryMachine.iterationBase
    (SixSol20261112.HistoryMachine.iterationStep (HistoryKernel.kernel v l a x)) hi
  exact Fuel.Equations.functionChild p _ (HistoryKernel.kernel v l a x)
    SixSol20261112.HistoryMachine.iterationArguments hs
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.InstallationProof
