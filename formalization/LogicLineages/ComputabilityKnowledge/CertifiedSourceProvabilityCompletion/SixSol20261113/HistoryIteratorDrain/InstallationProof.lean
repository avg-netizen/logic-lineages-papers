module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.InstallationProof
open GorbowPRProgram GorbowPRRegistry HistoryAppend

theorem dropOccurs : Occurs ⟨2,HistoryLookup.drop⟩ HistoryAppend.append := by
  have hl : Occurs ⟨2,HistoryLookup.drop⟩ HistoryLookup.lookup :=
    .compositionArgument HistoryLookup.reference (fun _ : Fin 1 => HistoryLookup.drop) 0 (.here _ rfl)
  have hr : Occurs ⟨2,HistoryLookup.drop⟩ HistoryAppend.reference :=
    .compositionFunction HistoryLookup.lookup referenceArguments hl
  have hrec : Occurs ⟨2,HistoryLookup.drop⟩ recursiveResult :=
    .compositionArgument HistoryCodec.predecessor (fun _ : Fin 1 => HistoryAppend.reference) 0 hr
  have hv : Occurs ⟨2,HistoryLookup.drop⟩ value :=
    .compositionArgument HistoryCodec.cons valueArguments 1 hrec
  have hs : Occurs ⟨2,HistoryLookup.drop⟩ tableStep :=
    .compositionArgument HistoryCodec.cons tableStepArguments 0 hv
  have ht : Occurs ⟨2,HistoryLookup.drop⟩ table := .recursionStep tableBase tableStep hs
  exact .compositionArgument HistoryLookup.head (fun _ : Fin 1 => table) 0 ht

theorem dropOffset : ∃ offset : Nat,
    (nodes HistoryAppend.append)[offset]? = some (⟨2,HistoryLookup.drop⟩ : Packed) := by
  obtain ⟨offset,_,he⟩ := (GorbowPRRegistry.Proof.taggedCoverage 2 HistoryAppend.append
    ⟨2,HistoryLookup.drop⟩).mp dropOccurs
  exact ⟨offset,he⟩

theorem rightInstalled {n : Nat} (p : Program n) (tag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.kernel v l a x⟩) :
    (nodes p)[tag+GorbowPRChildTags.argumentTag HistoryCodec.select
      (HistoryKernel.TransitionEquationsProof.kernelArguments v l a x) 0+1]? = some ⟨1,HistoryDecoder.decoder true⟩ := by
  have hs := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select
    (HistoryKernel.TransitionEquationsProof.kernelArguments v l a x) ht 0
  exact SixSol20261112.Fuel.Equations.functionChild p _ (HistoryDecoder.decoder true)
    (fun _ : Fin 1 => .projection (0 : Fin 3)) hs
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.InstallationProof
