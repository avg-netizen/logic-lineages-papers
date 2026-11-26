module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OccurrenceProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags
open HistoryKernel.TransitionEquationsProof

theorem dispatcherInstalled {n : Nat} (p : Program n) itag (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩) :
 (nodes p)[dispatcherTag (kernelTag itag) v l a x]? = some ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ := by
 have hk := HistoryRunSplice.IdleProof.kernelInstalled p itag v l a x hi
 have hc := checkInstalled p (kernelTag itag) v l a x hk
 exact SixSol20261112.Fuel.Equations.functionChild p _
   (HistoryDispatcher.lineDispatcher v l a x) (HistoryKernel.dispatcherArguments) hc

theorem actualValidityOccurrence : Targets.ActualValidityOccurrence := by
 intro v l a x n p itag hi
 have hd := dispatcherInstalled p itag v l a x hi
 have hw := SixSol20261112.Fuel.Equations.argumentChild p
   (dispatcherTag (kernelTag itag) v l a x) HistoryCodec.select
   (HistoryTopProvenance.dispatcherArguments v l a x) hd 0
 exact SixSol20261112.Fuel.Equations.functionChild p _ v
   (fun _ : Fin 1 => HistoryDispatcher.lineCode) hw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OccurrenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.OccurrenceProof
