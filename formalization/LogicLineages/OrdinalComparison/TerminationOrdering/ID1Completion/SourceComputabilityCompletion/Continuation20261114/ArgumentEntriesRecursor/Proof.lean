module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.CalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Proof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)
open RawProof CalibrationProof

theorem originalGraph : Targets.OriginalGraph := by
  intro n seed i param hi
  have hg := ExchangeGraphRecursion.CoherenceProof.nativeCoherentGraph rank dependency layer
    (fun raw _ => raw) (fun raw _ => ArgumentEntriesFrontier.rawChildren raw) layerAt
    (fun raw _ => rawValue raw) rankValue dependencyValue (fun raw vals param => layerValue raw param vals)
    (fun raw _ child hc => ArgumentEntriesFrontier.Proof.rawDecrease raw child hc)
    layerCoherence i (codeNumber seed) param hi
  change evaluate graph (List.Vector.ofFn ![i,codeNumber seed,param]) =
    numbersNumber ((Nat.rec (motive := fun _ => List Nat) [codeNumber seed]
      (fun _ nodes => nodes.flatMap ArgumentEntriesFrontier.rawChildren) (codeNumber seed+1-i)).map
      (fun node => Nat.pair node (rawValue node))) at hg
  rw [ArgumentEntriesFrontier.Proof.frontierImage] at hg
  simpa only [List.map_map,Function.comp_def,valueOnCode] using hg

theorem originalExtraction : Targets.OriginalExtraction := by
  intro n seed param
  have hv := ExchangeSelectedRecursor.NativeProof.nativeFinalValue rank dependency layer
    (fun raw _ => raw) (fun raw _ => ArgumentEntriesFrontier.rawChildren raw) layerAt
    (fun raw _ => rawValue raw) rankValue dependencyValue (fun raw vals param => layerValue raw param vals)
    (fun raw _ child hc => ArgumentEntriesFrontier.Proof.rawDecrease raw child hc)
    layerCoherence (codeNumber seed) param
  exact hv.trans (valueOnCode n seed)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Proof
