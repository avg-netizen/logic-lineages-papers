module
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Targets

def ExactTerminalTrace : Prop := ∀ k,
  (trace k).1<2 ∧ (∀ bit ∈ (trace k).2,bit<2) ∧ ((trace k).1=0 ↔ k=0)

def ExactReconstruction : Prop := ∀ k,reconstruct (trace k)=SourceAdditionCompletion.binaryDAG k

def UniformPrimitiveRecursive : Prop := Primrec advance ∧ Primrec trace
end LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Targets
