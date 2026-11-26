module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Targets
open GorbowPRProgram List.Vector
/-- Exact universal calibration of the actual compiler against the independent
original numeric recurrence. No certificate correctness or membership premises. -/
def NativeCompiler : Prop := ∀ n (q : Program n) target (inputs : List.Vector Nat n),
 evaluate (compile q) (target ::ᵥ inputs) = number q target inputs
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Targets
