module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexTargets
open Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ONE Program is selected before EVERY raw parameter/window/Gamma.
Calibration covers all five raw inputs, with no Context decode or valid
window premise; the runtime Gamma slice retains the actual raw context. -/
def ActualGlobalRuntimeVertexSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ vertex : Program 5,
    (∀ v : List.Vector Nat 5, evaluate vertex v = RuntimeVertex.value n arity v) ∧
      ∀ parameter : Nat, ∃ Gamma : List Ty,
        ∀ domain codomain argument value : Nat,
        evaluate vertex (List.Vector.ofFn ![parameter,domain,codomain,argument,value]) =
          ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair parameter).1
            domain codomain argument value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexTargets
