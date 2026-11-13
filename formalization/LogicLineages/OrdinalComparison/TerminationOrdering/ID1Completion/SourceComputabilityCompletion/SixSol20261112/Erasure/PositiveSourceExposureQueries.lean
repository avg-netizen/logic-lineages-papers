module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureQueries
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All eleven original deterministic queries read [f,g,path,Context].
Context is a runtime input. No native witness or graph law is installed. -/
def queries : Fin 11 → Program 4 :=
  let gamma := leftOf (.projection 0)
  let entry := .composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 2)
  let quotient := rightOf entry
  ![gamma,rightOf (.projection 0),rightOf (.projection 1),pairOf (.projection 3) gamma,
    entry,.composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 2),
    leftOf entry,quotient,.composition source (fun _ : Fin 1 => quotient),
    .composition target (fun _ : Fin 1 => quotient),.composition step (fun _ : Fin 1 => quotient)]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureQueries
