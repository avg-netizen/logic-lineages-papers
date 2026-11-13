module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Source-free CPS partition of the actual full annotated expansion and its
actual mapped/reversed result. No admission, semantic-content, canonicality,
completion, preselected partition, or standard-size premise is supplied. -/
def ActualPartition : Prop := ∀ (F : Program 1) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (job role typ typed rawJob raw parameter c gamma children deletions jobs forward produced : OTerm alpha)
 (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)) →
 Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) forward jobs)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (rawJobs annotatedPrefix childRow backwardChildren deletionPrefix : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (ExpansionMapGeometryDefinitions.Geometry F
     (role.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j)
     (children.relabel j) (deletions.relabel j) (produced.relabel j)
     rawJobs annotatedPrefix childRow backwardChildren deletionPrefix)) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryTargets
