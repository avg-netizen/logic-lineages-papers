module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original admitted job geometry and actual operational counters suffice.
No selector correctness, result value, framed return, per-child semantic value,
or native calibration is supplied. The produced row has only its actual length. -/
def ActualUniformReturn : Prop := ∀ (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (job role typ typed rawJob raw parameter gamma c children deletions counts payload frame produced : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add children deletions) produced)) →
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTargets
