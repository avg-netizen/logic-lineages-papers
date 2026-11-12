module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual packed source and original parameter plus literal annotated-job
pair witnesses; neither the job Program graph nor admissibility is a premise. -/
def Initialization : Prop := ∀ (body : Positive (Fin 1)) (H G : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter typ raw gamma c rawJob typed job : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta
  (graph2 OriginalHereditaryEvaluatorDefinitions.job job packed parameter ⊓
   (graph1 G (numeral 1) c ⊓ Admissible H M W (numeral 0) typ raw gamma c)))
def SupportedReturn : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (role typ raw gamma c tag payload : OTerm alpha),
 Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)) →
 Nonempty (Derivation body Delta (ReturnShape role typ tag))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTargets
