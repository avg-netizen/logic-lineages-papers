module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def Consumer (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (R : Program 2)
 (input rest : OTerm alpha) (psi : Formula alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (output newResults : OTerm beta),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing output (rest.relabel j) newResults)) →
 Nonempty (Derivation body Theta (graph1 (OriginalHereditaryCombinedStep.step R) output (input.relabel j))) →
 Nonempty (Derivation body Theta (psi.relabel j))
/-- Actual admissibility ensures a supported RETURN branch. Counts/results may
be arbitrary numeric values: only agenda pop is claimed, not result semantics,
correct stack partition, evaluator termination, or a native typing reflection. -/
def ActualReturn : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload parent counts role typed typ rawJob raw parameter c gamma : OTerm alpha)
 (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent role typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)) →
 Consumer body Delta R input rest psi → Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnTargets
