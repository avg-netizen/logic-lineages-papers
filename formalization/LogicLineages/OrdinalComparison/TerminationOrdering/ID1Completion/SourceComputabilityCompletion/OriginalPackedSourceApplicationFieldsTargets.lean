module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def ActualFieldsCases : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (H G : Program 1) (M W : Program 2) (packed parameter : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag (numeral 2) packed)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (arrow d e fp ap fn arg : OTerm beta),
   (∀ p ∈ Delta, p.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg (packed.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fn (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) arg (parameter.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) → Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsTargets
