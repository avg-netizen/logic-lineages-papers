module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The literal ordered raw expansion contains exactly its actual constructor
arity plus its actual original context length, including duplicate jobs. -/
def ActualRawExpansionLength : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw parameter window gamma arity deletions jobs : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) arity raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add arity deletions) jobs))
/-- Annotation preserves the exact same operational count. No source decoder,
admissibility, execution, result-stack or semantic-correctness premise is added.
The arity and context length are the literal counters stored by actual visit. -/
def ActualAnnotatedExpansionLength : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (role typ raw parameter window gamma rawJob typed job arity deletions jobs : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) arity raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add arity deletions) jobs))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountTargets
