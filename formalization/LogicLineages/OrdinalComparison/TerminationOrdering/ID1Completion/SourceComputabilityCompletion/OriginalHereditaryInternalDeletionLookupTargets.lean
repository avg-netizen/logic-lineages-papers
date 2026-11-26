module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion
/-- An actual in-range deletion-row lookup exposes its original context deletion
and raw erasure. No source validity, typedness, or native calibration premise. -/
def ActualLookup : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (raw parameter row count cutoff child : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs row raw parameter)) →
 Nonempty (Derivation body Delta (lengthGraph count row)) →
 Nonempty (Derivation body Delta (Below cutoff count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child cutoff row)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (window gamma typ deleted erased childParameter : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (parameter.relabel j) window gamma)) →
   Nonempty (Derivation body Theta (lengthGraph (count.relabel j) gamma)) →
   Nonempty (Derivation body Theta (Below (cutoff.relabel j) (count.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup typ (cutoff.relabel j) gamma)) →
   Nonempty (Derivation body Theta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted (cutoff.relabel j) gamma)) →
   Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.eraseRaw erased typ (cutoff.relabel j) (raw.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParameter window deleted)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (child.relabel j) erased childParameter)) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupTargets
