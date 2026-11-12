module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobRawCellCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationStoredProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildGeometryTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
def ActualGeometry : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent role typ typed rawJob raw parameter c gamma row count index child : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent role typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index row)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
  (childRole childType childTyped childRawJob childRaw childParameter childGamma : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (child.relabel j) childRole childTyped)) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childTyped childType childRawJob)) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childRawJob childRaw childParameter)) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParameter (c.relabel j) childGamma)) →
  Nonempty (Derivation body Theta (psi.relabel j))) → Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildGeometryTargets
