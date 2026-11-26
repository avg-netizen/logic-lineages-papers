module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleLookupTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalInternalJobAdmissible
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal actual annotated expansion lookup. Parent/child geometry exposes
the unchanged original c but allows genuine child-context variation. Neither
child acceptance nor an expansion-preservation supplier is a premise. -/
def ActualLookup : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2)
 (alpha : Type) (Delta : List (Formula alpha))
 (parent role typ typed rawJob raw parameter gamma c
  child childRole childType childTyped childRawJob childRaw childParameter childGamma
  row count index : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent role typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole childTyped)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childTyped childType childRawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childRawJob childRaw childParameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)) →
 Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index row)) →
 Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleLookupTargets
