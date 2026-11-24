module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryAtSharedTapesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport outputTransport valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape ParsedTriplet)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw typedScratch BoundaryReports)
open NumberedWindowInternalDirectBoundaryOpenProof (exact_OpenRawGuards)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem alignTyped (i : Program 1) (raw seen known : OTerm α)
    (seenParser : Nonempty (Derivation B Γ (unary parser (suc seen) raw)))
    (knownParser : Nonempty (Derivation B Γ (unary parser (suc known) raw)))
    (held : Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) seen))) :
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) known)) := by
  obtain ⟨same⟩ := valueUnique parser (suc seen) (suc known) ![raw] seenParser knownParser
  exact headTransport (typedScratch i) (suc z) seen known Fin.elim0 ⟨cancelSuc same⟩ held

private theorem alignRemoved (raw seen known head tail : OTerm α)
    (seenParser : Nonempty (Derivation B Γ (unary parser (suc seen) raw)))
    (knownParser : Nonempty (Derivation B Γ (unary parser (suc known) raw)))
    (held : Nonempty (Derivation B Γ (consGraph seen head tail))) :
    Nonempty (Derivation B Γ (consGraph known head tail)) := by
  obtain ⟨same⟩ := valueUnique parser (suc seen) (suc known) ![raw] seenParser knownParser
  exact outputTransport ID1Completion.InternalListCodec.consCode seen known
    (Fin.cons head (Fin.cons tail Fin.elim0)) ⟨cancelSuc same⟩ held

/-- Align the successful guard's own three chosen payloads with the
already held positive parser reports on the original three raw inputs.
Typing and the removed head/tail remain reports in the same calculus.
There are no independent scratch witnesses in the continuation. -/
theorem exact_OpenBoundaryAtSharedTapes (i : Program 1)
    (src dst removed sourceScratch targetScratch removedScratch : OTerm α)
    (known : ParsedTriplet B Γ src dst removed sourceScratch targetScratch removedScratch)
    (held : Nonempty (Derivation B Γ (programGraph (boundaryRaw i) (suc z) (sourceTape src dst removed))))
    (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (head tail : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (unary (typedScratch i) (suc z) (sourceScratch.relabel j))) →
      Nonempty (Derivation B Δ (unary (typedScratch i) (suc z) (targetScratch.relabel j))) →
      Nonempty (Derivation B Δ (consGraph (removedScratch.relabel j) head tail)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply exact_OpenRawGuards i B α Γ src dst removed goal held
  intro β j Δ ds dt dr head tail keep guard
  have hs := renameParser src sourceScratch known.source j Δ keep
  have ht := renameParser dst targetScratch known.kept j Δ keep
  have hr := renameParser removed removedScratch known.removed j Δ keep
  exact next β j Δ head tail keep
    (alignTyped i (src.relabel j) ds (sourceScratch.relabel j) guard.parsed.source hs guard.sourceTyped)
    (alignTyped i (dst.relabel j) dt (targetScratch.relabel j) guard.parsed.kept ht guard.targetTyped)
    (alignRemoved (removed.relabel j) dr (removedScratch.relabel j) head tail guard.parsed.removed hr guard.removedCons)

#print axioms exact_OpenBoundaryAtSharedTapes
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryAtSharedTapesProof
