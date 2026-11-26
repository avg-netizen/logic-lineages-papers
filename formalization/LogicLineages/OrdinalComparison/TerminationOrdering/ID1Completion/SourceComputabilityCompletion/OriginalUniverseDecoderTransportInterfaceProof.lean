module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfacesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInterfaceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Consume the completed internal induction statement at the public shift
interface, retaining the same insertion type although shift ignores it. This
is an induction interface only, not the still-pending all-raw induction. -/
theorem weakeningAt (H : Program 1) (M W : Program 2) (arguments : Bool)
    (d cutoff gamma extended typ raw shifted c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw H M W false raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftRaw shifted cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W arguments typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H M W arguments typ shifted extended c)) := by
  obtain ⟨hf⟩ := (OriginalRawSyntaxTransportInternalInterfacesProof.actualRawSyntaxInternalInterfaces
    body alpha Delta shifted d cutoff raw).1
  obtain ⟨hs⟩ := hs
  have hfold : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted d cutoff raw)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hf) hs⟩
  exact atRawApply H M W false arguments raw d cutoff gamma extended typ shifted c h hi hfold ha

/-- Erasure uses its literal ternary fold and the reversed source/target
contexts. No comparison of the two raw codes is introduced. -/
theorem erasureAt (H : Program 1) (M W : Program 2) (arguments : Bool)
    (d cutoff gamma extended typ raw erased c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw H M W true raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (he : Nonempty (Derivation body Delta (graph3 eraseRaw erased d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W arguments typ raw extended c))) :
    Nonempty (Derivation body Delta (Accepted H M W arguments typ erased gamma c)) :=
  atRawApply H M W true arguments raw d cutoff gamma extended typ erased c h hi he ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInterfaceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInterfaceProof
