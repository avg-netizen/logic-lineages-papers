module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfacesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInterfaceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Consume the completed internal induction statement at the public shift
interface, retaining the same insertion type although shift ignores it. This
is an induction interface only, not the still-pending all-raw induction. -/
theorem weakeningAt (H : Program 1) (arguments : Bool)
    (d cutoff gamma extended typ raw shifted : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw H false raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftRaw shifted cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H arguments typ raw gamma))) :
    Nonempty (Derivation body Delta (Accepted H arguments typ shifted extended)) := by
  obtain ⟨hf⟩ := (OriginalRawSyntaxTransportInternalInterfacesProof.actualRawSyntaxInternalInterfaces
    body alpha Delta shifted d cutoff raw).1
  obtain ⟨hs⟩ := hs
  have hfold : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted d cutoff raw)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hf) hs⟩
  exact atRawApply H false arguments raw d cutoff gamma extended typ shifted h hi hfold ha

/-- Erasure uses its literal ternary fold and the reversed source/target
contexts. No comparison of the two raw codes is introduced. -/
theorem erasureAt (H : Program 1) (arguments : Bool)
    (d cutoff gamma extended typ raw erased : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw H true raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (he : Nonempty (Derivation body Delta (graph3 eraseRaw erased d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H arguments typ raw extended))) :
    Nonempty (Derivation body Delta (Accepted H arguments typ erased gamma)) :=
  atRawApply H true arguments raw d cutoff gamma extended typ erased h hi he ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInterfaceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInterfaceProof
