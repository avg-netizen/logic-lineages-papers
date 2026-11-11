module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParameters
open OriginalRawSyntaxTransportInternalParametersBindingProof
open OriginalRawSyntaxTransportInternalInterfaceSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem shiftInterfaceAt (raw out d k : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw (fold .shift) false raw))) :
    Nonempty (Derivation body Delta
      ((graph3 (fold .shift) out d k raw).iff (graph2 shiftRaw out k raw))) := by
  let A := graph3 (fold .shift) out d k raw
  let B := graph2 shiftRaw out k raw
  have hf := atRawApply (fold .shift) false raw out d k (numeral 0) k (withHyp h A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hf⟩ := zeroFirstBackward (fold .shift) out k raw hf
  have hb := zeroFirstForward (fold .shift) out k raw
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := atRawApply (fold .shift) false raw out (numeral 0) k d k (withHyp h B) hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem rankInterfaceAt (raw out d k : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw (fold .rank) true raw))) :
    Nonempty (Derivation body Delta
      ((graph3 (fold .rank) out d k raw).iff (graph1 variableRankRaw out raw))) := by
  let A := graph3 (fold .rank) out d k raw
  let B := graph1 variableRankRaw out raw
  have hf := atRawApply (fold .rank) true raw out d k (numeral 0) (numeral 0) (withHyp h A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hf⟩ := zeroTwoBackward (fold .rank) out raw hf
  have hb := zeroTwoForward (fold .rank) out raw
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := atRawApply (fold .rank) true raw out (numeral 0) (numeral 0) d k (withHyp h B) hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- Erasure is literally the original ternary fold, with no unused argument. -/
theorem eraseInterface (raw out d k : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((graph3 (fold .erase) out d k raw).iff (graph3 eraseRaw out d k raw))) := by
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceAtProof
