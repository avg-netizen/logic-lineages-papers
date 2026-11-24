module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseKeepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCoordinatesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof (valueUnique outputTransport)
open InternalApplicationValidityStackAppendTransitionProof (pairZero)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseKeepProof (cons)
open NumberedWindowInternalLiteralScratchEraseValueProof (removeValue)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Any open reported state and coordinates agree with a computed state of the
same physical original eraser, by object graph functionality twice. -/
theorem coordinates (raw needle acc bit rest other otherBit otherRest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ha : Nonempty (Derivation body Delta (graph2 state other raw needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing other otherBit otherRest))) :
    Nonempty (Derivation body Delta (eqn bit otherBit ⊓ eqn rest otherRest)) := by
  have he := valueUnique state acc other ![raw,needle] hv ha
  have hpa := outputTransport InternalPairing.pairing acc other ![bit,rest] he hp
  obtain ⟨hb⟩ := valueUnique InternalUnpair.left bit otherBit ![other]
    (pairLeft other bit rest hpa) (pairLeft other otherBit otherRest hap)
  obtain ⟨hr⟩ := valueUnique InternalUnpair.right rest otherRest ![other]
    (pairRight other bit rest hpa) (pairRight other otherBit otherRest hap)
  exact ⟨Derivation.conjunctionIntroduction hb hr⟩

theorem nilCoordinates (needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc z needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest))) :
    Nonempty (Derivation body Delta (eqn bit z ⊓ eqn rest z)) :=
  coordinates z needle acc bit rest z z z hv hp
    (NumberedWindowInternalLiteralScratchEraseValueProof.nil needle) pairZero

/-- On an actual original cons with a matching head and no tail hit, any
reported result must carry the found flag and the same residual tail result. -/
theorem chosenHeadCoordinates (raw head tail needle prior tailRest canonical acc bit rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state prior tail needle)))
    (hpt : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing prior z tailRest)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (hcanonical : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (suc z) tailRest)))
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest))) :
    Nonempty (Derivation body Delta (eqn bit (suc z) ⊓ eqn rest tailRest)) :=
  coordinates raw needle acc bit rest canonical (suc z) tailRest hv hp
    (cons raw head tail needle prior canonical hc ht (removeValue head prior needle tailRest canonical hpt hcanonical he))
    hcanonical

#print axioms coordinates
#print axioms nilCoordinates
#print axioms chosenHeadCoordinates
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCoordinatesProof
