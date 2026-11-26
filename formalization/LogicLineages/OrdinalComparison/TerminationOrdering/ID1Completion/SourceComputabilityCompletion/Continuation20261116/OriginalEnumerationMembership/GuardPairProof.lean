module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 OriginalRawSyntaxTransport
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalControlGraphSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)

theorem pairLiteral (raw tag payload : OTerm alpha) (k : Nat)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k)))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral k) payload)) :=
  headTransport InternalPairing.pairing raw tag (numeral k) (Fin.cons payload Fin.elim0) he hp

theorem tagLiteral (raw tag payload : OTerm alpha) (k : Nat)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k)))) :
    Nonempty (Derivation body Delta (graph1 rawTag (numeral k) raw)) :=
  pairLeft raw (numeral k) payload (pairLiteral raw tag payload k hp he)

theorem nil (raw tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (ht : Nonempty (Derivation body Delta (eqn tag (numeral 6))))
    (hz : Nonempty (Derivation body Delta (eqn payload (numeral 0)))) :
    Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)) := by
  have hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) (numeral 0))) := by
    unfold graph2 programGraph at hp ⊢
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta (OrdinaryArithmetic.graphFormula InternalPairing.pairing)
      raw ![tag,payload] ![numeral 6,numeral 0] _ hp
    intro i
    fin_cases i
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact ht
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact hz
  exact binaryValue InternalPairing.pairing (constant 0 6) (constant 0 0) raw (numeral 6) (numeral 0)
    Fin.elim0 hpair (constantValue 6 Fin.elim0) (constantValue 0 Fin.elim0)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
