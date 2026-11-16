module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectNilProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andIntro)
open EraseInvariant
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem nil (needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc z needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest))) :
    Nonempty (Derivation body Delta (result z needle bit rest)) := by
  have hbit : Nonempty (Derivation body Delta (eqn z z ⊔ eqn z (suc z))) :=
    ⟨InternalQuotientComparisonProof.orLeft (refl z)⟩
  have hres : Nonempty (Derivation body Delta (result z needle z z)) :=
    andIntro hbit (CountEffectNilProof.unchanged z needle)
  exact EraseOutputProof.transfer z needle z z z acc bit rest
    (EraseValueProof.nil needle) InternalApplicationValidityStackAppendTransitionProof.pairZero hv hp hres
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseNilProof
