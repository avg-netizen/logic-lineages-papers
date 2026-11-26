module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SuccessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andLeft)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem accepted (n : Nat) (arity : Fin n → Nat) (node source target window : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (suc z) source ⊓
       graph1 (OriginalCodeValidityGuard.check n) (suc z) target)) := by
  have hg := OriginalDecodedLambdaRecurrence.SuccessProof.guardNecessary n arity node window he
  have hn := InternalAcceptanceConjunctionProof.conjunctionRecover (OriginalDecodedLayerCalibration.nodeAccepted n)
    (OriginalDecodedLayerCalibration.windowAccepted n) ![node,z,window] hg
  exact OriginalDecodedLayerCalibration.InternalProof.nodeForward n node z window source target hp (andLeft hn)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
