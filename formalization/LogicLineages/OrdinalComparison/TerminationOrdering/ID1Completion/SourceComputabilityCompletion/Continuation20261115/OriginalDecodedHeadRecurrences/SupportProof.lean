module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem equalityImp (n : Nat) (numbered : Bool) (source target k l f g tau upsilon base dest ts us extras otherExtras node answers param : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (OriginalGuardedHeadEquality.Targets.constructor numbered source k f tau base ts extras)))
    (ht : Nonempty (Derivation body Delta (OriginalGuardedHeadEquality.Targets.constructor numbered target l g upsilon dest us otherExtras)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hv : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node answers param))) :
    Nonempty (Derivation body Delta
      (((graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g).imp (eqn f g)) ⊓
        ((eqn f g).imp (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g)))) := by
  apply andIntro
  · let A := graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g
    have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := (OriginalGuardedHeadEquality.Proof.guardedEquality n numbered body alpha (A :: Delta)
      source target k l f g tau upsilon base dest ts us extras otherExtras node answers param (withHyp hs A) (withHyp ht A) (withHyp hn A) (withHyp hv A)).mp ha
    exact ⟨Derivation.implicationIntroduction h⟩
  · let A := eqn f g
    have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := (OriginalGuardedHeadEquality.Proof.guardedEquality n numbered body alpha (A :: Delta)
      source target k l f g tau upsilon base dest ts us extras otherExtras node answers param (withHyp hs A) (withHyp ht A) (withHyp hn A) (withHyp hv A)).mpr ha
    exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.SupportProof
