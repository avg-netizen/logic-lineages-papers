module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.EqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedHeadEqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem equal (n : Nat)
    (left right label f g recorded base dest extraTypes extras otherExtras : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,dest,extraTypes,otherExtras])))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hencoded : Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) f g)))
 :
    Nonempty (Derivation body Delta (eqn f g)) := by
  have hleft := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n left label f recorded base extraTypes extras hlc hlg
  have hright := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n right label g recorded dest extraTypes otherExtras hrc hrg
  have hrelation := OriginalGuardedHeadEquality.EqualityProof.accepted n f g (andLeft hleft) (andLeft hright)
  obtain ⟨himp⟩ := andLeft hrelation
  obtain ⟨hencoded⟩ := hencoded
  exact ⟨Derivation.implicationElimination himp hencoded⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedHeadEqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedHeadEqualityProof
