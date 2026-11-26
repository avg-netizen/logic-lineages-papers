module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.SourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.BooleanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114.HeadWindowBooleanRange
open ProgramRangeProof
open OriginalTypedDecoder
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem finishedRange : Ranged finished :=
  branchRange _ _ _ (constantRange 1 0)
    (branchRange _ _ _ (constantRange 1 0) (constantRange 1 1))

theorem packedRange (H : Program 1) : Ranged (packedCheck H) :=
  compositionRange _ _ (compositionRange _ _ finishedRange)

theorem packedNonzero (H : Program 1) (candidate gamma value : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (packedCheck H) value candidate gamma)))
    (hn : Nonempty (Derivation body Delta (eqn value (numeral 0)).not)) :
    Nonempty (Derivation body Delta (graph2 (packedCheck H) (numeral 1) candidate gamma)) := by
  have he := SourceProof.nonzeroOne value (packedRange H body alpha Delta value ![candidate,gamma] hv) hn
  exact outputTransport (packedCheck H) value (numeral 1) ![candidate,gamma] he hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.BooleanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.BooleanProof
