module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorUnaryRebuildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineExpansionProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof OriginalRawSyntaxTransportInternalFoldUnaryProof
open OriginalRawSyntaxTransportInternalConstructorUnaryRebuildProof

theorem lambdaForward (mode : Mode) (raw out d k domain body bodyOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph2 lambdaConstructor raw domain body)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (fold mode) bodyOut d (suc k) body)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (UnaryResult mode lambdaConstructor out domain bodyOut)) :=
  lambdaRebuildForward mode raw out domain body bodyOut z hc
    (unaryForward mode d k raw body (suc k) bodyOut out (lambdaFields raw k domain body hc) hchild ho)

theorem lambdaBackward (mode : Mode) (raw out d k domain body bodyOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph2 lambdaConstructor raw domain body)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (fold mode) bodyOut d (suc k) body)))
    (ho : Nonempty (Derivation positive Delta (UnaryResult mode lambdaConstructor out domain bodyOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  unaryBackward mode d k raw body (suc k) bodyOut out (lambdaFields raw k domain body hc) hchild
    (lambdaRebuildBackward mode raw out domain body bodyOut z hc ho)

theorem actualRawSyntaxInternalLambda : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalLambda := by
  intro positive mode alpha Delta raw out d k domain body bodyOut
  let C := graph2 lambdaConstructor raw domain body ⊓ graph3 (fold mode) bodyOut d (suc k) body
  let G := graph3 (fold mode) out d k raw
  let R := UnaryResult mode lambdaConstructor out domain bodyOut
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := lambdaForward mode raw out d k domain body bodyOut
    (andLeft hcG) (andRight hcG) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := lambdaBackward mode raw out d k domain body bodyOut
    (andLeft hcR) (andRight hcR) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
