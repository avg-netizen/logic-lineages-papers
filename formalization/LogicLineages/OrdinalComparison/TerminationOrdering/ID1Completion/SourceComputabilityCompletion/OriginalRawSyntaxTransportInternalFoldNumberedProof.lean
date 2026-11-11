module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorNumberedRebuildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
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
open OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof OriginalRawSyntaxTransportInternalFoldBinaryProof
open OriginalRawSyntaxTransportInternalConstructorNumberedRebuildProof

theorem numberedForward (mode : Mode) (raw out d k label head tau base types extras baseOut extrasOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) baseOut d k base)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) extrasOut d k extras)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (NumberedResult mode out label head tau baseOut types extrasOut)) :=
  numberedRebuildForward mode raw out label head tau base types extras baseOut extrasOut hc
    (binaryForward mode d k raw base extras baseOut extrasOut out (numberedFields raw label head tau base types extras hc) hfirst hsecond ho)

theorem numberedBackward (mode : Mode) (raw out d k label head tau base types extras baseOut extrasOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) baseOut d k base)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) extrasOut d k extras)))
    (ho : Nonempty (Derivation positive Delta (NumberedResult mode out label head tau baseOut types extrasOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  binaryBackward mode d k raw base extras baseOut extrasOut out (numberedFields raw label head tau base types extras hc) hfirst hsecond
    (numberedRebuildBackward mode raw out label head tau base types extras baseOut extrasOut hc ho)

theorem actualRawSyntaxInternalNumbered : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalNumbered := by
  intro positive mode alpha Delta raw out d k label head tau base types extras baseOut extrasOut
  let C := programGraph numberedConstructor raw ![label,head,tau,base,types,extras] ⊓ (graph3 (fold mode) baseOut d k base ⊓ graph3 (fold mode) extrasOut d k extras)
  let G := graph3 (fold mode) out d k raw
  let R := NumberedResult mode out label head tau baseOut types extrasOut
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := numberedForward mode raw out d k label head tau base types extras baseOut extrasOut
    (andLeft hcG) (andLeft (andRight hcG)) (andRight (andRight hcG)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := numberedBackward mode raw out d k label head tau base types extras baseOut extrasOut
    (andLeft hcR) (andLeft (andRight hcR)) (andRight (andRight hcR)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
