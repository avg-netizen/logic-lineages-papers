module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBinaryRebuildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
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
open OriginalRawSyntaxTransportInternalConstructorBinaryRebuildProof

theorem applicationForward (mode : Mode) (raw out d k domain fn arg fnOut argOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph3 applicationConstructor raw domain fn arg)))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) fnOut d k fn)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) argOut d k arg)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (BinaryResult mode applicationConstructor out domain fnOut argOut)) :=
  applicationRebuildForward mode raw out domain fn arg fnOut argOut hc
    (binaryForward mode d k raw fn arg fnOut argOut out (applicationFields raw domain fn arg hc) hfirst hsecond ho)

theorem applicationBackward (mode : Mode) (raw out d k domain fn arg fnOut argOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph3 applicationConstructor raw domain fn arg)))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) fnOut d k fn)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) argOut d k arg)))
    (ho : Nonempty (Derivation positive Delta (BinaryResult mode applicationConstructor out domain fnOut argOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  binaryBackward mode d k raw fn arg fnOut argOut out (applicationFields raw domain fn arg hc) hfirst hsecond
    (applicationRebuildBackward mode raw out domain fn arg fnOut argOut hc ho)

theorem actualRawSyntaxInternalApplication : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalApplication := by
  intro positive mode alpha Delta raw out d k domain fn arg fnOut argOut
  let C := graph3 applicationConstructor raw domain fn arg ⊓ (graph3 (fold mode) fnOut d k fn ⊓ graph3 (fold mode) argOut d k arg)
  let G := graph3 (fold mode) out d k raw
  let R := BinaryResult mode applicationConstructor out domain fnOut argOut
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := applicationForward mode raw out d k domain fn arg fnOut argOut
    (andLeft hcG) (andLeft (andRight hcG)) (andRight (andRight hcG)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := applicationBackward mode raw out d k domain fn arg fnOut argOut
    (andLeft hcR) (andLeft (andRight hcR)) (andRight (andRight hcR)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
