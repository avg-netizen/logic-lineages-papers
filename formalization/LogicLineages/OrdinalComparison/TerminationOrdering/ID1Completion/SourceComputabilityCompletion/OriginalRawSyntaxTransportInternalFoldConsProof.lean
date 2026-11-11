module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBinaryRebuildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConsProof
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

theorem consForward (mode : Mode) (raw out d k tau head tail headOut tailOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph3 consConstructor raw tau head tail)))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) headOut d k head)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) tailOut d k tail)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (BinaryResult mode consConstructor out tau headOut tailOut)) :=
  consRebuildForward mode raw out tau head tail headOut tailOut hc
    (binaryForward mode d k raw head tail headOut tailOut out (consFields raw tau head tail hc) hfirst hsecond ho)

theorem consBackward (mode : Mode) (raw out d k tau head tail headOut tailOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph3 consConstructor raw tau head tail)))
    (hfirst : Nonempty (Derivation positive Delta (graph3 (fold mode) headOut d k head)))
    (hsecond : Nonempty (Derivation positive Delta (graph3 (fold mode) tailOut d k tail)))
    (ho : Nonempty (Derivation positive Delta (BinaryResult mode consConstructor out tau headOut tailOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  binaryBackward mode d k raw head tail headOut tailOut out (consFields raw tau head tail hc) hfirst hsecond
    (consRebuildBackward mode raw out tau head tail headOut tailOut hc ho)

theorem actualRawSyntaxInternalCons : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalCons := by
  intro positive mode alpha Delta raw out d k tau head tail headOut tailOut
  let C := graph3 consConstructor raw tau head tail ⊓ (graph3 (fold mode) headOut d k head ⊓ graph3 (fold mode) tailOut d k tail)
  let G := graph3 (fold mode) out d k raw
  let R := BinaryResult mode consConstructor out tau headOut tailOut
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := consForward mode raw out d k tau head tail headOut tailOut
    (andLeft hcG) (andLeft (andRight hcG)) (andRight (andRight hcG)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := consBackward mode raw out d k tau head tail headOut tailOut
    (andLeft hcR) (andLeft (andRight hcR)) (andRight (andRight hcR)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConsProof
