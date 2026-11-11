module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorUnaryRebuildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
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

theorem ordinaryForward (mode : Mode) (raw out d k head base baseOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph2 ordinaryConstructor raw head base)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (fold mode) baseOut d k base)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (UnaryResult mode ordinaryConstructor out head baseOut)) :=
  ordinaryRebuildForward mode raw out head base baseOut z hc
    (unaryForward mode d k raw base k baseOut out (ordinaryFields raw k head base hc) hchild ho)

theorem ordinaryBackward (mode : Mode) (raw out d k head base baseOut : OTerm alpha)
    (hc : Nonempty (Derivation positive Delta (graph2 ordinaryConstructor raw head base)))
    (hchild : Nonempty (Derivation positive Delta (graph3 (fold mode) baseOut d k base)))
    (ho : Nonempty (Derivation positive Delta (UnaryResult mode ordinaryConstructor out head baseOut))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  unaryBackward mode d k raw base k baseOut out (ordinaryFields raw k head base hc) hchild
    (ordinaryRebuildBackward mode raw out head base baseOut z hc ho)

theorem actualRawSyntaxInternalOrdinary : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalOrdinary := by
  intro positive mode alpha Delta raw out d k head base baseOut
  let C := graph2 ordinaryConstructor raw head base ⊓ graph3 (fold mode) baseOut d k base
  let G := graph3 (fold mode) out d k raw
  let R := UnaryResult mode ordinaryConstructor out head baseOut
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := ordinaryForward mode raw out d k head base baseOut
    (andLeft hcG) (andRight hcG) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := ordinaryBackward mode raw out d k head base baseOut
    (andLeft hcR) (andRight hcR) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
