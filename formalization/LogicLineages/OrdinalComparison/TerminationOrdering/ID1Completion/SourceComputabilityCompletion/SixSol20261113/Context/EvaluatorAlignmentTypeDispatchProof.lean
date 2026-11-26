module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentBranchesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSourceTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypeDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalTypedDecoderInternalBranchProof (orCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem types (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter tag out lt rt : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag tag left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag tag right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lt left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rt right))) :
 Nonempty (Derivation body Delta (equal lt rt)) := by
 have htags := EvaluatorAlignmentSourceTagsProof.sourceTags H G M W left parameter tag hsl htl
 let A0 := equal tag (numeral 0)
 let A1 := equal tag (numeral 1)
 let A2 := equal tag (numeral 2)
 let A3 := equal tag (numeral 3)
 let A4 := equal tag (numeral 4)
 let A5 := equal tag (numeral 5)
 let B5 := A5
 let B4 := A4 ⊔ B5
 let B3 := A3 ⊔ B4
 let B2 := A2 ⊔ B3
 let B1 := A1 ⊔ B2
 apply orCases htags
 ·
   have he : Nonempty (Derivation body (A0 :: Delta) A0) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have heq := (congrArg (fun f => Nonempty (Derivation body (A0 :: Delta) f)) (equalEqn tag (numeral 0))).mp he
   have htl := outputTransport OriginalRootObservation.tag tag (numeral 0) (![left,parameter]) heq (withHyp htl A0)
   have htr := outputTransport OriginalRootObservation.tag tag (numeral 0) (![right,parameter]) heq (withHyp htr A0)
   exact EvaluatorAlignmentTypesProof.types0 R H G M W left right parameter out lt rt
     (withHyp hsl A0) (withHyp hsr A0) htl htr (withHyp hvl A0) (withHyp hvr A0) (withHyp hyl A0) (withHyp hyr A0)
 ·
   apply orCases (show Nonempty (Derivation body (B1 :: Delta) B1) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   ·
     have he : Nonempty (Derivation body (A1 :: B1 :: Delta) A1) := ⟨Derivation.hypothesis List.mem_cons_self⟩
     have heq := (congrArg (fun f => Nonempty (Derivation body (A1 :: B1 :: Delta) f)) (equalEqn tag (numeral 1))).mp he
     have htl := outputTransport OriginalRootObservation.tag tag (numeral 1) (![left,parameter]) heq (withHyp (withHyp htl B1) A1)
     have htr := outputTransport OriginalRootObservation.tag tag (numeral 1) (![right,parameter]) heq (withHyp (withHyp htr B1) A1)
     exact EvaluatorAlignmentTypesProof.types1 R H G M W left right parameter out lt rt
       (withHyp (withHyp hsl B1) A1) (withHyp (withHyp hsr B1) A1) htl htr (withHyp (withHyp hvl B1) A1) (withHyp (withHyp hvr B1) A1) (withHyp (withHyp hyl B1) A1) (withHyp (withHyp hyr B1) A1)
   ·
     apply orCases (show Nonempty (Derivation body (B2 :: B1 :: Delta) B2) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
     ·
       have he : Nonempty (Derivation body (A2 :: B2 :: B1 :: Delta) A2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
       have heq := (congrArg (fun f => Nonempty (Derivation body (A2 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 2))).mp he
       have htl := outputTransport OriginalRootObservation.tag tag (numeral 2) (![left,parameter]) heq (withHyp (withHyp (withHyp htl B1) B2) A2)
       have htr := outputTransport OriginalRootObservation.tag tag (numeral 2) (![right,parameter]) heq (withHyp (withHyp (withHyp htr B1) B2) A2)
       exact EvaluatorAlignmentTypesProof.types2 R H G M W left right parameter out lt rt
         (withHyp (withHyp (withHyp hsl B1) B2) A2) (withHyp (withHyp (withHyp hsr B1) B2) A2) htl htr (withHyp (withHyp (withHyp hvl B1) B2) A2) (withHyp (withHyp (withHyp hvr B1) B2) A2) (withHyp (withHyp (withHyp hyl B1) B2) A2) (withHyp (withHyp (withHyp hyr B1) B2) A2)
     ·
       apply orCases (show Nonempty (Derivation body (B3 :: B2 :: B1 :: Delta) B3) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
       ·
         have he : Nonempty (Derivation body (A3 :: B3 :: B2 :: B1 :: Delta) A3) := ⟨Derivation.hypothesis List.mem_cons_self⟩
         have heq := (congrArg (fun f => Nonempty (Derivation body (A3 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 3))).mp he
         have htl := outputTransport OriginalRootObservation.tag tag (numeral 3) (![left,parameter]) heq (withHyp (withHyp (withHyp (withHyp htl B1) B2) B3) A3)
         have htr := outputTransport OriginalRootObservation.tag tag (numeral 3) (![right,parameter]) heq (withHyp (withHyp (withHyp (withHyp htr B1) B2) B3) A3)
         exact EvaluatorAlignmentTypesProof.types3 R H G M W left right parameter out lt rt
           (withHyp (withHyp (withHyp (withHyp hsl B1) B2) B3) A3) (withHyp (withHyp (withHyp (withHyp hsr B1) B2) B3) A3) htl htr (withHyp (withHyp (withHyp (withHyp hvl B1) B2) B3) A3) (withHyp (withHyp (withHyp (withHyp hvr B1) B2) B3) A3) (withHyp (withHyp (withHyp (withHyp hyl B1) B2) B3) A3) (withHyp (withHyp (withHyp (withHyp hyr B1) B2) B3) A3)
       ·
         apply orCases (show Nonempty (Derivation body (B4 :: B3 :: B2 :: B1 :: Delta) B4) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
         ·
           have he : Nonempty (Derivation body (A4 :: B4 :: B3 :: B2 :: B1 :: Delta) A4) := ⟨Derivation.hypothesis List.mem_cons_self⟩
           have heq := (congrArg (fun f => Nonempty (Derivation body (A4 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 4))).mp he
           have htl := outputTransport OriginalRootObservation.tag tag (numeral 4) (![left,parameter]) heq (withHyp (withHyp (withHyp (withHyp (withHyp htl B1) B2) B3) B4) A4)
           have htr := outputTransport OriginalRootObservation.tag tag (numeral 4) (![right,parameter]) heq (withHyp (withHyp (withHyp (withHyp (withHyp htr B1) B2) B3) B4) A4)
           exact EvaluatorAlignmentTypesProof.types4 R H G M W left right parameter out lt rt
             (withHyp (withHyp (withHyp (withHyp (withHyp hsl B1) B2) B3) B4) A4) (withHyp (withHyp (withHyp (withHyp (withHyp hsr B1) B2) B3) B4) A4) htl htr (withHyp (withHyp (withHyp (withHyp (withHyp hvl B1) B2) B3) B4) A4) (withHyp (withHyp (withHyp (withHyp (withHyp hvr B1) B2) B3) B4) A4) (withHyp (withHyp (withHyp (withHyp (withHyp hyl B1) B2) B3) B4) A4) (withHyp (withHyp (withHyp (withHyp (withHyp hyr B1) B2) B3) B4) A4)
         ·
           have he : Nonempty (Derivation body (B5 :: B4 :: B3 :: B2 :: B1 :: Delta) A5) := ⟨Derivation.hypothesis List.mem_cons_self⟩
           have heq := (congrArg (fun f => Nonempty (Derivation body (B5 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 5))).mp he
           have htl := outputTransport OriginalRootObservation.tag tag (numeral 5) (![left,parameter]) heq (withHyp (withHyp (withHyp (withHyp (withHyp htl B1) B2) B3) B4) B5)
           have htr := outputTransport OriginalRootObservation.tag tag (numeral 5) (![right,parameter]) heq (withHyp (withHyp (withHyp (withHyp (withHyp htr B1) B2) B3) B4) B5)
           exact EvaluatorAlignmentTypesProof.types5 R H G M W left right parameter out lt rt
             (withHyp (withHyp (withHyp (withHyp (withHyp hsl B1) B2) B3) B4) B5) (withHyp (withHyp (withHyp (withHyp (withHyp hsr B1) B2) B3) B4) B5) htl htr (withHyp (withHyp (withHyp (withHyp (withHyp hvl B1) B2) B3) B4) B5) (withHyp (withHyp (withHyp (withHyp (withHyp hvr B1) B2) B3) B4) B5) (withHyp (withHyp (withHyp (withHyp (withHyp hyl B1) B2) B3) B4) B5) (withHyp (withHyp (withHyp (withHyp (withHyp hyr B1) B2) B3) B4) B5)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypeDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypeDispatchProof
