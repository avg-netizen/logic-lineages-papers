module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentBranchesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSourceTagsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTagRecoverProof
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
theorem sourceTag (R : Program 2) (H G : Program 1) (M W : Program 2)
 (input parameter tag out observedTag : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag tag input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observedTag out))) :
 Nonempty (Derivation body Delta (equal tag observedTag)) := by
 have htags := EvaluatorAlignmentSourceTagsProof.sourceTags H G M W input parameter tag hs ht
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
   have htag := outputTransport OriginalRootObservation.tag tag (numeral 0) (![input,parameter]) heq (withHyp ht A0)
   have heo := EvaluatorAlignmentBranchesProof.tag0 R input parameter out observedTag htag (withHyp hv A0) (withHyp ho A0)
   have heoq := (congrArg (fun f => Nonempty (Derivation body (A0 :: Delta) f)) (equalEqn observedTag (numeral 0))).mp heo
   obtain ⟨he⟩ := heq
   obtain ⟨heo⟩ := heoq
   exact (congrArg (fun f => Nonempty (Derivation body (A0 :: Delta) f)) (equalEqn tag observedTag)).mpr
     ⟨InternalTagArithmeticSupportProof.trans he (InternalTagArithmeticSupportProof.symm heo)⟩
 ·
   apply orCases (show Nonempty (Derivation body (B1 :: Delta) B1) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   ·
     have he : Nonempty (Derivation body (A1 :: B1 :: Delta) A1) := ⟨Derivation.hypothesis List.mem_cons_self⟩
     have heq := (congrArg (fun f => Nonempty (Derivation body (A1 :: B1 :: Delta) f)) (equalEqn tag (numeral 1))).mp he
     have htag := outputTransport OriginalRootObservation.tag tag (numeral 1) (![input,parameter]) heq (withHyp (withHyp ht B1) A1)
     have heo := EvaluatorAlignmentBranchesProof.tag1 R input parameter out observedTag htag (withHyp (withHyp hv B1) A1) (withHyp (withHyp ho B1) A1)
     have heoq := (congrArg (fun f => Nonempty (Derivation body (A1 :: B1 :: Delta) f)) (equalEqn observedTag (numeral 1))).mp heo
     obtain ⟨he⟩ := heq
     obtain ⟨heo⟩ := heoq
     exact (congrArg (fun f => Nonempty (Derivation body (A1 :: B1 :: Delta) f)) (equalEqn tag observedTag)).mpr
       ⟨InternalTagArithmeticSupportProof.trans he (InternalTagArithmeticSupportProof.symm heo)⟩
   ·
     apply orCases (show Nonempty (Derivation body (B2 :: B1 :: Delta) B2) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
     ·
       have he : Nonempty (Derivation body (A2 :: B2 :: B1 :: Delta) A2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
       have heq := (congrArg (fun f => Nonempty (Derivation body (A2 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 2))).mp he
       have htag := outputTransport OriginalRootObservation.tag tag (numeral 2) (![input,parameter]) heq (withHyp (withHyp (withHyp ht B1) B2) A2)
       have heo := EvaluatorAlignmentBranchesProof.tag2 R input parameter out observedTag htag (withHyp (withHyp (withHyp hv B1) B2) A2) (withHyp (withHyp (withHyp ho B1) B2) A2)
       have heoq := (congrArg (fun f => Nonempty (Derivation body (A2 :: B2 :: B1 :: Delta) f)) (equalEqn observedTag (numeral 2))).mp heo
       obtain ⟨he⟩ := heq
       obtain ⟨heo⟩ := heoq
       exact (congrArg (fun f => Nonempty (Derivation body (A2 :: B2 :: B1 :: Delta) f)) (equalEqn tag observedTag)).mpr
         ⟨InternalTagArithmeticSupportProof.trans he (InternalTagArithmeticSupportProof.symm heo)⟩
     ·
       apply orCases (show Nonempty (Derivation body (B3 :: B2 :: B1 :: Delta) B3) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
       ·
         have he : Nonempty (Derivation body (A3 :: B3 :: B2 :: B1 :: Delta) A3) := ⟨Derivation.hypothesis List.mem_cons_self⟩
         have heq := (congrArg (fun f => Nonempty (Derivation body (A3 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 3))).mp he
         have htag := outputTransport OriginalRootObservation.tag tag (numeral 3) (![input,parameter]) heq (withHyp (withHyp (withHyp (withHyp ht B1) B2) B3) A3)
         have heo := EvaluatorAlignmentBranchesProof.tag3 R input parameter out observedTag htag (withHyp (withHyp (withHyp (withHyp hv B1) B2) B3) A3) (withHyp (withHyp (withHyp (withHyp ho B1) B2) B3) A3)
         have heoq := (congrArg (fun f => Nonempty (Derivation body (A3 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn observedTag (numeral 3))).mp heo
         obtain ⟨he⟩ := heq
         obtain ⟨heo⟩ := heoq
         exact (congrArg (fun f => Nonempty (Derivation body (A3 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag observedTag)).mpr
           ⟨InternalTagArithmeticSupportProof.trans he (InternalTagArithmeticSupportProof.symm heo)⟩
       ·
         apply orCases (show Nonempty (Derivation body (B4 :: B3 :: B2 :: B1 :: Delta) B4) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
         ·
           have he : Nonempty (Derivation body (A4 :: B4 :: B3 :: B2 :: B1 :: Delta) A4) := ⟨Derivation.hypothesis List.mem_cons_self⟩
           have heq := (congrArg (fun f => Nonempty (Derivation body (A4 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 4))).mp he
           have htag := outputTransport OriginalRootObservation.tag tag (numeral 4) (![input,parameter]) heq (withHyp (withHyp (withHyp (withHyp (withHyp ht B1) B2) B3) B4) A4)
           have heo := EvaluatorAlignmentBranchesProof.tag4 R input parameter out observedTag htag (withHyp (withHyp (withHyp (withHyp (withHyp hv B1) B2) B3) B4) A4) (withHyp (withHyp (withHyp (withHyp (withHyp ho B1) B2) B3) B4) A4)
           have heoq := (congrArg (fun f => Nonempty (Derivation body (A4 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn observedTag (numeral 4))).mp heo
           obtain ⟨he⟩ := heq
           obtain ⟨heo⟩ := heoq
           exact (congrArg (fun f => Nonempty (Derivation body (A4 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag observedTag)).mpr
             ⟨InternalTagArithmeticSupportProof.trans he (InternalTagArithmeticSupportProof.symm heo)⟩
         ·
           have he : Nonempty (Derivation body (B5 :: B4 :: B3 :: B2 :: B1 :: Delta) A5) := ⟨Derivation.hypothesis List.mem_cons_self⟩
           have heq := (congrArg (fun f => Nonempty (Derivation body (B5 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag (numeral 5))).mp he
           have htag := outputTransport OriginalRootObservation.tag tag (numeral 5) (![input,parameter]) heq (withHyp (withHyp (withHyp (withHyp (withHyp ht B1) B2) B3) B4) B5)
           have heo := EvaluatorAlignmentBranchesProof.tag5 R input parameter out observedTag htag (withHyp (withHyp (withHyp (withHyp (withHyp hv B1) B2) B3) B4) B5) (withHyp (withHyp (withHyp (withHyp (withHyp ho B1) B2) B3) B4) B5)
           have heoq := (congrArg (fun f => Nonempty (Derivation body (B5 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn observedTag (numeral 5))).mp heo
           obtain ⟨he⟩ := heq
           obtain ⟨heo⟩ := heoq
           exact (congrArg (fun f => Nonempty (Derivation body (B5 :: B4 :: B3 :: B2 :: B1 :: Delta) f)) (equalEqn tag observedTag)).mpr
             ⟨InternalTagArithmeticSupportProof.trans he (InternalTagArithmeticSupportProof.symm heo)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTagRecoverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTagRecoverProof
