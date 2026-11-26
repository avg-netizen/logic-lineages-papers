module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalProof
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename binaryVectorRename)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTypedArgumentObservations (reverse)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromOriginal (raw out : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph1 reverse out raw))) :
 Nonempty (Derivation body Delta (graph2 accumulated out raw z)) := by
 obtain ⟨he⟩ := OriginalTypedArgumentObservationsReverseInternalAccumulatorZeroProof.zeroCorrespondence body alpha raw out
 exact closedApply ⟨Derivation.conjunctionRight he⟩ h

theorem forward (front value singleton combined mapped out : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton value z)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append combined front singleton)))
 (hm : Nonempty (Derivation body Delta (graph1 reverse mapped front)))
 (ho : Nonempty (Derivation body Delta (graph1 reverse out combined))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value mapped)) :=
 closedApply (OriginalTypedArgumentObservationsReverseInternalAccumulatorProof.actualAppendSingleton body alpha front value singleton combined z mapped out)
   (andIntro hs (andIntro hj (andIntro (fromOriginal front mapped hm) (fromOriginal combined out ho))))

theorem backward (front value singleton combined mapped out : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton value z)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append combined front singleton)))
 (hm : Nonempty (Derivation body Delta (graph1 reverse mapped front)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value mapped))) :
 Nonempty (Derivation body Delta (graph1 reverse out combined)) := by
 apply programCases reverse ![combined] _
 intro beta rho Theta actual hrho hv
 rw [unaryVectorRename] at hv
 simp only [graph1Rename]
 have hs' := renameInto hs rho Theta hrho
 have hj' := renameInto hj rho Theta hrho
 have hm' := renameInto hm rho Theta hrho
 have ho' := renameInto ho rho Theta hrho
 simp only [graph2Rename,zRelabel] at hs'
 simp only [graph2Rename] at hj' ho'
 simp only [graph1Rename] at hm'
 have hc := forward (front.relabel rho) (value.relabel rho) (singleton.relabel rho)
   (combined.relabel rho) (mapped.relabel rho) actual hs' hj' hm' hv
 have he := valueUnique InternalListCodec.consCode actual (out.relabel rho)
   ![value.relabel rho,mapped.relabel rho] hc ho'
 exact outputTransport reverse actual (out.relabel rho) ![combined.relabel rho] he hv

theorem actualAppendSingleton : OriginalTypedArgumentObservationsReverseInternalTargets.AppendSingleton := by
 intro body alpha front value singleton combined mapped out
 let H := graph2 InternalListCodec.consCode singleton value z ⊓
   (graph2 InternalApplicationValidityStackAppend.append combined front singleton ⊓ graph1 reverse mapped front)
 let P := graph1 reverse out combined
 let Q := graph2 InternalListCodec.consCode out value mapped
 have h : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hf : Nonempty (Derivation body (P :: [H]) Q) :=
   forward front value singleton combined mapped out (withHyp (andLeft h) P)
     (withHyp (andLeft (andRight h)) P) (withHyp (andRight (andRight h)) P)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hb : Nonempty (Derivation body (Q :: [H]) P) :=
   backward front value singleton combined mapped out (withHyp (andLeft h) Q)
     (withHyp (andLeft (andRight h)) Q) (withHyp (andRight (andRight h)) Q)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hf⟩ := hf
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
   (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalProof
