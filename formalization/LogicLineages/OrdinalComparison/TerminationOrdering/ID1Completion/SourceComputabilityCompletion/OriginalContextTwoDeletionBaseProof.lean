module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalClassContextAllPositionObserver (deleteAt)
open InternalListCodecSupportProof (consGraph)
open OriginalAllPositionContextDeleteBaseProof OriginalAllPositionContextDeleteConsProof
open OriginalAllPositionContextDeleteDropProof
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalContextTwoDeletionCoreProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consGraphRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)

theorem zeroWithTail (gamma head tail upper lower left right j a b upperTail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hu : Nonempty (Derivation body Delta (graph2 deleteAt upper (suc j) gamma)))
    (hl : Nonempty (Derivation body Delta (graph2 deleteAt left z upper)))
    (hd : Nonempty (Derivation body Delta (graph2 deleteAt lower z gamma)))
    (hr : Nonempty (Derivation body Delta (graph2 deleteAt right j lower)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup a z gamma)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup b (suc j) gamma)))
    (ht : Nonempty (Derivation body Delta (graph2 deleteAt upperTail j tail)))
    : Nonempty (Derivation body Delta (equal left right ⊓
      (graph2 InternalRawListRecursion.lookup a z upper ⊓ graph2 InternalRawListRecursion.lookup b j lower))) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons upperTail Fin.elim0)) _
  intro beta rho Theta actual hrho hactual
  simp only [conjunctionRename,equalRename,graph2Rename,zRelabel]
  have hc' := renameInto hc rho Theta hrho
  have hu' := renameInto hu rho Theta hrho
  have hl' := renameInto hl rho Theta hrho
  have hd' := renameInto hd rho Theta hrho
  have hr' := renameInto hr rho Theta hrho
  have ha' := renameInto ha rho Theta hrho
  have hb' := renameInto hb rho Theta hrho
  have ht' := renameInto ht rho Theta hrho
  simp only [consGraphRename,graph2Rename,sucRelabel,zRelabel] at hc' hu' hl' hd' hr' ha' hb' ht'
  simp only [consTermRename,emptyRename] at hactual
  have hdel := iffBackward (deleteConsIff (gamma.relabel rho) (head.relabel rho) (tail.relabel rho)
    (j.relabel rho) actual (upperTail.relabel rho) hc' hactual) ht'
  have he := valueUnique deleteAt actual (upper.relabel rho)
    (Fin.cons (suc (j.relabel rho)) (Fin.cons (gamma.relabel rho) Fin.elim0)) hdel hu'
  have hcons := outputTransport InternalListCodec.consCode actual (upper.relabel rho)
    (Fin.cons (head.relabel rho) (Fin.cons (upperTail.relabel rho) Fin.elim0)) he hactual
  exact zeroAtCons (gamma.relabel rho) (head.relabel rho) (tail.relabel rho) (upper.relabel rho)
    (upperTail.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (j.relabel rho)
    (a.relabel rho) (b.relabel rho) hc' hcons ht' hl' hd' hr' ha' hb'

theorem zeroKnownCons (gamma head tail upper lower left right j a b : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hu : Nonempty (Derivation body Delta (graph2 deleteAt upper (suc j) gamma)))
    (hl : Nonempty (Derivation body Delta (graph2 deleteAt left z upper)))
    (hd : Nonempty (Derivation body Delta (graph2 deleteAt lower z gamma)))
    (hr : Nonempty (Derivation body Delta (graph2 deleteAt right j lower)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup a z gamma)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup b (suc j) gamma)))
    : Nonempty (Derivation body Delta (equal left right ⊓
      (graph2 InternalRawListRecursion.lookup a z upper ⊓ graph2 InternalRawListRecursion.lookup b j lower))) := by
  apply programCases deleteAt (Fin.cons j (Fin.cons tail Fin.elim0)) _
  intro beta rho Theta upperTail hrho ht
  simp only [conjunctionRename,equalRename,graph2Rename,zRelabel]
  have hc' := renameInto hc rho Theta hrho
  have hu' := renameInto hu rho Theta hrho
  have hl' := renameInto hl rho Theta hrho
  have hd' := renameInto hd rho Theta hrho
  have hr' := renameInto hr rho Theta hrho
  have ha' := renameInto ha rho Theta hrho
  have hb' := renameInto hb rho Theta hrho
  simp only [consGraphRename,graph2Rename,sucRelabel,zRelabel] at hc' hu' hl' hd' hr' ha' hb'
  simp only [consTermRename,emptyRename] at ht
  exact zeroWithTail (gamma.relabel rho) (head.relabel rho) (tail.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) upperTail hc' hu' hl' hd' hr' ha' hb' ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionBaseProof
