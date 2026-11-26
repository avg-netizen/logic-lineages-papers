module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl)
open OriginalLambdaErasureSquareDichotomyDefinitions (Witness Certificate Frame)
open OriginalLambdaErasureSquareDichotomySyntaxProof (frameRename witnessRename witnessIntro localOrRename)
open OriginalLambdaErasureSquareDichotomyProof (equalParents frameHop)
open OriginalLambdaOriginalRankDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


@[simp] theorem rankDropRename {beta : Type} (oldS oldT before after : OTerm alpha) (j : alpha → beta) :
    (PackedRankDrop oldS oldT before after).relabel j =
      PackedRankDrop (oldS.relabel j) (oldT.relabel j) (before.relabel j) (after.relabel j) := by
  simp only [PackedRankDrop,conjunctionRename,graph1Rename,
    InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename]

@[simp] theorem resultRename {beta : Type} (leaf : Program 4)
    (s t parameter oldS oldT before after : OTerm alpha) (j : alpha → beta) :
    (Result leaf s t parameter oldS oldT before after).relabel j =
      Result leaf (s.relabel j) (t.relabel j) (parameter.relabel j)
        (oldS.relabel j) (oldT.relabel j) (before.relabel j) (after.relabel j) := by
  simp only [Result,localOrRename,conjunctionRename,
    OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,rankDropRename,witnessRename]

/-- Local induction closure only: the caller supplies the child dichotomy.
Only the new original lambda prefix is constructed here. -/
theorem actualLocalRankedCongruence : LocalRankedCongruence := by
  intro source oldStep endpoint window body alpha Delta s t parameter childS childT childParam
    d e context gamma extended oldS oldT oldChildS oldChildT before after
  dsimp only
  intro hf holdS holdT supplier
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined source oldStep)
  apply supplier (Result leaf s t parameter oldS oldT before after)
  · intro he
    obtain ⟨hp⟩ := equalParents s t d e childS childT
      (andLeft (andRight hf)) (andLeft (andRight (andRight hf))) (andLeft he)
    have ranks := OriginalLambdaOriginalRankProof.liftOriginalRanks
      oldS oldT oldChildS oldChildT d e before after holdS holdT (andRight he)
    obtain ⟨conclusion⟩ := andIntro ⟨hp⟩ ranks
    exact ⟨orLeft conclusion⟩
  · intro beta j Theta childCert hj hc
    rw [resultRename]
    have hf' := renameInto hf j Theta hj
    rw [frameRename] at hf'
    have witness : Nonempty (Derivation body Theta
        (Witness leaf (s.relabel j) (t.relabel j) (parameter.relabel j))) := by
      apply programCases OriginalHereditaryLambda.prefixCertificate (Fin.cons childCert Fin.elim0) _
      intro gamma' k Xi cert hk hprefix
      rw [witnessRename]
      simp only [consTermRename,emptyRename] at hprefix
      have hf'' := renameInto hf' k Xi hk
      rw [frameRename] at hf''
      have hc' := renameInto hc k Xi hk
      simp only [Certificate,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hc'
      have hop := frameHop source ((s.relabel j).relabel k) ((t.relabel j).relabel k)
        ((parameter.relabel j).relabel k) ((childS.relabel j).relabel k) ((childT.relabel j).relabel k)
        ((childParam.relabel j).relabel k) ((d.relabel j).relabel k) ((e.relabel j).relabel k)
        ((context.relabel j).relabel k) ((gamma.relabel j).relabel k) ((extended.relabel j).relabel k)
        cert (childCert.relabel k) hf'' hprefix
      obtain ⟨law⟩ := OriginalTransparentLambdaStepWrapperProof.actualOriginalTransparentLambdaClosedLeafIntroduction
        source oldStep endpoint window body gamma' Xi ((s.relabel j).relabel k) ((t.relabel j).relabel k)
        cert ((parameter.relabel j).relabel k) ((childS.relabel j).relabel k) ((childT.relabel j).relabel k)
        (childCert.relabel k) ((childParam.relabel j).relabel k) ((d.relabel j).relabel k) ((e.relabel j).relabel k)
        ((context.relabel j).relabel k) ((gamma.relabel j).relabel k) ((extended.relabel j).relabel k)
      obtain ⟨args⟩ := andIntro hop hc'
      exact witnessIntro leaf ((s.relabel j).relabel k) ((t.relabel j).relabel k)
        ((parameter.relabel j).relabel k) cert ⟨Derivation.implicationElimination law args⟩
    obtain ⟨witness⟩ := witness
    exact ⟨orRight witness⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
