module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepWrapperProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl)
open OriginalLambdaErasureSquareDichotomyDefinitions OriginalLambdaErasureSquareDichotomySyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem equalParents (s t d e childS childT : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor s d e childS)))
    (ht : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor t d e childT)))
    (he : Nonempty (Derivation body Delta (equal childS childT))) :
    Nonempty (Derivation body Delta (equal s t)) := by
  have hs' : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor s d e childT)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 Delta
      (OrdinaryArithmetic.graphFormula OriginalLambdaConstructor.constructor) s
      (Fin.cons d (Fin.cons e (Fin.cons childS Fin.elim0)))
      (Fin.cons d (Fin.cons e (Fin.cons childT Fin.elim0))) _ hs
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact ⟨refl d⟩
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact ⟨refl e⟩
    · simpa only [InternalSourceInversionSupportProof.onEquality,equalEqn] using he
  obtain ⟨h⟩ := valueUnique OriginalLambdaConstructor.constructor s t
    (Fin.cons d (Fin.cons e (Fin.cons childT Fin.elim0))) hs' ht
  exact ⟨by simpa only [equalEqn] using h⟩

theorem frameHop (source : Program 2)
    (s t parameter childS childT childParam d e context gamma extended cert childCert : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (Frame source s t parameter childS childT childParam d e context gamma extended)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryLambda.prefixCertificate cert childCert))) :
    Nonempty (Derivation body Delta
      (OriginalTransparentLambdaStep.LambdaHop source s t cert parameter childS childT childCert childParam
        d e context gamma extended)) := by
  have h1 := andRight hf
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  exact andIntro (andLeft hf) (andIntro (andLeft h1) (andIntro (andLeft h2)
    (andIntro (andLeft h3) (andIntro (andLeft h4) (andIntro hp (andRight h4))))))

/-- Local induction closure only: the caller supplies the child dichotomy.
Only the new original lambda prefix is constructed here. -/
theorem actualLocalCongruence : LocalCongruence := by
  intro source oldStep endpoint window body alpha Delta s t parameter childS childT childParam
    d e context gamma extended hf supplier
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined source oldStep)
  apply supplier (Result leaf s t parameter)
  · intro he
    obtain ⟨hp⟩ := equalParents s t d e childS childT
      (andLeft (andRight hf)) (andLeft (andRight (andRight hf))) he
    exact ⟨orLeft hp⟩
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyProof
