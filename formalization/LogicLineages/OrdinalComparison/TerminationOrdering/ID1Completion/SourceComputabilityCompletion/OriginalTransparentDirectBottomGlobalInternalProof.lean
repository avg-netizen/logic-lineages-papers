module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomWrapperSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNilNormalizationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTransparentDirectBottomGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both refinements capture the original concrete decoder before the
minimum/variable/final base preparations. -/
theorem initialSource (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (initial p H G W).base.oldSource = source p H G W := rfl

theorem finalLeaf (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :
    let b := initial p H G W
    let r := OriginalTransparentLambdaStepGlobal.refined b H G W P
    (finalInputs p H G W P).oldStep =
      OriginalHereditaryLambdaGlobal.closedLeaf
        (OriginalHereditaryLambdaGlobal.endpoint (OriginalLambdaTraversalSelection.prepareInputs r)) r.window
        (OriginalTransparentLambdaStep.refined (source p H G W)
          (OriginalHereditaryLambdaGlobal.priorFinal b).oldStep) := rfl

/-- The concrete source pays spine once, for both wrapper layers. The raw
chosen nil certificate stops normalization without requiring any hop guard.
This is entirely internal and retains the exact original certificate. -/
theorem actualOriginalDirectBottomGlobalIntroduction :
    OriginalTransparentDirectBottomGlobalTargets.ActualOriginalDirectBottomGlobalIntroduction := by
  intro p H G W P body alpha Delta s t cert parameter typ
  let S := source p H G W
  let b := initial p H G W
  let r := OriginalTransparentLambdaStepGlobal.refined b H G W P
  let E := OriginalHereditaryLambdaGlobal.endpoint (OriginalLambdaTraversalSelection.prepareInputs r)
  let N := OriginalTransparentLambdaStep.refined S (OriginalHereditaryLambdaGlobal.priorFinal b).oldStep
  let A := OriginalTransparentDirectBottom.Premises S s t cert parameter typ
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andLeft h
  have hn := andLeft (andRight h)
  have ht := andLeft (andRight (andRight h))
  have hb := andLeft (andRight (andRight (andRight h)))
  have hc := andRight (andRight (andRight (andRight h)))
  have hspine := OriginalTransparentDirectBottomSourceSpineProof.sourceSpine
    H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
    s t cert parameter typ hs hn hb
  have hraw := OriginalTransparentDirectBottomInternalProof.introduction S p.oldStep
    s t cert typ parameter hs hn ht hb hc
  have hprior : Nonempty (Derivation body (A :: Delta)
      (graph4 (OriginalHereditaryLambdaGlobal.priorFinal b).oldStep (suc z) s t cert parameter)) :=
    OriginalTransparentDirectBottomWrapperSupportProof.wrapperIntroduction
      (OriginalHereditaryLambdaGlobal.endpoint b) b.window b.oldStep
      s t cert parameter typ hn ht hb hspine hraw
  have hpath := OriginalTransparentVariableStepHereditaryProof.certificatePath s cert hc
  have hnormal := OriginalTransparentLambdaStepNilNormalizationProof.introduction
    S (OriginalHereditaryLambdaGlobal.priorFinal b).oldStep (suc z) s t cert parameter hpath hprior
  let inner := OriginalHereditaryLambdaGlobal.wrapper E r.window N
  have hi := OriginalTransparentDirectBottomWrapperSupportProof.wrapperIntroduction E r.window N
    s t cert parameter typ hn ht hb hspine hnormal
  have hg := OriginalTransparentVariableStepHereditaryProof.nilGuard inner
    s t cert parameter typ ht hb hc
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hh := conjunctionAccept inner (OriginalHereditaryLambda.guard inner) xs hi hg
  obtain ⟨hout⟩ := OriginalTransparentDirectBottomWrapperSupportProof.wrapperIntroduction E r.window
    (OriginalHereditaryLambda.refined inner) s t cert parameter typ hn ht hb hspine hh
  have hfinal : Derivation body (A :: Delta)
      (graph4 (finalInputs p H G W P).oldStep (suc z) s t cert parameter) := by
    rw [finalLeaf p H G W P]
    exact hout
  exact ⟨Derivation.implicationIntroduction hfinal⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof.actualOriginalDirectBottomGlobalIntroduction
