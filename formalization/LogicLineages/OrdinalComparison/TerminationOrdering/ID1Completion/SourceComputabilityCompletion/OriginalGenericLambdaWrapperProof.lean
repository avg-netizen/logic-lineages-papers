module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTransparentLambdaStep OriginalHereditaryLambdaGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem introduction (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
 (rawIntroduction : OriginalGenericLambdaWrapperTargets.RawIntroduction source oldStep)
    (s t cert parameter childS childT childCert childParam d e context gamma extended : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended)))
    (hchild : Nonempty (Derivation body Delta
      (graph4 (closedLeaf endpoint window oldStep) (suc z) childS childT childCert childParam))) :
    Nonempty (Derivation body Delta
      (graph4 (closedLeaf endpoint window oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 14 → OTerm alpha := ![s,t,cert,parameter,childS,childT,childCert,childParam,d,e,context,gamma,extended,suc z]
  apply queryCases OriginalTransparentLambdaStepInternalProof.queries xs _
  intro beta j ys Gamma hj hq
  have h' := renameInto h j Gamma hj
  have hchild' := renameInto hchild j Gamma hj
  simp only [graph4Rename,sucRelabel,zRelabel] at hchild'
  simp only [LambdaHop,conjunctionRename,graph1Rename,graph2Rename,graph3Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel] at h'
  let xx : Fin 14 → OTerm beta := fun i => (xs i).relabel j
  have harrow := binaryRecover OriginalLambdaConstructor.arrow (.projection 8) (.projection 9)
    (ys 0) (d.relabel j) (e.relabel j) xx (hq 0) (projectionValue 8 xx) (projectionValue 9 xx)
  have hleft := unaryRecover InternalUnpair.left (.projection (6 : Fin 14))
    (ys 1) (childCert.relabel j) xx (hq 1) (projectionValue 6 xx)
  have hright := unaryRecover InternalUnpair.right (.projection (6 : Fin 14))
    (ys 2) (childCert.relabel j) xx (hq 2) (projectionValue 6 xx)
  have hcons := binaryRecover InternalListCodec.consCode (InternalAcceptance.constantZero 14)
    (leftOf (.projection 6)) (ys 3) z (ys 1) xx (hq 3) (constantZeroValue xx) (hq 1)
  have hstate := OriginalTransparentLambdaStepInternalProof.wireRecover OriginalHereditaryLambda.live (![0,1,2,3] : Fin 4 → Fin 14)
    (ys 4) xx (hq 4)
  have hnext := OriginalTransparentLambdaStepInternalProof.wireRecover OriginalHereditaryLambda.live (![4,5,6,7] : Fin 4 → Fin 14)
    (ys 5) xx (hq 5)
  have hparentWire : (fun i => xx ((![0,1,2,3] : Fin 4 → Fin 14) i)) =
      ![s.relabel j,t.relabel j,cert.relabel j,parameter.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
  have hchildWire : (fun i => xx ((![4,5,6,7] : Fin 4 → Fin 14) i)) =
      ![childS.relabel j,childT.relabel j,childCert.relabel j,childParam.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
  rw [hparentWire] at hstate
  rw [hchildWire] at hnext
  have hout := OriginalGenericLambdaWrapperCoreProof.atWitnesses source oldStep endpoint window rawIntroduction
    (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
    (childS.relabel j) (childT.relabel j) (childCert.relabel j) (childParam.relabel j)
    (d.relabel j) (e.relabel j) (context.relabel j) (gamma.relabel j) (extended.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    h' hchild' harrow hleft hright hcons hstate hnext
  simpa only [graph4Rename,sucRelabel,zRelabel] using hout
theorem actualOriginalTransparentLambdaClosedLeafIntroduction :
    OriginalGenericLambdaWrapperTargets.ActualIntroduction := by
  intro source oldStep endpoint window rawIntroduction body alpha Delta s t cert parameter childS childT childCert childParam d e context gamma extended
  let leaf := closedLeaf endpoint window oldStep
  let A := LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended ⊓
    graph4 leaf (suc z) childS childT childCert childParam
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := introduction source oldStep endpoint window rawIntroduction s t cert parameter
    childS childT childCert childParam d e context gamma extended (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperProof
