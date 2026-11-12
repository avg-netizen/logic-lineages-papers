module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureQueryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedCongruenceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointFrameProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedClosedApplicationErasureDefinitions
open OriginalMixedExistentialCongruenceSupportProof (resultRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem childIHRename {beta : Type} (leaf outLeaf : Program 4) (source : Program 2)
 (oldChildS oldChildT oldChildCert oldParam erasedType cutoff context : OTerm alpha)
 (j : alpha → beta) (Theta : List (Formula beta)) (hj : ∀ f ∈ Delta, f.relabel j ∈ Theta)
 (h : ChildIH body Delta leaf outLeaf source oldChildS oldChildT oldChildCert oldParam erasedType cutoff context) :
 ChildIH body Theta leaf outLeaf source (oldChildS.relabel j) (oldChildT.relabel j) (oldChildCert.relabel j)
  (oldParam.relabel j) (erasedType.relabel j) (cutoff.relabel j) (context.relabel j) := by
 intro gamma k Xi hk
 have hc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
  intro f hf
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (f.relabel j) (hj f hf)
 simpa only [Term.relabel_relabel] using h gamma (k ∘ j) Xi hc

def queries : Fin 3 → Program 5 := fun i =>
 .composition OriginalRawSyntaxTransport.erasePackedRaw ![.projection 3,.projection 4,.projection i.castSucc.castSucc]

theorem actualAtFields : OriginalMixedClosedApplicationErasureQueryTargets.ActualAtFields := by
 intro H G M W oldStep window body alpha Delta oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow fp ap
  newS newT newParam erasedType cutoff gamma extended context hctor hh hparent hrec hi hop hnp hes het ih
 let xs : Fin 5 → OTerm alpha := ![oldChildS,oldChildT,oldArg,erasedType,cutoff]
 apply queryCases queries xs _
 intro beta j ys Theta hj hq
 rw [resultRename]
 have hctor' := renameInto hctor j Theta hj
 simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hctor'
 have hh' := renameInto hh j Theta hj
 simp only [OriginalTransparentMixedPathInternalDefinitions.ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
  GuardedSourceSyntaxProof.numeralRename] at hh'
 have hparent' := renameInto hparent j Theta hj
 simp only [graph4Rename,GuardedSourceSyntaxProof.numeralRename] at hparent'
 have hrec' := renameInto hrec j Theta hj
 simp only [graph4Rename,GuardedSourceSyntaxProof.numeralRename] at hrec'
 have hi' := renameInto hi j Theta hj
 rw [OriginalContextInsertionSyntaxProof.insertRename] at hi'
 have hop' := renameInto hop j Theta hj
 have hnp' := renameInto hnp j Theta hj
 rw [graph2Rename] at hop' hnp'
 have hes' := renameInto hes j Theta hj
 have het' := renameInto het j Theta hj
 rw [graph3Rename] at hes' het'
 have ih' := childIHRename (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
  (OriginalTransparentMixedDirectBottom.source H G M W) oldChildS oldChildT oldChildCert oldParam erasedType cutoff context j Theta hj ih
 let xx : Fin 5 → OTerm beta := ![oldChildS.relabel j,oldChildT.relabel j,oldArg.relabel j,erasedType.relabel j,cutoff.relabel j]
 have heq : (fun i => (xs i).relabel j) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
 rw [heq] at hq
 have hcs := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw
  (.projection 3) (.projection 4) (.projection 0) (ys 0) (erasedType.relabel j) (cutoff.relabel j) (oldChildS.relabel j) xx (hq 0)
  (projectionValue 3 xx) (projectionValue 4 xx) (projectionValue 0 xx)
 have hct := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw
  (.projection 3) (.projection 4) (.projection 1) (ys 1) (erasedType.relabel j) (cutoff.relabel j) (oldChildT.relabel j) xx (hq 1)
  (projectionValue 3 xx) (projectionValue 4 xx) (projectionValue 1 xx)
 have hca := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw
  (.projection 3) (.projection 4) (.projection 2) (ys 2) (erasedType.relabel j) (cutoff.relabel j) (oldArg.relabel j) xx (hq 2)
  (projectionValue 3 xx) (projectionValue 4 xx) (projectionValue 2 xx)
 exact OriginalMixedClosedApplicationErasureProof.actualAtCoordinates H G M W oldStep window body beta Theta
  (oldS.relabel j) (oldT.relabel j) (oldCert.relabel j) (oldParam.relabel j) (oldChildS.relabel j) (oldChildT.relabel j)
  (oldChildCert.relabel j) (oldArg.relabel j) (domain.relabel j) (codomain.relabel j) (arrow.relabel j) (fp.relabel j) (ap.relabel j)
  (newS.relabel j) (newT.relabel j) (ys 0) (ys 1) (ys 2) (newParam.relabel j) (erasedType.relabel j) (cutoff.relabel j)
  (gamma.relabel j) (extended.relabel j) (context.relabel j) hctor' hh' hparent' hrec' hi' hop' hnp' hes' het' hcs hct hca ih'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureQueryProof
