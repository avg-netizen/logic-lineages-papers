module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight queryCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalControlGraphSupportProof (emptyRename)
open InternalTagArithmeticSyntaxProof (OTerm)
open GuardedPositiveApplicationSyntaxProof
open SpineApplicationTargets (selectedData)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem guardedLift {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (data : Data) (window : Program 1) (oldStep : Program 4)
    (arrow d e f g a out other certificate mapped parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (hypotheses data window oldStep arrow d e f g a out other certificate mapped parameter))) :
    Nonempty (Derivation body Gamma
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        (edgeChecker (selectedData data window) oldStep) out other mapped parameter)) := by
  apply queryCases (GuardedPositiveApplicationQueriesProof.queries BottomSpineMeasure.measure)
    (Fin.cons f (Fin.cons g Fin.elim0)) _
  intro β j ys Delta hj hq
  rw [acceptedRename]
  have h' := renameInto h j Delta hj
  rw [hypothesesRename] at h'
  simp only [consTermRename,emptyRename] at hq
  have hfacts := GuardedPositiveApplicationQueriesProof.queryFacts BottomSpineMeasure.measure
    (f.relabel j) (g.relabel j) ys hq
  have tail1 := andRight h'
  have tail2 := andRight tail1
  have tail3 := andRight tail2
  exact GuardedPositiveApplicationCoreProof.atValues data window oldStep
    (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (g.relabel j)
    (a.relabel j) (out.relabel j) (other.relabel j) (certificate.relabel j)
    (mapped.relabel j) (parameter.relabel j) ys
    (andLeft h') (andLeft tail1) (andLeft tail2) (andLeft tail3) (andRight tail3) hfacts

theorem actualGuardedPositiveApplicationLift :
    GuardedPositiveApplicationTargets.ActualGuardedPositiveApplicationLift := by
  intro body data window oldStep
  dsimp only
  intro α Delta arrow d e f g a out other certificate mapped parameter
  let H := hypotheses data window oldStep arrow d e f g a out other certificate mapped parameter
  obtain ⟨d⟩ := guardedLift (body := body) (Gamma := H :: Delta)
    data window oldStep arrow d e f g a out other certificate mapped parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationProof
