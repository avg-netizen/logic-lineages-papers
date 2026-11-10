module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open OriginalNeutralQuotient OriginalNeutralQuotientTargets OriginalNeutralQuotientSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Bind every field of the actual quotient certificate internally and
retain its selector equations. The original checker factorization, full-fold
neutrality and SAME-checker child reconstruction then supply the exact
same-type-bottom or canonical-function-step continuation. -/
theorem actualOriginalNeutralQuotientEdgeElimination :
    ActualOriginalNeutralQuotientEdgeElimination := by
  intro p
  dsimp only
  intro body alpha Gamma x y certificate parameter typeCode psi hw he hn ht hbottom next
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  let qs : Fin 3 → Program 1 := Fin.cons source (Fin.cons target (Fin.cons step Fin.elim0))
  have hbottomImp : Nonempty (Derivation body Gamma
      ((graph1 BottomRepresentative.bottomCode y typeCode).imp psi)) := by
    obtain ⟨hbottom⟩ := hbottom
    exact ⟨Derivation.implicationIntroduction hbottom⟩
  apply queryCases qs (Fin.cons certificate Fin.elim0) psi
  intro beta j ys Delta hj hq
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hf : Nonempty (Derivation body Delta
      (selectors (certificate.relabel j) (ys 0) (ys 1) (ys 2))) := by
    apply andIntro
    · have hvalue := hq 0
      rw [show qs (0 : Fin 3) = source from rfl] at hvalue
      simpa only [consTermRename,emptyRename] using hvalue
    · apply andIntro
      · have hvalue := hq 1
        rw [show qs (1 : Fin 3) = target from rfl] at hvalue
        simpa only [consTermRename,emptyRename] using hvalue
      · have hvalue := hq 2
        rw [show qs (2 : Fin 3) = step from rfl] at hvalue
        simpa only [consTermRename,emptyRename] using hvalue
  have hr := checkerRecover data r.oldStep (x.relabel j) (y.relabel j)
    (certificate.relabel j) (ys 0) (ys 1) (ys 2) (parameter.relabel j) hf he'
  have hw' := renameInto hw j Delta hj
  rw [windowRename] at hw'
  have hn' := renameInto hn j Delta hj
  simp only [graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hn'
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at ht'
  apply OriginalNeutralQuotientRawProof.atRaw p (x.relabel j) (y.relabel j)
    (certificate.relabel j) (ys 0) (ys 1) (ys 2) (parameter.relabel j)
    (typeCode.relabel j) (psi.relabel j) hf hr hw' hn' ht'
  · have hc := renameInto hbottomImp j Delta hj
    change Nonempty (Derivation body Delta
      (((graph1 BottomRepresentative.bottomCode y typeCode).relabel j).imp (psi.relabel j))) at hc
    rw [graph1Rename] at hc
    obtain ⟨hc⟩ := withHyp hc (graph1 BottomRepresentative.bottomCode (y.relabel j) (typeCode.relabel j))
    exact ⟨Derivation.implicationElimination hc (Derivation.hypothesis List.mem_cons_self)⟩
  · intro gamma q Theta hq S T K state d e arrow f g a k child F G A recovered
    have hinc : ∀ h ∈ Gamma, h.relabel (q ∘ j) ∈ Theta := by
      intro h hh
      simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
        hq (h.relabel j) (hj h hh)
    simp only [Term.relabel_relabel] at recovered
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      next gamma (q ∘ j) Theta hinc S T K state d e arrow f g a k child F G A recovered

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientProof.actualOriginalNeutralQuotientEdgeElimination
