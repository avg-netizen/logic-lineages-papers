module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalApplicationSidecar OriginalCanonicalApplicationInversionTargets
open OriginalPairedCanonicalApplicationEliminationTargets
open OriginalPairedCanonicalApplicationEliminationSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)

/-- Two genuine original existential eliminations bind both constructor
records. Their context inclusions and variable maps are composed explicitly;
only then is paired component coherence applied to the common actual output. -/
theorem actualOriginalPairedCanonicalApplicationElimination :
    ActualOriginalPairedCanonicalApplicationElimination := by
  intro body data window alpha Delta input input' out parameter psi
  dsimp only
  intro hw hw' hv hv' ht ht' hn hn' next
  apply OriginalCanonicalApplicationInversionProof.actualOriginalCanonicalApplicationElimination
    body (selectedData data window) alpha Delta input out parameter psi hv ht hn
  intro beta j Theta hj arrow d e fp ap fn arg functionOut argumentOut rebuilt hr
  have hv1 := renameInto hv' j Theta hj
  have ht1 := renameInto ht' j Theta hj
  have hn1 := renameInto hn' j Theta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv1
  simp only [OriginalConstructorShapeSyntaxProof.tagGraphRename,positionTermRename] at ht1
  rw [foldGraphRename] at hn1
  apply OriginalCanonicalApplicationInversionProof.actualOriginalCanonicalApplicationElimination
    body (selectedData data window) beta Theta (input'.relabel j) (out.relabel j)
    (parameter.relabel j) (psi.relabel j) hv1 ht1 hn1
  intro gamma q Xi hq arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt' hr'
  have hinc : ∀ h ∈ Delta, h.relabel (q ∘ j) ∈ Xi := by
    intro h hh
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      hq (h.relabel j) (hj h hh)
  have hr1 := renameInto hr q Xi hq
  rw [recoveredRename] at hr1
  simp only [Term.relabel_relabel] at hr1 hr'
  have hw2 := renameInto hw (q ∘ j) Xi hinc
  have hw2' := renameInto hw' (q ∘ j) Xi hinc
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw2 hw2'
  have hv2 := renameInto hv (q ∘ j) Xi hinc
  have hv2' := renameInto hv' (q ∘ j) Xi hinc
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv2 hv2'
  have hn2 := renameInto hn (q ∘ j) Xi hinc
  have hn2' := renameInto hn' (q ∘ j) Xi hinc
  rw [foldGraphRename] at hn2 hn2'
  have both := pairRecovered data window
    (arrow.relabel q) (d.relabel q) (e.relabel q) (fp.relabel q) (ap.relabel q)
    (fn.relabel q) (arg.relabel q) (functionOut.relabel q) (argumentOut.relabel q) (rebuilt.relabel q)
    arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt'
    (input.relabel (q ∘ j)) (input'.relabel (q ∘ j)) (out.relabel (q ∘ j)) (parameter.relabel (q ∘ j))
    hw2 hw2' hv2 hv2' hn2 hn2' hr1 hr'
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
    next gamma (q ∘ j) Xi hinc
      (arrow.relabel q) (d.relabel q) (e.relabel q) (fp.relabel q) (ap.relabel q)
      (fn.relabel q) (arg.relabel q) (functionOut.relabel q) (argumentOut.relabel q) (rebuilt.relabel q)
      arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt' both

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationProof.actualOriginalPairedCanonicalApplicationElimination
