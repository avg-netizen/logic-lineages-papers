module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldSyntaxProof
open OriginalCanonicalApplicationInversionTargets

/-- The tag-only opening recovers the original constructors. Parent validity
then pays the actual canonical guard, and the queried child folds and rebuilt
application supply the unchanged final representative graph. -/
theorem actualOriginalCanonicalApplicationElimination :
    ActualOriginalCanonicalApplicationElimination := by
  intro body data α Gamma input out parameter psi hv ht hn next
  let tagTest := InternalApplicationStepPeel.same OriginalConstructorShape.tag (two 1)
  let xs : Fin 1 → OTerm α := Fin.cons input Fin.elim0
  let xp : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  have htag : Nonempty (Derivation body Gamma (programGraph tagTest (suc z) xs)) :=
    sameAccept OriginalConstructorShape.tag (two 1) positionTerm xs ht (twoValue xs)
  have hopen : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP (InternalLessThan.constantOne 2))
        (suc z) input parameter)) := by
    exact conjunctionAccept _ _ xp
      (InternalParameterizedApplicationResultStackWiringProof.liftValue tagTest (suc z) input parameter htag)
      (InternalLessThanSupportProof.oneConstantValue xp)
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (InternalLessThan.constantOne 2) input parameter psi hopen
  intro β j Delta payload arrow d e fp ap fn arg hj hc _ _ _ _ _ _
  have hv' := renameInto hv j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hv'
  rw [foldGraphRename] at hn'
  apply atConstructors data arrow d e fp ap fn arg (input.relabel j) (out.relabel j)
    (parameter.relabel j) (psi.relabel j) hc hv' hn'
  intro γ q Theta hq functionOut argumentOut rebuilt recovered
  have hinc : ∀ h ∈ Gamma, h.relabel (q ∘ j) ∈ Theta := by
    intro h hh
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      hq (h.relabel j) (hj h hh)
  simp only [Term.relabel_relabel] at recovered
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
    next γ (q ∘ j) Theta hinc (arrow.relabel q) (d.relabel q) (e.relabel q)
      (fp.relabel q) (ap.relabel q) (fn.relabel q) (arg.relabel q)
      functionOut argumentOut rebuilt recovered

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
