module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathFirstStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationEdgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open UniformCertificateCompletion OriginalNonLambdaApplicationPath OriginalNonLambdaApplicationPathTargets
open OriginalNonLambdaApplicationPathSyntaxProof

/-- Apply the non-lambda rule once, at the original first quotient edge.
The entire original first-entry record and its reflexive suffix are retained
under every continuation renaming, including a possible later beta step. -/
theorem actualOriginalNonLambdaApplicationPositivePathElimination :
    ActualOriginalNonLambdaApplicationPositivePathElimination := by
  intro p
  dsimp only
  intro body alpha Gamma arrow d e function argument x y pathCode parameter psi
    hi hj hn hp bottom next
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  apply OriginalNonLambdaApplicationPathFirstStepProof.actualOriginalPositivePathFirstStepElimination
    data r.oldStep body alpha Gamma x y pathCode parameter psi hp
  intro beta j Delta hinc raw tail vertex certificate hfirst
  have hi' := renameInto hi j Delta hinc
  rw [OriginalNeutralApplicationSyntaxProof.inputPremisesRename] at hi'
  have hj' := renameInto hj j Delta hinc
  rw [applicationGraphRename] at hj'
  have hn' := renameInto hn j Delta hinc
  rw [OriginalNonLambdaApplicationSyntaxProof.nonLambdaRename] at hn'
  have he := andLeft (andRight (andRight hfirst))
  apply OriginalNonLambdaApplicationEdgeProof.actualOriginalNonLambdaApplicationEdgeElimination p
    body beta Delta (arrow.relabel j) (d.relabel j) (e.relabel j)
    (function.relabel j) (argument.relabel j) (x.relabel j) vertex certificate
    (parameter.relabel j) (psi.relabel j) hi' hj' hn' he
  · exact bottom beta j Delta hinc raw tail vertex certificate hfirst
  · intro gamma q Theta hq S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument
      rawStep child functionOut targetFunctionOut canonicalArgument argumentOut hrecovered
    have hfirst' := renameInto hfirst q Theta hq
    rw [firstStepRename] at hfirst'
    simp only [Term.relabel_relabel] at hfirst' hrecovered
    have hcomp : ∀ h ∈ Gamma, h.relabel (q ∘ j) ∈ Theta := by
      intro h hh
      simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
        hq (h.relabel j) (hinc h hh)
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      next gamma (q ∘ j) Theta hcomp (raw.relabel q) (tail.relabel q)
        (vertex.relabel q) (certificate.relabel q) hfirst'
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
        functionOut targetFunctionOut canonicalArgument argumentOut hrecovered

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathProof.actualOriginalNonLambdaApplicationPositivePathElimination
