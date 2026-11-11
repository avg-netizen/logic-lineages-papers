module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion
open OriginalSourceNeutralApplicationObjectPathSyntaxProof

/-- Reconstruct the first application vertex as an accepted original
Object application. Every original prefix, quotient witness and suffix is
retained; no claim is made about the final endpoint's constructor shape. -/
theorem actualOriginalSourceNeutralApplicationObjectPositivePathElimination :
    OriginalSourceNeutralApplicationObjectPathTargets.ActualOriginalSourceNeutralApplicationObjectPositivePathElimination := by
  intro n arity p hcal
  dsimp only
  intro symbols S table hS
  intro alpha Gamma sigma tau F A X Y witness psi hd ha hn hc bottom next
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let body := SourcePresentation.sourceBody (GlobalSourcePackage.source r) context
  apply OriginalSourceNeutralApplicationPathProof.actualOriginalSourceNeutralApplicationPositivePathElimination
    n arity p hcal symbols S table hS alpha Gamma sigma tau F A X Y witness psi hd ha hn hc bottom
  intro beta j Delta hinc gammaCode function argument x y parameter raw tail vertex certificate hprefix
    Sraw T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
    functionOut targetFunctionOut canonicalArgument argumentOut haligned
  have hinput := andLeft (andLeft hprefix)
  have htarget := andRight (andRight (andRight (andRight (andRight (andRight (andRight haligned))))))
  apply OriginalSourceApplicationReconstructionProof.actualOriginalSourceApplicationReconstruction
    data r.window r.oldComp r.oldVertex r.oldResult context
    body beta Delta sigma tau (F.relabel j) (A.relabel j) (X.relabel j)
    gammaCode function argument x parameter targetFunctionOut vertex (psi.relabel j)
    hinput (andLeft htarget) (andRight htarget)
  intro gamma q Theta hq G V hobjects
  have hprefix' := renameInto hprefix q Theta hq
  rw [OriginalSourceNeutralApplicationPathSyntaxProof.recoveredPrefixRename] at hprefix'
  have haligned' := renameInto haligned q Theta hq
  rw [alignedRecoveredRename] at haligned'
  simp only [Term.relabel_relabel,numeralRename] at hprefix' haligned' hobjects
  have hinc2 : ∀ h ∈ Gamma, h.relabel (q ∘ j) ∈ Theta := by
    intro h hh
    simpa only [formulaRelabelComposition] using hq (h.relabel j) (hinc h hh)
  simpa only [formulaRelabelComposition] using
    next gamma (q ∘ j) Theta hinc2
      (gammaCode.relabel q) (function.relabel q) (argument.relabel q)
      (x.relabel q) (y.relabel q) (parameter.relabel q)
      (raw.relabel q) (tail.relabel q) (vertex.relabel q) (certificate.relabel q) hprefix'
      (Sraw.relabel q) (T.relabel q) (K.relabel q) (state.relabel q)
      (rawD.relabel q) (rawE.relabel q) (rawArrow.relabel q)
      (rawFunction.relabel q) (rawTarget.relabel q) (rawArgument.relabel q)
      (rawStep.relabel q) (child.relabel q) (functionOut.relabel q)
      (targetFunctionOut.relabel q) (canonicalArgument.relabel q) (argumentOut.relabel q)
      haligned' G V hobjects

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathProof.actualOriginalSourceNeutralApplicationObjectPositivePathElimination
