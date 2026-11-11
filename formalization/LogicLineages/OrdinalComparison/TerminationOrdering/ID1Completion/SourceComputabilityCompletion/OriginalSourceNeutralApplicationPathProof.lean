module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open UniformCertificateCompletion OriginalSourceNeutralApplicationPath
open OriginalSourceNeutralApplicationPathSyntaxProof
open OriginalSourceNeutralApplicationFieldsProof

/-- Open the original accepted Object application and its actual positive
source certificate. Inversion applies only at the first edge; the original
requested endpoint remains connected by the exact reflexive suffix. -/
theorem actualOriginalSourceNeutralApplicationPositivePathElimination :
    OriginalSourceNeutralApplicationPathTargets.ActualOriginalSourceNeutralApplicationPositivePathElimination := by
  intro n arity p hcal
  dsimp only
  intro symbols S table hS
  intro alpha Gamma sigma tau F A X Y witness psi hd ha hn hc bottom next
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let body := SourcePresentation.sourceBody (GlobalSourcePackage.source r) context
  apply OriginalSourceNeutralApplicationProof.actualOriginalSourceNeutralApplicationInputs
    n arity p hcal symbols S table hS body alpha Gamma sigma tau F A X psi hd ha
  intro beta j Delta hinc gammaCode function argument x parameter hrecovered
  have hn' := renameInto hn j Delta hinc
  rw [OriginalSourceNeutralApplicationSyntaxProof.nonLambdaObjectRename] at hn'
  have hc' := renameInto hc j Delta hinc
  rw [InternalComputabilityDownwardSyntaxProof.certificateRename] at hc'
  apply programCases InternalUnpair.right (Fin.cons (Y.relabel j) Fin.elim0) (psi.relabel j)
  intro gamma q Theta y hq hy
  simp only [consTermRename,emptyRename] at hy
  have hr' := renameInto hrecovered q Theta hq
  rw [OriginalSourceNeutralApplicationSyntaxProof.recoveredRename] at hr'
  have hn'' := renameInto hn' q Theta hq
  rw [OriginalSourceNeutralApplicationSyntaxProof.nonLambdaObjectRename] at hn''
  have hc'' := renameInto hc' q Theta hq
  rw [InternalComputabilityDownwardSyntaxProof.certificateRename] at hc''
  simp only [Term.relabel_relabel] at hr' hn'' hc'' hy
  rw [formulaRelabelComposition]
  have hinputs := OriginalSourceNeutralApplicationPathRawProof.atTargetCoordinates
    n arity p hcal symbols S table hS sigma tau
    (F.relabel (q ∘ j)) (A.relabel (q ∘ j)) (X.relabel (q ∘ j)) (Y.relabel (q ∘ j))
    (witness.relabel (q ∘ j)) (gammaCode.relabel q) (function.relabel q)
    (argument.relabel q) (x.relabel q) y (parameter.relabel q) hr' hn'' hc'' hy
  have hi := inputPremisesOf (andLeft hinputs)
  have hj := actualJOf (andLeft hinputs)
  have hnonlambda := andLeft (andRight (andRight hinputs))
  have hpositive := andRight (andRight (andRight (andRight (andRight hinputs))))
  have hinc2 : ∀ h ∈ Gamma, h.relabel (q ∘ j) ∈ Theta := by
    intro h hh
    simpa only [formulaRelabelComposition] using hq (h.relabel j) (hinc h hh)
  apply OriginalNonLambdaApplicationPathProof.actualOriginalNonLambdaApplicationPositivePathElimination
    p body gamma Theta (numeral (typeNumber (.arrow sigma tau)))
    (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (function.relabel q) (argument.relabel q) (x.relabel q) y
    (witness.relabel (q ∘ j)) (parameter.relabel q) (psi.relabel (q ∘ j))
    hi hj hnonlambda hpositive
  · intro delta k Xi hk raw tail vertex certificate hfirst
    have hinputs' := renameInto hinputs k Xi hk
    rw [pathInputsRename] at hinputs'
    simp only [Term.relabel_relabel] at hinputs' hfirst
    have hinc3 : ∀ h ∈ Gamma, h.relabel (k ∘ (q ∘ j)) ∈ Xi := by
      intro h hh
      simpa only [formulaRelabelComposition] using hk (h.relabel (q ∘ j)) (hinc2 h hh)
    simpa only [formulaRelabelComposition,numeralRename] using
      bottom delta (k ∘ (q ∘ j)) Xi hinc3 (gammaCode.relabel (k ∘ q))
        (function.relabel (k ∘ q)) (argument.relabel (k ∘ q)) (x.relabel (k ∘ q))
        (y.relabel k) (parameter.relabel (k ∘ q)) raw tail vertex certificate
        (andIntro hinputs' hfirst)
  · intro delta k Xi hk raw tail vertex certificate hfirst
      Sraw T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
      functionOut targetFunctionOut canonicalArgument argumentOut haligned
    have hinputs' := renameInto hinputs k Xi hk
    rw [pathInputsRename] at hinputs'
    simp only [Term.relabel_relabel] at hinputs' hfirst
    simp only [Term.relabel_relabel,numeralRename] at haligned
    have hinc3 : ∀ h ∈ Gamma, h.relabel (k ∘ (q ∘ j)) ∈ Xi := by
      intro h hh
      simpa only [formulaRelabelComposition] using hk (h.relabel (q ∘ j)) (hinc2 h hh)
    simpa only [formulaRelabelComposition] using
      next delta (k ∘ (q ∘ j)) Xi hinc3 (gammaCode.relabel (k ∘ q))
        (function.relabel (k ∘ q)) (argument.relabel (k ∘ q)) (x.relabel (k ∘ q))
        (y.relabel k) (parameter.relabel (k ∘ q)) raw tail vertex certificate
        (andIntro hinputs' hfirst)
        Sraw T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child
        functionOut targetFunctionOut canonicalArgument argumentOut haligned

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathProof.actualOriginalSourceNeutralApplicationPositivePathElimination
