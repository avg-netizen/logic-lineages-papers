module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationInputsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalComputabilityDownwardSyntaxProof (domainRename)
open InternalComputabilityApplicationSyntaxProof (acceptedRename)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalSourceNeutralApplication UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original totality binds the shared Gamma, requested raw coordinates,
symbolic parameter and actual vertex before the accepted application is
inverted. The duplicate queries in the existing source-lift supplier are
unused; no extra mathematical premise enters the public continuation. -/
theorem eliminate (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window)
    (oldComp : JointGammaComputability.Data) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) :
    ApplicationInputs (OuterSelection.data base window) window
      (OuterSelection.computability oldComp base window oldVertex oldResult)
      (OrdinaryArithmeticQuotient.contextCode symbols S table) := by
  intro body alpha Gamma sigma tau functionObject argumentObject outputObject psi hd hjObject next
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  apply OuterInputCasesProof.inputCases (OuterSelection.data base window) window oldVertex
    context sigma tau functionObject functionObject argumentObject psi
  intro beta j gammaCode function _otherFunction argument parameter out _otherOut Delta hj
    hg hf _hother ha hp hv _hotherV
  have hd' := renameInto hd j Delta hj
  rw [domainRename] at hd'
  have hjObject' := renameInto hjObject j Delta hj
  simp only [acceptedRename,numeralRename] at hjObject'
  have hr := OriginalSourceNeutralApplicationInputsProof.recoveredAt n arity base hc window hw
    oldComp oldVertex oldResult symbols S table hS sigma tau
    (functionObject.relabel j) (argumentObject.relabel j) (outputObject.relabel j)
    gammaCode function argument out parameter hg hf ha hp hd' hjObject' hv
  exact next beta j Delta hj gammaCode function argument out parameter hr

theorem actualOriginalSourceNeutralApplicationInputs :
    OriginalSourceNeutralApplicationTargets.ActualOriginalSourceNeutralApplicationInputs := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS
  let r := OriginalApplicationSidecar.finalInputs p
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity p hp
  exact eliminate n arity r.base hr.1 r.window hr.2.1 r.oldComp r.oldVertex r.oldResult
    symbols S table hS

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationProof.actualOriginalSourceNeutralApplicationInputs
