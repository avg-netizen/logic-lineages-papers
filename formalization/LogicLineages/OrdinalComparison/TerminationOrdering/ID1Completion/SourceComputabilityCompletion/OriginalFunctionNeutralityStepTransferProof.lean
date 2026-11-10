module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFullFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof UniformCertificateCompletion

/-- The actual final fold's proved reflection supplies the original raw
neutral premise. The existing raw-step eliminator then retains its original
certificate, parameter, endpoint and both continuations on this SAME tuple. -/
theorem actualOriginalFunctionNeutralityStepElimination :
    OriginalFunctionNeutralityStepTransferTargets.ActualOriginalFunctionNeutralityStepElimination := by
  intro p
  dsimp only
  intro body alpha Gamma S T K out parameter typeCode psi
    hstep hwindow hsource hfold hneutral htype hbottom hpeeled
  let r := OriginalFunctionNeutrality.finalInputs p
  let data := OuterSelection.data r.base r.window
  have hfull : OriginalFunctionNeutrality.FullFoldMarkPreservation data r.window := by
    change OriginalFunctionNeutrality.FullFoldMarkPreservation
      (OuterSelection.data (OriginalFunctionNeutrality.finalInputs p).base
        (OriginalFunctionNeutrality.finalInputs p).window)
      (OriginalFunctionNeutrality.finalInputs p).window
    rw [OriginalFunctionNeutralityInputProof.finalSelectedData,
      OriginalFunctionNeutralityInputProof.finalWindow]
    exact OriginalFunctionNeutralityFullFoldProof.fullFoldMarkPreservation p.base p.window
  obtain ⟨hlaw⟩ := hfull body alpha Gamma out S typeCode parameter InternalOriginalStepGuard.one
  obtain ⟨hp⟩ := andIntro hwindow (andIntro hsource hfold)
  have hboth := Derivation.implicationElimination hlaw hp
  obtain ⟨hneutral⟩ := hneutral
  have hraw : Nonempty (Derivation body Gamma
      (graph1 OriginalNeutralLeaf.neutralTest InternalOriginalStepGuard.one S)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hboth) hneutral⟩
  exact OriginalNeutralStepProof.actualOriginalNeutralStepElimination
    (OriginalConstructorShape.refineInputs (OriginalFunctionNeutrality.refineInputs p))
    body alpha Gamma S T K parameter typeCode psi
    hstep hwindow hraw htype hbottom hpeeled

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferProof
