module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSelectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalStructuralKeyIteration
open SourceComputabilityCompletion.OriginalStructuralKeyIterationSyntaxProof SourceComputabilityCompletion.OriginalStructuralKeyIterationStepProof
open SourceComputabilityCompletion.OriginalStructuralKeyIterationProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalParameterizedNumericIteration InternalParameterizedNumericIterationSyntaxProof
open InternalParameterizedBoundedDescentNormalizerSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem indicatorIff (test : Program 2) (indicator x y vx vy parameter : OTerm α)
    (hx : Nonempty (Derivation body Gamma (graph2 test vx x parameter)))
    (hy : Nonempty (Derivation body Gamma (graph2 test vy y parameter)))
    (he : Nonempty (Derivation body Gamma (eqn vx vy))) :
    Nonempty (Derivation body Gamma ((graph2 test indicator x parameter).iff (graph2 test indicator y parameter))) := by
  have hf : Nonempty (Derivation body Gamma
      ((graph2 test indicator x parameter).imp (graph2 test indicator y parameter))) := by
    let P := graph2 test indicator x parameter
    obtain ⟨hix⟩ := valueUnique test indicator vx (Fin.cons x (Fin.cons parameter Fin.elim0))
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hx P)
    obtain ⟨hxy⟩ := withHyp he P
    obtain ⟨d⟩ := outputTransport test vy indicator (Fin.cons y (Fin.cons parameter Fin.elim0))
      ⟨symm (trans hix hxy)⟩ (withHyp hy P)
    exact ⟨Derivation.implicationIntroduction d⟩
  have hb : Nonempty (Derivation body Gamma
      ((graph2 test indicator y parameter).imp (graph2 test indicator x parameter))) := by
    let P := graph2 test indicator y parameter
    obtain ⟨hiy⟩ := valueUnique test indicator vy (Fin.cons y (Fin.cons parameter Fin.elim0))
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hy P)
    obtain ⟨hxy⟩ := withHyp he P
    obtain ⟨d⟩ := outputTransport test vx indicator (Fin.cons x (Fin.cons parameter Fin.elim0))
      ⟨symm (trans hiy (symm hxy))⟩ (withHyp hx P)
    exact ⟨Derivation.implicationIntroduction d⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction hf hb⟩

theorem repeatIff (data : Data) (closure : Closure data) (supply : Preservation data) (out count input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data) out count input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph data indicator out parameter).iff (markGraph data indicator input parameter))) := by
  apply programCases data.observer (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta value hj hv
  change Nonempty (Derivation body Delta
    (((graph2 data.observer indicator out parameter).relabel j).iff
      ((graph2 data.observer indicator input parameter).relabel j)))
  rw [graph2Rename, graph2Rename]
  have hv' : Nonempty (Derivation body Delta (markGraph data value (input.relabel j) (parameter.relabel j))) := by
    simpa only [markGraph,graph2,consTermRename,emptyRename] using hv
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hr' := renameInto hr j Delta hj
  rw [parameterRepeatRename] at hr'
  have hout := repeatForward data closure supply (count.relabel j) (input.relabel j) (out.relabel j)
    (parameter.relabel j) value hr' ha' hv'
  exact indicatorIff data.observer
    (indicator.relabel j) (out.relabel j) (input.relabel j) value value (parameter.relabel j) hout hv' ⟨refl value⟩


theorem selectedIff (data : Data) (validity : Validity data) (closure : Closure data) (supply : Preservation data) (out input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.fallbackRepresentative data.representative data.valid) out input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph data indicator out parameter).iff (markGraph data indicator input parameter))) := by
  have hv := validity body α Gamma input parameter ha
  have hn := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover
    data.representative data.valid out input parameter hr hv
  have hrepeat := normalizerRecover data.representative data.valid
    out input parameter hn
  exact repeatIff data closure supply out (suc input) input parameter indicator ha hrepeat



end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSelectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSelectedProof
