module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationIffProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalIndexedObserverIteration
open SourceComputabilityCompletion.OriginalIndexedObserverIterationSyntaxProof SourceComputabilityCompletion.OriginalIndexedObserverIterationStepProof
open SourceComputabilityCompletion.OriginalIndexedObserverIterationProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalParameterizedNumericIteration InternalParameterizedNumericIterationSyntaxProof
open InternalParameterizedBoundedDescentNormalizerSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalIndexedObserverDefinitions (ActualRange)
open OriginalIndexedObserverRangeSyntaxProof (rangeRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem indicatorIff (test : Program 3) (indicator x y vx vy parameter cutoff : OTerm α)
    (hx : Nonempty (Derivation body Gamma (graph3 test vx cutoff x parameter)))
    (hy : Nonempty (Derivation body Gamma (graph3 test vy cutoff y parameter)))
    (he : Nonempty (Derivation body Gamma (eqn vx vy))) :
    Nonempty (Derivation body Gamma ((graph3 test indicator cutoff x parameter).iff (graph3 test indicator cutoff y parameter))) := by
  have hf : Nonempty (Derivation body Gamma
      ((graph3 test indicator cutoff x parameter).imp (graph3 test indicator cutoff y parameter))) := by
    let P := graph3 test indicator cutoff x parameter
    obtain ⟨hix⟩ := valueUnique test indicator vx (Fin.cons cutoff (Fin.cons x (Fin.cons parameter Fin.elim0)))
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hx P)
    obtain ⟨hxy⟩ := withHyp he P
    obtain ⟨d⟩ := outputTransport test vy indicator (Fin.cons cutoff (Fin.cons y (Fin.cons parameter Fin.elim0)))
      ⟨symm (trans hix hxy)⟩ (withHyp hy P)
    exact ⟨Derivation.implicationIntroduction d⟩
  have hb : Nonempty (Derivation body Gamma
      ((graph3 test indicator cutoff y parameter).imp (graph3 test indicator cutoff x parameter))) := by
    let P := graph3 test indicator cutoff y parameter
    obtain ⟨hiy⟩ := valueUnique test indicator vy (Fin.cons cutoff (Fin.cons y (Fin.cons parameter Fin.elim0)))
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hy P)
    obtain ⟨hxy⟩ := withHyp he P
    obtain ⟨d⟩ := outputTransport test vx indicator (Fin.cons cutoff (Fin.cons x (Fin.cons parameter Fin.elim0)))
      ⟨symm (trans hiy (symm hxy))⟩ (withHyp hx P)
    exact ⟨Derivation.implicationIntroduction d⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction hf hb⟩

theorem repeatIff (data : Data) (closure : Closure data) (supply : Preservation data) (out count input parameter indicator cutoff : OTerm α)
    (hRange : Nonempty (Derivation body Gamma (ActualRange cutoff parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data) out count input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph data indicator out parameter cutoff).iff (markGraph data indicator input parameter cutoff))) := by
  apply programCases data.observer (Fin.cons cutoff (Fin.cons input (Fin.cons parameter Fin.elim0))) _
  intro β j Delta value hj hv
  change Nonempty (Derivation body Delta
    (((graph3 data.observer indicator cutoff out parameter).relabel j).iff
      ((graph3 data.observer indicator cutoff input parameter).relabel j)))
  rw [graph3Rename, graph3Rename]
  have hv' : Nonempty (Derivation body Delta (markGraph data value (input.relabel j) (parameter.relabel j) (cutoff.relabel j))) := by
    simpa only [markGraph,graph3,consTermRename,emptyRename] using hv
  have hRange' := renameInto hRange j Delta hj
  rw [rangeRename] at hRange'
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hr' := renameInto hr j Delta hj
  rw [parameterRepeatRename] at hr'
  have hout := repeatForward data closure supply (count.relabel j) (input.relabel j) (out.relabel j)
    (parameter.relabel j) value (cutoff.relabel j) hr' ha' hRange' hv'
  exact indicatorIff data.observer
    (indicator.relabel j) (out.relabel j) (input.relabel j) value value (parameter.relabel j) (cutoff.relabel j) hout hv' ⟨refl value⟩


theorem actualIndexedObserverIteration : OriginalIndexedObserverIterationTargets.ActualIndexedObserverIteration := by
  intro data closure supply body alpha Delta out count input parameter mark cutoff
  let A := repeatGraph (step data) out count input parameter ⊓
    (activeGraph data input parameter ⊓ ActualRange cutoff parameter)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := repeatIff data closure supply out count input parameter mark cutoff
    (andRight (andRight h)) (andLeft (andRight h)) (andLeft h)
  exact ⟨Derivation.implicationIntroduction hi⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationIffProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationIffProof

#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationIffProof.actualIndexedObserverIteration
