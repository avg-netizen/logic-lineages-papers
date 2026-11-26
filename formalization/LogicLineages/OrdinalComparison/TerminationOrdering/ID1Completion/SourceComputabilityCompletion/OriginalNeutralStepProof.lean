module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepInverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableEndpointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion ClaudeSupervisedCompletion

/-- The original checker supplies its state and branch witnesses internally.
The final tuple's proved neutral law discharges its unchanged zero-guard
leaf into literal same-type bottom. The recovered peeled branch retains
every original witness and the SAME full accepted child step. -/
theorem actualOriginalNeutralStepElimination :
    OriginalNeutralStepTargets.ActualOriginalNeutralStepElimination := by
  intro p
  dsimp only
  intro body alpha Gamma S T K parameter typeCode psi hstep hwindow hneutral htype hbottom hpeeled
  let r := OriginalVariableRepresentative.refineInputs (OriginalNeutralLeaf.refineInputs p)
  let data := OuterSelection.data r.base r.window
  have hcontinuation : Nonempty (Derivation body Gamma
      ((graph1 BottomRepresentative.bottomCode T typeCode).imp psi)) := by
    obtain ⟨hbottom⟩ := hbottom
    exact ⟨Derivation.implicationIntroduction hbottom⟩
  apply OriginalSelectedStepInverseProof.actualSelectedStepElimination
    body data r.oldStep alpha Gamma S T K parameter psi hstep ?_ hpeeled
  intro beta j Delta hj state hunpeeled
  have hw := renameInto hwindow j Delta hj
  have hn := renameInto hneutral j Delta hj
  have ht := renameInto htype j Delta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw
  simp only [graph1Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hn
  rw [graph1Rename] at ht
  have hresult : Nonempty (Derivation body Delta
      (graph1 BottomRepresentative.bottomCode (T.relabel j) (typeCode.relabel j))) := by
    obtain ⟨hlaw⟩ := OriginalNeutralVariableProof.finalNeutralLaw p
      body beta Delta (S.relabel j) (T.relabel j) (K.relabel j)
      (parameter.relabel j) state (typeCode.relabel j)
    obtain ⟨hp⟩ := andIntro
      (andRight (andRight (andRight hunpeeled)))
      (andIntro (andLeft hunpeeled)
        (andIntro hw (andIntro hn (andIntro (andLeft (andRight hunpeeled)) ht))))
    exact ⟨Derivation.implicationElimination hlaw hp⟩
  have hcontinuation' := renameInto hcontinuation j Delta hj
  change Nonempty (Derivation body Delta
    (((graph1 BottomRepresentative.bottomCode T typeCode).relabel j).imp (psi.relabel j)))
      at hcontinuation'
  rw [graph1Rename] at hcontinuation'
  obtain ⟨hcontinuation'⟩ := hcontinuation'
  obtain ⟨hresult⟩ := hresult
  exact ⟨Derivation.implicationElimination hcontinuation' hresult⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralStepProof
