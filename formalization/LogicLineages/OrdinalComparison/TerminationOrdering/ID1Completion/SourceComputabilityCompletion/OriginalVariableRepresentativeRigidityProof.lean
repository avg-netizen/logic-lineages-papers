module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeFoldOpeningProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRigidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableRepresentative OriginalVariableRepresentativeMarkProof
open OriginalVariableRepresentativeFoldOpeningProof
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Identify the supplied full-fold output with the actual leaf output.
The old run/leaf closure and functionality apply even when that output is zero. -/
theorem closedLeafGraph (data : Data) (out input parameter : OTerm α)
    (hz : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard data)) z input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter))) :
    Nonempty (Derivation body Gamma (graph2 (leaf data) out input parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply programCases (leaf data) xs _
  intro β j Delta produced hj hl
  rw [graph2Rename]
  have hz' := renameInto hz j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [graph2Rename,zRelabel] at hz'
  rw [foldGraphRename] at hn'
  simp only [xs,consTermRename,emptyRename] at hl
  have hc := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    (rootGuard data) (leaf data) (combine data) (input.relabel j) produced (parameter.relabel j) hz' hl
  have he := valueUnique (foldN data) produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (andRight hc) hn'
  exact outputTransport (leaf data) produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hl

theorem closedRigidity (data : Data) (window : Program 1) (out input parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity (selectedData data window)) (suc z) input parameter)))
    (hz : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (rootGuard (selectedData data window))) z input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out input parameter)))
    (hvar : Nonempty (Derivation body Gamma
      (graph1 OriginalConstructorLeaf.variableTest (suc z) input ⊔
        graph1 OriginalConstructorLeaf.variableTest (suc z) out))) :
    Nonempty (Derivation body Gamma (equal out input)) := by
  have hl := closedLeafGraph (selectedData data window) out input parameter hz hn
  apply programCases variableMark (Fin.cons input Fin.elim0) _
  intro β j Delta mark hj hm
  simp only [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
  have hw' := renameInto hw j Delta hj
  have hv' := renameInto hv j Delta hj
  have hl' := renameInto hl j Delta hj
  have hvar' := renameInto hvar j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  rw [graph2Rename] at hl'
  simp only [InternalBetaBoundaryProof.supRename,graph1Rename,sucRelabel,zRelabel] at hvar'
  have hm' : Nonempty (Derivation body Delta (markGraph mark (input.relabel j))) := by
    simpa only [markGraph,graph1,consTermRename,emptyRename] using hm
  have hout := selectedMarked data window (out.relabel j) (input.relabel j) (parameter.relabel j)
    mark hw' hv' hl' hm'
  exact eitherVariableRigid mark (input.relabel j) (out.relabel j) hvar' hm' hout

/-- Closed roots use the literal selected representative. Open roots have
actual tag-two constructors at input and rebuilt output, hence mark zero.
This proves reverse as well as forward rigidity without a new fold induction. -/
theorem fullFoldRigidity (data : Data) (window : Program 1) :
    FullFoldRigidity (selectedData data window) window := by
  intro body α Delta out input typeCode parameter
  let selected := selectedData data window
  let A := windowGraph window input parameter ⊓
    (sourcePremises selected input typeCode parameter ⊓
      (foldGraph selected out input parameter ⊓
        (graph1 OriginalConstructorLeaf.variableTest (suc z) input ⊔
          graph1 OriginalConstructorLeaf.variableTest (suc z) out)))
  have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw := andLeft hA
  have hv := andLeft (andLeft (andRight hA))
  have hn := andLeft (andRight (andRight hA))
  have hvar := andRight (andRight (andRight hA))
  have hresult : Nonempty (Derivation body (A :: Delta) (equal out input)) := by
    let P := graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard selected))
      (suc z) input parameter
    apply formulaCases P
    · have hp : Nonempty (Derivation body (P :: A :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hm := openingMarks data window out input parameter (withHyp hw P) (withHyp hn P) hp
      simpa only [equalEqn] using
        (eitherVariableRigid z input out (withHyp hvar P) (andRight hm) (andLeft hm))
    · have hz : Nonempty (Derivation body (P.not :: A :: Delta)
          (graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard selected)) z input parameter)) :=
        InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
          (Fin.cons input (Fin.cons parameter Fin.elim0))
          (show Nonempty (Derivation body (P.not :: A :: Delta) P.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      exact closedRigidity data window out input parameter (withHyp hw P.not) (withHyp hv P.not)
        hz (withHyp hn P.not) (withHyp hvar P.not)
  obtain ⟨hresult⟩ := hresult
  exact ⟨Derivation.implicationIntroduction hresult⟩

theorem actualOriginalSelectedVariableRepresentativeRigidity :
    OriginalVariableRepresentativeTargets.ActualOriginalSelectedVariableRepresentativeRigidity := by
  intro data window
  exact ⟨OriginalVariableRepresentativeSelectedProof.selectedMarkPreservation data window,
    fullFoldRigidity data window⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRigidityProof
