module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeFullFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The paid shape-selected leaf is exactly S0's leaf, before the sidecar.
Only the original window and source validity are used. -/
theorem leafMarkIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalConstructorShape.markGraph value out).iff (OriginalConstructorShape.markGraph value input))) := by
  exact OriginalConstructorShapeFullFoldProof.leafMarkIff
    (OriginalFunctionNeutrality.baseData data window) window out input parameter value hw hv hl

/-- A closed root's actual C output is an actual S0 leaf output. Internal
Program totality and graph functionality eliminate the auxiliary value. -/
theorem closedLeafGraph (data : Data) (window : Program 1)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter)))
    (hz : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) z input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (originalData data window)) out input parameter)) := by
  apply programCases (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta produced hj hl
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hl
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hz' := renameInto hz j Theta hj
  simp only [graph2Rename,zRelabel] at hz'
  have closed := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))
    (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    InternalParameterizedCanonicalResultFold.rawApplicationAt
    (input.relabel j) produced (parameter.relabel j) hz' hl
  have he := valueUnique (fold data window) produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (andRight closed) hc'
  exact outputTransport (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hl

theorem rejectedMarkIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter)))
    (hz : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) z input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalConstructorShape.markGraph value out).iff (OriginalConstructorShape.markGraph value input))) :=
  leafMarkIff data window out input parameter value hw hv (closedLeafGraph data window out input parameter hc hz)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkLeafProof
