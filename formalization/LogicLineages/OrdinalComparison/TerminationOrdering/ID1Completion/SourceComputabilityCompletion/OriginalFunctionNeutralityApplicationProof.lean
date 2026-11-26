module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalNeutralLeaf OriginalFunctionNeutralityApplicationValuesProof
open OriginalCanonicalApplicationInversionTargets
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFold (sourcePremises foldGraph validity)
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem neutralIffRename {beta : Type} (value out input : OTerm alpha) (j : alpha → beta) :
    ((graph1 neutralTest value out).iff (graph1 neutralTest value input)).relabel j =
      (graph1 neutralTest (value.relabel j) (out.relabel j)).iff
        (graph1 neutralTest (value.relabel j) (input.relabel j)) := by
  change ((graph1 neutralTest value out).relabel j).iff
    ((graph1 neutralTest value input).relabel j) = _
  rw [graph1Rename,graph1Rename]

/-- The SAME function-child fold preserves its actual root tag by the
already checked root-field theorem. Consequently the parent and its actual
rebuilt application have the same neutrality flag. The final selected-leaf
graph remains in Recovered and is not equated with the rebuilt input. -/
theorem recoveredNeutralityIff (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter value : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalConstructorShape.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (validity (OriginalConstructorShape.selectedData data window)) (suc z) input parameter)))
    (hr : Nonempty (Derivation body Delta
      (Recovered (OriginalConstructorShape.selectedData data window)
        arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 neutralTest value rebuilt).iff (graph1 neutralTest value input))) := by
  let selected := OriginalConstructorShape.selectedData data window
  have hc := andLeft hr
  have hfunction := andLeft (andRight (andRight hr))
  have hrebuilt := andLeft (andRight (andRight (andRight (andRight hr))))
  have hchildren := OriginalApplicationInverseValidityProof.sourceRecover selected
    arrow d e fp ap fn arg input parameter hc hv
  have hfnSource : Nonempty (Derivation body Delta (sourcePremises selected fn arrow parameter)) :=
    andIntro (andLeft (andRight hchildren))
      (pairLeft fn arrow fp (andLeft (andRight hc)))
  have hfnFold : Nonempty (Derivation body Delta (foldGraph selected functionOut fn parameter)) :=
    andRight (andLeft hfunction)
  have hfnWindow := BottomDescentStepProof.windowChange window (suc z) input fn parameter hw
  have hinput := applicationBackward d e fn arg fp ap input
    (pairRight fn arrow fp (andLeft (andRight hc)))
    (pairRight arg d ap (andLeft (andRight (andRight hc))))
    (andRight (andRight (andRight hc)))
  apply programCases OriginalConstructorShape.tag (Fin.cons fn Fin.elim0) _
  intro beta j Theta tag hj ht
  rw [neutralIffRename]
  simp only [consTermRename,emptyRename] at ht
  have htag : Nonempty (Derivation body Theta
      (OriginalConstructorShape.tagGraph tag (fn.relabel j))) := ht
  have hw' := renameInto hfnWindow j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hw'
  have hs' := renameInto hfnSource j Theta hj
  rw [sourcePremisesRename] at hs'
  have hn' := renameInto hfnFold j Theta hj
  rw [foldGraphRename] at hn'
  obtain ⟨hlaw⟩ := OriginalConstructorShapeRootFieldsProof.fullFoldRootFields
    data window body beta Theta (functionOut.relabel j) (fn.relabel j)
    (arrow.relabel j) (parameter.relabel j) tag z
  obtain ⟨hpre⟩ := andIntro hw' (andIntro hs' hn')
  have hfields := Derivation.implicationElimination hlaw hpre
  obtain ⟨htagProof⟩ := htag
  have houtputTag : Nonempty (Derivation body Theta
      (OriginalConstructorShape.tagGraph tag (functionOut.relabel j))) :=
    ⟨Derivation.implicationElimination
      (Derivation.conjunctionRight (Derivation.conjunctionLeft hfields)) htagProof⟩
  have hi' := renameInto hinput j Theta hj
  have hb' := renameInto hrebuilt j Theta hj
  rw [graph4Rename] at hi' hb'
  apply formulaCases (eqn tag (suc z))
  · let P := eqn tag (suc z)
    have he : Nonempty (Derivation body (P :: Theta) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BottomRepresentativeInternalProof.indicatorIff neutralTest
      (value.relabel j) (rebuilt.relabel j) (input.relabel j) z z
      (neutralAtLambda (d.relabel j) (e.relabel j) (functionOut.relabel j)
        (argumentOut.relabel j) (rebuilt.relabel j) tag (withHyp hb' P) (withHyp houtputTag P) he)
      (neutralAtLambda (d.relabel j) (e.relabel j) (fn.relabel j)
        (arg.relabel j) (input.relabel j) tag (withHyp hi' P) (withHyp ⟨htagProof⟩ P) he)
      ⟨refl z⟩
  · let P := (eqn tag (suc z)).not
    have he : Nonempty (Derivation body (P :: Theta) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BottomRepresentativeInternalProof.indicatorIff neutralTest
      (value.relabel j) (rebuilt.relabel j) (input.relabel j) (suc z) (suc z)
      (neutralAtNonlambda (d.relabel j) (e.relabel j) (functionOut.relabel j)
        (argumentOut.relabel j) (rebuilt.relabel j) tag (withHyp hb' P) (withHyp houtputTag P) he)
      (neutralAtNonlambda (d.relabel j) (e.relabel j) (fn.relabel j)
        (arg.relabel j) (input.relabel j) tag (withHyp hi' P) (withHyp ⟨htagProof⟩ P) he)
      ⟨refl (suc z)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationProof
