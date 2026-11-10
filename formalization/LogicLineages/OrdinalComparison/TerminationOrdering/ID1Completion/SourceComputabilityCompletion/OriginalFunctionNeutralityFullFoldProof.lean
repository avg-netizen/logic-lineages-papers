module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralitySelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRigidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFullFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalFunctionNeutrality
open OriginalConstructorShapeApplicationProof (iffCompose)
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalApplicationValidityClosure (applicationConstructors)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Apply the selected invariant to the literal final leaf of the canonical
fold. The original validator and symbolic window remain explicit. -/
theorem leafMarkIff (data : Data) (window : Program 1) (out input parameter value : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (validity (selectedData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (leaf (selectedData data window)) out input parameter))) :
    Nonempty (Derivation body Delta ((markGraph value out).iff (markGraph value input))) := by
  obtain ⟨h⟩ := OriginalFunctionNeutralitySelectedProof.selectedMarkPreservation
    data window body alpha Delta out input parameter value
  obtain ⟨hp⟩ := andIntro hw (andIntro hv hl)
  exact ⟨Derivation.implicationElimination h hp⟩

/-- The reconstructed application's function is the actual child-fold output.
The paid root-field law on that child transfers its lambda flag. The last
selected leaf then preserves the original neutral test, without identifying
its output with the reconstructed application. -/
theorem recoveredMarkIff (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter value : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (validity (selectedData data window)) (suc z) input parameter)))
    (hr : Nonempty (Derivation body Delta
      (OriginalCanonicalApplicationInversionTargets.Recovered (selectedData data window)
        arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter))) :
    Nonempty (Derivation body Delta ((markGraph value out).iff (markGraph value input))) := by
  have htail := andRight (andRight (andRight (andRight hr)))
  have hsrc := andLeft (andRight htail)
  have hleaf := andRight (andRight htail)
  have hwi := BottomDescentStepProof.windowChange window (suc z) input rebuilt parameter hw
  have hs := leafMarkIff data window out rebuilt parameter value hwi (andLeft hsrc) hleaf
  have hbi := OriginalFunctionNeutralityApplicationProof.recoveredNeutralityIff
    (baseData data window) window arrow d e fp ap fn arg functionOut argumentOut rebuilt
    input out parameter value hw hv hr
  exact iffCompose _ _ _ hs hbi

/-- Open the actual canonical guard, then bind the original child folds and
rebuilt application using the generic canonical application eliminator. -/
theorem openingMarkIff (data : Data) (window : Program 1) (out input parameter value : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (validity (selectedData data window)) (suc z) input parameter)))
    (hn : Nonempty (Derivation body Delta (foldGraph (selectedData data window) out input parameter)))
    (hg : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (rootGuard (selectedData data window))) (suc z) input parameter))) :
    Nonempty (Derivation body Delta ((markGraph value out).iff (markGraph value input))) := by
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (rootGuard (selectedData data window)) input parameter _ hg
  intro beta j Theta payload arrow d e fp ap fn arg hj hc _ _ _ _ _ _
  rw [OriginalFunctionNeutralityGuardProof.markIffRename]
  have hw' := renameInto hw j Theta hj
  have hv' := renameInto hv j Theta hj
  have hn' := renameInto hn j Theta hj
  simp only [windowGraph,OriginalVariableRepresentative.windowGraph,graph2Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  rw [foldGraphRename] at hn'
  apply OriginalCanonicalApplicationInversionProof.atConstructors (selectedData data window)
    arrow d e fp ap fn arg (input.relabel j) (out.relabel j) (parameter.relabel j) _ hc hv' hn'
  intro gamma q Lambda hq functionOut argumentOut rebuilt recovered
  rw [OriginalFunctionNeutralityGuardProof.markIffRename]
  have hw'' := renameInto hw' q Lambda hq
  simp only [graph2Rename,sucRelabel,zRelabel] at hw''
  have hv'' := renameInto hv' q Lambda hq
  simp only [graph2Rename,sucRelabel,zRelabel] at hv''
  exact recoveredMarkIff data window (arrow.relabel q) (d.relabel q) (e.relabel q)
    (fp.relabel q) (ap.relabel q) (fn.relabel q) (arg.relabel q)
    functionOut argumentOut rebuilt ((input.relabel j).relabel q) ((out.relabel j).relabel q)
    ((parameter.relabel j).relabel q) ((value.relabel j).relabel q) hw'' hv'' recovered

/-- Open roots use the original reconstructed application and its selected
leaf. Closed roots use the original run/leaf closure. Both directions are
internal arithmetic derivations at arbitrary symbolic mark values. -/
theorem fullFoldMarkPreservation (data : Data) (window : Program 1) :
    FullFoldMarkPreservation (selectedData data window) window := by
  intro body alpha Delta out input typeCode parameter value
  let selected := selectedData data window
  let A := windowGraph window input parameter ⊓
    (sourcePremises selected input typeCode parameter ⊓ foldGraph selected out input parameter)
  have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw := andLeft hA
  have hv := andLeft (andLeft (andRight hA))
  have hn := andRight (andRight hA)
  have result : Nonempty (Derivation body (A :: Delta)
      ((markGraph value out).iff (markGraph value input))) := by
    let P := graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard selected))
      (suc z) input parameter
    apply formulaCases P
    · have hp : Nonempty (Derivation body (P :: A :: Delta) P) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact openingMarkIff data window out input parameter value
        (withHyp hw P) (withHyp hv P) (withHyp hn P) hp
    · have hz : Nonempty (Derivation body (P.not :: A :: Delta)
          (graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard selected))
            z input parameter)) :=
        InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
          (Fin.cons input (Fin.cons parameter Fin.elim0))
          (show Nonempty (Derivation body (P.not :: A :: Delta) P.not) from
            ⟨Derivation.hypothesis List.mem_cons_self⟩)
      exact leafMarkIff data window out input parameter value
        (withHyp hw P.not) (withHyp hv P.not)
        (OriginalVariableRepresentativeRigidityProof.closedLeafGraph selected out input parameter
          hz (withHyp hn P.not))
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

theorem actualOriginalFunctionNeutralityFullFoldPreservation :
    OriginalFunctionNeutralityTargets.ActualOriginalFunctionNeutralityFullFoldPreservation := by
  intro data window
  exact fullFoldMarkPreservation data window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFullFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFullFoldProof
