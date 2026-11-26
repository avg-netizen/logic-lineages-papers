module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafEquationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The generic successful stack application rule retains the ACTUAL N1,
G1, L1 and combine. Its literal final leaf self-output is the derived bridge. -/
theorem canonicalAtRaw (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut rebuilt parameter : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window parent parameter)))
    (hc : Nonempty (Derivation body Delta
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) argumentOut arg parameter)))
    (hr : Nonempty (Derivation body Delta (graph4 application rebuilt d e functionOut argumentOut))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) rebuilt parent parameter)) := by
  have hleaf := OriginalApplicationSidecarSameLeafApplicationProof.rebuiltLeafValue data window
    arrow d e fp ap fn arg parent functionOut argumentOut rebuilt parameter hw hc hv hf ha hr
  have children := OriginalApplicationInverseValidityProof.sourceRecover (selectedData data window)
    arrow d e fp ap fn arg parent parameter hc hv
  have hg := InternalParameterizedCanonicalResultFoldOpeningProof.rootGuardValue (selectedData data window)
    arrow d e fp ap fn arg parent parameter hc hv
    (andLeft (andRight children)) (andRight (andRight children)) (andLeft children)
  have hcomb := InternalParameterizedCanonicalResultFoldOpeningProof.combineValue (selectedData data window)
    d e functionOut argumentOut rebuilt rebuilt parameter hr hleaf
  exact InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationForward
    (InternalParameterizedCanonicalResultFold.rootGuard (selectedData data window))
    (InternalParameterizedCanonicalResultFold.leaf (selectedData data window))
    (InternalParameterizedCanonicalResultFold.combine (selectedData data window))
    arrow d e fp ap fn arg parent functionOut argumentOut rebuilt parameter hc hg hf ha hcomb

/-- Query the actual raw application witness internally. The forward stack
rule yields its N1 graph, and functionality identifies the supplied N1 output.
This avoids any native factorization or assumed N1 idempotence. -/
theorem canonicalRecover (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window parent parameter)))
    (hc : Nonempty (Derivation body Delta
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) argumentOut arg parameter)))
    (hn : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out parent parameter))) :
    Nonempty (Derivation body Delta (graph4 application out d e functionOut argumentOut)) := by
  let xs : Fin 4 → OrdinaryArithmetic.Term alpha :=
    Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut Fin.elim0)))
  apply programCases application xs _
  intro beta j Theta rebuilt hj hr
  rw [graph4Rename]
  simp only [xs,consTermRename,emptyRename] at hr
  have hw' := renameInto hw j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have hc' := renameInto hc j Theta hj
  simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  have hf' := renameInto hf j Theta hj
  have ha' := renameInto ha j Theta hj
  have hn' := renameInto hn j Theta hj
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename] at hf' ha' hn'
  have hrn := canonicalAtRaw data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) rebuilt (parameter.relabel j)
    hw' hc' hv' hf' ha' hr
  have he := valueUnique (InternalParameterizedCanonicalResultFold.foldN (selectedData data window))
    rebuilt (out.relabel j) (Fin.cons (parent.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hrn hn'
  exact outputTransport application rebuilt (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (functionOut.relabel j) (Fin.cons (argumentOut.relabel j) Fin.elim0)))) he hr

theorem actualOriginalApplicationSidecarCanonicalApplicationEquation :
    OriginalApplicationSidecarSameLeafTargets.ActualOriginalApplicationSidecarCanonicalApplicationEquation := by
  intro body data window alpha Delta arrow d e fp ap fn arg parent functionOut argumentOut out parameter
  let P := OriginalFunctionNeutrality.windowGraph window parent parameter ⊓
    (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) (suc z) parent parameter ⊓
        (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) functionOut fn parameter ⊓
          InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) argumentOut arg parameter)))
  let A := InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out parent parameter
  let B := graph4 application out d e functionOut argumentOut
  have hp : Nonempty (Derivation body (A :: P :: Delta) P) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨forward⟩ := canonicalRecover data window arrow d e fp ap fn arg parent functionOut argumentOut out parameter
    (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
    (andLeft (andRight (andRight (andRight hp)))) (andRight (andRight (andRight (andRight hp))))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp' : Nonempty (Derivation body (B :: P :: Delta) P) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨backward⟩ := canonicalAtRaw data window arrow d e fp ap fn arg parent functionOut argumentOut out parameter
    (andLeft hp') (andLeft (andRight hp')) (andLeft (andRight (andRight hp')))
    (andLeft (andRight (andRight (andRight hp')))) (andRight (andRight (andRight (andRight hp'))))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafEquationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafEquationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafEquationProof.actualOriginalApplicationSidecarCanonicalApplicationEquation
