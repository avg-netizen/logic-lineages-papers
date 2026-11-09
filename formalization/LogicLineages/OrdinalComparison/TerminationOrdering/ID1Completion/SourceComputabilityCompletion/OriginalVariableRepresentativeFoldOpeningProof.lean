module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeApplicationMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeFoldOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableRepresentative OriginalVariableRepresentativeApplicationMarkProof
open InternalParameterizedCanonicalResultFold
open InternalParameterizedCanonicalResultFoldSyntaxProof InternalParameterizedCanonicalResultFoldBindingProof
open InternalParameterizedCanonicalResultFoldOpeningProof InternalParameterizedCanonicalResultFoldInductionProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityClosure
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem selectedMarked (data : Data) (window : Program 1) (out input parameter mark : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity (selectedData data window)) (suc z) input parameter)))
    (hr : Nonempty (Derivation body Gamma (graph2 (leaf (selectedData data window)) out input parameter)))
    (hm : Nonempty (Derivation body Gamma (markGraph mark input))) :
    Nonempty (Derivation body Gamma (markGraph mark out)) := by
  obtain ⟨h⟩ := OriginalVariableRepresentativeSelectedProof.selectedMarkPreservation
    data window body α Gamma out input parameter mark
  obtain ⟨hp⟩ := andIntro hw (andIntro hv hr)
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination h hp)) hm⟩

/-- Both child invariants and parent membership come from paid concrete
fold laws and the original root guard. No child-success premise is invented. -/
theorem applicationMarkAtRaw (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut raw out parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window parent parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (certifiedOutput (selectedData data window) functionOut fn arrow parameter)))
    (ha : Nonempty (Derivation body Gamma (certifiedOutput (selectedData data window) argumentOut arg d parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out parent parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e functionOut argumentOut))) :
    Nonempty (Derivation body Gamma (markGraph z out)) := by
  let selected := selectedData data window
  have hm := memberFromGuard selected d e fp ap parent parameter
    (andRight (andRight (andRight hc))) hg
  have hv := rawValidity selected arrow d e functionOut argumentOut raw parameter
    (andLeft hc) (andLeft (andRight (andRight hf)))
    (andLeft (andRight (andRight ha))) hm (andLeft (andRight hf)) (andLeft (andRight ha)) hr
  have hcomb := InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationBackward
    (rootGuard selected) (leaf selected) (combine selected)
    arrow d e fp ap fn arg parent functionOut argumentOut out parameter hc hg
    (andRight (andLeft hf)) (andRight (andLeft ha)) hn
  have hd := combineRecover selected d e functionOut argumentOut raw out parameter hr hcomb
  have hwraw := BottomDescentStepProof.windowChange window (suc z) parent raw parameter hw
  exact selectedMarked data window out raw parameter z hwraw hv hd
    (applicationMarkZero d e functionOut argumentOut raw hr)

theorem applicationMarkAtChildren (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window parent parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (certifiedOutput (selectedData data window) functionOut fn arrow parameter)))
    (ha : Nonempty (Derivation body Gamma (certifiedOutput (selectedData data window) argumentOut arg d parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out parent parameter))) :
    Nonempty (Derivation body Gamma (markGraph z out)) := by
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut Fin.elim0)))
  apply programCases application xs _
  intro β j Delta raw hj hr
  simp only [markGraph,graph1Rename,zRelabel]
  have hw' := renameInto hw j Delta hj
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [certifiedOutputRename] at hf' ha'
  rw [foldGraphRename] at hn'
  simp only [xs,consTermRename,emptyRename] at hr
  exact applicationMarkAtRaw data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) raw (out.relabel j) (parameter.relabel j)
    hw' hc' hg' hf' ha' hn' hr

theorem applicationMarkAtFunction (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut out parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window parent parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (certifiedOutput (selectedData data window) functionOut fn arrow parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out parent parameter))) :
    Nonempty (Derivation body Gamma (markGraph z out)) := by
  let selected := selectedData data window
  have hv := rootGuardRecover selected arrow d e fp ap fn arg parent parameter hc hg
  have hex := certifiedOutputExists selected arg d parameter
    (andIntro (andLeft (andRight (andRight hv)))
      (pairLeft arg d ap (andLeft (andRight (andRight hc)))))
  apply hasCertifiedOutputCases selected arg d parameter _ hex
  intro β j Delta argumentOut hj ha
  simp only [markGraph,graph1Rename,zRelabel]
  have hw' := renameInto hw j Delta hj
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hf' := renameInto hf j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [certifiedOutputRename] at hf'
  rw [foldGraphRename] at hn'
  exact applicationMarkAtChildren data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (functionOut.relabel j) argumentOut (out.relabel j) (parameter.relabel j)
    hw' hc' hg' hf' ha hn'

theorem applicationOutputMark (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent out parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window parent parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard (selectedData data window)) (suc z) parent parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out parent parameter))) :
    Nonempty (Derivation body Gamma (markGraph z out)) := by
  let selected := selectedData data window
  have hv := rootGuardRecover selected arrow d e fp ap fn arg parent parameter hc hg
  have hex := certifiedOutputExists selected fn arrow parameter
    (andIntro (andLeft (andRight hv)) (pairLeft fn arrow fp (andLeft (andRight hc))))
  apply hasCertifiedOutputCases selected fn arrow parameter _ hex
  intro β j Delta functionOut hj hf
  simp only [markGraph,graph1Rename,zRelabel]
  have hw' := renameInto hw j Delta hj
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [foldGraphRename] at hn'
  exact applicationMarkAtFunction data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    functionOut (out.relabel j) (parameter.relabel j) hw' hc' hg' hf hn'

/-- Original openGuard inversion supplies the real constructors. Every
bound child output is supplied by existing internal canonical-fold totality. -/
theorem openingMarks (data : Data) (window : Program 1) (out input parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out input parameter)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (rootGuard (selectedData data window))) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (markGraph z out ⊓ markGraph z input)) := by
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (rootGuard (selectedData data window)) input parameter _ hg
  intro β j Delta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal hguard
  simp only [conjunctionRename,markGraph,graph1Rename,zRelabel]
  have hw' := renameInto hw j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  rw [foldGraphRename] at hn'
  have hout := applicationOutputMark data window arrow d e fp ap fn arg
    (input.relabel j) (out.relabel j) (parameter.relabel j) hw' hc hguard hn'
  have hraw := InternalApplicationCertificateConstructorsSupportProof.applicationBackward
    d e fn arg fp ap (input.relabel j) hfr har (andRight (andRight (andRight hc)))
  exact andIntro hout (applicationMarkZero d e fn arg (input.relabel j) hraw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeFoldOpeningProof
