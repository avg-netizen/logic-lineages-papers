module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafEquationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data validity)
open OriginalApplicationSidecar UniformCertificateCompletion
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Reconstruct the original typed payload witnesses from the two actual
right projections, then apply the SAME-final-leaf canonical equation. -/
theorem atPayloads (data : Data) (window : Program 1)
    (arrow d e f a parent fp ap F A out parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window parent parameter)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (haright : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) F f parameter)))
    (ha : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) A a parameter)))
    (hn : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out parent parameter))) :
    Nonempty (Derivation body Gamma (graph4 application out d e F A)) := by
  have hc : Nonempty (Derivation body Gamma
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap f a parent)) :=
    andIntro har (andIntro (reconstructPair f arrow fp hfl hfr)
      (andIntro (reconstructPair a d ap hal haright)
        (applicationForward d e f a fp ap parent hfr haright hp)))
  exact OriginalApplicationSidecarSameLeafEquationProof.canonicalRecover data window
    arrow d e fp ap f a parent F A out parameter hw hc hv hf ha hn

theorem atFunctionPayload (data : Data) (window : Program 1)
    (arrow d e f a parent fp F A out parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window parent parameter)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) F f parameter)))
    (ha : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) A a parameter)))
    (hn : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out parent parameter))) :
    Nonempty (Derivation body Gamma (graph4 application out d e F A)) := by
  apply programCases InternalUnpair.right (Fin.cons a Fin.elim0) _
  intro beta j Delta ap hj hap
  rw [graph4Rename]
  simp only [consTermRename,emptyRename] at hap
  have hw' := renameInto hw j Delta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hfr' := renameInto hfr j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
    at har' hfl' hal' hfr' hp' hv'
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hn' := renameInto hn j Delta hj
  rw [foldGraphRename] at hf' ha' hn'
  exact atPayloads data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (parent.relabel j) (fp.relabel j) ap
    (F.relabel j) (A.relabel j) (out.relabel j) (parameter.relabel j)
    hw' har' hfl' hal' hfr' hap hp' hv' hf' ha' hn'

/-- Both payloads are bound by the original Program totality theorem.
The canonical application equation is applied to these actual constructors,
not to an assumed injective raw application function. -/
theorem rawApplication (data : Data) (window : Program 1)
    (arrow d e f a parent F A out parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window parent parameter)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity (selectedData data window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) F f parameter)))
    (ha : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) A a parameter)))
    (hn : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out parent parameter))) :
    Nonempty (Derivation body Gamma (graph4 application out d e F A)) := by
  apply programCases InternalUnpair.right (Fin.cons f Fin.elim0) _
  intro beta j Delta fp hj hfp
  rw [graph4Rename]
  simp only [consTermRename,emptyRename] at hfp
  have hw' := renameInto hw j Delta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
    at har' hfl' hal' hp' hv'
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hn' := renameInto hn j Delta hj
  rw [foldGraphRename] at hf' ha' hn'
  exact atFunctionPayload data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (parent.relabel j) fp
    (F.relabel j) (A.relabel j) (out.relabel j) (parameter.relabel j)
    hw' har' hfl' hal' hfp hp' hv' hf' ha' hn'

/-- Place the constructor equation at the exact final tuple used by the
original quotient checker and its complete global source package. -/
theorem finalApplication (p : GlobalSourcePackage.Inputs)
    (arrow d e f a parent F A out parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window parent parameter)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity (OuterSelection.data (finalInputs p).base (finalInputs p).window)) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph
        (OuterSelection.data (finalInputs p).base (finalInputs p).window) F f parameter)))
    (ha : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph
        (OuterSelection.data (finalInputs p).base (finalInputs p).window) A a parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph
        (OuterSelection.data (finalInputs p).base (finalInputs p).window) out parent parameter))) :
    Nonempty (Derivation body Gamma (graph4 application out d e F A)) := by
  have hi := OriginalApplicationSidecarIdentityProof.actualOriginalApplicationSidecarSelectionIdentity.2 p
  rw [hi.1] at hw
  rw [hi.2] at hv hf ha hn
  exact rawApplication p.base p.window arrow d e f a parent F A out parameter
    hw har hfl hal hp hv hf ha hn

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientApplicationProof
