module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar OriginalCanonicalApplicationInversionTargets
open OriginalPairedCanonicalApplicationEliminationTargets
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Rename the complete existing record, including its original final leaf
graph. This neither discards nor strengthens any certified-output field. -/
theorem recoveredRename {beta : Type} (data : Data)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter : OTerm alpha)
    (j : alpha → beta) :
    (Recovered data arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter).relabel j =
      Recovered data (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
        (fn.relabel j) (arg.relabel j) (functionOut.relabel j) (argumentOut.relabel j)
        (rebuilt.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j) := by
  simp only [Recovered,InternalApplicationValidityClosure.applicationConstructors,
    conjunctionRename,graph2Rename,graph4Rename,certifiedOutputRename,sourcePremisesRename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

/-- The internally recovered certified outputs supply the exact child
canonical graphs needed by the frozen paired component contract. -/
theorem pairRecovered (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt
      arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt'
      input input' out parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hw' : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input' parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) InternalOriginalStepGuard.one input parameter)))
    (hv' : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window)) InternalOriginalStepGuard.one input' parameter)))
    (hn : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out input parameter)))
    (hn' : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out input' parameter)))
    (hr : Nonempty (Derivation body Delta
      (Recovered (selectedData data window) arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter)))
    (hr' : Nonempty (Derivation body Delta
      (Recovered (selectedData data window) arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt' input' out parameter))) :
    Nonempty (Derivation body Delta
      (PairedRecovered (selectedData data window) arrow d e fp ap fn arg functionOut argumentOut rebuilt
        arrow' d' e' fp' ap' fn' arg' functionOut' argumentOut' rebuilt' input input' out parameter)) := by
  have hf := andRight (andLeft (andLeft (andRight (andRight hr))))
  have ha := andRight (andLeft (andLeft (andRight (andRight (andRight hr)))))
  have hf' := andRight (andLeft (andLeft (andRight (andRight hr'))))
  have ha' := andRight (andLeft (andLeft (andRight (andRight (andRight hr')))))
  have hs := andIntro hw (andIntro (andLeft hr) (andIntro hv (andIntro hf (andIntro ha hn))))
  have hs' := andIntro hw' (andIntro (andLeft hr') (andIntro hv' (andIntro hf' (andIntro ha' hn'))))
  obtain ⟨law⟩ := OriginalApplicationComponentCoherenceProof.actualOriginalApplicationComponentCoherence
    body data window alpha Delta arrow d e fp ap fn arg input functionOut argumentOut
    arrow' d' e' fp' ap' fn' arg' input' functionOut' argumentOut' out parameter
  obtain ⟨premises⟩ := andIntro hs hs'
  exact andIntro hr (andIntro hr' ⟨Derivation.implicationElimination law premises⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPairedCanonicalApplicationEliminationSupportProof
