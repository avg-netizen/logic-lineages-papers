module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalParameterizedCanonicalResultFoldBindingProof InternalParameterizedCanonicalResultFoldLeafProof
open InternalParameterizedCanonicalResultFoldOpeningProof InternalApplicationValidityClosure
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The concrete C output is the original raw application followed by D.
Source closure derives the raw parent's validity from both certified children. -/
theorem applicationAtRawOutput (data : Data)
    (arrow d e fp ap fn arg parent functionOut argumentOut rawApp out parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (certifiedOutput data functionOut fn arrow parameter)))
    (ha : Nonempty (Derivation body Gamma (certifiedOutput data argumentOut arg d parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application rawApp d e functionOut argumentOut)))
    (hd : Nonempty (Derivation body Gamma (graph2 (leaf data) out rawApp parameter))) :
    Nonempty (Derivation body Gamma (certifiedOutput data out parent e parameter)) := by
  have hparent := andRight (andRight (andRight hc))
  have hm := memberFromGuard data d e fp ap parent parameter hparent hg
  have hv := rawValidity data arrow d e functionOut argumentOut rawApp parameter
    (andLeft hc) (andLeft (andRight (andRight hf)))
    (andLeft (andRight (andRight ha))) hm (andLeft (andRight hf)) (andLeft (andRight ha)) hr
  have hl := rawLeft d e functionOut argumentOut rawApp hr
  have hcombine := combineValue data d e functionOut argumentOut rawApp out parameter hr hd
  have hfold := InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    (rootGuard data) (leaf data) (combine data) parameter
    arrow d e fp ap fn arg parent functionOut argumentOut out
    (andLeft hc) (andLeft (andRight hc)) (andLeft (andRight (andRight hc))) hparent hg
    (andLeft hf) (andLeft ha) hcombine
  exact andIntro hfold (descentInvariant data out rawApp e parameter hd (andIntro hv hl))

theorem applicationAtRaw (data : Data)
    (arrow d e fp ap fn arg parent functionOut argumentOut rawApp parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (certifiedOutput data functionOut fn arrow parameter)))
    (ha : Nonempty (Derivation body Gamma (certifiedOutput data argumentOut arg d parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application rawApp d e functionOut argumentOut))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data parent e parameter)) := by
  apply programCases (leaf data) (Fin.cons rawApp (Fin.cons parameter Fin.elim0)) _
  intro β j Delta out hj hd
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hd
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hr' := renameInto hr j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [certifiedOutputRename] at hf' ha'
  rw [graph4Rename] at hr'
  exact hasCertifiedOutputIntro data out (parent.relabel j) (e.relabel j) (parameter.relabel j)
    (applicationAtRawOutput data (arrow.relabel j) (d.relabel j) (e.relabel j)
      (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
      (functionOut.relabel j) (argumentOut.relabel j) (rawApp.relabel j) out (parameter.relabel j)
      hc' hg' hf' ha' hr' hd)

theorem applicationHasOutput (data : Data)
    (arrow d e fp ap fn arg parent functionOut argumentOut parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (certifiedOutput data functionOut fn arrow parameter)))
    (ha : Nonempty (Derivation body Gamma (certifiedOutput data argumentOut arg d parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data parent e parameter)) := by
  apply programCases application
    (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut Fin.elim0)))) _
  intro β j Delta rawApp hj hr
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [certifiedOutputRename] at hf' ha'
  exact applicationAtRaw data (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) rawApp (parameter.relabel j) hc' hg' hf' ha' hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldApplicationProof
