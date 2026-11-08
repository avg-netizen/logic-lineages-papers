module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalCanonicalResultFoldInvariant InternalCanonicalResultFoldInvariantSyntaxProof
open InternalCanonicalResultFoldInvariantBindingProof
open InternalCanonicalResultFoldInvariantApplicationSupportProof
open InternalCanonicalResultFoldOpening InternalCanonicalDescentSelection
open InternalCanonicalDescentSelectionInternalProof
open InternalApplicationValidityClosure
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Concrete application output, retaining the original raw application and D.
Both exact validity branches and the literal combine graph are derived here. -/
theorem applicationAtRawOutput (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut rawApp out : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma
      (graph1 (rootGuard (validity old member) member) (suc z) parent)))
    (hf : Nonempty (Derivation body Gamma
      (certifiedOutput old R member functionOut fn arrow)))
    (ha : Nonempty (Derivation body Gamma
      (certifiedOutput old R member argumentOut arg d)))
    (hr : Nonempty (Derivation body Gamma (graph4 application rawApp d e functionOut argumentOut)))
    (hd : Nonempty (Derivation body Gamma
      (representativeGraph R (validity old member) out rawApp))) :
    Nonempty (Derivation body Gamma (certifiedOutput old R member out parent e)) := by
  have hparent := andRight (andRight (andRight hc))
  have hm := memberFromGuard (validity old member) member d e fp ap parent hparent hg
  have hv := rawValidity old member arrow d e functionOut argumentOut rawApp
    (andLeft hc) (andLeft (andRight (andRight hf)))
    (andLeft (andRight (andRight ha))) hm
    (andLeft (andRight hf)) (andLeft (andRight ha)) hr
  have hl := rawLeft d e functionOut argumentOut rawApp hr
  have hcombine : Nonempty (Derivation body Gamma
      (graph4 (combine R (validity old member)) out d e functionOut argumentOut)) :=
    unaryValue (leaf R (validity old member)) application out rawApp
      (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut Fin.elim0)))) hd hr
  have hfold := InternalApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    (rootGuard (validity old member) member) (leaf R (validity old member))
    (combine R (validity old member)) arrow d e fp ap fn arg parent functionOut argumentOut out
    (andLeft hc) (andLeft (andRight hc)) (andLeft (andRight (andRight hc))) hparent hg
    (andLeft hf) (andLeft ha) hcombine
  exact andIntro hfold
    (andIntro (descentValidity R (validity old member) out rawApp hd hv)
      (andIntro (descentLeft R (validity old member) out rawApp e hd hv hl)
        (descentFixed R (validity old member) out rawApp hd hv)))

/-- The original total D supplies its output inside the arithmetic calculus. -/
theorem applicationAtRaw (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut rawApp : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma
      (graph1 (rootGuard (validity old member) member) (suc z) parent)))
    (hf : Nonempty (Derivation body Gamma
      (certifiedOutput old R member functionOut fn arrow)))
    (ha : Nonempty (Derivation body Gamma
      (certifiedOutput old R member argumentOut arg d)))
    (hr : Nonempty (Derivation body Gamma (graph4 application rawApp d e functionOut argumentOut))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member parent e)) := by
  apply programCases (leaf R (validity old member)) (Fin.cons rawApp Fin.elim0) _
  intro β j Delta out hj hd
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hd
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hr' := renameInto hr j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  rw [certifiedOutputRename] at hf' ha'
  rw [graph4Rename] at hr'
  exact hasCertifiedOutputIntro old R member out (parent.relabel j) (e.relabel j)
    (applicationAtRawOutput old R member (arrow.relabel j) (d.relabel j) (e.relabel j)
      (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
      (functionOut.relabel j) (argumentOut.relabel j) (rawApp.relabel j) out
      hc' hg' hf' ha' hr' hd)

/-- Query the actual raw application, then D, then bind the certified output.
No bound on child outputs and no externally calibrated function is used. -/
theorem applicationHasOutput (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma
      (graph1 (rootGuard (validity old member) member) (suc z) parent)))
    (hf : Nonempty (Derivation body Gamma
      (certifiedOutput old R member functionOut fn arrow)))
    (ha : Nonempty (Derivation body Gamma
      (certifiedOutput old R member argumentOut arg d))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member parent e)) := by
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
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  rw [certifiedOutputRename] at hf' ha'
  exact applicationAtRaw old R member (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) rawApp hc' hg' hf' ha' hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationProof
