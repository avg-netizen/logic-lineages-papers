module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open OriginalQuotientSpine OriginalQuotientSpineTargets OriginalQuotientSpineRawProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Bind the three ORIGINAL quotient-certificate selectors; all later
witnesses are eliminated by the raw guard transport. The conclusion retains
the supplied quotient certificate, rather than its internal step field. -/
theorem quotientGuard (data : Data) (window : Program 1) (oldStep : Program 4)
    (hFold : OriginalFullFoldSpine.FullFoldMarkPreservation data window)
    (hStep : OriginalSelectedStepSpine.RawStepHasSpineGuard data oldStep)
    (x y certificate parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (OriginalFunctionNeutrality.windowGraph window x parameter)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted x y certificate parameter)) := by
  let qs : Fin 3 → Program 1 := Fin.cons source (Fin.cons target (Fin.cons step Fin.elim0))
  apply queryCases qs (Fin.cons certificate Fin.elim0) _
  intro beta j ys Delta hj hq
  rw [spineRename]
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hf : Nonempty (Derivation body Delta
      (selectors (certificate.relabel j) (ys 0) (ys 1) (ys 2))) := by
    apply andIntro
    · have hvalue := hq 0
      rw [show qs (0 : Fin 3) = source from rfl] at hvalue
      simpa only [consTermRename,emptyRename] using hvalue
    · apply andIntro
      · have hvalue := hq 1
        rw [show qs (1 : Fin 3) = target from rfl] at hvalue
        simpa only [consTermRename,emptyRename] using hvalue
      · have hvalue := hq 2
        rw [show qs (2 : Fin 3) = step from rfl] at hvalue
        simpa only [consTermRename,emptyRename] using hvalue
  have hr := checkerRecover data oldStep (x.relabel j) (y.relabel j)
    (certificate.relabel j) (ys 0) (ys 1) (ys 2) (parameter.relabel j) hf he'
  have hw' := renameInto hw j Delta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  exact atRaw data window oldStep hFold hStep (x.relabel j) (y.relabel j)
    (certificate.relabel j) (ys 0) (ys 1) (ys 2) (parameter.relabel j) hw' hr

theorem actualOriginalQuotientSpineTransport : ActualOriginalQuotientSpineTransport := by
  intro data window oldStep hFold hStep body alpha Delta x y certificate parameter
  let P := OriginalFunctionNeutrality.windowGraph window x parameter ⊓
    edgeAccepted data oldStep x y certificate parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := quotientGuard data window oldStep hFold hStep x y certificate parameter
    (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalFinalQuotientSpineGuard : ActualOriginalFinalQuotientSpineGuard := by
  intro p
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  exact actualOriginalQuotientSpineTransport (OuterSelection.data r.base r.window) r.window r.oldStep
    (OriginalFullFoldSpineProof.actualOriginalFinalFullFoldSpinePreservation q)
    (OriginalSelectedStepSpineProof.actualOriginalFinalRawStepSpineGuard p)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof.actualOriginalQuotientSpineTransport
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof.actualOriginalFinalQuotientSpineGuard
