module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientPeeledProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityStepTransferProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientRawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open OriginalNeutralQuotient OriginalNeutralQuotientSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Factor the original raw step at the SAME canonical source. Neutrality
reflects through its actual fold; its raw bottom is transported through the
actual target fold, and its peeled child reconstructs the original quotient
edge with the shared canonical argument. -/
theorem atRaw (p : GlobalSourcePackage.Inputs) :
    let r := OriginalApplicationSidecar.finalInputs p
    let data := OuterSelection.data r.base r.window
    ∀ (x y certificate S T K parameter typeCode : OTerm alpha) (psi : Formula alpha),
    Nonempty (Derivation body Gamma (selectors certificate S T K)) →
    Nonempty (Derivation body Gamma (requirements data r.oldStep x y S T K parameter)) →
    Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph r.window x parameter)) →
    Nonempty (Derivation body Gamma (graph1 OriginalNeutralLeaf.neutralTest InternalOriginalStepGuard.one x)) →
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x)) →
    Nonempty (Derivation body (graph1 BottomRepresentative.bottomCode y typeCode :: Gamma) psi) →
    (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
      (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
      ∀ S T K state d e arrow f g a k child F G A : OTerm beta,
      Nonempty (Derivation body Delta
        (Recovered data r.oldStep (x.relabel j) (y.relabel j)
          (certificate.relabel j) (parameter.relabel j) S T K state d e arrow f g a k child F G A)) →
      Nonempty (Derivation body Delta (psi.relabel j))) →
    Nonempty (Derivation body Gamma psi) := by
  dsimp only
  intro x y certificate S T K parameter typeCode psi hselectors hrequirements hw hn ht hbottom next
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  have hstep := andLeft hrequirements
  obtain ⟨hvs,hvt,_⟩ := TypingProof.stepParts data r.oldStep S T K parameter hstep
  have hs := TypingProof.sourceFold data x S parameter hvs (andLeft (andRight hrequirements))
  have htarget := andRight (andRight hrequirements)
  have hsourceType := OriginalNeutralQuotientBottomProof.sourceType data x S typeCode parameter hvs hs ht
  have hws := BottomDescentStepProof.windowChange r.window (suc z) x S parameter hw
  have hwt := BottomDescentStepProof.windowChange r.window (suc z) x T parameter hw
  have hbottomImp : Nonempty (Derivation body Gamma
      ((graph1 BottomRepresentative.bottomCode y typeCode).imp psi)) := by
    obtain ⟨hbottom⟩ := hbottom
    exact ⟨Derivation.implicationIntroduction hbottom⟩
  apply OriginalFunctionNeutralityStepTransferProof.actualOriginalFunctionNeutralityStepElimination
    (OriginalApplicationSidecar.refineInputs p) body alpha Gamma S T K x parameter typeCode psi
    hstep hws (andIntro hvs hsourceType) hs hn hsourceType
  · let B := graph1 BottomRepresentative.bottomCode T typeCode
    have hb : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hby := OriginalNeutralQuotientBottomProof.bottomThroughFold r.base r.window
      y T typeCode parameter (withHyp hwt B) (withHyp hvt B) (withHyp htarget B) hb
    obtain ⟨hc⟩ := withHyp hbottomImp B
    obtain ⟨hby⟩ := hby
    exact ⟨Derivation.implicationElimination hc hby⟩
  · intro beta j Delta hj state d e arrow f g a k child hraw
    have hselectors' := renameInto hselectors j Delta hj
    rw [selectorsRename] at hselectors'
    have hrequirements' := renameInto hrequirements j Delta hj
    rw [requirementsRename] at hrequirements'
    have hw' := renameInto hw j Delta hj
    rw [windowRename] at hw'
    apply OriginalNeutralQuotientPeeledProof.atPeeled p
      (x.relabel j) (y.relabel j) (certificate.relabel j) (parameter.relabel j)
      (S.relabel j) (T.relabel j) (K.relabel j) state d e arrow f g a k child
      (psi.relabel j) hselectors' hrequirements' hw'
      (andLeft hraw) (andLeft (andRight hraw)) (andRight (andRight hraw))
    intro gamma q Theta hq F G A hr
    have hinc : ∀ h ∈ Gamma, h.relabel (q ∘ j) ∈ Theta := by
      intro h hh
      simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
        hq (h.relabel j) (hj h hh)
    simp only [Term.relabel_relabel] at hr
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      next gamma (q ∘ j) Theta hinc (S.relabel (q ∘ j)) (T.relabel (q ∘ j))
        (K.relabel (q ∘ j)) (state.relabel q) (d.relabel q) (e.relabel q)
        (arrow.relabel q) (f.relabel q) (g.relabel q) (a.relabel q) (k.relabel q)
        (child.relabel q) F G A hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientRawProof
