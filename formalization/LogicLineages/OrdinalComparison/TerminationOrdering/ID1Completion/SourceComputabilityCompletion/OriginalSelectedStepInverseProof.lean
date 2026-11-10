module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepInverseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ClaudeSupervisedCompletion.InverseGuardCandidate
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepInverseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalParameterizedApplicationStepChecker
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalParameterizedStructuralEndpointGuard (selectedEndpoint)
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open UniformCertificateCompletion
open OriginalSelectedCheckerInverseGuardProof
open ClaudeSupervisedCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The selected child checker is upgraded to the SAME full guarded step.
Target source-validity is recovered from the actual target application fold,
not inferred from the endpoint's weaker packed-target validity test. -/
theorem peeledStep (data : Data) (oldStep : Program 4)
    (d e arrow f g a k S T K parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises (selectedEndpoint data) d e arrow f g a k S T K parameter)))
    (hparent : Nonempty (Derivation body Gamma (stepAccepted data oldStep S T K parameter)))
    (hchild : Nonempty (Derivation body Gamma
      (checkerGraph (selectedEndpoint data) oldStep (suc z) f g k parameter))) :
    Nonempty (Derivation body Gamma (stepAccepted data oldStep f g k parameter)) := by
  have har := andLeft hp
  have hfl := andLeft (andRight hp)
  have hgl := andLeft (andRight (andRight hp))
  have hal := andLeft (andRight (andRight (andRight hp)))
  have hend := andLeft (andRight (andRight (andRight (andRight hp))))
  have htapp := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hp))))))
  obtain ⟨_,htarget,_⟩ := TypingProof.stepParts data oldStep S T K parameter hparent
  have hsourceChildren := OriginalApplicationInverseValidityProof.rawSourceRecover
    data arrow d e g a T parameter har hgl hal htapp htarget
  have hgsource := andLeft (andRight hsourceChildren)
  have hendpoint := InternalParameterizedStructuralEndpointGuardSupportProof.endpointRecover
    (validity data) (targetValidity data) data.member arrow d e f g a parameter har hend
  have hguards := ApplicationStepProof.rawGuardsValue data f g k parameter arrow
    (andLeft hendpoint) (andLeft (andRight hendpoint)) hfl hgl
  let xs : Fin 4 → OTerm α := ![f,g,k,parameter]
  exact conjunctionAccept _ _ xs (conjunctionAccept _ _ xs hguards hchild)
    (ApplicationStepProof.validityAtValue (validity data) 1 xs hgsource)

/-- At an internally supplied original edge state, preserve every recovered
raw constructor and transition while adding full child-step acceptance. -/
theorem stepAtStateCases (data : Data) (oldStep : Program 4)
    (state S T K parameter : OTerm α) (psi : Formula α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)))
    (hparent : Nonempty (Derivation body Gamma (stepAccepted data oldStep S T K parameter)))
    (hzero : Nonempty (Derivation body
      (rejectedBranch (selectedEndpoint data) oldStep (suc z) state S T K parameter :: Gamma) psi))
    (hpeel : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      ∀ d e arrow f g a k child : OTerm β,
      Nonempty (Derivation body Delta
        (peeledBranch (selectedEndpoint data) oldStep d e arrow f g a k child
          (suc z) (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j) ⊓
          stepAccepted data oldStep f g k (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply selectedCheckerCases (selectedEndpoint data) oldStep (suc z)
    state S T K parameter psi he
    (OriginalNonapplicationCheckerConstructorProof.selectedAcceptance data oldStep S T K parameter hparent)
    hzero
  intro β j Delta hj d e arrow f g a k child hw
  have hparent' := renameInto hparent j Delta hj
  simp only [stepAccepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hparent'
  simp only [sucRelabel,zRelabel] at hw
  have hstep := peeledStep data oldStep d e arrow f g a k
    (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j)
    (andLeft (andLeft (andRight hw))) hparent' (andRight (andRight hw))
  exact hpeel β j Delta hj d e arrow f g a k child (andIntro hw hstep)

/-- Bind the actual edge code internally, then eliminate the two original
checker branches with full renaming and context-extension quantifiers. -/
theorem actualSelectedStepElimination :
    OriginalSelectedStepInverseTargets.ActualSelectedStepElimination := by
  intro body data oldStep α Gamma S T K parameter psi hparent hzero hpeel
  apply programCases edgeCode (Fin.cons S (Fin.cons T (Fin.cons K Fin.elim0))) psi
  intro β j Delta state hj he
  simp only [consTermRename,emptyRename] at he
  have hparent' := renameInto hparent j Delta hj
  simp only [stepAccepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hparent'
  apply stepAtStateCases data oldStep state (S.relabel j) (T.relabel j) (K.relabel j)
    (parameter.relabel j) (psi.relabel j) he hparent'
  · let R := rejectedBranch (selectedEndpoint data) oldStep (suc z) state
      (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j)
    have hr : Nonempty (Derivation body (R :: Delta) R) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact hzero β j (R :: Delta)
      (fun r h => List.mem_cons_of_mem R (hj r h)) state
      (andIntro (withHyp he R) hr)
  · intro γ q Theta hq d e arrow f g a k child hw
    have hinc : ∀ r ∈ Gamma, r.relabel (q ∘ j) ∈ Theta := by
      intro r hr
      simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
        hq (r.relabel j) (hj r hr)
    have he' := renameInto he q Theta hq
    simp only [graph3Rename,Term.relabel_relabel] at he'
    have hp : Nonempty (Derivation body Theta
        (graph3 edgeCode (state.relabel q) (S.relabel (q ∘ j))
          (T.relabel (q ∘ j)) (K.relabel (q ∘ j)) ⊓
          (InverseGuardTargets.Peeled (selectedEndpoint data) oldStep d e arrow f g a k child
            InternalOriginalStepGuard.one (state.relabel q) (S.relabel (q ∘ j))
            (T.relabel (q ∘ j)) (K.relabel (q ∘ j)) (parameter.relabel (q ∘ j)) ⊓
              stepAccepted data oldStep f g k (parameter.relabel (q ∘ j))))) := by
      exact andIntro he' (by
        simpa only [peeledBranch,acceptedWitness,InverseGuardTargets.Peeled,
          InverseGuardTargets.Recovered,InternalOriginalStepGuard.one,Term.relabel_relabel] using hw)
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      hpeel γ (q ∘ j) Theta hinc (state.relabel q) d e arrow f g a k child hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepInverseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepInverseProof
