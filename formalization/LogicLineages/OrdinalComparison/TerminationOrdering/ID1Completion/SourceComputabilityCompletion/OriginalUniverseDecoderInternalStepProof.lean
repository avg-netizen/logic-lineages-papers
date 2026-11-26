module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalNonemptyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSupportProof (symm)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalBranchProof
open OriginalUniverseDecoderInternalSyntaxProof OriginalUniverseDecoderInternalNonemptyProof
open OriginalUniverseDecoderInternalGuardProof
open OriginalUniverseDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
 theorem identityForward (out input c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (.projection 0) out input c))) :
    Nonempty (Derivation body Delta (equal out input)) := by
  simpa only [equalEqn] using valueUnique (.projection (0 : Fin 2)) out input
    (![input,c] : Fin 2 → OTerm alpha) h (projectionValue 0 (![input,c] : Fin 2 → OTerm alpha))

 theorem identityBackward (out input c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (equal out input))) :
    Nonempty (Derivation body Delta (graph2 (.projection 0) out input c)) := by
  have he : Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn out input)) := by
    simpa only [equalEqn] using h
  obtain ⟨he⟩ := he
  exact outputTransport (.projection (0 : Fin 2)) input out (![input,c] : Fin 2 → OTerm alpha)
    ⟨symm he⟩ (projectionValue 0 (![input,c] : Fin 2 → OTerm alpha))

/-- Open actual status and work internally, retaining both failure and the
live-empty fixed point before connecting a genuine nonempty request. -/
 theorem fullForward (H : Program 1) (M W : Program 2) (out input c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.transition H M W) out input c))) :
    Nonempty (Derivation body Delta (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input c)) := by
  apply queryCases (![stateStatus,stateWork] : Fin 2 → Program 2) (![input,c] : Fin 2 → OTerm alpha) _
  intro beta j ys Theta hj hq
  rw [stateRename]
  have ho' := renameInto ho j Theta hj
  rw [graph2Rename] at ho'
  simp only [Matrix.vecCons,Matrix.vecEmpty,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := ![input.relabel j,c.relabel j]
  let live := InternalAcceptance.branch stateWork (.projection 0) (guardedStep H M W)
  have hpair := pairFields stateInput (input.relabel j) (ys 0) (ys 1) xx (projectionValue 0 xx) (hq 0) (hq 1)
  apply stateIntro H M W _ _ _ ys
  apply andIntro hpair
  apply formulaCases (equal (ys 0) (numeral 1)) _
  · have hs : Nonempty (Derivation body (equal (ys 0) (numeral 1) :: Theta)
        (equal (ys 0) (numeral 1))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hlive := sameYesElim stateStatus (constant 2 1) live (constant 2 0)
      (out.relabel j) (ys 0) (numeral 1) xx (withHyp (hq 0) _) (constantValue 1 xx) hs (withHyp ho' _)
    apply formulaCases (equal (ys 1) (numeral 0)) _
    · have hwzero : Nonempty (Derivation body
          (equal (ys 1) (numeral 0) :: equal (ys 0) (numeral 1) :: Theta)
          (equal (ys 1) (numeral 0))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hidentity := zeroAtElim stateWork (.projection 0) (guardedStep H M W) (out.relabel j) (ys 1) xx
        (withHyp (withHyp (hq 1) _) _) hwzero (withHyp hlive _)
      obtain ⟨he⟩ := andIntro hwzero (identityForward (out.relabel j) (input.relabel j) (c.relabel j) hidentity)
      obtain ⟨hs⟩ := withHyp hs (equal (ys 1) (numeral 0))
      exact ⟨orRight (Derivation.conjunctionIntroduction hs (orLeft he))⟩
    · have hwnonzero : Nonempty (Derivation body
          ((equal (ys 1) (numeral 0)).not :: equal (ys 0) (numeral 1) :: Theta)
          (equal (ys 1) (numeral 0)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hmode := nonzeroAtElim stateWork (.projection 0) (guardedStep H M W) (out.relabel j) (ys 1) xx
        (withHyp (withHyp (hq 1) _) _) hwnonzero (withHyp hlive _)
      have hnonempty := nonemptyForward H M W (out.relabel j) (input.relabel j) (ys 1) (c.relabel j)
        (withHyp (withHyp (hq 1) _) _) hwnonzero hmode
      obtain ⟨he⟩ := andIntro hwnonzero hnonempty
      obtain ⟨hs⟩ := withHyp hs (equal (ys 1) (numeral 0)).not
      exact ⟨orRight (Derivation.conjunctionIntroduction hs (orRight he))⟩
  · have hs : Nonempty (Derivation body ((equal (ys 0) (numeral 1)).not :: Theta)
        (equal (ys 0) (numeral 1)).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hzero := sameNoElim stateStatus (constant 2 1) live (constant 2 0)
      (out.relabel j) (ys 0) (numeral 1) xx (withHyp (hq 0) _) (constantValue 1 xx) hs (withHyp ho' _)
    obtain ⟨he⟩ := andIntro hs (constantForward 0 (out.relabel j) xx hzero)
    exact ⟨orLeft he⟩

/-- Rebuild the identical finite transition AST from the independent arithmetic
specification. No native calibration or successful-run assumption is used. -/
 theorem fullBackward (H : Program 1) (M W : Program 2) (out input c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input c))) :
    Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.transition H M W) out input c)) := by
  apply stateCases H M W out input c _ ho
  intro beta j Theta ys hj hq
  rw [graph2Rename]
  let xx : Fin 2 → OTerm beta := ![input.relabel j,c.relabel j]
  let liveProgram := InternalAcceptance.branch stateWork (.projection 0) (guardedStep H M W)
  have hs := pairLeftValue stateInput (input.relabel j) (ys 0) (ys 1) xx (projectionValue 0 xx) (andLeft hq)
  have hw := pairRightValue stateInput (input.relabel j) (ys 0) (ys 1) xx (projectionValue 0 xx) (andLeft hq)
  let rejected : Formula beta := (equal (ys 0) (numeral 1)).not ⊓ equal (out.relabel j) (numeral 0)
  let empty : Formula beta := equal (ys 1) (numeral 0) ⊓ equal (out.relabel j) (input.relabel j)
  let pending : Formula beta := (equal (ys 1) (numeral 0)).not ⊓ nonemptySpec H M W (out.relabel j) (input.relabel j) (ys 1) (c.relabel j)
  let active : Formula beta := equal (ys 0) (numeral 1) ⊓ (empty ⊔ pending)
  apply orCases (andRight hq)
  · have hbad : Nonempty (Derivation body (rejected :: Theta) rejected) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameNoIntro stateStatus (constant 2 1) liveProgram (constant 2 0)
      (out.relabel j) (ys 0) (numeral 1) xx (withHyp hs _) (constantValue 1 xx) (andLeft hbad)
      (constantBackward 0 (out.relabel j) xx (andRight hbad))
  · have hgood : Nonempty (Derivation body (active :: Theta) active) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply orCases (andRight hgood)
    · have hempty : Nonempty (Derivation body (empty :: active :: Theta) empty) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply sameYesIntro stateStatus (constant 2 1) liveProgram (constant 2 0)
        (out.relabel j) (ys 0) (numeral 1) xx (withHyp (withHyp hs _) _) (constantValue 1 xx)
        (withHyp (andLeft hgood) _)
      exact zeroAtIntro stateWork (.projection 0) (guardedStep H M W) (out.relabel j) (ys 1) xx
        (withHyp (withHyp hw _) _) (andLeft hempty)
        (identityBackward (out.relabel j) (input.relabel j) (c.relabel j) (andRight hempty))
    · have hpending : Nonempty (Derivation body (pending :: active :: Theta) pending) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply sameYesIntro stateStatus (constant 2 1) liveProgram (constant 2 0)
        (out.relabel j) (ys 0) (numeral 1) xx (withHyp (withHyp hs _) _) (constantValue 1 xx)
        (withHyp (andLeft hgood) _)
      apply nonzeroAtIntro stateWork (.projection 0) (guardedStep H M W) (out.relabel j) (ys 1) xx
        (withHyp (withHyp hw _) _) (andLeft hpending)
      exact nonemptyBackward H M W (out.relabel j) (input.relabel j) (ys 1) (c.relabel j)
        (withHyp (withHyp hw _) _) (andRight hpending)


theorem stepEquivalence (H : Program 1) (M W : Program 2) (out input context : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalUniverseDecoder.transition H M W) out input context).iff
        (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context))) := by
  obtain ⟨hf⟩ := fullForward (body := body)
    (Delta := graph2 (OriginalUniverseDecoder.transition H M W) out input context :: Delta)
    H M W out input context ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := fullBackward (body := body)
    (Delta := OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context :: Delta)
    H M W out input context ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalUniverseInternalStep :
    OriginalUniverseDecoderTargets.ActualOriginalUniverseInternalStep := by
  constructor
  · intro M W body alpha out request context
    exact guardEquivalence M W out request context
  · intro H M W body alpha out input context
    exact stepEquivalence H M W out input context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalStepProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalStepProof.actualOriginalUniverseInternalStep
