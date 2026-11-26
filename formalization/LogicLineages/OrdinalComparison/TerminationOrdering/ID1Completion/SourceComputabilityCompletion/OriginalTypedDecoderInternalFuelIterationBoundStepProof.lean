module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalFuelSupportProof (fuelRename withHyp)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof
open OriginalTypedDecoderInternalFuelIterationBoundSyntaxProof
open OriginalTypedDecoderInternalFuelIterationBoundCoreProof
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
open OriginalTypedDecoderInternalFuelDecreaseProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem afterDecrease (H : Program 1) (count state workCode required out : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow H count)))
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count))))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition H) out state)))
    (hd : Nonempty (Derivation body Gamma (DecreasedOrFailed out required))) :
    Nonempty (Derivation body Gamma (TerminatedWork H (suc count) workCode)) := by
  apply decreasedCases out required _ hd
  · let A := equal out z
    have he : Nonempty (Derivation body (A :: Gamma) (eqn out z)) := by
      rw [← equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := outputTransport (transition H) out z (Fin.cons state Fin.elim0) he (withHyp ht A)
    exact rejectedWorkTerminated H count state workCode (withHyp hs A) hf
  · intro beta j Delta nextWork nextFuel hj hnext
    simp only [terminatedWorkRename,sucRelabel]
    have hrow' := renameInto hrow j Delta hj
    rw [sufficientRowRename] at hrow'
    have hs' := renameInto hs j Delta hj
    rw [stepLiveRename] at hs'
    have hb' := renameInto hb j Delta hj
    simp only [weakBoundRename,sucRelabel] at hb'
    have ht' := renameInto ht j Delta hj
    rw [graph1Rename] at ht'
    have hr := rowApply H (count.relabel j) nextWork nextFuel hrow'
      (andLeft (andRight hnext))
      (decreasedBound nextFuel (required.relabel j) (count.relabel j) (andRight (andRight hnext)) hb')
    exact continuedWorkTerminated H (count.relabel j) (state.relabel j)
      (workCode.relabel j) (out.relabel j) nextWork hs' (andLeft hnext) ht' hr

theorem nonemptySuccessor (H : Program 1) (count state workCode required : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow H count)))
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count))))
    (hn : Nonempty (Derivation body Gamma (eqn workCode z).not)) :
    Nonempty (Derivation body Gamma (TerminatedWork H (suc count) workCode)) := by
  apply programCases (transition H) (Fin.cons state Fin.elim0) _
  intro beta j Delta out hj ho
  simp only [terminatedWorkRename,sucRelabel]
  simp only [consTermRename,emptyRename] at ho
  have hrow' := renameInto hrow j Delta hj
  rw [sufficientRowRename] at hrow'
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have hb' := renameInto hb j Delta hj
  simp only [weakBoundRename,sucRelabel] at hb'
  have hn' := renameInto hn j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  have hnonzero : Nonempty (Derivation body Delta
      (equal (workCode.relabel j) OrdinaryArithmetic.zeroTerm).not) := by
    simpa only [equalEqn] using hn'
  have hd := decreaseCore H (state.relabel j) (workCode.relabel j) (required.relabel j)
    out hs' hnonzero hf' ho
  exact afterDecrease H (count.relabel j) (state.relabel j) (workCode.relabel j)
    (required.relabel j) out hrow' hs' hb' ho hd

theorem successorCore (H : Program 1) (count workCode required : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow H count)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count)))) :
    Nonempty (Derivation body Gamma (TerminatedWork H (suc count) workCode)) := by
  apply InternalOriginalPairingOrderArithmeticProof.formulaCases (eqn workCode z)
  · have he : Derivation body (eqn workCode z :: Gamma) (eqn workCode z) :=
      Derivation.hypothesis List.mem_cons_self
    exact terminatedWorkTransport H (suc count) z workCode ⟨symm he⟩ (nilTerminated H (suc count))
  · let N := (eqn workCode z).not
    have hn : Nonempty (Derivation body (N :: Gamma) N) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hrowN := withHyp hrow N
    have hfN := withHyp hf N
    have hbN := withHyp hb N
    apply programCases InternalPairing.pairing (Fin.cons (numeral 1) (Fin.cons workCode Fin.elim0)) _
    intro beta j Delta state hj hs
    simp only [terminatedWorkRename,sucRelabel]
    simp only [consTermRename,emptyRename,oneRename] at hs
    have hrow' := renameInto hrowN j Delta hj
    rw [sufficientRowRename] at hrow'
    have hf' := renameInto hfN j Delta hj
    rw [fuelRename] at hf'
    have hb' := renameInto hbN j Delta hj
    simp only [weakBoundRename,sucRelabel] at hb'
    have hn' := renameInto hn j Delta hj
    change Nonempty (Derivation body Delta (((eqn workCode z).relabel j).not)) at hn'
    rw [eqnRelabel,zRelabel] at hn'
    exact nonemptySuccessor H (count.relabel j) state (workCode.relabel j)
      (required.relabel j) hrow' hs hf' hb' hn'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundStepProof
