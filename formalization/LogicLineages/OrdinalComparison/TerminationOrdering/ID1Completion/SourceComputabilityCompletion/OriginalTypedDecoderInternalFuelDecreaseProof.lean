module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open OriginalLambdaConstructorGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalStateSyntaxProof OriginalTypedDecoderInternalStateProof
open OriginalTypedDecoderInternalBranchProof
open OriginalTypedDecoderInternalFuelSupportProof
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
open OriginalTypedDecoderInternalFuelDecreaseDispatchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual suffix weight is supplied by totality of the literal work
program. It is not an extra premise of the original transition theorem. -/
 theorem requestDecrease (H : Program 1)
    (out workCode request rest mode gamma typ raw tag payload previous : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (StepCons workCode request rest)))
    (hr : Nonempty (Derivation body Delta (StepRequest request mode gamma typ raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hm : Nonempty (Derivation body Delta (StepModeDispatch H out mode gamma typ tag payload rest)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph previous workCode))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply queryCases (![workFuel] : Fin 1 → Program 1) (Fin.cons rest Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [decreasedRename]
  simp only [consTermRename,emptyRename] at hq
  have hc' := renameInto hc j Theta hj
  rw [OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename] at hc'
  have hr' := renameInto hr j Theta hj
  rw [OriginalTypedDecoderInternalRequestSyntaxProof.stepRequestRename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [OriginalTypedDecoderInternalScalarSyntaxProof.stepPairRename] at hp'
  have hm' := renameInto hm j Theta hj
  rw [OriginalTypedDecoderInternalDispatchSyntaxProof.stepModeDispatchRename] at hm'
  have hf' := renameInto hf j Theta hj
  rw [fuelRename] at hf'
  have ht : Nonempty (Derivation body Theta (WorkFuelGraph (ys 0) (rest.relabel j))) := hq 0
  have he := consRecover (workCode.relabel j) (request.relabel j) (rest.relabel j)
    (suc (raw.relabel j)) (ys 0) (previous.relabel j) hc'
    (requestValue (request.relabel j) (mode.relabel j) (gamma.relabel j)
      (typ.relabel j) (raw.relabel j) hr') ht hf'
  exact modeDecrease H (out.relabel j) (mode.relabel j) (gamma.relabel j) (typ.relabel j)
    (tag.relabel j) (payload.relabel j) (rest.relabel j) (raw.relabel j) (ys 0)
    (previous.relabel j) hp' hm' ht he

 theorem nonemptyDecrease (H : Program 1) (out workCode previous : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepNonemptyWork H out workCode)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph previous workCode))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  apply nonemptyCases H out workCode _ h
  intro beta j Theta ys hj fields
  rw [decreasedRename]
  have hf' := renameInto hf j Theta hj
  rw [fuelRename] at hf'
  exact requestDecrease H (out.relabel j) (workCode.relabel j) (ys 0) (ys 1)
    (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (previous.relabel j)
    (andLeft fields) (andLeft (andRight fields)) (andLeft (andRight (andRight fields)))
    (andRight (andRight (andRight fields))) hf'

/-- Open the live nonempty branch of the unchanged original transition,
then consume its independently proved mode/tag specification. Every actual
request mode, constructor tag and rejecting guard remains in the proof. -/
 theorem decreaseCore (H : Program 1) (state workCode previous out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state workCode)))
    (hn : Nonempty (Derivation body Delta (equal workCode z).not))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph previous workCode)))
    (ho : Nonempty (Derivation body Delta (graph1 (OriginalTypedDecoder.transition H) out state))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let live := InternalAcceptance.branch OriginalTypedDecoder.work (.projection 0)
    (OriginalTypedDecoderInternalModeProof.modeProgram H)
  have hstatus := pairLeft state (numeral 1) workCode hs
  have hwork := pairRight state (numeral 1) workCode hs
  have heq : Nonempty (Derivation body Delta (equal (numeral 1) (numeral 1))) := by
    rw [equalEqn]
    exact ⟨refl (numeral 1)⟩
  have hlive := sameYesElim OriginalTypedDecoder.status (constant 1 1) live (constant 1 0)
    out (numeral 1) (numeral 1) xs hstatus (constantValue 1 xs) heq ho
  have hmode := nonzeroAtElim OriginalTypedDecoder.work (.projection 0)
    (OriginalTypedDecoderInternalModeProof.modeProgram H) out workCode xs hwork hn hlive
  exact nonemptyDecrease H out workCode previous
    (nonemptyForward H state out workCode hwork hn hmode) hf

 theorem actualOriginalTypedInternalWorkDecrease :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalWorkDecrease := by
  intro body H alpha state workCode previous out
  let A := StepLive state workCode ⊓ ((equal workCode z).not ⊓ WorkFuelGraph previous workCode)
  let G := graph1 (OriginalTypedDecoder.transition H) out state
  have h : Nonempty (Derivation body [G,A] A) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨d⟩ := decreaseCore H state workCode previous out (andLeft h)
    (andLeft (andRight h)) (andRight (andRight h)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseProof
