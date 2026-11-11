module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelFinishedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalRequestProof
open OriginalTypedDecoderInternalFuelSupportProof
open OriginalTypedDecoderInternalFuelFinishedProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelIterationSaturationSupportProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A proof-local abbreviation for the two UNCHANGED initial ASTs. At zero
and one this is definitionally termInitial and argumentsInitial. -/
def requestFor (mode : Nat) : Program 3 :=
  pairOf (constant 3 mode) (pairOf (.projection 2) (pairOf (.projection 0) (.projection 1)))
def initialFor (mode : Nat) : Program 3 :=
  liveOf (consOf (requestFor mode) (constant 3 0))
def runFor (H : Program 1) (mode : Nat) : Program 3 :=
  .composition (iterate H) ![fuel,initialFor mode]
def checkFor (H : Program 1) (mode : Nat) : Program 3 :=
  .composition finished (fun _ : Fin 1 => runFor H mode)

theorem singletonWeight (work request mode gamma typ raw : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request mode gamma typ raw))) :
    Nonempty (Derivation body Delta (WorkFuelGraph (suc raw) work)) :=
  outputTransport workFuel (add (suc raw) z) (suc raw) (Fin.cons work Fin.elim0)
    ⟨addZero (suc raw)⟩
    (consValue work request z (suc raw) z hc
      (requestValue request mode gamma typ raw hr) nilValue)

theorem initialAtSingleton (mode : Nat) (state work request gamma typ raw : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw))) :
    Nonempty (Derivation body Delta
      (programGraph (initialFor mode) state ![typ,raw,gamma])) := by
  let xs : Fin 3 → OTerm alpha := ![typ,raw,gamma]
  have hrequest := requestBackward (constant 3 mode) (.projection 2) (.projection 0) (.projection 1)
    request (numeral mode) gamma typ raw xs (constantValue mode xs)
    (projectionValue 2 xs) (projectionValue 0 xs) (projectionValue 1 xs) hr
  have hwork := binaryValue InternalListCodec.consCode (requestFor mode) (constant 3 0)
    work request z xs hc hrequest (constantValue 0 xs)
  exact liveBackward (consOf (requestFor mode) (constant 3 0)) state work xs hwork hs

theorem ownFuelValue (gamma typ raw : OTerm alpha) :
    Nonempty (Derivation body Delta (programGraph fuel (suc raw) ![typ,raw,gamma])) := by
  let xs : Fin 3 → OTerm alpha := ![typ,raw,gamma]
  exact unaryValue .succ (.projection 1) (suc raw) raw xs
    (successorValue (Fin.cons raw Fin.elim0)) (projectionValue 1 xs)

theorem finishedCompositionForward {n : Nat} (p : Program n) (xs : Fin n → OTerm alpha)
    (hv : Nonempty (Derivation body Delta
      (programGraph (.composition finished (fun _ : Fin 1 => p)) (numeral 1) xs))) :
    Nonempty (Derivation body Delta (programGraph p (numeral 2) xs)) := by
  apply programCases p xs _
  intro beta j Theta result hj hr
  simp only [programRename,numeral,sucRelabel,zRelabel]
  have hv' := renameInto hv j Theta hj
  simp only [programRename,numeral,sucRelabel,zRelabel] at hv'
  let xx := fun i => (xs i).relabel j
  have hf := unaryRecover finished p (numeral 1) result xx hv' hr
  exact outputTransport p result (numeral 2) xx (finishedAcceptedState result hf) hr

theorem singletonToCheck (H : Program 1) (mode : Nat)
    (state work request gamma typ raw : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Delta (WorkAccepted H work))) :
    Nonempty (Derivation body Delta (programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma])) := by
  let xs : Fin 3 → OTerm alpha := ![typ,raw,gamma]
  have hweight := singletonWeight work request (numeral mode) gamma typ raw hc hr
  have hown := acceptedAtOwnFuel H (suc raw) work hweight ha
  have hi := workRunAt H (numeral 2) (suc raw) work state hs hown
  have hrun := binaryValue (iterate H) fuel (initialFor mode) (numeral 2) (suc raw) state xs
    hi (ownFuelValue gamma typ raw) (initialAtSingleton mode state work request gamma typ raw hs hc hr)
  exact unaryValue finished (runFor H mode) (numeral 1) (numeral 2) xs finishedSuccess hrun

theorem checkToSingleton (H : Program 1) (mode : Nat)
    (state work request gamma typ raw : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Delta (programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma]))) :
    Nonempty (Derivation body Delta (WorkAccepted H work)) := by
  let xs : Fin 3 → OTerm alpha := ![typ,raw,gamma]
  have hrun := finishedCompositionForward (runFor H mode) xs ha
  have hi := binaryRecover (iterate H) fuel (initialFor mode) (numeral 2) (suc raw) state xs
    hrun (ownFuelValue gamma typ raw) (initialAtSingleton mode state work request gamma typ raw hs hc hr)
  exact acceptedIntro H work (suc raw)
    (singletonWeight work request (numeral mode) gamma typ raw hc hr)
    (workRunIntro H (numeral 2) (suc raw) work state hs hi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonSupportProof
