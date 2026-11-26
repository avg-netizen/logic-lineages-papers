module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelFinishedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (WorkFuelGraph DecreasedOrFailed)
open OriginalTypedDecoderInternalRequestProof
open OriginalTypedDecoderInternalFuelSupportProof
open OriginalTypedDecoderInternalFuelFinishedProof
open OriginalTypedDecoderInternalFuelSingletonSupportProof (singletonWeight finishedCompositionForward)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue ternaryRecover)
open OriginalTypedDecoder (liveOf finished)
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A proof-local abbreviation for the two UNCHANGED initial ASTs. At zero
and one this is definitionally termInitial and argumentsInitial. -/
def requestFor (mode : Nat) : Program 4 :=
  pairOf (constant 4 mode) (pairOf (.projection 2) (pairOf (.projection 0) (.projection 1)))
def initialFor (mode : Nat) : Program 4 :=
  liveOf (consOf (requestFor mode) (constant 4 0))
def runFor (H : Program 1) (M contextWindow : Program 2) (mode : Nat) : Program 4 :=
  .composition (iterate H M contextWindow) ![fuel,initialFor mode,.projection 3]
def checkFor (H : Program 1) (M contextWindow : Program 2) (mode : Nat) : Program 4 :=
  .composition finished (fun _ : Fin 1 => runFor H M contextWindow mode)

theorem initialAtSingleton (mode : Nat) (state work request gamma typ raw c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw))) :
    Nonempty (Derivation body Delta
      (programGraph (initialFor mode) state ![typ,raw,gamma,c])) := by
  let xs : Fin 4 → OTerm alpha := ![typ,raw,gamma,c]
  have hrequest := requestBackward (constant 4 mode) (.projection 2) (.projection 0) (.projection 1)
    request (numeral mode) gamma typ raw xs (constantValue mode xs)
    (projectionValue 2 xs) (projectionValue 0 xs) (projectionValue 1 xs) hr
  have hwork := binaryValue InternalListCodec.consCode (requestFor mode) (constant 4 0)
    work request z xs hc hrequest (constantValue 0 xs)
  exact liveBackward (consOf (requestFor mode) (constant 4 0)) state work xs hwork hs

theorem ownFuelValue (gamma typ raw c : OTerm alpha) :
    Nonempty (Derivation body Delta (programGraph fuel (suc raw) ![typ,raw,gamma,c])) := by
  let xs : Fin 4 → OTerm alpha := ![typ,raw,gamma,c]
  exact unaryValue .succ (.projection 1) (suc raw) raw xs
    (successorValue (Fin.cons raw Fin.elim0)) (projectionValue 1 xs)

theorem singletonToCheck (H : Program 1) (M contextWindow : Program 2) (mode : Nat)
    (state work request gamma typ raw c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Delta (WorkAccepted H M contextWindow work c))) :
    Nonempty (Derivation body Delta (programGraph (checkFor H M contextWindow mode) (numeral 1) ![typ,raw,gamma,c])) := by
  let xs : Fin 4 → OTerm alpha := ![typ,raw,gamma,c]
  have hweight := singletonWeight work request (numeral mode) gamma typ raw hc hr
  have hown := acceptedAtOwnFuel H M contextWindow (suc raw) work c hweight ha
  have hi := workRunAt H M contextWindow (numeral 2) (suc raw) work state c hs hown
  have hrun := ternaryValue (iterate H M contextWindow) fuel (initialFor mode) (.projection 3) (numeral 2) (suc raw) state c xs
    hi (ownFuelValue gamma typ raw c) (initialAtSingleton mode state work request gamma typ raw c hs hc hr) (projectionValue 3 xs)
  exact unaryValue finished (runFor H M contextWindow mode) (numeral 1) (numeral 2) xs finishedSuccess hrun

theorem checkToSingleton (H : Program 1) (M contextWindow : Program 2) (mode : Nat)
    (state work request gamma typ raw c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Delta (programGraph (checkFor H M contextWindow mode) (numeral 1) ![typ,raw,gamma,c]))) :
    Nonempty (Derivation body Delta (WorkAccepted H M contextWindow work c)) := by
  let xs : Fin 4 → OTerm alpha := ![typ,raw,gamma,c]
  have hrun := finishedCompositionForward (runFor H M contextWindow mode) xs ha
  have hi := ternaryRecover (iterate H M contextWindow) fuel (initialFor mode) (.projection 3) (numeral 2) (suc raw) state c xs
    hrun (ownFuelValue gamma typ raw c) (initialAtSingleton mode state work request gamma typ raw c hs hc hr) (projectionValue 3 xs)
  exact acceptedIntro H M contextWindow work (suc raw) c
    (singletonWeight work request (numeral mode) gamma typ raw hc hr)
    (workRunIntro H M contextWindow (numeral 2) (suc raw) work state c hs hi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonSupportProof
