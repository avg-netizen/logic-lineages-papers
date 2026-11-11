module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInclusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalAcceptanceCheckerProof (singletonCases)
open OriginalTypedDecoderInternalFuelSingletonSupportProof (finishedCompositionForward)
open OriginalTypedDecoderInternalFuelSingletonProof (tripleRename)
open OriginalUniverseDecoderInternalFuelSingletonProof (quadrupleRename)
open OriginalTypedDecoderInternalFuelFinishedProof (finishedSuccess)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Both literal original checkers execute at the same original raw+1 count
and the same original singleton state. The source outer context remains an
unchanged extra parameter, and no native calibration supplies a derivation. -/
theorem singletonSourceToTarget (H : Program 1) (M W : Program 2) (mode : Nat)
    (state work request gamma typ raw c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma
      (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Gamma
      (programGraph (OriginalUniverseDecoderInternalFuelSingletonSupportProof.checkFor H M W mode)
        (numeral 1) ![typ,raw,gamma,c]))) :
    Nonempty (Derivation body Gamma
      (programGraph (OriginalTypedDecoderInternalFuelSingletonSupportProof.checkFor H mode)
        (numeral 1) ![typ,raw,gamma])) := by
  let sourceInputs : Fin 4 → OTerm alpha := ![typ,raw,gamma,c]
  let targetInputs : Fin 3 → OTerm alpha := ![typ,raw,gamma]
  have hsourceRun := finishedCompositionForward
    (OriginalUniverseDecoderInternalFuelSingletonSupportProof.runFor H M W mode)
    sourceInputs ha
  have hsourceIterate := ternaryRecover (OriginalUniverseDecoder.iterate H M W)
    OriginalUniverseDecoder.fuel
    (OriginalUniverseDecoderInternalFuelSingletonSupportProof.initialFor mode)
    (.projection 3) (numeral 2) (suc raw) state c sourceInputs hsourceRun
    (OriginalUniverseDecoderInternalFuelSingletonSupportProof.ownFuelValue gamma typ raw c)
    (OriginalUniverseDecoderInternalFuelSingletonSupportProof.initialAtSingleton
      mode state work request gamma typ raw c hs hc hr)
    (projectionValue 3 sourceInputs)
  have htargetIterate := OriginalUniverseDecoderInternalFuelInclusionProof.sameFuelAccepted
    H M W (suc raw) state c hsourceIterate
  have htargetRun := binaryValue (OriginalTypedDecoder.iterate H)
    OriginalTypedDecoder.fuel
    (OriginalTypedDecoderInternalFuelSingletonSupportProof.initialFor mode)
    (numeral 2) (suc raw) state targetInputs htargetIterate
    (OriginalTypedDecoderInternalFuelSingletonSupportProof.ownFuelValue gamma typ raw)
    (OriginalTypedDecoderInternalFuelSingletonSupportProof.initialAtSingleton
      mode state work request gamma typ raw hs hc hr)
  exact unaryValue OriginalTypedDecoder.finished
    (OriginalTypedDecoderInternalFuelSingletonSupportProof.runFor H mode)
    (numeral 1) (numeral 2) targetInputs finishedSuccess htargetRun

/-- Total construction of the common singleton discharges its state, work,
and request witnesses. The mode and every raw coordinate remain arbitrary. -/
theorem checkSourceToTarget (H : Program 1) (M W : Program 2) (mode : Nat)
    (typ raw gamma c : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (programGraph (OriginalUniverseDecoderInternalFuelSingletonSupportProof.checkFor H M W mode)
        (numeral 1) ![typ,raw,gamma,c]))) :
    Nonempty (Derivation body Gamma
      (programGraph (OriginalTypedDecoderInternalFuelSingletonSupportProof.checkFor H mode)
        (numeral 1) ![typ,raw,gamma])) := by
  apply singletonCases mode typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  simp only [programRename,numeral,sucRelabel,zRelabel,tripleRename]
  have ha' := renameInto ha j Delta hj
  simp only [programRename,numeral,sucRelabel,zRelabel,quadrupleRename] at ha'
  exact singletonSourceToTarget H M W mode state work request
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (c.relabel j) hs hc hr ha'

/-- Actual original term-source acceptance implies actual original typed
acceptance. Both checkers keep their own definitionally identical raw+1 fuel. -/
theorem termSourceToTarget (H : Program 1) (M W : Program 2)
    (typ raw gamma c : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma
      (OriginalTypedDecoderInternalAcceptance.TermAccepted H typ raw gamma)) :=
  checkSourceToTarget H M W 0 typ raw gamma c ha

/-- The same source inclusion for the actual original argument-list checker,
without assuming successful child checks or changing its original raw fuel. -/
theorem argumentsSourceToTarget (H : Program 1) (M W : Program 2)
    (types raw gamma c : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma c))) :
    Nonempty (Derivation body Gamma
      (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H types raw gamma)) :=
  checkSourceToTarget H M W 1 types raw gamma c ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInclusionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInclusionProof
