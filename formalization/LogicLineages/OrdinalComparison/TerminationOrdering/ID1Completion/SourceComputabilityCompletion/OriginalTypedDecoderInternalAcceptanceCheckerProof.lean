module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalTypedDecoderInternalRequestProof
open OriginalTypedDecoderInternalFuelSingletonSupportProof
open OriginalTypedDecoderInternalFuelSingletonProof
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

def workFor (mode : Nat) : Program 3 := consOf (requestFor mode) (constant 3 0)
def singletonQueries (mode : Nat) : Fin 3 → Program 3 := ![requestFor mode,workFor mode,initialFor mode]

/-- Construct the exact original singleton state from total original programs,
without assuming an accepted run or well-formed raw code. -/
theorem singletonCases (mode : Nat) (typ raw gamma : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (state work request : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (StepLive state work)) →
      Nonempty (Derivation body Delta (StepCons work request z)) →
      Nonempty (Derivation body Delta (StepRequest request (numeral mode)
        (gamma.relabel j) (typ.relabel j) (raw.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply queryCases (singletonQueries mode) (![typ,raw,gamma] : Fin 3 → OTerm alpha) _
  intro beta j ys Delta hj hq
  simp only [tripleRename] at hq
  let xs : Fin 3 → OTerm beta := ![typ.relabel j,raw.relabel j,gamma.relabel j]
  have hr := requestForward (constant 3 mode) (.projection 2) (.projection 0) (.projection 1)
    (ys 0) (numeral mode) (gamma.relabel j) (typ.relabel j) (raw.relabel j) xs
    (constantValue mode xs) (projectionValue 2 xs) (projectionValue 0 xs) (projectionValue 1 xs) (hq 0)
  have hc := binaryRecover InternalListCodec.consCode (requestFor mode) (constant 3 0)
    (ys 1) (ys 0) z xs (hq 1) (hq 0) (constantValue 0 xs)
  have hs := liveForward (workFor mode) (ys 2) (ys 1) xs (hq 1) (hq 2)
  exact step beta j Delta (ys 2) (ys 1) (ys 0) hj hs hc hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
