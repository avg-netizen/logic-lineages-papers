module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Allraw exact original decoded Context-member calibration, including failure.
This is separate from the internal arithmetic endpoints, never their premise. -/
def NativeOriginalMember : Prop := ∀ n : Nat,
  OriginalUniverseDecoder.ContextMemberCalibrated n (member n)

/-- The actual lambda universe guard supplies the domain conjunct needed by
original Fields. No recursive Fields oracle, raw validity, Gamma-in-window,
calibration or pre-supplied domain membership is assumed. Outer Context is fixed. -/
def InternalLambdaDomain : Prop := ∀ (n : Nat) (H : Program 1) (W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw domain child typ gamma context types : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)) →
  Nonempty (Derivation body Delta (TermAccepted H (member n) W typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 contextTypes types context)) →
  Nonempty (Derivation body Delta
    (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) types domain))

/-- The actual application argument request is accepted in the same outer
Context; its requested-type guard supplies the original Fields domain conjunct.
H and W remain arbitrary. No semantic subtype or successful-child oracle premise. -/
def InternalApplicationDomain : Prop := ∀ (n : Nat) (H : Program 1) (W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw domain fn arg typ gamma context types : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain fn arg)) →
  Nonempty (Derivation body Delta (TermAccepted H (member n) W typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 contextTypes types context)) →
  Nonempty (Derivation body Delta
    (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) types domain))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Targets
