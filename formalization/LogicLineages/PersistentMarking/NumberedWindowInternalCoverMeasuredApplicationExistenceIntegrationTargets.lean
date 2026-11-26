module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)

/-- Two actual accepted scalar addresses, with their original common-context
field reports, supply the carrier windows required for application formation.
The measured least of their application therefore exists. No function window,
argument window, least call or measure-preservation law is an extra premise.
The syntax and refitted type guards remain explicit. -/
def ExactInstalledCarrierApplicationExists : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv tv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (qf qa ctx dom cod fn arg : OTerm α),
    let Q := install s V TV M M0 B T base cv tv root other
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ (addressReport qa ctx dom arg)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qf)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) qa)) →
    Nonempty (Derivation body Γ
      (hasLeast Q.source.cover Q.exchange Q.window s ctx cod (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationTargets
