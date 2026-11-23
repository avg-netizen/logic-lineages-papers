module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinSyntaxWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseRoundWindowChecks (exact_SelectedWindowFromRetained)
open NumberedWindowInternalSparseRoundLeastChecks (exact_CoveredLeastIdempotent)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof (exact_OpenCoverCombinedWrappedAuxFormation)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)
open NumberedWindowInternalCoverCombinedMeasuredInstallProof
  (exact_InstalledCarrierCoordinates exact_InstalledCarrierFromCoordinates)
open NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationProof
  (exact_InstalledCarrierApplicationExists)
open NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets

attribute [local irreducible] programGraph

theorem exact_InstalledApplicationOutputAddress : ExactInstalledApplicationOutputAddress := by
  intro V TV M M0 B T base s cv tv root other body α Γ qf qa ctx dom cod fn arg goal Q
    syn ty result functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨f⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv tv root other
    body α Γ qf ctx (rawCons dom cod) fn functionReport functionAccepted
  obtain ⟨a⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv tv root other
    body α Γ qa ctx dom arg argumentReport argumentAccepted
  have context : Nonempty (Derivation body Γ (unary cv (suc z) ctx)) :=
    ⟨Derivation.conjunctionLeft f⟩
  have function : Nonempty (Derivation body Γ (windowAt Q.window ctx (rawCons dom cod) fn)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight f))⟩
  have argument : Nonempty (Derivation body Γ (windowAt Q.window ctx dom arg)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight a))⟩
  have formed : Nonempty (Derivation body Γ
      (windowAt Q.window ctx cod (auxiliaryTerm dom cod fn arg))) :=
    exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body α Γ
      ctx dom cod fn arg syn ty function argument
  have available : Nonempty (Derivation body Γ
      (hasLeast Q.source.cover Q.exchange Q.window s ctx cod (auxiliaryTerm dom cod fn arg))) :=
    exact_InstalledCarrierApplicationExists V TV M M0 B T base s cv tv root other body α Γ
      qf qa ctx dom cod fn arg syn ty functionReport argumentReport
      functionAccepted argumentAccepted
  apply casesLeast Q.source.cover Q.exchange Q.window s ctx cod
    (auxiliaryTerm dom cod fn arg) goal available
  intro β j Δ m keep least
  have context' := renameInto context j Δ keep
  have result' := renameInto result j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at context' result'
  have formed' := renameInto formed j Δ keep
  rw [windowRename] at formed'
  obtain ⟨context'⟩ := context'
  obtain ⟨result'⟩ := result'
  obtain ⟨formed'⟩ := formed'
  obtain ⟨selected⟩ := least
  obtain ⟨windowLaw⟩ := exact_SelectedWindowFromRetained exact_RetainedPredecessor
    Q.source.cover Q.exchange Q.window s body β Δ (ctx.relabel j) (cod.relabel j)
    ((auxiliaryTerm dom cod fn arg).relabel j) m
  have window : Derivation body Δ (windowAt Q.window (ctx.relabel j) (cod.relabel j) m) :=
    Derivation.implicationElimination windowLaw
      (Derivation.conjunctionIntroduction formed' selected)
  obtain ⟨fixedLaw⟩ := exact_CoveredLeastIdempotent Q.source.cover s
    (measuredExchange (selectedMeasure Q.source.R) (directedX base Q.source.V))
    (thinSyntaxWindow Q.source.W Q.source.V) body β Δ (ctx.relabel j) (cod.relabel j)
    ((auxiliaryTerm dom cod fn arg).relabel j) m
  have fixed : Derivation body Δ
      (leastGraph Q.source.cover Q.exchange Q.window s (ctx.relabel j) (cod.relabel j) m m) :=
    Derivation.implicationElimination fixedLaw selected
  obtain ⟨⟨good⟩,⟨hc⟩,⟨ht⟩,⟨hk⟩⟩ := literalAddress (body := body) (Γ := Δ)
    (ctx.relabel j) (cod.relabel j) m
  have report : Nonempty (Derivation body Δ
      (addressReport (addressTerm (ctx.relabel j) (cod.relabel j) m)
        (ctx.relabel j) (cod.relabel j) m)) :=
    ⟨Derivation.conjunctionIntroduction good
      (Derivation.conjunctionIntroduction hc (Derivation.conjunctionIntroduction ht hk))⟩
  have accepted : Nonempty (Derivation body Δ
      (unary Q.scalar (suc z) (addressTerm (ctx.relabel j) (cod.relabel j) m))) :=
    exact_InstalledCarrierFromCoordinates V TV M M0 B T base s cv tv root other body β Δ
      (addressTerm (ctx.relabel j) (cod.relabel j) m) (ctx.relabel j) (cod.relabel j) m report
      ⟨Derivation.conjunctionIntroduction context'
        (Derivation.conjunctionIntroduction result'
          (Derivation.conjunctionIntroduction window fixed))⟩
  exact finish β j Δ m keep ⟨selected⟩ report accepted

theorem exact_InstalledSyntaxGuardedApplicationOutputAddress :
    ExactInstalledSyntaxGuardedApplicationOutputAddress := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    syn ty functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨guards⟩ := syn
  exact exact_InstalledApplicationOutputAddress V TV M M0 B T base s cv TV root other body α Γ
    qf qa ctx dom cod fn arg goal ⟨guards⟩ ty ⟨Derivation.conjunctionRight guards⟩
    functionReport argumentReport functionAccepted argumentAccepted finish

#print axioms exact_InstalledApplicationOutputAddress
#print axioms exact_InstalledSyntaxGuardedApplicationOutputAddress
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
