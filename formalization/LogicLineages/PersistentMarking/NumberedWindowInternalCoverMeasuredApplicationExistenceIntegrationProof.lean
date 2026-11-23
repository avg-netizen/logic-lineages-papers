module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalCoverMeasuredApplicationExistenceProof (exact_MeasuredApplicationExists)
open NumberedWindowInternalCoverCombinedMeasuredInstallProof (exact_InstalledCarrierCoordinates)
open NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationTargets

theorem exact_InstalledCarrierApplicationExists : ExactInstalledCarrierApplicationExists := by
  intro V TV M M0 B T base s cv tv root other body α Γ qf qa ctx dom cod fn arg Q
    syn ty functionReport argumentReport functionAccepted argumentAccepted
  obtain ⟨f⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv tv root other
    body α Γ qf ctx (rawCons dom cod) fn functionReport functionAccepted
  obtain ⟨a⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv tv root other
    body α Γ qa ctx dom arg argumentReport argumentAccepted
  have function := Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight f))
  have argument := Derivation.conjunctionLeft
    (Derivation.conjunctionRight (Derivation.conjunctionRight a))
  exact exact_MeasuredApplicationExists V TV M M0 B T base s body α Γ ctx dom cod fn arg
    syn ty ⟨function⟩ ⟨argument⟩

#print axioms exact_InstalledCarrierApplicationExists
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationProof
