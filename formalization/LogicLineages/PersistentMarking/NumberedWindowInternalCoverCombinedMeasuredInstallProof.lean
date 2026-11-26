module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTestProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseCanonicalAddressFieldsProof (reported)
open NumberedWindowInternalSparseCanonicalCoordinatesTestProof (openTest)
open NumberedWindowInternalSparseApplicationFrontendOpenChecks (exact_OpenGuardedApplication)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
  (exact_MeasuredExchangePreservesMeasure)
open NumberedWindowInternalCoverCombinedMeasuredInstallTargets

attribute [local irreducible] programGraph

theorem exact_InstalledCarrierCoordinates : ExactInstalledCarrierCoordinates := by
  intro V TV M M0 B T base s cv tv root other body α Γ q ctx ty k Q report hit
  obtain ⟨report⟩ := report
  obtain ⟨hit⟩ := hit
  obtain ⟨law⟩ := reported cv tv Q.window Q.least body α Γ q ctx ty k
  have fields := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination law report)) hit
  obtain ⟨coordinateLaw⟩ := openTest Q.window Q.least body α Γ ctx ty k
  have coordinates := Derivation.implicationElimination (Derivation.conjunctionLeft coordinateLaw)
    (Derivation.conjunctionRight (Derivation.conjunctionRight fields))
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft fields)
    (Derivation.conjunctionIntroduction
      (Derivation.conjunctionLeft (Derivation.conjunctionRight fields)) coordinates)⟩

theorem exact_InstalledCarrierFromCoordinates : ExactInstalledCarrierFromCoordinates := by
  intro V TV M M0 B T base s cv tv root other body α Γ q ctx ty k Q report fields
  obtain ⟨report⟩ := report
  obtain ⟨fields⟩ := fields
  obtain ⟨coordinateLaw⟩ := openTest Q.window Q.least body α Γ ctx ty k
  have coordinates := Derivation.implicationElimination (Derivation.conjunctionRight coordinateLaw)
    (Derivation.conjunctionRight (Derivation.conjunctionRight fields))
  obtain ⟨law⟩ := reported cv tv Q.window Q.least body α Γ q ctx ty k
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law report))
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft fields)
      (Derivation.conjunctionIntroduction
        (Derivation.conjunctionLeft (Derivation.conjunctionRight fields)) coordinates))⟩

theorem exact_InstalledApplicationReport : ExactInstalledApplicationReport := by
  intro V TV M M0 B T base s cv tv root other body α Γ f u y Q accepted report
  exact exact_OpenGuardedApplication body Q.scalar Q.least α Γ f u y

theorem exact_InstalledMeasurePreserving : ExactInstalledMeasurePreserving := by
  intro V TV M M0 B T base s cv tv root other Q
  exact exact_MeasuredExchangePreservesMeasure Q.source.cover s (selectedMeasure Q.source.R)
    (directedX base Q.source.V) Q.window

#print axioms exact_InstalledCarrierCoordinates
#print axioms exact_InstalledCarrierFromCoordinates
#print axioms exact_InstalledApplicationReport
#print axioms exact_InstalledMeasurePreserving
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof
