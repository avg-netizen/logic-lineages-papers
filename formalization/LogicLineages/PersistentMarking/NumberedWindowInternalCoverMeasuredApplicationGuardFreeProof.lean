module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationGuardFreeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)
open NumberedWindowInternalCoverCombinedMeasuredInstallProof (exact_InstalledCarrierCoordinates)
open NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
  (exact_InstalledSyntaxGuardedApplicationOutputAddress)
open NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
  (exact_InstalledSyntaxGuardedApplicationFrontendAcceptance)
open NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityProof
  (exact_InstalledSyntaxGuardedApplicationOutputFunctionalityContinuation)
open NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets

attribute [local irreducible] programGraph

theorem exact_TypeGuardArrowCalibrationFromComponents :
    ExactTypeGuardArrowCalibrationFromComponents := by
  intro body s TV T inversion refits α Γ dom cod arrow domain
  obtain ⟨codomain⟩ := inversion α Γ dom cod arrow
  obtain ⟨refitDomain⟩ := refits α Γ dom domain
  obtain ⟨refitCodomain⟩ := refits α Γ cod ⟨codomain⟩
  exact ⟨Derivation.conjunctionIntroduction codomain
    (Derivation.conjunctionIntroduction refitDomain refitCodomain)⟩

theorem exact_InstalledApplicationTypeGuards : ExactInstalledApplicationTypeGuards := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg Q
    calibration functionReport argumentReport functionAccepted argumentAccepted
  obtain ⟨f⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv TV root other
    body α Γ qf ctx (rawCons dom cod) fn functionReport functionAccepted
  obtain ⟨a⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv TV root other
    body α Γ qa ctx dom arg argumentReport argumentAccepted
  have arrow : Derivation body Γ (unary TV (suc z) (rawCons dom cod)) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight f)
  have domain : Derivation body Γ (unary TV (suc z) dom) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight a)
  obtain ⟨guards⟩ := calibration α Γ dom cod ⟨arrow⟩ ⟨domain⟩
  exact ⟨⟨Derivation.conjunctionIntroduction domain (Derivation.conjunctionLeft guards)⟩,
    ⟨Derivation.conjunctionRight guards⟩⟩

theorem exact_InstalledGuardFreeApplicationOutputAddress :
    ExactInstalledGuardFreeApplicationOutputAddress := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    calibration functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨syn,ty⟩ := exact_InstalledApplicationTypeGuards V TV M M0 B T base s cv root other
    body α Γ qf qa ctx dom cod fn arg calibration functionReport argumentReport
    functionAccepted argumentAccepted
  exact exact_InstalledSyntaxGuardedApplicationOutputAddress V TV M M0 B T base s cv root other
    body α Γ qf qa ctx dom cod fn arg goal syn ty functionReport argumentReport
    functionAccepted argumentAccepted finish

theorem exact_InstalledGuardFreeApplicationFrontendAcceptance :
    ExactInstalledGuardFreeApplicationFrontendAcceptance := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    calibration functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨syn,ty⟩ := exact_InstalledApplicationTypeGuards V TV M M0 B T base s cv root other
    body α Γ qf qa ctx dom cod fn arg calibration functionReport argumentReport
    functionAccepted argumentAccepted
  exact exact_InstalledSyntaxGuardedApplicationFrontendAcceptance V TV M M0 B T base s cv
    root other body α Γ qf qa ctx dom cod fn arg goal syn ty functionReport argumentReport
    functionAccepted argumentAccepted finish

theorem exact_InstalledGuardFreeApplicationOutputFunctionalityContinuation :
    ExactInstalledGuardFreeApplicationOutputFunctionalityContinuation := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    calibration functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨syn,ty⟩ := exact_InstalledApplicationTypeGuards V TV M M0 B T base s cv root other
    body α Γ qf qa ctx dom cod fn arg calibration functionReport argumentReport
    functionAccepted argumentAccepted
  exact exact_InstalledSyntaxGuardedApplicationOutputFunctionalityContinuation V TV M M0 B T
    base s cv root other body α Γ qf qa ctx dom cod fn arg goal syn ty functionReport
    argumentReport functionAccepted argumentAccepted finish

#print axioms exact_TypeGuardArrowCalibrationFromComponents
#print axioms exact_InstalledApplicationTypeGuards
#print axioms exact_InstalledGuardFreeApplicationOutputAddress
#print axioms exact_InstalledGuardFreeApplicationFrontendAcceptance
#print axioms exact_InstalledGuardFreeApplicationOutputFunctionalityContinuation
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationGuardFreeProof
