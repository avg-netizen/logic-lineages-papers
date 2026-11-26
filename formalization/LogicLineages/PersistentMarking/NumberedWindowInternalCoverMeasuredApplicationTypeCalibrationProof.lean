module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardOpenProof (exact_OpenSettingsRefitGuardReports)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)
open NumberedWindowInternalCoverCombinedMeasuredInstallProof (exact_InstalledCarrierCoordinates)
open NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
  (exact_InstalledApplicationOutputAddress)
open NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
  (exact_InstalledApplicationFrontendAcceptance)
open NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityProof
  (exact_InstalledApplicationOutputFunctionalityContinuation)
open NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets (ArrowCodomainInversion)
open NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets

attribute [local irreducible] programGraph

theorem exact_RefitGuardCodomainInversionFromComponents :
    ExactRefitGuardCodomainInversionFromComponents := by
  intro body s T inversionT inversionGrammar α Γ dom cod arrow
  obtain ⟨arrow⟩ := arrow
  have atArrow : Nonempty (Derivation body Γ
      (((unary (refitGuard s T) (suc z) (rawCons dom cod)).imp
          (unary T (suc z) (rawCons dom cod) ⊓
            memberGraph (numeral (Encodable.encode s.types)) (rawCons dom cod))) ⊓
        ((unary T (suc z) (rawCons dom cod) ⊓
            memberGraph (numeral (Encodable.encode s.types)) (rawCons dom cod)).imp
          (unary (refitGuard s T) (suc z) (rawCons dom cod))))) :=
    exact_OpenSettingsRefitGuardReports s T body α Γ (rawCons dom cod)
  have atCod : Nonempty (Derivation body Γ
      (((unary (refitGuard s T) (suc z) cod).imp
          (unary T (suc z) cod ⊓ memberGraph (numeral (Encodable.encode s.types)) cod)) ⊓
        ((unary T (suc z) cod ⊓ memberGraph (numeral (Encodable.encode s.types)) cod).imp
          (unary (refitGuard s T) (suc z) cod)))) :=
    exact_OpenSettingsRefitGuardReports s T body α Γ cod
  obtain ⟨atArrow⟩ := atArrow
  obtain ⟨atCod⟩ := atCod
  have reports := Derivation.implicationElimination (Derivation.conjunctionLeft atArrow) arrow
  obtain ⟨tCod⟩ := inversionT α Γ dom cod ⟨Derivation.conjunctionLeft reports⟩
  obtain ⟨gCod⟩ := inversionGrammar α Γ dom cod ⟨Derivation.conjunctionRight reports⟩
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight atCod)
    (Derivation.conjunctionIntroduction tCod gCod)⟩

theorem exact_RefittedInstalledApplicationTypeGuards :
    ExactRefittedInstalledApplicationTypeGuards := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg Q
    inversionTV inversionRefit functionReport argumentReport functionAccepted argumentAccepted
  obtain ⟨f⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv
    (refittedScalarType s TV T) root other body α Γ qf ctx (rawCons dom cod) fn
    functionReport functionAccepted
  obtain ⟨a⟩ := exact_InstalledCarrierCoordinates V TV M M0 B T base s cv
    (refittedScalarType s TV T) root other body α Γ qa ctx dom arg
    argumentReport argumentAccepted
  have arrowBoth : Nonempty (Derivation body Γ
      (programGraph (conjunction TV (refitGuard s T)) (suc z) ![rawCons dom cod])) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight f)⟩
  have domainBoth : Nonempty (Derivation body Γ
      (programGraph (conjunction TV (refitGuard s T)) (suc z) ![dom])) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight a)⟩
  obtain ⟨arrow⟩ := conjunctionRecover TV (refitGuard s T) ![rawCons dom cod] arrowBoth
  obtain ⟨domain⟩ := conjunctionRecover TV (refitGuard s T) ![dom] domainBoth
  have syntaxArrow : Derivation body Γ (unary TV (suc z) (rawCons dom cod)) :=
    Derivation.conjunctionLeft arrow
  have refitArrow : Derivation body Γ (unary (refitGuard s T) (suc z) (rawCons dom cod)) :=
    Derivation.conjunctionRight arrow
  have syntaxDomain : Derivation body Γ (unary TV (suc z) dom) :=
    Derivation.conjunctionLeft domain
  have refitDomain : Derivation body Γ (unary (refitGuard s T) (suc z) dom) :=
    Derivation.conjunctionRight domain
  obtain ⟨syntaxCodomain⟩ := inversionTV α Γ dom cod ⟨syntaxArrow⟩
  obtain ⟨refitCodomain⟩ := inversionRefit α Γ dom cod ⟨refitArrow⟩
  have own : Nonempty (Derivation body Γ
      (programGraph (conjunction TV (refitGuard s T)) (suc z) ![cod])) :=
    conjunctionAccept TV (refitGuard s T) ![cod] ⟨syntaxCodomain⟩ ⟨refitCodomain⟩
  exact ⟨⟨Derivation.conjunctionIntroduction syntaxDomain syntaxCodomain⟩,
    ⟨Derivation.conjunctionIntroduction refitDomain refitCodomain⟩, own⟩

theorem exact_RefittedInstalledApplicationOutputAddress :
    ExactRefittedInstalledApplicationOutputAddress := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    inversionTV inversionRefit functionReport argumentReport functionAccepted argumentAccepted
    finish
  obtain ⟨syn,ty,own⟩ := exact_RefittedInstalledApplicationTypeGuards V TV M M0 B T base s cv
    root other body α Γ qf qa ctx dom cod fn arg inversionTV inversionRefit functionReport
    argumentReport functionAccepted argumentAccepted
  exact exact_InstalledApplicationOutputAddress V TV M M0 B T base s cv
    (refittedScalarType s TV T) root other body α Γ qf qa ctx dom cod fn arg goal syn ty own
    functionReport argumentReport functionAccepted argumentAccepted finish

theorem exact_RefittedInstalledApplicationFrontendAcceptance :
    ExactRefittedInstalledApplicationFrontendAcceptance := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    inversionTV inversionRefit functionReport argumentReport functionAccepted argumentAccepted
    finish
  obtain ⟨syn,ty,own⟩ := exact_RefittedInstalledApplicationTypeGuards V TV M M0 B T base s cv
    root other body α Γ qf qa ctx dom cod fn arg inversionTV inversionRefit functionReport
    argumentReport functionAccepted argumentAccepted
  exact exact_InstalledApplicationFrontendAcceptance V TV M M0 B T base s cv
    (refittedScalarType s TV T) root other body α Γ qf qa ctx dom cod fn arg goal syn ty own
    functionReport argumentReport functionAccepted argumentAccepted finish

theorem exact_RefittedInstalledApplicationOutputFunctionalityContinuation :
    ExactRefittedInstalledApplicationOutputFunctionalityContinuation := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    inversionTV inversionRefit functionReport argumentReport functionAccepted argumentAccepted
    finish
  obtain ⟨syn,ty,own⟩ := exact_RefittedInstalledApplicationTypeGuards V TV M M0 B T base s cv
    root other body α Γ qf qa ctx dom cod fn arg inversionTV inversionRefit functionReport
    argumentReport functionAccepted argumentAccepted
  exact exact_InstalledApplicationOutputFunctionalityContinuation V TV M M0 B T base s cv
    (refittedScalarType s TV T) root other body α Γ qf qa ctx dom cod fn arg goal syn ty own
    functionReport argumentReport functionAccepted argumentAccepted finish

#print axioms exact_RefitGuardCodomainInversionFromComponents
#print axioms exact_RefittedInstalledApplicationTypeGuards
#print axioms exact_RefittedInstalledApplicationOutputAddress
#print axioms exact_RefittedInstalledApplicationFrontendAcceptance
#print axioms exact_RefittedInstalledApplicationOutputFunctionalityContinuation
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationProof
