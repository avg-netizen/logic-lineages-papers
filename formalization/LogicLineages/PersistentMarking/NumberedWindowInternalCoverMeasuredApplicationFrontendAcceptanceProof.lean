module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z emb sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitter
  (addressGood arrowGood rawContext rawResult rawLeast rawDomain rawCodomain)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm addressReports arrowReports)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
  (reportUnfold reportInstance auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs applicationReport)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (inputsRename)
open NumberedWindowInternalSparseApplicationFrontendOpenShapeProof (assembleInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (row someRow supply)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)
open NumberedWindowInternalCoverCombinedMeasuredInstallProof (exact_InstalledApplicationReport)
open NumberedWindowInternalCoverMeasuredApplicationOutputAddressProof
  (exact_InstalledApplicationOutputAddress)
open NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceTargets

attribute [local irreducible] programGraph

/-- All nine parsed-input conjuncts of the original application row from the
two original operand reports alone. The arrow guard and the two arrow reports
come from the literal sparse cell `rawCons dom cod` in the function's result
slot; the three shell equations come from the accepted shape assembly. -/
private theorem parsedFromReports {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (qf qa ctx dom cod fn arg : OTerm α)
    (functionReport : Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)))
    (argumentReport : Nonempty (Derivation body Γ (addressReport qa ctx dom arg))) :
    Nonempty (Derivation body Γ
      (parsedApplicationInputs qf qa ctx (rawCons dom cod) dom cod fn arg)) := by
  obtain ⟨fr⟩ := functionReport
  obtain ⟨ar⟩ := argumentReport
  have leftShape : Derivation body Γ (unary addressGood (suc z) qf) :=
    Derivation.conjunctionLeft fr
  have leftContext : Derivation body Γ (unary rawContext ctx qf) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight fr)
  have leftResult : Derivation body Γ (unary rawResult (rawCons dom cod) qf) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight fr))
  have leftLeast : Derivation body Γ (unary rawLeast fn qf) :=
    Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight fr))
  have rightShape : Derivation body Γ (unary addressGood (suc z) qa) :=
    Derivation.conjunctionLeft ar
  have rightFields : Derivation body Γ (addressReports qa ctx dom arg) :=
    Derivation.conjunctionRight ar
  have leftFields : Derivation body Γ (addressReports qf ctx (rawCons dom cod) fn) :=
    Derivation.conjunctionIntroduction leftContext
      (Derivation.conjunctionIntroduction leftResult leftLeast)
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) dom cod
  have cellOk : Nonempty (Derivation body Γ (unary cellGood (suc z) (rawCons dom cod))) :=
    ⟨Derivation.conjunctionLeft cell⟩
  have cellDom : Nonempty (Derivation body Γ (unary cellHead dom (rawCons dom cod))) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have cellCod : Nonempty (Derivation body Γ (unary cellTail cod (rawCons dom cod))) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩
  have arrowShape : Nonempty (Derivation body Γ (unary arrowGood (suc z) qf)) :=
    makeUnary cellGood rawResult (suc z) qf (rawCons dom cod) cellOk ⟨leftResult⟩
  obtain ⟨domainField⟩ : Nonempty (Derivation body Γ (unary rawDomain dom qf)) :=
    makeUnary cellHead rawResult dom qf (rawCons dom cod) cellDom ⟨leftResult⟩
  obtain ⟨codomainField⟩ : Nonempty (Derivation body Γ (unary rawCodomain cod qf)) :=
    makeUnary cellTail rawResult cod qf (rawCons dom cod) cellCod ⟨leftResult⟩
  have arrowFields : Derivation body Γ (arrowReports qf dom cod) :=
    Derivation.conjunctionIntroduction domainField codomainField
  exact assembleInputs qf qa ctx (rawCons dom cod) dom cod fn arg
    ⟨leftShape⟩ ⟨rightShape⟩ arrowShape ⟨leftFields⟩ ⟨rightFields⟩ ⟨arrowFields⟩

/-- The original output report at the literal output address: the supplied
least call is the genuine single witness, and the address equation is
reflexivity. -/
private theorem outputFromLeast {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (least : Program 3) (ctx cod raw m : OTerm α)
    (selected : Nonempty (Derivation body Γ (programGraph least (suc m) ![ctx,cod,raw]))) :
    Nonempty (Derivation body Γ (outputReport least ctx cod raw (addressTerm ctx cod m))) := by
  obtain ⟨actual⟩ := selected
  rw [reportUnfold]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb m)
  rw [reportInstance]
  exact Derivation.conjunctionIntroduction actual (refl (addressTerm ctx cod m))

theorem exact_InstalledApplicationFrontendAcceptance :
    ExactInstalledApplicationFrontendAcceptance := by
  intro V TV M M0 B T base s cv tv root other body α Γ qf qa ctx dom cod fn arg goal Q
    syn ty result functionReport argumentReport functionAccepted argumentAccepted finish
  have inputs := parsedFromReports qf qa ctx dom cod fn arg functionReport argumentReport
  apply exact_InstalledApplicationOutputAddress V TV M M0 B T base s cv tv root other body α Γ
    qf qa ctx dom cod fn arg goal syn ty result functionReport argumentReport
    functionAccepted argumentAccepted
  intro β j Δ m keep least report accepted
  have inputs' := renameInto inputs j Δ keep
  rw [inputsRename] at inputs'
  have functionAccepted' := renameInto functionAccepted j Δ keep
  have argumentAccepted' := renameInto argumentAccepted j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at functionAccepted' argumentAccepted'
  have selected : Nonempty (Derivation body Δ
      (programGraph Q.least (suc m) ![ctx.relabel j,cod.relabel j,
        auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)])) := by
    have moved := least
    rw [auxiliaryRename] at moved
    exact moved
  have output := outputFromLeast Q.least (ctx.relabel j) (cod.relabel j)
    (auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)) m selected
  obtain ⟨inputs'⟩ := inputs'
  obtain ⟨output⟩ := output
  have bound : Nonempty (Derivation body Δ
      (someRow Q.least (qf.relabel j) (qa.relabel j)
        (addressTerm (ctx.relabel j) (cod.relabel j) m))) :=
    supply Q.least (qf.relabel j) (qa.relabel j) (addressTerm (ctx.relabel j) (cod.relabel j) m)
      (ctx.relabel j) ((rawCons dom cod).relabel j) (dom.relabel j) (cod.relabel j)
      (fn.relabel j) (arg.relabel j) ⟨Derivation.conjunctionIntroduction inputs' output⟩
  obtain ⟨bound⟩ := bound
  obtain ⟨functionAccepted'⟩ := functionAccepted'
  obtain ⟨argumentAccepted'⟩ := argumentAccepted'
  have reported : Derivation body Δ
      (applicationReport Q.scalar Q.least (qf.relabel j) (qa.relabel j)
        (addressTerm (ctx.relabel j) (cod.relabel j) m)) :=
    Derivation.conjunctionIntroduction functionAccepted'
      (Derivation.conjunctionIntroduction argumentAccepted' bound)
  obtain ⟨law⟩ := exact_InstalledApplicationReport V TV M M0 B T base s cv tv root other
    body β Δ (qf.relabel j) (qa.relabel j) (addressTerm (ctx.relabel j) (cod.relabel j) m)
  exact finish β j Δ m keep least report accepted
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight law) reported⟩

theorem exact_InstalledSyntaxGuardedApplicationFrontendAcceptance :
    ExactInstalledSyntaxGuardedApplicationFrontendAcceptance := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    syn ty functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨guards⟩ := syn
  exact exact_InstalledApplicationFrontendAcceptance V TV M M0 B T base s cv TV root other body α Γ
    qf qa ctx dom cod fn arg goal ⟨guards⟩ ty ⟨Derivation.conjunctionRight guards⟩
    functionReport argumentReport functionAccepted argumentAccepted finish

#print axioms exact_InstalledApplicationFrontendAcceptance
#print axioms exact_InstalledSyntaxGuardedApplicationFrontendAcceptance
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
