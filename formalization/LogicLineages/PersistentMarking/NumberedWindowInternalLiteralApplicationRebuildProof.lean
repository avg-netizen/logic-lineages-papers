module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRebuildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm addressReports arrowReports)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs applicationReport)
open NumberedWindowInternalSparseApplicationFrontendOpenShapeProof (assembleInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (row someRow supply)
open NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof (backward)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportUnfold reportInstance)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)

attribute [local irreducible] programGraph

/-- All nine parsed-input conjuncts of the original application row from the
two original operand reports alone. The arrow guard and the two arrow reports
come from the literal sparse cell `rawCons dom cod` in the function's result
slot; the three shell equations come from the accepted shape assembly. -/
theorem exact_OpenApplicationParsedFromReports {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
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


variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Rebuild the ORIGINAL application acceptance from the actual two
operand addresses, their original scalar guards, and the original
least result on exactly the same function and unchanged argument.
The same proof works for any physically installed least program. -/
theorem exact_OpenLiteralApplicationFromReportedLeast (i : Program 1) (L : Program 3)
    (f u y ctx dom cod fn arg k : OTerm α)
    (fAddress : D B Γ (addressReport f ctx (rawCons dom cod) fn))
    (uAddress : D B Γ (addressReport u ctx dom arg))
    (fScalar : D B Γ (unary i (suc z) f)) (uScalar : D B Γ (unary i (suc z) u))
    (latest : D B Γ (programGraph L (suc k) ![ctx,cod,auxiliaryTerm dom cod fn arg]))
    (emitted : D B Γ (eqn y (addressTerm ctx cod k))) :
    D B Γ (programGraph (applicationGuard i L) (suc z) ![f,u,y]) := by
  let seed := auxiliaryTerm dom cod fn arg
  obtain ⟨p⟩ := exact_OpenApplicationParsedFromReports f u ctx dom cod fn arg fAddress uAddress
  have result : D B Γ (outputReport L ctx cod seed y) := by
    obtain ⟨raw⟩ := latest
    obtain ⟨eq⟩ := emitted
    rw [reportUnfold]
    apply Nonempty.intro
    apply Derivation.existentialIntroduction (emb k)
    rw [reportInstance]
    exact Derivation.conjunctionIntroduction raw eq
  obtain ⟨actual⟩ := result
  obtain ⟨chosen⟩ := supply L f u y ctx (rawCons dom cod) dom cod fn arg
    ⟨Derivation.conjunctionIntroduction p actual⟩
  obtain ⟨left⟩ := fScalar
  obtain ⟨right⟩ := uScalar
  exact backward i L f u y ⟨Derivation.conjunctionIntroduction left
    (Derivation.conjunctionIntroduction right chosen)⟩

#print axioms exact_OpenApplicationParsedFromReports
#print axioms exact_OpenLiteralApplicationFromReportedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRebuildProof
