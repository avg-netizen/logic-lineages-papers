module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (certain shapeCheck childAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (bothChildBounds)
open NumberedWindowInternalAuxWindowStepTargets (admittedChildren functionCode argumentCode resultCode reportTest)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalCoverStrictAuxIntroduceShapeProof (actualAuxPhysicalData)
open NumberedWindowInternalCoverStrictAuxIntroduceChildProof (actualReportedAuxChild)
open NumberedWindowInternalCoverStrictAuxIntroduceTargets

theorem exact_OpenCoverStrictAuxIntroduceRow : ExactOpenCoverStrictAuxIntroduceRow := by
  intro B T body α Γ ctx dom cod fn arg old actual table
  let R := strictAuxUpdate B T
  let prior := memoPrior dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  obtain ⟨reports⟩ := actual
  have types := Derivation.conjunctionLeft reports
  have wins := Derivation.conjunctionRight reports
  have selected := actualAuxPhysicalData (body := body) (Γ := Γ) ctx dom cod fn arg old
  have order := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have domain := unaryGraph T (childAt 0) (suc z) dom xs ⟨Derivation.conjunctionLeft types⟩ selected.domain
  have codomain := unaryGraph T (childAt 1) (suc z) cod xs ⟨Derivation.conjunctionRight types⟩ selected.codomain
  have first := actualReportedAuxChild R functionCode 2 ctx prior old fn (rawCons dom cod)
    order.1 selected.function selected.fnCode table ⟨Derivation.conjunctionLeft wins⟩
  have second := actualReportedAuxChild R argumentCode 3 ctx prior old arg dom
    order.2 selected.argument selected.argCode table ⟨Derivation.conjunctionRight wins⟩
  let P := reportTest 2 functionCode
  let Q := reportTest 3 argumentCode
  let D := unaryAfter T (childAt 0)
  let C := unaryAfter T (childAt 1)
  have pair := conjunctionAccept P Q xs first second
  have typesAnd := conjunctionAccept C (conjunction P Q) xs codomain pair
  have admitted := conjunctionAccept D (conjunction C (conjunction P Q)) xs domain typesAnd
  have ok := conjunctionAccept certain (admittedChildren T) xs selected.bothEarlier admitted
  have positive : Nonempty (Derivation body Γ (programGraph (strictAuxPositive T) (suc cod) xs)) :=
    successorBranchIntro (conjunction certain (admittedChildren T)) (constantZero 4) resultCode
      (suc cod) z xs ok selected.result
  exact successorBranchIntro shapeCheck (binaryAfter B (.projection 2) currentKey) (strictAuxPositive T)
    (suc cod) z xs selected.shape positive

#print axioms exact_OpenCoverStrictAuxIntroduceRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceRowProof
