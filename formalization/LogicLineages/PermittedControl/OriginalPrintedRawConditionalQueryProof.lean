module
public import LogicLineages.PermittedControl.OriginalPrintedRawConditionalQueryTargets
import LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontendProof
import LogicLineages.PermittedControl.OriginalPrintedTypedExistentialSourceProof
import LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriverFuelProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawConditionalQuery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedRawFamilyFrontend (exactOriginalRawFamilyFrontend)
open OriginalPrintedTypedExistential (HasSuccessfulObservation literalFamily
  exactOriginalLiteralFamilyExistential exactOriginalTypedObservationExistential)
open ActualBitFamilyRawDriver (solve)
open ActualBitFamilyRawSemanticDriver (exactSemanticDriverSolve)

private theorem falseIff (b : Bool) : b = false ↔ ¬ b = true := by
  cases b <;> simp

private theorem notOpposite (f : Nat → Nat) (gs : List Gate) (p : NormalForm.Formula)
    (positive : Bool) :
    (¬ HasSuccessfulObservation f gs p (!positive)) ↔
      EverySuccessfulObservation f gs p positive := by
  constructor
  · intro h base b ok
    cases positive <;> cases b
    · rfl
    · exact False.elim (h ⟨base,ok⟩)
    · exact False.elim (h ⟨base,ok⟩)
    · rfl
  · intro h opp
    obtain ⟨base,ok⟩ := opp
    have eq := h base (!positive) ok
    cases positive <;> cases eq

theorem exactOriginalRawConditionalQuery : ExactOriginalRawConditionalQuery := by
  intro f B bound high children cert known gs p topo plain positive
  have yes (pol : Bool) :
      result f bound high (OriginalPrintedRawFamilyFrontend.encodeInput known gs p pol) = some true ↔
        HasSuccessfulObservation f gs p pol := by
    rw [result,exactOriginalRawFamilyFrontend,Option.map_some,Option.some.injEq]
    exact (exactSemanticDriverSolve f B bound high children cert (literalFamily known gs p pol)).trans
      ((exactOriginalLiteralFamilyExistential f known gs p plain pol).trans
        (exactOriginalTypedObservationExistential f known gs p topo plain pol))
  have no (pol : Bool) :
      result f bound high (OriginalPrintedRawFamilyFrontend.encodeInput known gs p pol) = some false ↔
        ¬ HasSuccessfulObservation f gs p pol := by
    have h := yes pol
    rw [result,exactOriginalRawFamilyFrontend,Option.map_some,Option.some.injEq] at h ⊢
    exact (falseIff _).trans (not_congr h)
  exact ⟨yes positive,no positive,(no (!positive)).trans (notOpposite f gs p positive)⟩

theorem exactOriginalRawQueryFailure : ExactOriginalRawQueryFailure := by
  intro f bound high p
  unfold result
  cases OriginalPrintedRawFamilyFrontend.familyCode p <;> simp

end LogicLineages.PermittedControl.OriginalPrintedRawConditionalQuery
