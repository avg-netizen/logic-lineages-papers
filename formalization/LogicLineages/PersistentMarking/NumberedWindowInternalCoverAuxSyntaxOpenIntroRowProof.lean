module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenIntroRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection bothChildBounds)
open NumberedWindowInternalAuxMeasureStepTargets (childAt certain measureAt)
open NumberedWindowInternalAuxWindowOpenTargets (contextRow)
open NumberedWindowInternalStrictAuxWindowThinTableProof (earlierValue)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalCoverAuxSyntaxTargets (typeAt auxAccept auxSyntaxUpdate auxSyntaxChildren auxTape)
open NumberedWindowInternalCoverStrictAuxIntroduceShapeProof (actualAuxPhysicalData)

attribute [local irreducible] programGraph

/-- Introduction at the literal, already observed scratch row. Each of the
two recursive child reports uses this very same physical unary program. -/
theorem exact_OpenCoverAuxSyntaxIntroRow
    (V TV : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg old : OTerm α)
    (child : Nonempty (Derivation body Γ (auxSyntaxChildren V TV dom cod fn arg)))
    (table : Nonempty (Derivation body Γ (tableAt (auxSyntaxUpdate V TV) old
      (memoPrior dom cod fn arg)))) :
    Nonempty (Derivation body Γ
      (programGraph (auxSyntaxUpdate V TV) (suc z) (auxTape dom cod fn arg old))) := by
  let R : Program 4 := auxSyntaxUpdate V TV
  let prior := memoPrior dom cod fn arg
  let xs : Fin 4 → OTerm α := auxTape dom cod fn arg old
  obtain ⟨children⟩ := child
  have types := Derivation.conjunctionLeft children
  have terms := Derivation.conjunctionRight children
  have actual := actualAuxPhysicalData (body := body) (Γ := Γ) z dom cod fn arg old
  have order := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have domBit := unaryGraph TV (childAt 0) (suc z) dom xs ⟨Derivation.conjunctionLeft types⟩ actual.domain
  have codBit := unaryGraph TV (childAt 1) (suc z) cod xs ⟨Derivation.conjunctionRight types⟩ actual.codomain
  have fnRow : Nonempty (Derivation body Γ (contextRow R (suc z) fn z)) :=
    (projection R (suc z) fn).mp ⟨Derivation.conjunctionLeft terms⟩
  have argRow : Nonempty (Derivation body Γ (contextRow R (suc z) arg z)) :=
    (projection R (suc z) arg).mp ⟨Derivation.conjunctionRight terms⟩
  have fnBit := earlierValue R 2 fn (suc z) prior old z actual.function order.1 fnRow table
  have argBit := earlierValue R 3 arg (suc z) prior old z actual.argument order.2 argRow table
  let both := conjunction (measureAt 2) (measureAt 3)
  have reads := conjunctionAccept (measureAt 2) (measureAt 3) xs fnBit argBit
  have bothRead := conjunctionAccept (typeAt TV 1) both xs codBit reads
  have admitted := conjunctionAccept (typeAt TV 0) (conjunction (typeAt TV 1) both) xs domBit bothRead
  exact successorBranchIntro certain (unaryAfter V currentKey) (auxAccept TV)
    (suc z) z xs actual.bothEarlier admitted

#print axioms exact_OpenCoverAuxSyntaxIntroRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenIntroRowProof
